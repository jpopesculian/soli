use std::{collections::HashMap, fmt::Debug, io::Write, path::PathBuf};

use ethabi::{ethereum_types::U256, param_type::ParamType};
use ethers::core::types::Bytes;
use ethers_solc::{
    artifacts::{BytecodeObject, Contract, Source, Sources},
    Artifact, CompilerInput, Solc,
};
use revm::{CreateScheme, Database, InMemoryDB, Inspector, OpCode, TransactTo};
use semver::Version;
use solang_parser::{
    diagnostics::Diagnostic,
    pt::{self, CodeLocation, StorageLocation},
};

#[derive(Clone, Copy, Ord, PartialOrd, Eq, PartialEq, Hash)]
struct Instruction {
    pub pc: usize,
    pub opcode: u8,
    pub data: [u8; 32],
    pub data_len: u8,
}

impl<'a> Instruction {
    fn data(&self) -> &[u8] {
        &self.data[..self.data_len as usize]
    }
}

impl<'a> Debug for Instruction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Instruction")
            .field("pc", &self.pc)
            .field(
                "opcode",
                &format_args!(
                    "{}",
                    OpCode::try_from_u8(self.opcode)
                        .map(|op| op.as_str().to_owned())
                        .unwrap_or_else(|| format!("0x{}", hex::encode(&[self.opcode])))
                ),
            )
            .field("data", &format_args!("0x{}", hex::encode(self.data())))
            .finish()
    }
}

struct InstructionIter<'a> {
    bytes: &'a [u8],
    offset: usize,
}

impl<'a> InstructionIter<'a> {
    pub fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, offset: 0 }
    }
}

impl<'a> Iterator for InstructionIter<'a> {
    type Item = Instruction;
    fn next(&mut self) -> Option<Self::Item> {
        let pc = self.offset;
        self.offset += 1;
        let opcode = *self.bytes.get(pc)?;
        let (data, data_len) = if matches!(opcode, 0x60..=0x7F) {
            let mut data = [0; 32];
            let data_len = (opcode - 0x60 + 1) as usize;
            data[..data_len].copy_from_slice(&self.bytes[self.offset..self.offset + data_len]);
            self.offset += data_len;
            (data, data_len as u8)
        } else {
            ([0; 32], 0)
        };
        Some(Instruction {
            pc,
            opcode,
            data,
            data_len,
        })
    }
}

pub trait ArtifactExt: Artifact {
    fn get_init_bytecode_bytes(&self) -> Option<Bytes> {
        let bytecode_bytes = self.get_bytecode_bytes()?;
        let deployed_bytes = self.get_deployed_bytecode_bytes()?;
        Some(
            bytecode_bytes[..bytecode_bytes.len() - deployed_bytes.len()]
                .to_vec()
                .into(),
        )
    }
    fn get_init_bytecode_object(&self) -> Option<BytecodeObject> {
        Some(BytecodeObject::Bytecode(self.get_init_bytecode_bytes()?))
    }
}
impl<T> ArtifactExt for T where T: Artifact {}

struct Logger {
    last_instruction: usize,
    state: Option<(revm::Return, revm::Stack, revm::Memory)>,
}

impl Logger {
    fn new(last_instruction: usize) -> Self {
        Self {
            last_instruction,
            state: None,
        }
    }
}

impl<DB> Inspector<DB> for Logger
where
    DB: Database + std::fmt::Debug,
{
    fn step_end(
        &mut self,
        interp: &mut revm::Interpreter,
        _data: &mut revm::EVMData<'_, DB>,
        _is_static: bool,
        eval: revm::Return,
    ) -> revm::Return {
        if interp.program_counter() - 1 == self.last_instruction {
            self.state = Some((eval.clone(), interp.stack.clone(), interp.memory.clone()));
        }
        eval
    }
}

#[derive(Debug, Clone)]
struct ConstructedSource<'a> {
    file_name: PathBuf,
    contract_name: String,
    solc: &'a Solc,
    pre_contract: String,
    pre_constructor: String,
    constructor: String,
}

impl<'a> ConstructedSource<'a> {
    fn new(solc: &'a Solc) -> Self {
        assert!(solc.version().is_ok());
        Self {
            file_name: PathBuf::from("__ReplContract.sol".to_string()),
            contract_name: "__ReplContract".to_string(),
            solc,
            pre_constructor: Default::default(),
            pre_contract: Default::default(),
            constructor: Default::default(),
        }
    }

    fn insert_before_contract(&mut self, content: &str) -> &mut Self {
        self.pre_contract.push_str(content);
        self
    }

    fn insert_before_constructor(&mut self, content: &str) -> &mut Self {
        self.pre_constructor.push_str(content);
        self
    }

    fn insert_in_constructor(&mut self, content: &str) -> &mut Self {
        self.constructor.push_str(content);
        self
    }

    fn compiler_input(&self) -> CompilerInput {
        let mut sources = Sources::new();
        sources.insert(
            self.file_name.clone(),
            Source {
                content: self.to_string(),
            },
        );
        CompilerInput::with_sources(sources).pop().unwrap()
    }

    fn parse_tree(&self) -> Result<pt::SourceUnit, Vec<Diagnostic>> {
        solang_parser::parse(&self.to_string(), 0).map(|(pt, _)| pt)
    }

    fn decompose(
        &self,
        parse_tree: pt::SourceUnit,
    ) -> Option<(
        Vec<pt::SourceUnitPart>,
        Vec<pt::ContractPart>,
        Vec<pt::Statement>,
    )> {
        let mut source_unit_parts = parse_tree.0;
        if !matches!(
            source_unit_parts.get(0),
            Some(pt::SourceUnitPart::PragmaDirective(..))
        ) {
            return None;
        }
        source_unit_parts.remove(0);

        let mut contract_parts = match source_unit_parts.pop()? {
            pt::SourceUnitPart::ContractDefinition(contract) => {
                if contract.name.name == self.contract_name {
                    Some(contract.parts)
                } else {
                    None
                }
            }
            _ => None,
        }?;

        let statements = match contract_parts.pop()? {
            pt::ContractPart::FunctionDefinition(func) => {
                if !matches!(func.ty, pt::FunctionTy::Constructor) {
                    return None;
                }
                match func.body? {
                    pt::Statement::Block { statements, .. } => Some(statements),
                    _ => None,
                }
            }
            _ => None,
        }?;
        Some((source_unit_parts, contract_parts, statements))
    }

    fn parse_and_decompose(
        &self,
    ) -> Option<(
        Vec<pt::SourceUnitPart>,
        Vec<pt::ContractPart>,
        Vec<pt::Statement>,
    )> {
        self.parse_tree()
            .ok()
            .and_then(|parse_tree| self.decompose(parse_tree))
    }

    fn compile(&self) -> Result<Contract, Vec<Box<dyn std::fmt::Display>>> {
        let mut compiled = match self.solc.compile_exact(&self.compiler_input()) {
            Ok(compiled) => compiled,
            Err(err) => return Err(vec![Box::new(err)]),
        };
        let errors = compiled
            .errors
            .into_iter()
            .filter(|error| error.severity.is_error())
            .map(|error| Box::new(error) as Box<dyn std::fmt::Display>)
            .collect::<Vec<_>>();
        if !errors.is_empty() {
            return Err(errors);
        }
        Ok(compiled
            .contracts
            .remove(&self.file_name.display().to_string())
            .unwrap()
            .remove(&self.contract_name)
            .unwrap())
    }
}

impl<'a> std::fmt::Display for ConstructedSource<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("// SPDX-License-Identifier: UNLICENSED\n")?;
        let Version {
            major,
            minor,
            patch,
            ..
        } = self.solc.version().unwrap();
        f.write_fmt(format_args!("pragma solidity ^{major}.{minor}.{patch};\n",))?;
        f.write_str(&self.pre_contract)?;
        f.write_fmt(format_args!("contract {} {{\n", self.contract_name))?;
        f.write_str(&self.pre_constructor)?;
        f.write_str("constructor() {\n")?;
        f.write_str(&self.constructor)?;
        f.write_str("}\n}")?;
        Ok(())
    }
}

fn parse_identifier(input: &str) -> (&str, &str) {
    let mut iter = input.char_indices();
    let mut end = 0;
    if let Some((idx, ch)) = iter.next() {
        match ch {
            'a'..='z' | 'A'..='Z' | '$' | '_' => {
                end = idx + 1;
            }
            _ => return input.split_at(end),
        }
    }
    for (idx, ch) in iter {
        match ch {
            'a'..='z' | 'A'..='Z' | '0'..='9' | '$' | '_' => {
                end = idx + 1;
            }
            _ => return input.split_at(end),
        }
    }
    input.split_at(end)
}

#[derive(Debug)]
pub enum ParseTreeFragment {
    Source(Vec<pt::SourceUnitPart>),
    Contract(Vec<pt::ContractPart>),
    Function(Vec<pt::Statement>),
}

pub fn parse_fragment(solc: &Solc, buffer: &str) -> Option<ParseTreeFragment> {
    let base = ConstructedSource::new(solc);

    if let Some((_, _, statements)) = base
        .clone()
        .insert_in_constructor(buffer)
        .parse_and_decompose()
    {
        return Some(ParseTreeFragment::Function(statements));
    }
    if let Some((_, contract_parts, _)) = base
        .clone()
        .insert_before_constructor(buffer)
        .parse_and_decompose()
    {
        return Some(ParseTreeFragment::Contract(contract_parts));
    }
    if let Some((source_unit_parts, _, _)) = base
        .clone()
        .insert_before_contract(buffer)
        .parse_and_decompose()
    {
        return Some(ParseTreeFragment::Source(source_unit_parts));
    }

    None
}

#[derive(Debug, Clone)]
enum Type {
    Builtin(ParamType),
    Array(Box<Type>),
    FixedArray(Box<Type>, usize),
    Map(Box<Type>, Box<Type>),
    Custom(Vec<String>),
}

impl Type {
    fn from_expression(expr: &pt::Expression) -> Option<Self> {
        Some(match expr {
            pt::Expression::Type(_, ty) => match ty {
                pt::Type::Address | pt::Type::AddressPayable | pt::Type::Payable => {
                    Type::Builtin(ParamType::Address)
                }
                pt::Type::Bool => Type::Builtin(ParamType::Bytes),
                pt::Type::String => Type::Builtin(ParamType::String),
                pt::Type::Int(size) => Type::Builtin(ParamType::Int(*size as usize)),
                pt::Type::Uint(size) => Type::Builtin(ParamType::Uint(*size as usize)),
                pt::Type::Bytes(size) => Type::Builtin(ParamType::FixedBytes(*size as usize)),
                pt::Type::DynamicBytes => Type::Builtin(ParamType::Bytes),
                pt::Type::Mapping(_, left, right) => Self::Map(
                    Box::new(Type::from_expression(left)?),
                    Box::new(Type::from_expression(right)?),
                ),
                pt::Type::Function { .. } => Type::Custom(vec!["[Function]".to_string()]),
                pt::Type::Rational => Type::Custom(vec!["[Rational]".to_string()]),
            },
            pt::Expression::Variable(ident) => Type::Custom(vec![ident.name.clone()]),
            pt::Expression::ArraySubscript(_, expr, num) => {
                let num = num.as_ref().and_then(|num| {
                    if let pt::Expression::NumberLiteral(_, num, exp) = num.as_ref() {
                        let num = if num.is_empty() {
                            0usize
                        } else {
                            num.parse().ok()?
                        };
                        let exp = if exp.is_empty() {
                            0u32
                        } else {
                            exp.parse().ok()?
                        };
                        Some(num * 10usize.pow(exp))
                    } else {
                        None
                    }
                });
                let ty = Type::from_expression(expr)?;
                if let Some(num) = num {
                    Self::FixedArray(Box::new(ty), num)
                } else {
                    Self::Array(Box::new(ty))
                }
            }
            pt::Expression::MemberAccess(_, expr, ident) => {
                let mut out = vec![ident.name.clone()];
                let mut cur_expr = expr;
                while let pt::Expression::MemberAccess(_, expr, ident) = cur_expr.as_ref() {
                    out.insert(0, ident.name.clone());
                    cur_expr = expr;
                }
                if let pt::Expression::Variable(ident) = cur_expr.as_ref() {
                    out.insert(0, ident.name.clone());
                }
                Type::Custom(out)
            }
            _ => return None,
        })
    }

    fn as_ethabi(&self) -> Option<ParamType> {
        match self {
            Self::Builtin(param) => Some(param.clone()),
            Self::Array(inner) => inner
                .as_ethabi()
                .map(|inner| ParamType::Array(Box::new(inner))),
            Self::FixedArray(inner, size) => inner
                .as_ethabi()
                .map(|inner| ParamType::FixedArray(Box::new(inner), *size)),
            _ => None,
        }
    }
}

fn get_contract_part_definition(
    contract_part: &pt::ContractPart,
) -> Option<(&str, &pt::Expression)> {
    match contract_part {
        pt::ContractPart::VariableDefinition(var_def) => Some((&var_def.name.name, &var_def.ty)),
        _ => None,
    }
}

fn get_statement_definitions(
    statement: &pt::Statement,
) -> Vec<(&str, &pt::Expression, Option<&StorageLocation>)> {
    match statement {
        pt::Statement::VariableDefinition(_, def, _) => {
            vec![(def.name.name.as_str(), &def.ty, def.storage.as_ref())]
        }
        pt::Statement::Expression(_, pt::Expression::Assign(_, left, _)) => {
            if let pt::Expression::List(_, list) = left.as_ref() {
                list.iter()
                    .filter_map(|(_, param)| {
                        param.as_ref().and_then(|param| {
                            param
                                .name
                                .as_ref()
                                .map(|name| (name.name.as_str(), &param.ty, None))
                        })
                    })
                    .collect()
            } else {
                vec![]
            }
        }
        _ => vec![],
    }
}

fn insert_into_source<'a>(
    source: &ConstructedSource<'a>,
    mut buffer: String,
) -> Result<ConstructedSource<'a>, String> {
    let parsed_fragment = if let Some(parsed) = parse_fragment(source.solc, &buffer)
        .or_else(|| {
            buffer = buffer.trim_end().to_string();
            buffer.push_str(";\n");
            parse_fragment(source.solc, &buffer)
        })
        .or_else(|| {
            buffer = buffer.trim_end().trim_end_matches(';').to_string();
            buffer.push('\n');
            parse_fragment(source.solc, &buffer)
        }) {
        parsed
    } else {
        return Err(buffer.trim().to_string());
    };

    let mut new_source = source.clone();
    match parsed_fragment {
        ParseTreeFragment::Source(_) => {
            new_source.insert_before_contract(&buffer);
        }
        ParseTreeFragment::Contract(_) => {
            new_source.insert_before_constructor(&buffer);
        }
        ParseTreeFragment::Function(_) => {
            new_source.insert_in_constructor(&buffer);
        }
    };
    Ok(new_source)
}

pub struct Compiled {
    contract: Contract,
    source_unit_parts: Vec<pt::SourceUnitPart>,
    contract_parts: Vec<pt::ContractPart>,
    statements: Vec<pt::Statement>,
    variable_definitions: HashMap<String, (pt::Expression, Option<StorageLocation>)>,
}

fn compile_source<'a>(
    source: &ConstructedSource<'a>,
) -> Result<Compiled, Vec<Box<dyn std::fmt::Display>>> {
    let contract = source.compile()?;

    let (source_unit_parts, contract_parts, statements) = source.parse_and_decompose().unwrap();

    let mut variable_definitions = HashMap::new();
    for (key, ty) in contract_parts.iter().flat_map(get_contract_part_definition) {
        variable_definitions.insert(
            key.to_string(),
            (ty.clone(), Some(StorageLocation::Memory(ty.loc()))),
        );
    }
    for (key, ty, storage) in statements.iter().flat_map(get_statement_definitions) {
        variable_definitions.insert(key.to_string(), (ty.clone(), storage.cloned()));
    }

    Ok(Compiled {
        contract,
        source_unit_parts,
        contract_parts,
        statements,
        variable_definitions,
    })
}

struct RunResult {
    database: InMemoryDB,
    stack: revm::Stack,
    memory: revm::Memory,
}

fn run_compiled(compiled: &Compiled) -> Result<RunResult, revm::Return> {
    let init_bytecode_bytes = compiled.contract.get_init_bytecode_bytes().unwrap();

    let last_statement = compiled.statements.last().unwrap();
    let last_instruction = {
        let end_loc = last_statement.loc();
        let offset = end_loc.start();
        let length = end_loc.end() - end_loc.start();
        compiled
            .contract
            .get_source_map()
            .unwrap()
            .unwrap()
            .into_iter()
            .zip(InstructionIter::new(&init_bytecode_bytes))
            .filter(|(s, _)| s.offset == offset && s.length == length)
            .map(|(_, i)| i.pc)
            .max()
            .unwrap_or_default()
    };

    let mut database = InMemoryDB::default();
    let mut logger = Logger::new(last_instruction);

    let mut evm = revm::new();
    evm.database(&mut database);

    evm.env.tx.caller = "0x1000000000000000000000000000000000000000"
        .parse()
        .unwrap();
    evm.env.tx.transact_to = TransactTo::Create(CreateScheme::Create2 {
        salt: Default::default(),
    });
    evm.env.tx.data = init_bytecode_bytes.to_vec().into();

    let (ret, ..) = evm.inspect(&mut logger);

    if let Some(res) = logger.state {
        match res.0 {
            revm::Return::Continue => Ok(RunResult {
                database,
                stack: res.1,
                memory: res.2,
            }),
            res => Err(res),
        }
    } else {
        Err(ret)
    }
}

fn handle_line(source: &mut ConstructedSource, buffer: String) {
    let new_source = match insert_into_source(source, buffer) {
        Ok(new_source) => new_source,
        Err(buffer) => {
            return println!("Error: Failed to parse: `{}`", buffer.trim());
        }
    };
    let compiled = match compile_source(&new_source) {
        Ok(compiled) => compiled,
        Err(errors) => {
            for error in errors {
                println!("{error}");
            }
            return;
        }
    };
    if !compiled.statements.is_empty() {
        if let Err(ret) = run_compiled(&compiled) {
            println!("Error: Failed to run: {ret:?}");
            return;
        };
    }

    *source = new_source;
}

fn inspect(source: &ConstructedSource, identifier: &str) {
    let (source_unit_parts, contract_parts, statements) = source.parse_and_decompose().unwrap();

    let mut variable_definitions = HashMap::new();
    for (key, ty) in contract_parts.iter().flat_map(get_contract_part_definition) {
        variable_definitions.insert(
            key.to_string(),
            (ty.clone(), Some(StorageLocation::Memory(ty.loc()))),
        );
    }
    for (key, ty, storage) in statements.iter().flat_map(get_statement_definitions) {
        variable_definitions.insert(key.to_string(), (ty.clone(), storage.cloned()));
    }

    let (ty, _) = if let Some(def) = variable_definitions.get(identifier) {
        def
    } else {
        println!("Error: `{identifier}` could not be found");
        return;
    };
    let ty = if let Some(ty) = Type::from_expression(ty).and_then(|ty| ty.as_ethabi()) {
        ty
    } else {
        println!("Error: Identifer type currently not supported");
        return;
    };

    let new_source = if let Ok(new_source) = insert_into_source(
        source,
        format!("bytes memory __inspect__ = abi.encode({identifier})"),
    ) {
        new_source
    } else {
        println!("Error: failed to compile instruction");
        return;
    };

    let compiled = match compile_source(&new_source) {
        Ok(compiled) => compiled,
        Err(errors) => {
            for error in errors {
                println!("{error}");
            }
            return;
        }
    };

    let res = match run_compiled(&compiled) {
        Ok(res) => res,
        Err(ret) => {
            println!("Error: failed to run instruction: {ret:?}");
            return;
        }
    };

    let memory_offset = if let Some(offset) = res.stack.data().last() {
        offset.as_usize()
    } else {
        println!("Error: No result found");
        return;
    };
    if memory_offset + 32 > res.memory.len() {
        println!("Error: Memory size insufficient");
        return;
    }
    let data = &res.memory.data()[memory_offset + 32..];
    let token = match ethabi::decode(&[ty], data) {
        Ok(mut tokens) => {
            if let Some(token) = tokens.pop() {
                token
            } else {
                println!("Error: No tokens decoded");
                return;
            }
        }
        Err(err) => {
            println!("Error: Could not decode ABI: {err}");
            return;
        }
    };

    match serde_json::to_string_pretty(&token) {
        Ok(res) => println!("{res}"),
        Err(err) => println!("Error: Could not serialize token: {err}"),
    }
}

fn handle_cmd(source: &mut ConstructedSource, cmd: &str) {
    let (cmd, params) = cmd.split_once(' ').unwrap_or((cmd, ""));
    match cmd {
        "quit" => std::process::exit(0),
        "print" => println!("{source}"),
        "clear" => {
            source.constructor = Default::default();
            println!("Stack cleared");
        }
        "inspect" => {
            inspect(source, params.trim());
        }
        "help" => {
            println!(
                r#"
The following commands are available:

/inspect => inspect a variable by name (e.g. /inspect var)
/quit    => quit the repl
/print   => print the compiled source
/clear   => clear the current stack
"#
            );
        }
        _ => println!("Error: Command `{cmd}` not found"),
    }
}

fn main() {
    let solc = Solc::default();
    println!("solc {}", solc.version().unwrap());
    let mut source = ConstructedSource::new(&solc);
    loop {
        std::io::stdout().write_all(b">>> ").unwrap();
        std::io::stdout().flush().unwrap();
        let mut buffer = String::new();
        std::io::stdin().read_line(&mut buffer).unwrap();
        let buffer_trimmed = buffer.trim();
        if buffer_trimmed.is_empty() || buffer_trimmed.trim_end_matches(';').is_empty() {
            continue;
        }

        if let Some(cmd) = buffer_trimmed.strip_prefix('/') {
            if !cmd.starts_with(['/', '*']) {
                handle_cmd(&mut source, cmd.trim());
                continue;
            }
        }

        handle_line(&mut source, buffer)
    }
}
