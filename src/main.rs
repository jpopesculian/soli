use std::{collections::HashMap, fmt::Debug, path::PathBuf, sync::atomic};

use ethabi::param_type::ParamType;
use ethers::core::types::Bytes;
use ethers_solc::{
    artifacts::{BytecodeObject, Contract, Source, Sources},
    Artifact, CompilerInput, Solc,
};
use revm::{CreateScheme, Database, InMemoryDB, Inspector, OpCode, TransactTo};
use semver::Version;
use solang_parser::{
    diagnostics::Diagnostic,
    pt::{self, CodeLocation},
};

#[derive(Clone, Copy, Ord, PartialOrd, Eq, PartialEq, Hash)]
struct Instruction {
    pub pc: usize,
    pub opcode: u8,
    pub data: [u8; 32],
    pub data_len: u8,
}

impl Instruction {
    fn data(&self) -> &[u8] {
        &self.data[..self.data_len as usize]
    }
}

impl Debug for Instruction {
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
            self.state = Some((eval, interp.stack.clone(), interp.memory.clone()));
        }
        eval
    }
}

#[derive(Debug, Clone)]
pub struct Compiled {
    contract: Contract,
    _source_unit_parts: Vec<pt::SourceUnitPart>,
    _contract_parts: Vec<pt::ContractPart>,
    statements: Vec<pt::Statement>,
    variable_definitions: HashMap<String, (pt::Expression, Option<pt::StorageLocation>)>,
}

#[derive(Debug, Clone)]
struct ConstructedSource<'a> {
    file_name: PathBuf,
    contract_name: String,
    solc: &'a Solc,
    pre_contract: String,
    pre_constructor: String,
    constructor: String,
    cached_compiled: Option<Compiled>,
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
            cached_compiled: None,
        }
    }

    fn insert_before_contract(&mut self, content: &str) -> &mut Self {
        self.pre_contract.push_str(content);
        self.cached_compiled = None;
        self
    }

    fn insert_before_constructor(&mut self, content: &str) -> &mut Self {
        self.pre_constructor.push_str(content);
        self.cached_compiled = None;
        self
    }

    fn insert_in_constructor(&mut self, content: &str) -> &mut Self {
        self.constructor.push_str(content);
        self.cached_compiled = None;
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

    fn compile_contract(&self) -> Result<Contract, Vec<Box<dyn std::fmt::Display>>> {
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

    fn compile_source(&mut self) -> Result<Compiled, Vec<Box<dyn std::fmt::Display>>> {
        if let Some(cached) = self.cached_compiled.as_ref() {
            return Ok(cached.clone());
        }
        let contract = self.compile_contract()?;

        let (source_unit_parts, contract_parts, statements) = self.parse_and_decompose().unwrap();

        let mut variable_definitions = HashMap::new();
        for (key, ty) in contract_parts.iter().flat_map(get_contract_part_definition) {
            variable_definitions.insert(
                key.to_string(),
                (ty.clone(), Some(pt::StorageLocation::Memory(ty.loc()))),
            );
        }
        for (key, ty, storage) in statements.iter().flat_map(get_statement_definitions) {
            variable_definitions.insert(key.to_string(), (ty.clone(), storage.cloned()));
        }

        let compiled = Compiled {
            contract,
            _source_unit_parts: source_unit_parts,
            _contract_parts: contract_parts,
            statements,
            variable_definitions,
        };
        self.cached_compiled = Some(compiled.clone());
        Ok(compiled)
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
) -> Vec<(&str, &pt::Expression, Option<&pt::StorageLocation>)> {
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

struct RunResult {
    _database: InMemoryDB,
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
                _database: database,
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
    let mut new_source = match insert_into_source(source, buffer) {
        Ok(new_source) => new_source,
        Err(buffer) => {
            return println!("Error: Failed to parse: `{}`", buffer.trim());
        }
    };
    let compiled = match new_source.compile_source() {
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

fn format_ethabi_token(token: &ethabi::Token, indent: usize) -> String {
    use ethabi::Token::*;
    match token {
        Address(address) => format!(
            "{} {}",
            Color::Cyan.paint("address"),
            Color::Red.paint(format!("0x{:x}", address))
        ),
        FixedBytes(bytes) | Bytes(bytes) => format!(
            "{} {}",
            Color::Cyan.paint("bytes"),
            Color::Red.paint(format!("0x{}", hex::encode(bytes)))
        ),
        Int(num) => format!(
            "{} {}",
            Color::Cyan.paint("int"),
            Color::Red.paint(format!("0x{:x}", num))
        ),
        Uint(num) => format!(
            "{} {}",
            Color::Cyan.paint("uint"),
            Color::Red.paint(format!("0x{:x}", num))
        ),
        Bool(boolean) => format!(
            "{} {}",
            Color::Cyan.paint("bool"),
            Color::Red.paint(format!("{}", boolean))
        ),
        String(string) => format!(
            "{} {}",
            Color::Cyan.paint("string"),
            Color::Green.paint(format!("{:?}", string))
        ),
        FixedArray(tokens) | Array(tokens) => {
            let mut out = format!("{}", Color::Cyan.paint("array"));
            out.push_str(" [\n");
            for token in tokens {
                out.push_str(&"  ".repeat(indent + 1));
                out.push_str(&format_ethabi_token(token, indent + 1));
                out.push_str(",\n");
            }
            out.push_str(&"  ".repeat(indent));
            out.push(']');
            out
        }
        Tuple(tokens) => {
            let mut out = format!("{}", Color::Cyan.paint("tuple"));
            out.push_str(" (\n");
            for token in tokens {
                out.push_str(&"  ".repeat(indent + 1));
                out.push_str(&format_ethabi_token(token, indent + 1));
                out.push_str(",\n");
            }
            out.push_str(&"  ".repeat(indent));
            out.push(')');
            out
        }
    }
}

fn inspect(source: &mut ConstructedSource, identifier: &str) {
    let compiled = match source.compile_source() {
        Ok(compiled) => compiled,
        Err(errors) => {
            for error in errors {
                println!("{error}");
            }
            return;
        }
    };
    let (ty, _) = if let Some(def) = compiled.variable_definitions.get(identifier) {
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

    let mut new_source = if let Ok(new_source) = insert_into_source(
        source,
        format!("bytes memory __inspect__ = abi.encode({identifier})"),
    ) {
        new_source
    } else {
        println!("Error: failed to compile instruction");
        return;
    };

    let compiled = match new_source.compile_source() {
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

    println!("{}", format_ethabi_token(&token, 0));
}

fn handle_cmd<'a>(
    source: &mut ConstructedSource,
    cmd: &str,
    mut args: impl Iterator<Item = &'a str>,
) {
    match cmd {
        "exit" => {
            println!();
            std::process::exit(0);
        }
        "print" => println!("{}", SolidityHelper::highlight(&source.to_string())),
        "clear" => {
            source.constructor = Default::default();
            source.cached_compiled = None;
            println!("Stack cleared");
        }
        "inspect" => {
            if let Some(ident) = args.next() {
                inspect(source, ident);
            } else {
                println!(r#"Expected identifier as argument. See "/help" for details"#);
            }
        }
        "help" => {
            println!(
                r#"
The following commands are available:

/inspect => inspect a variable by name (e.g. /inspect var)
/exit    => exit the repl
/print   => print the constructed source
/clear   => clear the current stack
"#
            );
        }
        _ => println!("Error: Command `{cmd}` not found"),
    }
}

use ansi_term::{Color, Style};
use rustyline::{
    completion::Completer,
    error::ReadlineError,
    highlight::Highlighter,
    hint::Hinter,
    validate::{ValidationContext, ValidationResult, Validator},
    Cmd, ConditionalEventHandler, Editor, Event, EventContext, EventHandler, Helper, KeyCode,
    KeyEvent, Modifiers, RepeatCount,
};
use solang_parser::lexer::{Lexer, LexicalError, Token};

struct CtrlCHandler {
    loaded: atomic::AtomicBool,
}

impl CtrlCHandler {
    fn bind_to<H: Helper>(editor: &mut Editor<H>) {
        editor.bind_sequence(
            Event::Any,
            EventHandler::Conditional(Box::new(Self {
                loaded: false.into(),
            })),
        );
    }
}

impl ConditionalEventHandler for CtrlCHandler {
    fn handle(
        &self,
        evt: &Event,
        _n: RepeatCount,
        _positive: bool,
        _ctx: &EventContext,
    ) -> Option<Cmd> {
        if let Some(KeyEvent(KeyCode::Char('C'), Modifiers::CTRL)) = evt.get(0) {
            let loaded = self.loaded.swap(true, atomic::Ordering::Relaxed);
            if loaded {
                return Some(Cmd::EndOfFile);
            }
        } else {
            self.loaded.store(false, atomic::Ordering::Relaxed);
        }
        None
    }
}

struct CmdLexer<'a> {
    input: &'a str,
    index: usize,
    last_token: Option<CmdToken<'a>>,
}

#[derive(Clone, Copy, Debug)]
enum CmdToken<'a> {
    Cmd(&'a str),
    Arg(&'a str),
}

impl<'a> CmdToken<'a> {
    fn as_str(&self) -> &'a str {
        match self {
            Self::Cmd(s) => s,
            Self::Arg(s) => s,
        }
    }
}

impl<'a> CmdLexer<'a> {
    fn new(input: &'a str) -> Self {
        let input_len = input.len();
        let index = if let Some(cmd) = input.trim_start().strip_prefix('/') {
            if !cmd.starts_with(['/', '*']) {
                input_len - cmd.len()
            } else {
                input_len
            }
        } else {
            input_len
        };
        Self {
            input,
            index,
            last_token: None,
        }
    }

    fn rest(&self) -> &str {
        &self.input[self.index..]
    }

    fn is_empty(&self) -> bool {
        self.rest().is_empty()
    }

    fn is_command(input: &str) -> bool {
        !CmdLexer::new(input).is_empty()
    }
}

impl<'a> Iterator for CmdLexer<'a> {
    type Item = (usize, CmdToken<'a>, usize);
    fn next(&mut self) -> Option<Self::Item> {
        if self.is_empty() {
            return None;
        }
        let start = self.index;
        let mut iter = self.rest().char_indices();
        let end = iter
            .find(|(_, ch)| ch.is_whitespace())
            .map(|(idx, _)| idx + start)
            .unwrap_or_else(|| self.input.len());
        self.index = iter
            .find(|(_, ch)| !ch.is_whitespace())
            .map(|(idx, _)| idx + start)
            .unwrap_or_else(|| self.input.len());
        let token = &self.input[start..end];
        let token = if self.last_token.is_some() {
            CmdToken::Arg(token)
        } else {
            CmdToken::Cmd(token)
        };
        self.last_token = Some(token);
        Some((start, token, end))
    }
}

pub trait TokenStyle {
    fn style(&self) -> Style;
}

impl<'a> TokenStyle for CmdToken<'a> {
    fn style(&self) -> Style {
        use CmdToken::*;
        match self {
            Cmd(_) => Color::Purple.into(),
            Arg(_) => Color::Blue.into(),
        }
    }
}

impl<'a> TokenStyle for Token<'a> {
    fn style(&self) -> Style {
        use Token::*;
        match self {
            StringLiteral(_, _) => Color::Green.into(),
            AddressLiteral(_)
            | HexLiteral(_)
            | Number(_, _)
            | RationalNumber(_, _, _)
            | HexNumber(_)
            | True
            | False
            | Seconds
            | Minutes
            | Hours
            | Days
            | Weeks
            | Gwei
            | Wei
            | Ether
            | This => Color::Red.into(),
            Memory | Storage | Calldata | Public | Private | Internal | External | Constant
            | Pure | View | Payable | Anonymous | Indexed | Abstract | Virtual | Override
            | Modifier | Immutable | Unchecked => Color::Blue.into(),
            Contract | Library | Interface | Function | Pragma | Import | Struct | Event
            | Error | Enum | Type | Constructor | As | Is | Using => Color::Yellow.into(),
            New | Delete | Do | Continue | Break | Throw | Emit | Return | Returns | Revert
            | For | While | If | Else | Try | Catch | Assembly | Let | Leave | Switch | Case
            | Default | YulArrow | Arrow => Color::Purple.into(),
            Uint(_) | Int(_) | Bytes(_) | Byte | DynamicBytes | Bool | Address | String
            | Mapping => Color::Cyan.into(),
            Identifier(_) => Style::new(),
            _ => Style::new(),
        }
    }
}

struct SolidityHelper;

impl SolidityHelper {
    fn validate_closed(input: &str) -> ValidationResult {
        if CmdLexer::is_command(input) {
            return ValidationResult::Valid(None);
        }
        let mut bracket_depth = 0usize;
        let mut paren_depth = 0usize;
        let mut brace_depth = 0usize;
        let mut comments = Vec::new();
        for res in Lexer::new(input, 0, &mut comments) {
            match res {
                Err(err) => match err {
                    LexicalError::EndOfFileInComment(_)
                    | LexicalError::EndofFileInHex(_)
                    | LexicalError::EndOfFileInString(_) => return ValidationResult::Incomplete,
                    _ => return ValidationResult::Valid(None),
                },
                Ok((_, token, _)) => match token {
                    Token::OpenBracket => {
                        bracket_depth = bracket_depth.saturating_add(1);
                    }
                    Token::OpenCurlyBrace => {
                        brace_depth = brace_depth.saturating_add(1);
                    }
                    Token::OpenParenthesis => {
                        paren_depth = paren_depth.saturating_add(1);
                    }
                    Token::CloseBracket => {
                        bracket_depth = bracket_depth.saturating_sub(1);
                    }
                    Token::CloseCurlyBrace => {
                        brace_depth = brace_depth.saturating_sub(1);
                    }
                    Token::CloseParenthesis => {
                        paren_depth = paren_depth.saturating_sub(1);
                    }
                    _ => {}
                },
            }
        }
        if (bracket_depth | brace_depth | paren_depth) == 0 {
            ValidationResult::Valid(None)
        } else {
            ValidationResult::Incomplete
        }
    }

    fn get_styles(input: &str) -> Vec<(usize, Style, usize)> {
        let cmd_lexer = CmdLexer::new(input);
        if !cmd_lexer.is_empty() {
            cmd_lexer
                .map(|(start, token, end)| (start, token.style(), end))
                .collect()
        } else {
            let mut comments = Vec::new();
            let mut out = Lexer::new(input, 0, &mut comments)
                .flatten()
                .map(|(start, token, end)| (start, token.style(), end))
                .collect::<Vec<_>>();
            for comment in comments {
                let loc = match comment {
                    pt::Comment::Line(loc, _) => loc,
                    pt::Comment::Block(loc, _) => loc,
                    pt::Comment::DocLine(loc, _) => loc,
                    pt::Comment::DocBlock(loc, _) => loc,
                };
                out.push((loc.start(), Style::new().dimmed(), loc.end()))
            }
            out
        }
    }

    fn get_contiguous_styles(input: &str) -> Vec<(usize, Style, usize)> {
        let mut styles = Self::get_styles(input);
        styles.sort_by_key(|(start, _, _)| *start);
        let mut out = vec![];
        let mut index = 0;
        for (start, style, end) in styles {
            if index < start {
                out.push((index, Style::new(), start));
            }
            out.push((start, style, end));
            index = end;
        }
        if index < input.len() {
            out.push((index, Style::new(), input.len()));
        }
        out
    }

    fn highlight(input: &str) -> String {
        let mut out = String::new();
        for (start, style, end) in Self::get_contiguous_styles(input) {
            out.push_str(&format!("{}", style.paint(&input[start..end])))
        }
        out
    }
}

impl Validator for SolidityHelper {
    fn validate(&self, ctx: &mut ValidationContext) -> rustyline::Result<ValidationResult> {
        Ok(Self::validate_closed(ctx.input()))
    }
}

impl Highlighter for SolidityHelper {
    fn highlight<'l>(&self, line: &'l str, _pos: usize) -> std::borrow::Cow<'l, str> {
        std::borrow::Cow::Owned(Self::highlight(line))
    }
    fn highlight_char(&self, line: &str, pos: usize) -> bool {
        pos == line.len()
    }
}

impl Completer for SolidityHelper {
    type Candidate = String;
}

impl Hinter for SolidityHelper {
    type Hint = String;
}

impl Helper for SolidityHelper {}

pub struct Console {
    editor: Editor<SolidityHelper>,
}

impl Console {
    pub fn new() -> rustyline::Result<Self> {
        let mut editor = Editor::new()?;
        CtrlCHandler::bind_to(&mut editor);
        editor.set_helper(Some(SolidityHelper));
        Ok(Console { editor })
    }

    pub fn readline(&mut self) -> rustyline::Result<String> {
        loop {
            let line = self.editor.readline("> ");
            match line {
                Ok(line) => {
                    if line.trim().is_empty() {
                        continue;
                    }
                    self.editor.history_mut().add(&line);
                    return Ok(line);
                }
                Err(err) => match err {
                    ReadlineError::Interrupted => {
                        println!(
                            "{}",
                            Style::new().dimmed().paint(
                                r#"(To exit, press Ctrl+C again or Ctrl+D or type "/exit")"#
                            )
                        );
                    }
                    err => return Err(err),
                },
            }
        }
    }
}

fn main() -> rustyline::Result<()> {
    let solc = Solc::default();
    println!("solc {}", solc.version().expect("Solc version unavailable"));
    println!(r#"Type "/help" for more information"#);

    let mut source = ConstructedSource::new(&solc);
    let mut console = Console::new()?;
    loop {
        match console.readline() {
            Ok(mut line) => {
                let mut cmd_lexer = CmdLexer::new(&line);
                if !cmd_lexer.is_empty() {
                    let cmd = cmd_lexer.next().unwrap().1.as_str();
                    let args = cmd_lexer.map(|(_, arg, _)| arg.as_str());
                    handle_cmd(&mut source, cmd, args);
                } else {
                    let compiled = match source.compile_source() {
                        Ok(compiled) => compiled,
                        Err(errors) => {
                            for error in errors {
                                println!("{error}");
                            }
                            continue;
                        }
                    };
                    if compiled.variable_definitions.contains_key(&line) {
                        handle_cmd(&mut source, "inspect", [line.as_str()].into_iter())
                    } else {
                        if !line.ends_with('\n') {
                            line.push('\n');
                        }
                        handle_line(&mut source, line)
                    }
                }
            }
            Err(err) => match err {
                ReadlineError::Eof => {
                    std::process::exit(0);
                }
                err => {
                    println!("{err}");
                    std::process::exit(1);
                }
            },
        };
    }
}
