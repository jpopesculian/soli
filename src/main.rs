use std::{
    collections::{hash_map, HashMap},
    fmt::Debug,
    io::Write,
    path::PathBuf,
};

use ethers::core::types::Bytes;
use ethers_solc::{
    artifacts::{BytecodeObject, Contract, Source, Sources},
    Artifact, CompilerInput, Solc,
};
use primitive_types::U256;
use revm::{CreateScheme, Database, InMemoryDB, Inspector, OpCode, TransactTo};
use semver::Version;
use solang_parser::{
    diagnostics::Diagnostic,
    pt::{self, CodeLocation, Loc, StorageLocation},
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

#[derive(Debug)]
struct Logger {
    instructions: HashMap<Loc, Vec<Instruction>>,
    stack: HashMap<Loc, Vec<Option<U256>>>,
}

impl Logger {
    fn new(instructions: HashMap<Loc, Vec<Instruction>>) -> Self {
        let stack = instructions
            .iter()
            .map(|(k, v)| (*k, Vec::with_capacity(v.len())))
            .collect();
        Self {
            instructions,
            stack,
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
        for (loc, instructions) in self.instructions.iter() {
            for instruction in instructions {
                if instruction.pc == interp.program_counter() - 1 {
                    dbg!(instruction);
                    dbg!(interp.stack.data());
                }
            }
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

    fn compile(&mut self) -> Result<Contract, Vec<Box<dyn std::fmt::Display>>> {
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

#[derive(Debug)]
struct Label {
    pub name: String,
    pub storage: Option<pt::StorageLocation>,
    pub ty: Option<pt::Type>,
    pub loc: Loc,
    pub stack_offset: usize,
}

fn get_statement_labels<'a>(statements: impl IntoIterator<Item = &'a pt::Statement>) -> Vec<Label> {
    let mut out = Vec::new();
    for statement in statements {
        match statement {
            pt::Statement::Block { statements, .. } => {
                out.append(&mut get_statement_labels(statements));
            }
            pt::Statement::If(_, _, if_block, else_block) => {
                out.append(&mut get_statement_labels([if_block.as_ref()]));
                if let Some(else_block) = else_block {
                    out.append(&mut get_statement_labels([else_block.as_ref()]));
                }
            }
            pt::Statement::While(_, _, block) | pt::Statement::DoWhile(_, block, _) => {
                out.append(&mut get_statement_labels([block.as_ref()]));
            }
            pt::Statement::For(_, block1, _, block2, block3) => {
                for block in [block1, block2, block3].into_iter().flatten() {
                    out.append(&mut get_statement_labels([block.as_ref()]));
                }
            }
            pt::Statement::VariableDefinition(loc, def, _) => {
                let ty = match &def.ty {
                    pt::Expression::Type(_, ty) => Some(ty.clone()),
                    _ => None,
                };
                out.push(Label {
                    name: def.name.name.to_string(),
                    storage: def.storage.clone(),
                    ty,
                    loc: *loc,
                    stack_offset: 0,
                });
            }
            pt::Statement::Expression(loc, pt::Expression::Assign(_, left, _)) => {
                match left.as_ref() {
                    pt::Expression::Variable(ident) => out.push(Label {
                        name: ident.name.to_string(),
                        storage: None,
                        ty: None,
                        loc: *loc,
                        stack_offset: 0,
                    }),
                    pt::Expression::List(_, list) => {
                        let list_end = list.len() - 1;
                        for (idx, (_, param)) in list.iter().enumerate() {
                            if let Some(param) = param {
                                if let Some(ref name) = param.name {
                                    let ty = match &param.ty {
                                        pt::Expression::Type(_, ty) => Some(ty.clone()),
                                        _ => None,
                                    };
                                    out.push(Label {
                                        name: name.to_string(),
                                        storage: param.storage.clone(),
                                        ty,
                                        loc: *loc,
                                        stack_offset: list_end - idx,
                                    });
                                }
                            }
                        }
                    }
                    _ => {}
                }
            }
            _ => {}
        }
    }
    out
}

fn handle_line(solc: &Solc, source: &mut ConstructedSource, mut buffer: String) {
    let parsed_fragment = if let Some(parsed) = parse_fragment(solc, &buffer)
        .or_else(|| {
            buffer = buffer.trim_end().to_string();
            buffer.push_str(";\n");
            parse_fragment(solc, &buffer)
        })
        .or_else(|| {
            buffer = buffer.trim_end().trim_end_matches(';').to_string();
            buffer.push('\n');
            parse_fragment(solc, &buffer)
        }) {
        parsed
    } else {
        return println!("Error: Failed to parse: `{}`", buffer.trim());
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

    let contract = match new_source.compile() {
        Ok(contract) => contract,
        Err(errors) => {
            for error in errors {
                println!("{error}");
            }
            return;
        }
    };

    let statements = if let ParseTreeFragment::Function(stmts) = parsed_fragment {
        let mut statements = new_source.parse_and_decompose().unwrap().2;
        statements
            .drain(statements.len() - stmts.len()..)
            .map(|statement| (statement.loc(), statement))
            .collect::<HashMap<_, _>>()
    } else {
        HashMap::new()
    };

    dbg!(get_statement_labels(statements.values()));

    let init_bytecode_bytes = contract.get_init_bytecode_bytes().unwrap();
    let source_map = contract
        .get_source_map()
        .unwrap()
        .unwrap()
        .into_iter()
        .zip(InstructionIter::new(&init_bytecode_bytes))
        .collect::<Vec<_>>();

    let instructions = statements
        .keys()
        .map(|loc| {
            let offset = loc.start();
            let length = loc.end() - loc.start();
            let source_map_entries = source_map
                .iter()
                .filter(|(s, _)| s.offset == offset && s.length == length)
                .map(|(_, i)| *i)
                .collect::<Vec<_>>();
            (*loc, source_map_entries)
        })
        .collect::<HashMap<_, _>>();

    let mut logger = Logger::new(instructions);

    let mut evm = revm::new();
    evm.database(InMemoryDB::default());

    evm.env.tx.caller = "0x1000000000000000000000000000000000000000"
        .parse()
        .unwrap();
    evm.env.tx.transact_to = TransactTo::Create(CreateScheme::Create2 {
        salt: Default::default(),
    });
    evm.env.tx.data = init_bytecode_bytes.to_vec().into();

    evm.inspect(&mut logger);

    *source = new_source;
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

        handle_line(&solc, &mut source, buffer)
    }
}
