use ethers_solc::{
    artifacts::{Source, Sources},
    CompilerInput, CompilerOutput, Solc,
};
use revm::{Database, Inspector};

pub struct Logger;

impl<DB> Inspector<DB> for Logger
where
    DB: Database,
{
    fn initialize_interp(
        &mut self,
        _interp: &mut revm::Interpreter,
        _data: &mut revm::EVMData<'_, DB>,
        _is_static: bool,
    ) -> revm::Return {
        revm::Return::Continue
    }
    fn step(
        &mut self,
        _interp: &mut revm::Interpreter,
        _data: &mut revm::EVMData<'_, DB>,
        _is_static: bool,
    ) -> revm::Return {
        revm::Return::Continue
    }
    fn step_end(
        &mut self,
        _interp: &mut revm::Interpreter,
        _data: &mut revm::EVMData<'_, DB>,
        _is_static: bool,
        _eval: revm::Return,
    ) -> revm::Return {
        revm::Return::Continue
    }
}

pub const REPL_SOL_FILENAME: &str = "__ReplContract.sol";
pub const REPL_CONTRACT_NAME: &str = "__ReplContract";

fn compile(prelude: &str, body: &str) -> CompilerOutput {
    pub const SPDX_LICENSE: &str = "// SPDX-License-Identifier: UNLICENSED";
    pub const CONTRACT_END: &str = "} }";

    let solc = Solc::new("/usr/bin/solc");
    let version = solc.version().unwrap();

    let pragma = format!("pragma solidity ^{}.{}.0;", version.major, version.minor);
    let contract_start = format!("contract {REPL_CONTRACT_NAME} {{ constructor() {{");

    let func = [
        SPDX_LICENSE,
        &pragma,
        prelude,
        &contract_start,
        body,
        CONTRACT_END,
    ]
    .join("\n");
    let mut sources = Sources::new();
    sources.insert(REPL_SOL_FILENAME.into(), Source { content: func });
    let input = CompilerInput::with_sources(sources).pop().unwrap();
    solc.compile_exact(&input).unwrap()
}

fn main() {
    let prelude = r#"
    struct HelloWorld {
        uint foo;
    }
    "#;
    let body = r#"
    uint a = 5;
    "#;
    let mut compiled = compile(prelude, body);
    let contract = compiled
        .contracts
        .remove(REPL_SOL_FILENAME)
        .unwrap()
        .remove(REPL_CONTRACT_NAME)
        .unwrap();
    let bytecode = contract.evm.as_ref().unwrap().bytecode.as_ref().unwrap();
    println!("{bytecode:#?}");
}
