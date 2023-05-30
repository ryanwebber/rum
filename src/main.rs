use std::io::{self, BufRead, Write};

use crate::interpreter::PrintableValue;

mod ast;
mod gc;
mod interner;
mod interpreter;
mod parser;
mod types;

extern crate lalrpop_util;

struct ReplModule;

impl interpreter::Module for ReplModule {
    fn register_builtins(&self, backend: &mut interpreter::Backend) {
        backend.insert("repl$exit", |_, _, _| {
            std::process::exit(0);
        })
    }

    fn prelude() -> &'static str {
        r#"
        (def-fn! exit () (#Call :repl$exit))
        "#
    }
}

fn main() {
    let mut runtime = interpreter::Runtime::new();
    runtime.load_module(&ReplModule).unwrap();

    {
        println!(";");
        println!("; Rum v0.1.0 REPL");
        println!("; Available functions:");
        println!(";   (exit)    Exit the REPL");
        println!(";   (help)    Print additional help information");
        println!(";");

        let stdin = io::stdin();
        let mut line = String::new();
        loop {
            print!("> ");
            _ = io::stdout().flush();
            stdin.lock().read_line(&mut line).unwrap();
            match runtime.evaluate_expr(line.trim_end()) {
                Ok(value) => println!("{}", runtime.print_value(&value)),
                Err(e) => println!("! {}", e),
            }

            line.clear();
        }
    }
}
