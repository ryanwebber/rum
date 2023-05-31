use std::io::{self, BufRead, Write};

use interpreter::Value;

mod ast;
mod gc;
mod interner;
mod interpreter;
mod parser;
mod types;

mod modules {
    pub(crate) mod core;
    pub(crate) mod lists;
    pub(crate) mod math;
    pub(crate) mod tables;
}

extern crate lalrpop_util;

struct ReplModule;

fn print_banner() {
    println!(";");
    println!("; Rum v0.1.0 REPL");
    println!("; Available functions:");
    println!(";   (exit)    Exit the REPL");
    println!(";   (help)    Print additional help information");
    println!(";");
}

impl interpreter::Module for ReplModule {
    fn register_builtins(&self, backend: &mut interpreter::Backend) {
        backend.insert("repl$exit", |_, _, _| {
            std::process::exit(0);
        });

        backend.insert("repl$help", |_, _, _| {
            print_banner();
            return Ok(Value::empty());
        });
    }

    fn prelude() -> &'static str {
        r#"
        (def-fn! exit () (#Call :repl$exit))
        (def-fn! help () (#Call :repl$help))
        "#
    }
}

fn main() {
    let mut runtime = interpreter::Runtime::new();
    runtime.load_module(&ReplModule).unwrap();

    {
        print_banner();

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
