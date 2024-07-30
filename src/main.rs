use std::io::{self, BufRead, Write};

use indoc::indoc;
use interpreter::NativeCall;

mod ast;
mod gc;
mod interner;
mod interpreter;
mod parser;
mod types;

mod modules {
    pub mod collections;
    pub mod core;
    pub mod math;
    pub mod reflection;
}

extern crate lalrpop_util;

struct ReplModule;

fn print_banner() {
    println!(indoc::indoc! {"
        ;
        ; Rum v0.1.0 REPL
        ; Available functions:
        ;   (exit)    Exit the REPL
        ;   (help)    Print additional help information
        ;
    "});
}

impl interpreter::Module for ReplModule {
    fn register_builtins(&self, backend: &mut interpreter::Backend) {
        backend.register(
            "repl.exit",
            NativeCall::Function(|_, _, _| {
                std::process::exit(0);
            }),
        );

        backend.register(
            "repl.help",
            NativeCall::Function(|_, _, _| {
                print_banner();
                Ok(interpreter::Value::empty())
            }),
        );
    }

    fn prelude() -> &'static str {
        indoc! {"
            (def-fn! exit () (#bridge :repl.exit))
            (def-fn! help () (#bridge :repl.help))
        "}
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
            match runtime.parse_and_evaluate_expr(line.trim_end()) {
                Ok(value) => println!("{}", runtime.print_value(&value)),
                Err(e) => println!("! {}", e),
            }

            line.clear();
        }
    }
}
