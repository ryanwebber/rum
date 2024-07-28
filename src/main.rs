use std::io::{self, BufRead, Write};

mod ast;
mod gc;
mod interner;
mod interpreter;
mod parser;
mod types;

mod modules {
    pub mod core;
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
        backend.register("repl.exit", |_, _, _| todo!());

        backend.register("repl.help", |_, _, _| todo!());
    }

    fn prelude() -> &'static str {
        r#"
        (def-fn! exit () (call-native :repl.exit))
        (def-fn! help () (call-native :repl.help))
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
            match runtime.parse_and_evaluate_expr(line.trim_end()) {
                Ok(value) => println!("{}", runtime.print_value(&value)),
                Err(e) => println!("! {}", e),
            }

            line.clear();
        }
    }
}
