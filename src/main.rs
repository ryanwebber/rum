use std::io::{self, BufRead, Write};

mod ast;
mod interner;
mod interpreter;
mod parser;
mod types;

extern crate lalrpop_util;

fn main() {
    let mut runtime = interpreter::Runtime::new();

    {
        println!(";");
        println!("; Rum v0.1.0");
        println!("; Functions:");
        println!(";   (exit)    Exit the REPL");
        println!(";   (help)    Print additional help information");
        println!(";");

        let stdin = io::stdin();
        let mut line = String::new();
        loop {
            print!("> ");
            _ = io::stdout().flush();
            stdin.lock().read_line(&mut line).unwrap();

            // TODO: Add a module for the REPL
            if line == "(exit)\n" {
                break;
            }

            println!("{:?}", runtime.evaluate_str(line.trim_end()));
            line.clear();
        }
    }
}
