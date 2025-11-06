use std::collections::HashMap;

use anyhow::Result;
use channel_rust_impl::{
    ast::{Expr, FuncCall, Function, OpKind, Program, Statement, Type},
    utils::functions,
};

// main() = new s, r in proc1(s, r)
// proc1(s: Sender, r: Receiver) = send 1 to s; proc2(r)
// proc2(r: Receiver) = let v = recv r in assert(v == 1)
fn main() -> Result<()> {
    let main_func = Function {
        name: "main".to_string(),
        params: vec![],
        body: Statement::New {
            sender: "s".to_string(),
            receiver: "r".to_string(),
            body: FuncCall {
                name: "proc1".to_string(),
                args: vec![Expr::Var("s".to_string()), Expr::Var("r".to_string())],
            },
        },
    };
    let proc1_func = Function {
        name: "proc1".to_string(),
        params: vec![
            ("s".to_string(), Type::Sender),
            ("r".to_string(), Type::Receiver),
        ],
        body: Statement::Send {
            sender: "s".to_string(),
            value: Expr::Num(1),
            body: FuncCall {
                name: "proc2".to_string(),
                args: vec![Expr::Var("r".to_string())],
            },
        },
    };
    let proc2_func = Function {
        name: "proc2".to_string(),
        params: vec![("r".to_string(), Type::Receiver)],
        body: Statement::Recv {
            receiver: "r".to_string(),
            var: "v".to_string(),
            body: FuncCall {
                name: "assert".to_string(),
                args: vec![Expr::Op(
                    Expr::Var("v".to_string()).into(),
                    OpKind::Eq,
                    Expr::Num(1).into(),
                )],
            },
        },
    };

    let program = Program {
        functions: HashMap::from([
            ("main".to_string(), main_func),
            ("proc1".to_string(), proc1_func),
            ("proc2".to_string(), proc2_func),
            ("assert".to_string(), functions::gen_assert()),
            ("unit".to_string(), functions::gen_unit()),
            ("fail".to_string(), functions::gen_fail()),
        ]),
        init: FuncCall {
            name: "main".to_string(),
            args: vec![],
        },
    };
    let mut evaluator = channel_rust_impl::eval::Evaluator::new(program);
    loop {
        if let Err(e) = evaluator.step() {
            println!("Program failed: {}", e);
            break;
        }
        if evaluator.is_done() {
            println!("Program terminated successfully.");
            break;
        }
    }

    Ok(())
}
