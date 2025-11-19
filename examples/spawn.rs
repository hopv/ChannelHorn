use std::collections::HashMap;

use anyhow::Result;
use channel_rust_impl::{
    ast::{Expr, FuncCall, Function, OpKind, Program, Statement, Type},
    utils::functions,
};

/// main() = new s1, r in proc1(s1, r)
/// proc1(s1: Sender, r: Receiver) = let s2 = dup s1 in proc2(s1, s2, r)
/// proc2(s1: Sender, s2: Sender, r: Receiver) = spawn(proc3(s1, s2)); proc4(r)
/// proc3(s1: Sender, s2: Sender) = spawn(send_fun(s1, 10)); send_fun(s2, 20)
/// proc4(r: Receiver) = let recv1 = recv r in proc5(r, recv1)
/// proc5(r: Receiver, recv1: Int) = let recv2 = recv r in assert(recv1 + recv2 == 30)
/// may_fail_proc5(r: Receiver, recv1: Int) = let recv2 = recv r in assert(recv1 == 10)
fn main() -> Result<()> {
    let main_func = Function {
        name: "main".to_string(),
        params: vec![],
        body: Statement::New {
            sender: "s1".to_string(),
            receiver: "r".to_string(),
            body: FuncCall {
                name: "proc1".to_string(),
                args: vec![Expr::Var("s1".to_string()), Expr::Var("r".to_string())],
            },
        },
    };
    let proc1_func = Function {
        name: "proc1".to_string(),
        params: vec![
            ("s1".to_string(), Type::Sender),
            ("r".to_string(), Type::Receiver),
        ],
        body: Statement::Dup {
            sender: "s1".to_string(),
            var: "s2".to_string(),
            body: FuncCall {
                name: "proc2".to_string(),
                args: vec![
                    Expr::Var("s1".to_string()),
                    Expr::Var("s2".to_string()),
                    Expr::Var("r".to_string()),
                ],
            },
        },
    };
    let proc2_func = Function {
        name: "proc2".to_string(),
        params: vec![
            ("s1".to_string(), Type::Sender),
            ("s2".to_string(), Type::Sender),
            ("r".to_string(), Type::Receiver),
        ],
        body: Statement::Spawn(
            FuncCall {
                name: "proc3".to_string(),
                args: vec![Expr::Var("s1".to_string()), Expr::Var("s2".to_string())],
            },
            FuncCall {
                name: "proc4".to_string(),
                args: vec![Expr::Var("r".to_string())],
            },
        ),
    };
    let proc3_func = Function {
        name: "proc3".to_string(),
        params: vec![
            ("s1".to_string(), Type::Sender),
            ("s2".to_string(), Type::Sender),
        ],
        body: Statement::Spawn(
            FuncCall {
                name: "send_fun".to_string(),
                args: vec![Expr::Var("s1".to_string()), Expr::Num(10)],
            },
            FuncCall {
                name: "send_fun".to_string(),
                args: vec![Expr::Var("s2".to_string()), Expr::Num(20)],
            },
        ),
    };
    let proc4_func = Function {
        name: "proc4".to_string(),
        params: vec![("r".to_string(), Type::Receiver)],
        body: Statement::Recv {
            receiver: "r".to_string(),
            var: "recv1".to_string(),
            body: FuncCall {
                name: "proc5".to_string(),
                args: vec![Expr::Var("r".to_string()), Expr::Var("recv1".to_string())],
            },
        },
    };
    let proc5_func = Function {
        name: "proc5".to_string(),
        params: vec![
            ("r".to_string(), Type::Receiver),
            ("recv1".to_string(), Type::Int),
        ],
        body: Statement::Recv {
            receiver: "r".to_string(),
            var: "recv2".to_string(),
            body: FuncCall {
                name: "assert".to_string(),
                args: vec![Expr::Op(
                    Expr::Op(
                        Expr::Var("recv1".to_string()).into(),
                        OpKind::Add,
                        Expr::Var("recv2".to_string()).into(),
                    )
                    .into(),
                    OpKind::Eq,
                    Expr::Num(30).into(),
                )],
            },
        },
    };
    let may_fail_proc5_func = Function {
        name: "may_fail_proc5".to_string(),
        params: vec![
            ("r".to_string(), Type::Receiver),
            ("recv1".to_string(), Type::Int),
        ],
        body: Statement::Recv {
            receiver: "r".to_string(),
            var: "recv2".to_string(),
            body: FuncCall {
                name: "assert".to_string(),
                args: vec![Expr::Op(
                    Expr::Var("recv1".to_string()).into(),
                    OpKind::Eq,
                    Expr::Num(10).into(),
                )],
            },
        },
    };
    let program = Program {
        functions: HashMap::from([
            ("main".into(), main_func),
            ("unit".into(), functions::gen_unit()),
            ("fail".into(), functions::gen_fail()),
            ("send_fun".into(), functions::gen_send_fun()),
            ("assert".into(), functions::gen_assert()),
            ("proc1".into(), proc1_func),
            ("proc2".into(), proc2_func),
            ("proc3".into(), proc3_func),
            ("proc4".into(), proc4_func),
            ("proc5".into(), proc5_func),
            ("may_fail_proc5".into(), may_fail_proc5_func),
        ]),
        init: FuncCall {
            name: "main".to_string(),
            args: vec![],
        },
    };

    let chc = program.lower_to_chc()?;
    println!("Generated CHC:\n{}", chc);

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
