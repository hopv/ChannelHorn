use anyhow::{Result, anyhow};

use super::ast::{AssignOp, BinaryOp, Binding, Block, Expr, MethodCall, Program, Stmt};

peg::parser! {
    grammar sugar_parser() for str {
        pub rule program() -> Program
            = _ statements:stmt()* _ {
                Program { statements }
            }

        rule stmt() -> Stmt
            = let_channel_stmt()
            / let_stmt()
            / assign_stmt()
            / assert_stmt()
            / spawn_stmt()
            / while_stmt()
            / if_stmt()
            / call_stmt()
            / expr_stmt()

        rule block() -> Block
            = lbrace() statements:stmt()* rbrace() {
                Block { statements }
            }

        rule let_channel_stmt() -> Stmt
            = kw_let() sender:ident() comma() receiver:ident() assign() kw_channel() lparen() rparen() semi() {
                Stmt::LetChannel { sender, receiver }
            }

        rule let_stmt() -> Stmt
            = kw_let() var:ident() assign() value:expression() semi() {
                Stmt::Let {
                    binding: Binding { var },
                    value,
                }
            }

        rule assign_stmt() -> Stmt
            = target:ident() op:assign_op() value:expression() semi() {
                Stmt::Assign { target, op, value }
            }

        rule assert_stmt() -> Stmt
            = kw_assert() lparen() expr:expression() rparen() semi() {
                Stmt::Assert(expr)
            }

        rule spawn_stmt() -> Stmt
            = kw_spawn() block:block() {
                Stmt::Spawn(block)
            }

        rule while_stmt() -> Stmt
            = kw_while() lparen() cond:expression() rparen() body:block() {
                Stmt::While { cond, body }
            }

        rule if_stmt() -> Stmt
            = kw_if() lparen() cond:expression() rparen() then_block:block() else_block:else_part()? {
                Stmt::If { cond, then_block, else_block }
            }

        rule else_part() -> Block
            = kw_else() block:block() { block }

        rule call_stmt() -> Stmt
            = call:func_call() semi() {
                let (name, args) = call;
                Stmt::Call { name, args }
            }

        rule expr_stmt() -> Stmt
            = expr:expression() semi() {
                Stmt::Expr(expr)
            }

        rule func_call() -> (String, Vec<Expr>)
            = name:ident() lparen() args:(expression() ** comma())? rparen() {
                (name, args.unwrap_or_default())
            }

        rule assign_op() -> AssignOp
            = plus_assign() { AssignOp::AddAssign }
            / minus_assign() { AssignOp::SubAssign }
            / star_assign() { AssignOp::MulAssign }
            / assign() { AssignOp::Assign }

        rule expression() -> Expr
            = equality()

        rule equality() -> Expr
            = first:comparison() rest:(op:equality_op() right:comparison() { (op, right) })* {
                rest.into_iter().fold(first, |acc, (op, expr)| {
                    Expr::BinaryOp {
                        lhs: Box::new(acc),
                        op,
                        rhs: Box::new(expr),
                    }
                })
            }

        rule comparison() -> Expr
            = first:addition() rest:(op:comparison_op() right:addition() { (op, right) })* {
                rest.into_iter().fold(first, |acc, (op, expr)| {
                    Expr::BinaryOp {
                        lhs: Box::new(acc),
                        op,
                        rhs: Box::new(expr),
                    }
                })
            }

        rule addition() -> Expr
            = first:multiplication() rest:(op:add_op() right:multiplication() { (op, right) })* {
                rest.into_iter().fold(first, |acc, (op, expr)| {
                    Expr::BinaryOp {
                        lhs: Box::new(acc),
                        op,
                        rhs: Box::new(expr),
                    }
                })
            }

        rule multiplication() -> Expr
            = first:postfix() rest:(op:mul_op() right:postfix() { (op, right) })* {
                rest.into_iter().fold(first, |acc, (op, expr)| {
                    Expr::BinaryOp {
                        lhs: Box::new(acc),
                        op,
                        rhs: Box::new(expr),
                    }
                })
            }

        rule postfix() -> Expr
            = first:primary() rest:(dot() method:method_call() { method })* {
                rest.into_iter().fold(first, |receiver, method| {
                    Expr::MethodCall {
                        receiver: Box::new(receiver),
                        method,
                    }
                })
            }

        rule method_call() -> MethodCall
            = kw_send() lparen() value:expression() rparen() { MethodCall::Send(Box::new(value)) }
            / kw_recv() lparen() rparen() { MethodCall::Recv }
            / kw_drop() lparen() rparen() { MethodCall::Drop }
            / kw_clone() lparen() rparen() { MethodCall::Clone }

        rule primary() -> Expr
            = bool_literal()
            / number()
            / variable()
            / lparen() expr:expression() rparen() { expr }

        rule bool_literal() -> Expr
            = kw_false() { Expr::Int(0) }
            / kw_true() { Expr::Int(1) }

        rule number() -> Expr
            = s:$("-"? ['0'..='9']+) _() {
                let value: i32 = s.parse().expect("valid integer literal");
                Expr::Int(value)
            }

        rule variable() -> Expr
            = name:ident() { Expr::Var(name) }

        rule equality_op() -> BinaryOp
            = eqeq() { BinaryOp::Eq }
            / noteq() { BinaryOp::Ne }

        rule comparison_op() -> BinaryOp
            = le() { BinaryOp::Le }
            / lt() { BinaryOp::Lt }
            / ge() { BinaryOp::Ge }
            / gt() { BinaryOp::Gt }

        rule add_op() -> BinaryOp
            = plus() { BinaryOp::Add }
            / minus() { BinaryOp::Sub }

        rule mul_op() -> BinaryOp
            = star() { BinaryOp::Mul }

        rule ident() -> String
            = !reserved_word() s:$((ident_start()) (ident_char())*) _() { s.to_string() }

        rule reserved_word()
            = quiet!{ "let" } !ident_char()
            / quiet!{ "while" } !ident_char()
            / quiet!{ "if" } !ident_char()
            / quiet!{ "else" } !ident_char()
            / quiet!{ "spawn" } !ident_char()
            / quiet!{ "channel" } !ident_char()
            / quiet!{ "send" } !ident_char()
            / quiet!{ "recv" } !ident_char()
            / quiet!{ "drop" } !ident_char()
            / quiet!{ "clone" } !ident_char()
            / quiet!{ "assert" } !ident_char()
            / quiet!{ "false" } !ident_char()
            / quiet!{ "true" } !ident_char()

        rule ident_start()
            = ['a'..='z' | 'A'..='Z' | '_']

        rule ident_char()
            = ['a'..='z' | 'A'..='Z' | '0'..='9' | '_']

        rule kw_let()
            = quiet!{ "let" } !ident_char() _()

        rule kw_while()
            = quiet!{ "while" } !ident_char() _()

        rule kw_if()
            = quiet!{ "if" } !ident_char() _()

        rule kw_else()
            = quiet!{ "else" } !ident_char() _()

        rule kw_spawn()
            = quiet!{ "spawn" } !ident_char() _()

        rule kw_channel()
            = quiet!{ "channel" } !ident_char() _()

        rule kw_send()
            = quiet!{ "send" } !ident_char() _()

        rule kw_recv()
            = quiet!{ "recv" } !ident_char() _()

        rule kw_drop()
            = quiet!{ "drop" } !ident_char() _()

        rule kw_clone()
            = quiet!{ "clone" } !ident_char() _()

        rule kw_assert()
            = quiet!{ "assert!" } _()

        rule kw_false()
            = quiet!{ "false" } !ident_char() _()

        rule kw_true()
            = quiet!{ "true" } !ident_char() _()

        rule lparen()
            = quiet!{ "(" } _()

        rule rparen()
            = quiet!{ ")" } _()

        rule lbrace()
            = quiet!{ "{" } _()

        rule rbrace()
            = quiet!{ "}" } _()

        rule comma()
            = quiet!{ "," } _()

        rule semi()
            = quiet!{ ";" } _()

        rule dot()
            = quiet!{ "." } _()

        rule assign()
            = quiet!{ "=" } _()

        rule plus_assign()
            = quiet!{ "+=" } _()

        rule minus_assign()
            = quiet!{ "-=" } _()

        rule star_assign()
            = quiet!{ "*=" } _()

        rule plus()
            = quiet!{ "+" } _()

        rule minus()
            = quiet!{ "-" } _()

        rule star()
            = quiet!{ "*" } _()

        rule eqeq()
            = quiet!{ "==" } _()

        rule noteq()
            = quiet!{ "!=" } _()

        rule le()
            = quiet!{ "<=" } _()

        rule lt()
            = quiet!{ "<" } _()

        rule ge()
            = quiet!{ ">=" } _()

        rule gt()
            = quiet!{ ">" } _()

        rule whitespace()
            = [' ' | '\t' | '\r' | '\n']

        rule comment()
            = quiet!{
                "//" (!['\n'] [_])* ("\n" / "\r\n")?
            }
            / quiet!{
                "/*" (!("*/") [_])* "*/"
            }

        rule _
            = (whitespace() / comment())*
    }
}

pub fn parse_program(input: &str) -> Result<Program> {
    sugar_parser::program(input).map_err(|e| anyhow!("parse error: {}", e))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn var(name: &str) -> Expr {
        Expr::Var(name.to_string())
    }

    fn int(value: i32) -> Expr {
        Expr::Int(value)
    }

    #[test]
    fn parses_channel_example() {
        let program = parse_program(
            r#"
            let s, r = channel();
            s.send(1);
            let v = r.recv();
            s.drop();
            "#,
        )
        .expect("channel example should parse");

        assert_eq!(
            program.statements,
            vec![
                Stmt::LetChannel {
                    sender: "s".to_string(),
                    receiver: "r".to_string(),
                },
                Stmt::Expr(Expr::MethodCall {
                    receiver: Box::new(var("s")),
                    method: MethodCall::Send(Box::new(int(1))),
                }),
                Stmt::Let {
                    binding: Binding {
                        var: "v".to_string(),
                    },
                    value: Expr::MethodCall {
                        receiver: Box::new(var("r")),
                        method: MethodCall::Recv,
                    },
                },
                Stmt::Expr(Expr::MethodCall {
                    receiver: Box::new(var("s")),
                    method: MethodCall::Drop,
                }),
            ]
        );
    }

    #[test]
    fn parses_assignment_while_and_assert() {
        let program = parse_program(
            r#"
            let sum = 0;
            while (sum <= 10) {
              sum += 1;
            }
            assert!(sum == 11);
            "#,
        )
        .expect("while example should parse");

        assert_eq!(
            program.statements,
            vec![
                Stmt::Let {
                    binding: Binding {
                        var: "sum".to_string(),
                    },
                    value: int(0),
                },
                Stmt::While {
                    cond: Expr::BinaryOp {
                        lhs: Box::new(var("sum")),
                        op: BinaryOp::Le,
                        rhs: Box::new(int(10)),
                    },
                    body: Block {
                        statements: vec![Stmt::Assign {
                            target: "sum".to_string(),
                            op: AssignOp::AddAssign,
                            value: int(1),
                        }],
                    },
                },
                Stmt::Assert(Expr::BinaryOp {
                    lhs: Box::new(var("sum")),
                    op: BinaryOp::Eq,
                    rhs: Box::new(int(11)),
                }),
            ]
        );
    }

    #[test]
    fn parses_spawn_and_clone_example() {
        let program = parse_program(
            r#"
            let s1, r = channel();
            let s2 = s1.clone();
            spawn {
              s1.send(1);
            }
            spawn {
              s2.send(2);
            }
            let v1 = r.recv();
            let v2 = r.recv();
            assert!(v1 + v2 == 3);
            "#,
        )
        .expect("spawn example should parse");

        assert_eq!(
            program.statements,
            vec![
                Stmt::LetChannel {
                    sender: "s1".to_string(),
                    receiver: "r".to_string(),
                },
                Stmt::Let {
                    binding: Binding {
                        var: "s2".to_string(),
                    },
                    value: Expr::MethodCall {
                        receiver: Box::new(var("s1")),
                        method: MethodCall::Clone,
                    },
                },
                Stmt::Spawn(Block {
                    statements: vec![Stmt::Expr(Expr::MethodCall {
                        receiver: Box::new(var("s1")),
                        method: MethodCall::Send(Box::new(int(1))),
                    })],
                }),
                Stmt::Spawn(Block {
                    statements: vec![Stmt::Expr(Expr::MethodCall {
                        receiver: Box::new(var("s2")),
                        method: MethodCall::Send(Box::new(int(2))),
                    })],
                }),
                Stmt::Let {
                    binding: Binding {
                        var: "v1".to_string(),
                    },
                    value: Expr::MethodCall {
                        receiver: Box::new(var("r")),
                        method: MethodCall::Recv,
                    },
                },
                Stmt::Let {
                    binding: Binding {
                        var: "v2".to_string(),
                    },
                    value: Expr::MethodCall {
                        receiver: Box::new(var("r")),
                        method: MethodCall::Recv,
                    },
                },
                Stmt::Assert(Expr::BinaryOp {
                    lhs: Box::new(Expr::BinaryOp {
                        lhs: Box::new(var("v1")),
                        op: BinaryOp::Add,
                        rhs: Box::new(var("v2")),
                    }),
                    op: BinaryOp::Eq,
                    rhs: Box::new(int(3)),
                }),
            ]
        );
    }

    #[test]
    fn parses_if_else_and_call_statement() {
        let program = parse_program(
            r#"
            if (x > 0) {
              f(x);
            } else {
              g(0);
            }
            "#,
        )
        .expect("if/call example should parse");

        assert_eq!(
            program.statements,
            vec![Stmt::If {
                cond: Expr::BinaryOp {
                    lhs: Box::new(var("x")),
                    op: BinaryOp::Gt,
                    rhs: Box::new(int(0)),
                },
                then_block: Block {
                    statements: vec![Stmt::Call {
                        name: "f".to_string(),
                        args: vec![var("x")],
                    }],
                },
                else_block: Some(Block {
                    statements: vec![Stmt::Call {
                        name: "g".to_string(),
                        args: vec![int(0)],
                    }],
                }),
            }]
        );
    }

    #[test]
    fn expression_precedence_is_preserved() {
        let program =
            parse_program("assert!(1 + 2 * 3 == 7);").expect("precedence example should parse");

        assert_eq!(
            program.statements,
            vec![Stmt::Assert(Expr::BinaryOp {
                lhs: Box::new(Expr::BinaryOp {
                    lhs: Box::new(int(1)),
                    op: BinaryOp::Add,
                    rhs: Box::new(Expr::BinaryOp {
                        lhs: Box::new(int(2)),
                        op: BinaryOp::Mul,
                        rhs: Box::new(int(3)),
                    }),
                }),
                op: BinaryOp::Eq,
                rhs: Box::new(int(7)),
            })]
        );
    }

    #[test]
    fn rejects_channel_as_regular_let_expression() {
        let err = parse_program("let c = channel();").expect_err("channel() is not an expression");

        assert!(err.to_string().contains("parse error"));
    }

    #[test]
    fn parses_boolean_literals_as_integer_literals() {
        let program = parse_program(
            r#"
            assert!(false);
            assert!(true);
            "#,
        )
        .expect("boolean literal example should parse");

        assert_eq!(
            program.statements,
            vec![Stmt::Assert(int(0)), Stmt::Assert(int(1))]
        );
    }
}
