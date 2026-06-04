use anyhow::{Result, anyhow};

use crate::core::ast::{AdtDef, Type, VariantDef};

use super::ast::{AssignOp, BinaryOp, Binding, Block, Expr, MatchArm, MethodCall, Program, Stmt};

peg::parser! {
    grammar sugar_parser() for str {
        pub rule program() -> Program
            = _ adts:adt_def()* statements:stmt()* _ {
                Program { adts, statements }
            }

        rule adt_def() -> AdtDef
            = kw_data() name:ident() assign() variants:(variant_def() ++ bar()) {
                AdtDef { name, variants }
            }

        rule variant_def() -> VariantDef
            = name:ident() fields:(lparen() fields:(type_() ** comma())? rparen() { fields.unwrap_or_default() })? {
                VariantDef {
                    name,
                    fields: fields.unwrap_or_default(),
                }
            }

        rule stmt() -> Stmt
            = let_channel_stmt()
            / let_stmt()
            / assign_stmt()
            / assert_stmt()
            / spawn_stmt()
            / while_stmt()
            / if_stmt()
            / match_stmt()
            / call_stmt()
            / expr_stmt()

        rule block() -> Block
            = lbrace() statements:stmt()* rbrace() {
                Block { statements }
            }

        rule let_channel_stmt() -> Stmt
            = kw_let() sender:ident() comma() receiver:ident() assign() kw_channel() payload:generic_type_arg()? lparen() rparen() semi() {
                Stmt::LetChannel {
                    payload: payload.unwrap_or(Type::Int),
                    sender,
                    receiver,
                }
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

        rule match_stmt() -> Stmt
            = kw_match() scrutinee:ident() lbrace() arms:match_arm_with_sep()+ rbrace() {
                Stmt::Match { scrutinee, arms }
            }

        rule match_arm_with_sep() -> MatchArm
            = arm:match_arm() comma()? { arm }

        rule match_arm() -> MatchArm
            = type_name:ident() double_colon() variant:ident() lparen() vars:(ident() ** comma())? rparen() arrow() block:block() {
                MatchArm {
                    type_name,
                    variant,
                    vars: vars.unwrap_or_default(),
                    block,
                }
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
            / constructor()
            / variable()
            / lparen() expr:expression() rparen() { expr }

        rule constructor() -> Expr
            = type_name:ident() double_colon() variant:ident() lparen() args:(expression() ** comma())? rparen() {
                Expr::Ctor {
                    type_name,
                    variant,
                    args: args.unwrap_or_default(),
                }
            }

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

        rule type_() -> Type
            = sender_type()
            / receiver_type()
            / int_type()
            / adt_type()

        rule sender_type() -> Type
            = quiet!{ "Sender" }
              payload:generic_type_arg()? !ident_char() _() {
                  Type::sender(payload.unwrap_or(Type::Int))
              }

        rule receiver_type() -> Type
            = quiet!{ "Receiver" }
              payload:generic_type_arg()? !ident_char() _() {
                  Type::receiver(payload.unwrap_or(Type::Int))
              }

        rule generic_type_arg() -> Type
            = lt() ty:type_() gt() { ty }

        rule int_type() -> Type
            = quiet!{ "int" }
              !ident_char() _() { Type::Int }

        rule adt_type() -> Type
            = name:ident() { Type::Adt(name) }

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
            / quiet!{ "match" } !ident_char()
            / quiet!{ "data" } !ident_char()
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

        rule kw_data()
            = quiet!{ "data" } !ident_char() _()

        rule kw_while()
            = quiet!{ "while" } !ident_char() _()

        rule kw_if()
            = quiet!{ "if" } !ident_char() _()

        rule kw_else()
            = quiet!{ "else" } !ident_char() _()

        rule kw_match()
            = quiet!{ "match" } !ident_char() _()

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

        rule bar()
            = quiet!{ "|" } _()

        rule semi()
            = quiet!{ ";" } _()

        rule dot()
            = quiet!{ "." } _()

        rule double_colon()
            = quiet!{ "::" } _()

        rule arrow()
            = quiet!{ "=>" } _()

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
                    payload: Type::Int,
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
    fn parses_typed_channel_payload() {
        let program = parse_program(
            r#"
            let s, r = channel<Sender<int>>();
            "#,
        )
        .expect("typed channel should parse");

        assert_eq!(
            program.statements,
            vec![Stmt::LetChannel {
                payload: Type::int_sender(),
                sender: "s".to_string(),
                receiver: "r".to_string(),
            }]
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
                    payload: Type::Int,
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

    #[test]
    fn parses_adts_constructors_and_match() {
        let program = parse_program(
            r#"
            data Box = Empty | Hold(Sender<int>)
            let s, r = channel();
            let b = Box::Hold(s);
            match b {
              Box::Empty() => {
                r.drop();
              },
              Box::Hold(s2) => {
                s2.drop();
                r.drop();
              }
            }
            "#,
        )
        .expect("ADT example should parse");

        assert_eq!(
            program.adts,
            vec![AdtDef {
                name: "Box".to_string(),
                variants: vec![
                    VariantDef {
                        name: "Empty".to_string(),
                        fields: vec![],
                    },
                    VariantDef {
                        name: "Hold".to_string(),
                        fields: vec![Type::int_sender()],
                    },
                ],
            }]
        );
        assert_eq!(
            program.statements[1],
            Stmt::Let {
                binding: Binding {
                    var: "b".to_string(),
                },
                value: Expr::Ctor {
                    type_name: "Box".to_string(),
                    variant: "Hold".to_string(),
                    args: vec![var("s")],
                },
            }
        );
        assert!(matches!(program.statements[2], Stmt::Match { .. }));
    }

    #[test]
    fn parses_line_comments_as_whitespace() {
        let program = parse_program(
            r#"
            // before a statement
            let x = 1; // after a statement
            if (x == 1) { // after a block opener
              // inside a block
              assert!(true);
            } // before end of file
            "#,
        )
        .expect("line comments should parse as whitespace");

        assert_eq!(
            program.statements,
            vec![
                Stmt::Let {
                    binding: Binding {
                        var: "x".to_string(),
                    },
                    value: int(1),
                },
                Stmt::If {
                    cond: Expr::BinaryOp {
                        lhs: Box::new(var("x")),
                        op: BinaryOp::Eq,
                        rhs: Box::new(int(1)),
                    },
                    then_block: Block {
                        statements: vec![Stmt::Assert(int(1))],
                    },
                    else_block: None,
                },
            ]
        );
    }
}
