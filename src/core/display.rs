use std::fmt;

use super::ast::{Expr, FuncCall, Function, OpKind, Program, Statement, Type};

impl fmt::Display for Program {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "init = {}", self.init)?;

        let mut names: Vec<&str> = self.functions.keys().map(String::as_str).collect();
        names.sort_unstable();
        if let Some(init_pos) = names.iter().position(|name| *name == self.init.name) {
            names.remove(init_pos);
            names.insert(0, self.init.name.as_str());
        }

        if !names.is_empty() {
            writeln!(f)?;
        }

        for (index, name) in names.iter().enumerate() {
            if index > 0 {
                writeln!(f)?;
            }
            let function = self
                .functions
                .get(*name)
                .expect("function name came from Program::functions");
            write!(f, "{}", function)?;
        }

        Ok(())
    }
}

impl fmt::Display for Function {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let params = self
            .params
            .iter()
            .map(|(name, ty)| format!("{}: {}", name, ty))
            .collect::<Vec<_>>()
            .join(", ");
        write!(f, "{}({}) = {}", self.name, params, self.body)
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Int => write!(f, "int"),
            Type::Sender(payload) if **payload == Type::Int => write!(f, "Sender"),
            Type::Sender(payload) => write!(f, "Sender<{}>", payload),
            Type::Receiver(payload) if **payload == Type::Int => write!(f, "Receiver"),
            Type::Receiver(payload) => write!(f, "Receiver<{}>", payload),
            Type::Func { params } => {
                let params = params
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(f, "Func({})", params)
            }
        }
    }
}

impl fmt::Display for Statement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Statement::Fail => write!(f, "fail"),
            Statement::Unit => write!(f, "()"),
            Statement::Call(call) => write!(f, "{}", call),
            Statement::If(cond, then_call, else_call) => {
                write!(f, "if {} then {} else {}", cond, then_call, else_call)
            }
            Statement::Spawn(first, second) => write!(f, "spawn({}); {}", first, second),
            Statement::New {
                sender,
                receiver,
                body,
            } => write!(f, "new {}, {} in {}", sender, receiver, body),
            Statement::Send {
                sender,
                value,
                body,
            } => write!(f, "send {} to {}; {}", value, sender, body),
            Statement::Recv {
                receiver,
                var,
                body,
            } => write!(f, "let {} = recv {} in {}", var, receiver, body),
            Statement::Dup { sender, var, body } => {
                write!(f, "let {} = dup {} in {}", var, sender, body)
            }
        }
    }
}

impl fmt::Display for FuncCall {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let args = self
            .args
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join(", ");
        write!(f, "{}({})", self.name, args)
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write_expr(f, self, 0, false)
    }
}

impl fmt::Display for OpKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let op = match self {
            OpKind::Add => "+",
            OpKind::Sub => "-",
            OpKind::Mul => "*",
            OpKind::Eq => "==",
            OpKind::Ne => "!=",
            OpKind::Lt => "<",
            OpKind::Le => "<=",
            OpKind::Gt => ">",
            OpKind::Ge => ">=",
        };
        write!(f, "{}", op)
    }
}

fn write_expr(
    f: &mut fmt::Formatter<'_>,
    expr: &Expr,
    parent_precedence: u8,
    is_right_child: bool,
) -> fmt::Result {
    match expr {
        Expr::Num(value) => write!(f, "{}", value),
        Expr::Var(name) => write!(f, "{}", name),
        Expr::Op(lhs, op, rhs) => {
            let precedence = op.precedence();
            let needs_parens = precedence < parent_precedence
                || (is_right_child && precedence == parent_precedence);

            if needs_parens {
                write!(f, "(")?;
            }

            write_expr(f, lhs, precedence, false)?;
            write!(f, " {} ", op)?;
            write_expr(f, rhs, precedence, true)?;

            if needs_parens {
                write!(f, ")")?;
            }

            Ok(())
        }
    }
}

impl OpKind {
    fn precedence(self) -> u8 {
        match self {
            OpKind::Eq | OpKind::Ne => 1,
            OpKind::Lt | OpKind::Le | OpKind::Gt | OpKind::Ge => 2,
            OpKind::Add | OpKind::Sub => 3,
            OpKind::Mul => 4,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::parser;

    #[test]
    fn prints_core_syntax_like_test_files() {
        let input = r#"
            init = main()

            main() = new s, r in proc1(s, r)
            proc1(s: Sender, r: Receiver) = send 1 to s; proc2(s, r)
            proc2(s: Sender, r: Receiver) = let v = recv r in proc3(v, s, r)
            proc3(v: int, s: Sender, r: Receiver) = spawn(drop(s, r)); assert(v == 1)
            assert(cond: int) = if cond then unit() else fail()
            unit() = ()
            fail() = fail
            drop(s: Sender, r: Receiver) = ()
        "#;
        let program = parser::parse_program(input).expect("valid core program");

        assert_eq!(
            program.to_string(),
            "\
init = main()

main() = new s, r in proc1(s, r)
assert(cond: int) = if cond then unit() else fail()
drop(s: Sender, r: Receiver) = ()
fail() = fail
proc1(s: Sender, r: Receiver) = send 1 to s; proc2(s, r)
proc2(s: Sender, r: Receiver) = let v = recv r in proc3(v, s, r)
proc3(v: int, s: Sender, r: Receiver) = spawn(drop(s, r)); assert(v == 1)
unit() = ()"
        );

        parser::parse_program(&program.to_string()).expect("printed program parses");
    }

    #[test]
    fn keeps_expression_precedence_readable() {
        let expr = Expr::Op(
            Box::new(Expr::Op(
                Box::new(Expr::Var("recv1".to_string())),
                OpKind::Add,
                Box::new(Expr::Var("recv2".to_string())),
            )),
            OpKind::Eq,
            Box::new(Expr::Op(
                Box::new(Expr::Var("n".to_string())),
                OpKind::Mul,
                Box::new(Expr::Num(2)),
            )),
        );

        assert_eq!(expr.to_string(), "recv1 + recv2 == n * 2");
    }

    #[test]
    fn parenthesizes_right_associative_shapes() {
        let expr = Expr::Op(
            Box::new(Expr::Var("a".to_string())),
            OpKind::Sub,
            Box::new(Expr::Op(
                Box::new(Expr::Var("b".to_string())),
                OpKind::Sub,
                Box::new(Expr::Var("c".to_string())),
            )),
        );

        assert_eq!(expr.to_string(), "a - (b - c)");
    }
}
