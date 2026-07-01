use std::fmt;

use super::{PredicateAtom, Term};

impl fmt::Display for PredicateAtom {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let args_str: Vec<String> = self.args.iter().map(|arg| format!("{}", arg)).collect();
        write!(f, "(%{} {})", self.name, args_str.join(" "))
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Term::Var(v) => write!(f, "%{}", v),
            Term::Int(i) if *i < 0 => write!(f, "(- {})", i.unsigned_abs()),
            Term::Int(i) => write!(f, "{}", i),
            Term::Ctor { name, args } if args.is_empty() => write!(f, "{}", name),
            Term::Ctor { name, args } => {
                let args_str: Vec<String> = args.iter().map(|arg| format!("{}", arg)).collect();
                write!(f, "({} {})", name, args_str.join(" "))
            }
            Term::Add(lhs, rhs) => write!(f, "(+ {} {})", lhs, rhs),
            Term::Sub(term, term1) => write!(f, "(- {} {})", term, term1),
            Term::Mul(term, term1) => write!(f, "(* {} {})", term, term1),
            Term::Bool(b) => write!(f, "{}", b),
            Term::LOr(lhs, rhs) => write!(f, "(or {} {})", lhs, rhs),
            Term::Eq(lhs, rhs) => write!(f, "(ite (= {} {}) 1 0)", lhs, rhs),
            Term::Ne(term, term1) => write!(f, "(ite (not (= {} {})) 1 0)", term, term1),
            Term::Lt(term, term1) => write!(f, "(ite (< {} {}) 1 0)", term, term1),
            Term::Le(term, term1) => write!(f, "(ite (<= {} {}) 1 0)", term, term1),
            Term::Gt(term, term1) => write!(f, "(ite (> {} {}) 1 0)", term, term1),
            Term::Ge(term, term1) => write!(f, "(ite (>= {} {}) 1 0)", term, term1),
            Term::Cons(head, tail) => write!(f, "(cons {} {})", head, tail),
            Term::Nil(ty) => write!(f, "(as nil {})", ty),
            Term::Pair(first, second) => write!(f, "(mk {} {})", first, second),
            Term::Head(term) => write!(f, "(head {})", term),
            Term::Tail(term) => write!(f, "(tail {})", term),
            Term::Key(term) => write!(f, "(key {})", term),
            Term::Val(term) => write!(f, "(val {})", term),
        }
    }
}

impl fmt::Display for super::Constraint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            super::Constraint::Eq(term, term1) => write!(f, "(= {} {})", term, term1),
            super::Constraint::Ne(term, term1) => write!(f, "(not (= {} {}))", term, term1),
            super::Constraint::Lt(term, term1) => write!(f, "(< {} {})", term, term1),
            super::Constraint::Le(term, term1) => write!(f, "(<= {} {})", term, term1),
        }
    }
}

impl fmt::Display for super::Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            super::Type::Int => write!(f, "Int"),
            super::Type::Bool => write!(f, "Bool"),
            super::Type::Adt(name) => write!(f, "{}", name),
            super::Type::Lst(inner) => write!(f, "(Lst {})", inner),
            super::Type::Pair(first, second) => write!(f, "(Pair {} {})", first, second),
            super::Type::Func { args } => {
                let args_str: Vec<String> = args.iter().map(|arg| format!("{}", arg)).collect();
                write!(f, "({}) Bool", args_str.join(" "))
            }
        }
    }
}

impl fmt::Display for super::Body {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let preds_str: Vec<String> = self
            .predicates
            .iter()
            .map(|pred| format!("{}", pred))
            .collect();
        let constraints_str: Vec<String> = self
            .constraints
            .iter()
            .map(|constraint| format!("{}", constraint))
            .collect();
        let all_parts = [preds_str, constraints_str].concat();
        if all_parts.is_empty() {
            write!(f, "true")
        } else {
            write!(
                f,
                "(and {})",
                all_parts.join(&format!("\n{}", " ".repeat(4 + 9)))
            )
        }
    }
}

impl fmt::Display for super::Clause {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let forall_str: Vec<String> = self
            .forall
            .iter()
            .map(|(var, ty)| format!("(%{} {})", var, ty))
            .collect();
        let head_str = match &self.head {
            Some(head) => format!("{}", head),
            None => "false".to_string(),
        };
        write!(f, "(assert ")?;
        if self.forall.is_empty() {
            write!(f, "(=> {}\n    {})", self.body, head_str)?;
        } else {
            write!(
                f,
                "(forall ({})\n    (=> {}\n        {}))",
                forall_str.join(" "),
                self.body,
                head_str
            )?;
        }
        write!(f, ")")
    }
}

static DATATYPES_PROLOGUE: &str = "\
(set-logic HORN)

(declare-datatypes ((Pair 2))
  ((par (A B) ((mk (key A) (val B))))))

(declare-datatypes ((Lst 1))
  ((par (T) ((nil) (cons (head T) (tail (Lst T)))))))";

static EPILOGUE: &str = "(check-sat)";

fn write_prologue(f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "{DATATYPES_PROLOGUE}\n\n",)
}

impl fmt::Display for super::Datatype {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let variants = self
            .variants
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join(" ");
        write!(
            f,
            "(declare-datatypes (({} 0))\n  (({})))",
            self.name, variants
        )
    }
}

impl fmt::Display for super::DatatypeVariant {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.fields.is_empty() {
            return write!(f, "({})", self.name);
        }
        let fields = self
            .fields
            .iter()
            .map(|(name, ty)| format!("({} {})", name, ty))
            .collect::<Vec<_>>()
            .join(" ");
        write!(f, "({} {})", self.name, fields)
    }
}

impl fmt::Display for super::CHC {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write_prologue(f)?;
        if !self.datatypes.is_empty() {
            let datatype_declarations = self
                .datatypes
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join("\n\n");
            write!(f, "{}\n\n", datatype_declarations)?;
        }
        write!(f, "\n\n")?;
        let fun_declarations_str: Vec<String> = self
            .fun_declarations
            .iter()
            .map(|(name, types)| {
                let types_str: Vec<String> = types.iter().map(|ty| format!("{}", ty)).collect();
                format!("(declare-fun %{} ({}) Bool)", name, types_str.join(" "))
            })
            .collect();
        let clauses_str: Vec<String> = self
            .clauses
            .iter()
            .map(|clause| format!("{}", clause))
            .collect();
        write!(f, "{}\n\n", fun_declarations_str.join("\n"))?;
        write!(f, "{}", clauses_str.join("\n\n"))?;
        write!(f, "\n\n{}", EPILOGUE)
    }
}
