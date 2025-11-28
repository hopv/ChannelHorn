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
            Term::Int(i) => write!(f, "{}", i),
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
            Term::Nil => write!(f, "nil"),
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
            super::Type::List => write!(f, "Lst"),
            super::Type::Pair => write!(f, "Pair"),
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

static PROLOGUE: &str = "\
(set-logic HORN)

(declare-datatypes ((Pair 0))
  (((mk (key Int) (val Int)))))             ; a pair (t,v)

(declare-datatypes ((Lst 0))
  (((nil) (cons (head Pair) (tail Lst))))) ; [] | (p :: rest)";

static NO_TIMESTAMPS_PROLOGUE: &str = "\
(set-logic HORN)

(declare-datatypes ((Lst 0))
  (((nil) (cons (head Int) (tail Lst))))) ; [] | (n :: rest)";

static EPILOGUE: &str = "(check-sat)";

impl fmt::Display for super::CHC {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.setting.no_timestamps {
            write!(f, "{}\n\n", NO_TIMESTAMPS_PROLOGUE)?;
        } else {
            write!(f, "{}\n\n", PROLOGUE)?;
        }
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
