use crate::ast::VarName;

pub type PredicateName = String;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PredicateAtom {
    pub name: PredicateName,
    pub args: Vec<Term>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Term {
    Var(VarName),
    Int(i32),
    Add(Box<Term>, Box<Term>),
    Bool(bool),
    LOr(Box<Term>, Box<Term>),
    Eq(Box<Term>, Box<Term>),
    Cons(Box<Term>, Box<Term>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Constraint {
    Eq(Term, Term),
    Ne(Term, Term),
    Lt(Term, Term),
    Le(Term, Term),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    Int,
    Bool,
    List,
    Pair,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Clause {
    pub head: PredicateAtom,
    pub body: Vec<PredicateAtom>,
    pub constraints: Vec<Constraint>,
    pub query: Option<PredicateAtom>,
    pub rel_declarations: Vec<(PredicateName, Vec<Type>)>,
    pub var_declarations: Vec<(VarName, Type)>,
}

pub mod translation;
