// The Aeneas String probe (#282 / TR-080; docs/design/flattener-proof.md
// spike B2): term.rs's shape with String names kept, `Sort` renamed, no
// derives inside the unit, and the three String operations a name table
// needs (==, len, as_bytes) plus a lookup over &[String]. Run by
// scripts/aeneas_string_probe.sh; NOT part of any crate.
#![allow(dead_code)]

pub struct BvSort {
    pub width: u32,
}

#[non_exhaustive]
pub enum BvTerm {
    Const { value: u64, sort: BvSort },
    Var { name: String, sort: BvSort },
    Add(Box<BvTerm>, Box<BvTerm>),
    Ite { cond: Box<BoolTerm>, then_: Box<BvTerm>, else_: Box<BvTerm> },
}

#[non_exhaustive]
pub enum BoolTerm {
    True,
    Eq(Box<BvTerm>, Box<BvTerm>),
    Not(Box<BoolTerm>),
}

pub fn name_eq(a: &String, b: &String) -> bool {
    a == b
}

pub fn name_len(a: &String) -> usize {
    a.len()
}

pub fn name_byte(a: &String, j: usize) -> u8 {
    a.as_bytes()[j]
}

pub fn lookup(names: &[String], n: &String) -> Option<usize> {
    let mut i = 0;
    while i < names.len() {
        if name_eq(&names[i], n) {
            return Some(i);
        }
        i += 1;
    }
    None
}

pub fn size_bv(t: &BvTerm) -> usize {
    match t {
        BvTerm::Const { .. } => 1,
        BvTerm::Var { name, .. } => 1 + name_len(name),
        BvTerm::Add(a, b) => 1 + size_bv(a) + size_bv(b),
        BvTerm::Ite { cond, then_, else_ } => 1 + size_bool(cond) + size_bv(then_) + size_bv(else_),
    }
}

pub fn size_bool(t: &BoolTerm) -> usize {
    match t {
        BoolTerm::True => 1,
        BoolTerm::Eq(a, b) => 1 + size_bv(a) + size_bv(b),
        BoolTerm::Not(a) => 1 + size_bool(a),
    }
}
