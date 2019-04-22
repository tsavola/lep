// Copyright (c) 2019 Timo Savola. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

//! An interpreter for implementing interactive consoles.
//!
//! See https://crates.io/crates/lep for an overview.

use std::any::Any;
use std::rc::Rc;

pub mod builtin;
mod eval;
mod parse;

pub use eval::{eval_stmt, Domain, Fun, FunMut, Pair, Ref, State, World};

/// Stringify (), bool, i64, String, Ref or Pair.  () is represented by the
/// empty string.  String will be quoted.  None is returned if the type is not
/// supported.
pub fn stringify(x: Rc<dyn Any>) -> Option<String> {
    if let Some(_) = x.downcast_ref::<Pair>() {
        let mut s = String::new();
        s.push('(');
        s.push_str(&stringify_inner(&x).unwrap());
        s.push(')');
        Some(s)
    } else {
        stringify_inner(&x)
    }
}

fn stringify_inner(x: &Rc<dyn Any>) -> Option<String> {
    if let Some(_) = x.downcast_ref::<()>() {
        return Some("".to_string());
    }

    if let Some(b) = x.downcast_ref::<bool>() {
        return Some(b.to_string());
    }

    if let Some(n) = x.downcast_ref::<i64>() {
        return Some(n.to_string());
    }

    if let Some(s) = x.downcast_ref::<String>() {
        let escaped = s.escape_debug().to_string();
        let mut quoted = String::with_capacity(escaped.len() + 2);
        quoted.push('"');
        quoted.push_str(&escaped);
        quoted.push('"');
        return Some(quoted);
    }

    if let Some(r) = x.downcast_ref::<Ref>() {
        return Some(r.to_string());
    }

    if let Some(p) = x.downcast_ref::<Pair>() {
        let mut s = String::new();
        stringify_explicit(&mut s, &p.0);
        if let Some(_) = p.1.downcast_ref::<()>() {
            // Nothing.
        } else if let Some(_) = p.1.downcast_ref::<Pair>() {
            s.push(' ');
            s.push_str(&stringify_inner(&p.1).unwrap());
        } else {
            s.push_str(" . ");
            stringify_explicit(&mut s, &p.1);
        }
        return Some(s);
    }

    None
}

fn stringify_explicit(dest: &mut String, x: &Rc<dyn Any>) {
    if let Some(_) = x.downcast_ref::<()>() {
        dest.push_str("()");
    }

    if let Some(s) = stringify(x.clone()) {
        dest.push_str(&s);
    } else {
        dest.push('?');
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_list() {
        assert_eq!(
            stringify(Rc::new(Pair(Rc::new(1 as i64), Rc::new(2 as i64)))).unwrap(),
            "(1 . 2)"
        );

        assert_eq!(
            stringify(Rc::new(Pair(
                Rc::new(1 as i64),
                Rc::new(Pair(
                    Rc::new(2 as i64),
                    Rc::new(Pair(Rc::new(3 as i64), Rc::new(())))
                ))
            )))
            .unwrap(),
            "(1 2 3)"
        );
    }
}
