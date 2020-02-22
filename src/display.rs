// Copyright (c) 2019 Timo Savola. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

use super::eval::Ref;
use super::obj::{Name, Obj, Pair};

/// Stringify (), bool, i64, String, Ref or Pair.  String will be quoted.  None
/// is returned if the type is not supported.
pub fn stringify(x: &Obj) -> Option<String> {
    stringify_ex(x, |_: &Obj| None)
}

/// Stringify custom types.  All values (except pairs) are passed to the
/// supplied function first; if it returns None, the default implementation
/// (see `stringify`) is used.
pub fn stringify_ex<F: Fn(&Obj) -> Option<String> + Clone>(x: &Obj, f: F) -> Option<String> {
    if x.is::<Pair>() {
        let mut s = String::new();
        s.push('(');
        s.push_str(&stringify_inner(x, f).unwrap_or("?".to_string()));
        s.push(')');
        Some(s)
    } else {
        stringify_inner(x, f)
    }
}

fn stringify_inner<F: Fn(&Obj) -> Option<String> + Clone>(x: &Obj, f: F) -> Option<String> {
    if let Some(s) = f(x) {
        return Some(s);
    }

    if x.is::<()>() {
        return Some("()".to_string());
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

    if let Some(n) = x.downcast_ref::<Name>() {
        return Some(n.0.clone());
    }

    if let Some(r) = x.downcast_ref::<Ref>() {
        return Some(r.to_string());
    }

    if let Some(p) = x.downcast_ref::<Pair>() {
        let mut s = stringify_ex(&p.0, f.clone()).unwrap_or("?".to_string());
        if !p.1.is::<()>() {
            if p.1.is::<Pair>() {
                s.push(' ');
            } else {
                s.push_str(" . ");
            }
            s.push_str(&stringify_inner(&p.1, f).unwrap_or("?".to_string()));
        }
        return Some(s);
    }

    None
}

#[cfg(test)]
mod tests {
    use super::super::obj;
    use super::*;

    #[test]
    fn test_list() {
        assert_eq!(
            stringify(&obj::pair(obj::int(1), obj::int(2))).unwrap(),
            "(1 . 2)"
        );

        assert_eq!(
            stringify(&obj::pair(
                obj::int(1),
                obj::pair(obj::int(2), obj::pair(obj::int(3), obj::nil()))
            ))
            .unwrap(),
            "(1 2 3)"
        );

        assert_eq!(
            stringify(&obj::pair(
                obj::pair(obj::int(1), obj::int(2)),
                obj::pair(obj::int(3), obj::nil())
            ))
            .unwrap(),
            "((1 . 2) 3)"
        );

        assert_eq!(
            stringify(&obj::pair(obj::pair(obj::int(1), obj::int(2)), obj::int(3))).unwrap(),
            "((1 . 2) . 3)"
        );

        assert_eq!(
            stringify(&obj::pair(
                obj::int(1),
                obj::pair(obj::pair(obj::int(2), obj::int(3)), obj::nil())
            ))
            .unwrap(),
            "(1 (2 . 3))"
        );

        assert_eq!(
            stringify(&obj::pair(obj::int(1), obj::pair(obj::nil(), obj::nil()))).unwrap(),
            "(1 ())"
        );

        assert_eq!(
            stringify(&obj::pair(obj::int(1), obj::nil())).unwrap(),
            "(1)"
        );
    }
}
