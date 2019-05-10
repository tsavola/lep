// Copyright (c) 2019 Timo Savola. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

use super::eval::Ref;
use super::obj::{Name, Obj, Pair};

/// Stringify (), bool, i64, String, Ref or Pair.  String will be quoted.  None
/// is returned if the type is not supported.
pub fn stringify(x: &Obj) -> Option<String> {
    if x.is::<Pair>() {
        let mut s = String::new();
        s.push('(');
        s.push_str(&stringify_inner(x).unwrap());
        s.push(')');
        Some(s)
    } else {
        stringify_inner(x)
    }
}

fn stringify_inner(x: &Obj) -> Option<String> {
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
        let mut s = String::new();
        stringify_explicit(&mut s, &p.0);
        if p.1.is::<()>() {
            // Nothing.
        } else if p.1.is::<Pair>() {
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

fn stringify_explicit(dest: &mut String, x: &Obj) {
    if let Some(s) = stringify(&x) {
        dest.push_str(&s);
    } else {
        dest.push('?');
    }
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
    }
}
