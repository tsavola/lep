// Copyright (c) 2019 Timo Savola. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

use std::any::Any;
use std::rc::Rc;

pub mod builtin;
mod eval;
mod parse;

pub use eval::{eval_stmt, Env, Fun, FunMut, Ref, State};

/// Stringify (), bool, i64, String or Ref.  () is represented by the empty
/// string.  String will be quoted.  None is returned if the type is not
/// supported.
pub fn stringify(x: Rc<dyn Any>) -> Option<String> {
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

    None
}
