// Copyright (c) 2019 Timo Savola.
// Use of this source code is governed by the MIT
// license that can be found in the LICENSE file.

//! An interpreter for implementing interactive consoles.

pub mod builtin;
pub mod display;
mod eval;
pub mod obj;
mod parse;

pub use display::stringify;
pub use eval::{eval_stmt, Domain, Fun, FunMut, Ref, Res, State};
pub use obj::{Name, Obj, Pair};
