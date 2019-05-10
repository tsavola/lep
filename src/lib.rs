// Copyright (c) 2019 Timo Savola. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

//! An interpreter for implementing interactive consoles.

pub mod builtin;
mod eval;
pub mod obj;
mod parse;
mod stringify;

pub use eval::{eval_stmt, Domain, Fun, FunMut, Ref, State};
pub use obj::{Name, Obj, Pair};
pub use stringify::stringify;
