// Copyright (c) 2019 Timo Savola. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

use std::any::Any;
use std::rc::Rc;

/// Obj can be any object.
pub type Obj = Rc<dyn Any>;

#[derive(Eq, PartialEq)]
pub(crate) struct Name(pub String);

/// Pair may be a node in a singly linked list.
pub struct Pair(pub Obj, pub Obj);

/// () object.
pub fn nil() -> Obj {
    Rc::new(())
}

/// bool object.
pub fn boolean(b: bool) -> Obj {
    Rc::new(b)
}

/// i64 object.
pub fn int(n: i64) -> Obj {
    Rc::new(n)
}

/// String object.
pub fn string(s: String) -> Obj {
    Rc::new(s)
}

/// Name object.
pub(crate) fn name(s: String) -> Obj {
    Rc::new(Name(s))
}

/// Construct a Pair object.
pub fn pair(car: Obj, cdr: Obj) -> Obj {
    Rc::new(Pair(car, cdr))
}
