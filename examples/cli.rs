// Copyright (c) 2019 Timo Savola. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

use std::env::args;
use std::process::exit;

use lep::{builtin, eval_stmt, stringify, Env, State};

fn main() {
    let mut line = String::new();
    let mut it = args();
    it.next();
    for arg in it {
        line.push_str(&arg);
        line.push(' ');
    }

    let mut env = Env::new();
    builtin::register_all(&mut env);

    let state = State::new(&env);

    match eval_stmt(&mut env, state, &line) {
        Ok(state) => {
            if let Some(repr) = stringify(state.result.value.clone()) {
                if repr.len() > 0 {
                    println!("{}", repr);
                }
            } else {
                exit(1);
            }
        }

        Err(msg) => {
            println!("error: {}", msg);
            exit(2);
        }
    }
}
