// Copyright (c) 2019 Timo Savola.
// Use of this source code is governed by the MIT
// license that can be found in the LICENSE file.

use std::env::args;
use std::process::exit;

use lep::{builtin, eval_stmt, stringify, Domain, State};

fn main() {
    let mut line = String::new();
    let mut it = args();
    it.next();
    for arg in it {
        line.push_str(&arg);
        line.push(' ');
    }

    let mut domain = Domain::new();
    builtin::register(&mut domain);

    let state = State::new();

    match eval_stmt(&mut domain, state, &line) {
        Ok(state) => {
            println!(
                "{}",
                stringify(&state.result.value).unwrap_or("?".to_string())
            );
        }

        Err(msg) => {
            println!("error: {}", msg);
            exit(2);
        }
    }
}
