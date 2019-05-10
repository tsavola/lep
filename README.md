# Lep

Mini language for interactive consoles, featuring small code footprint.  It's
essentially a sugarcoated Lisp subset, approximating shell syntax, influenced
by Python.

The core language is functional/declarative.  It's not Turing complete:
function creation, looping and recursion are not supported.  Variable binding
is supported at the top-level (session scope).  Extension functions may
introduce side-effects.

The idea is that the Rust program (which embeds Lep) implements extension
functions, effectively creating a domain-specific query or administration
language.  The host program is also responsible for setting up the REPL
(read-eval-print-loop), thus choosing where the input is read from and what
gets printed.


## Syntax

Evaluation is line-oriented: one line corresponds to one statement.  A
statement yields an observable result value.

Statement syntax (both parts are optional):

    !variable expression

The variable name is any character string excluding whitespace, `(` and `)`.
The expression is an otherwise usual
[s-expression](https://en.wikipedia.org/wiki/S-expression), but the outermost
parentheses may be omitted.

The statement yields the value of the expression.  If the `!` prefix is
present, the value is also assigned to a variable.  If variable name is empty,
an unused name is chosen (e.g. `$1`).  If the `!` prefix is omitted, the value
is assigned to the `_` variable.  If the expression is omitted, the `_`
variable is evaluated.

Examples:

    >> echo "foo"
    foo
    >> + 1 2 3
    6
    >> (+ _ 10)
    16
    >> * (/ (- 10 5) 2) 50
    100
    >> ()
    >> cons 1 2
    (1 . 2)
    >> list 1 2
    (1 2)
    >> ! + 1 2 3
    $1 = 6
    >> !x + 1 2 3
    x = 6
    >> !y (* x 2)
    y = 12
    >> and (or (and x y) (or)) true false
    false
    >> !z
    z = false
    >> !
    $2 = false
    >> env
    (($2 . false) (z . false) (y . 12) (x . 6) ($1 . 6))

The statement syntax is optimized for two-step usage:

  1. Evaluate an expression
  2. Decide whether the result is worth remembering!

An expression without outer parentheses evaluates a variable/literal or invokes
a function depending on the type of the first term.  Therefore it's not
possible to directly get a reference to a function.  However, the built-in
`identity` function can be used to work around that:

    >> identity echo
    <function echo>
    >> _ "bar"
    bar

When the first term is a variable or a literal and there are multiple terms,
the expression is quoted:

    >> 1 2 3
    (1 2 3)

A statement consisting only of whitespace yields `()` and leaves the variables
unchanged.  When the user inputs an empty line, the embedder program doesn't
need to evaluate it, and may do something else instead.


## Functions

Built-in functions:

```scheme
(and arg1 arg2 ...)
(or arg1 arg2 ...)
(apply function arguments)
(+ arg1 arg2 ...)
(- arg1 arg2 ...)
(* arg1 arg2 ...)
(/ arg1 arg2 ...)
(car arg)
(cdr arg)
(cons arg1 arg2)
(list arg1 arg2 ...)
(not arg)
(identity arg)
(env)
```

Custom extension functions have signature
`fn(args: &Rc<dyn Any>) -> Result<Rc<dyn Any>, String>`
or implement the `lep::Fun` or the `lep::FunMut` trait.


## Types

Lep has a dynamic and open-ended type system.  Type `Rc<dyn Any>` (aliased as
`lep::Obj`) is used to pass immutable values to and from functions.  Extension
functions may return and accept custom types, but they cannot be used with
built-in arithmetic functions, and logical functions will treat their values as
truthful.

Fully supported types:

- `()`
- `bool`
- `i64`
- `String`
- `lep::Name` (symbol)
- `lep::Ref` (function)
- `lep::Pair` (cons cell, e.g. a list node)

The following values are considered untrue:

- `()`
- `false`
- `0` (only i64)
- `""` (only String)


## Evaluation

Extension functions are bound to a `lep::Domain` object:

```rust
let mut domain = lep::Domain::new();
lep::builtin::register(&mut domain);
domain.register("nop", |args: &lep::Obj| Ok(lep::obj::nil()));
```

An evaluation iteration takes an existing `lep::State` and replaces it with a
new one:

```rust
let mut state = lep::State::new();
loop {
    match lep::eval_stmt(&mut domain, state.clone(), read_line()) {
        Ok(new_state) => {
            // Print result here.
            state = new_state;
        }
        Err(msg) {
            println!("error: {}", msg);
        }
    }
}
```
