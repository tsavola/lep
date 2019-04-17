# Lep

Mini language for interactive consoles, featuring small code and memory
footprint.  It's essentially a sugarcoated Lisp subset, approximating shell
syntax, influenced by Python.

The core language is functional/declarative.  It's not Turing complete:
function creation, looping and recursion are not supported.  Variable binding
is supported at the top-level (session scope).  Extension functions may
introduce side-effects.

The idea is that the Rust program (which embeds Lep) implements extension
functions, effectively creating a domain-specific query or administration
language.  The host program is also responsible for setting up the
read-eval-print-loop (REPL) which calls Lep (for parsing and evaluation), thus
choosing where the input is read from and what gets printed.


## Syntax

Evaluation is line-oriented: one line corresponds to one statement.  A
statement yields an observable result value.

Statement syntax (both parts are optional):

    !variable expression

The variable name is any character string excluding whitespace, `(` and `)`
characters.  The expression is an otherwise usual
[S-expression](https://en.wikipedia.org/wiki/S-expression), but the outermost
parentheses may be omitted in some cases (when the first term is an atom).

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

The statement syntax is optimized for two-step usage:

  1. Evaluate an expression
  2. Decide whether the result is worth remembering!

An expression without outer parentheses evaluates a variable/literal or invokes
a function depending on the type of the first term.  Therefore it's not
possible to directly get a reference to a function.  However, the built-in
identity function can be used to work around that:

    >> identity echo
    <function echo>
    >> _ "bar"
    bar

Some expressions cannot be written without outer parentheses; the first one of
these statements doesn't work, but the second one does:

    >> (choose-operator) arg
    parse error
    >> ((choose-operator) arg)
    42

A statement consisting only of whitespace yields nil and leaves the variables
unchanged.  When the user inputs an empty line, the embedder program doesn't
need to evaluate it, and may display something else.


## Functions

Special forms are implemented internally:

```scheme
(and arg1 arg2 ...)
(or arg1 arg2 ...)
```

Built-in functions (optional):

```scheme
(+ arg1 arg2 ...)
(- arg1 arg2 ...)
(* arg1 arg2 ...)
(/ arg1 arg2 ...)
(identity arg)
(not arg)
```

Custom extension functions implement the `lep::Fun` or the `lep::FunMut` trait:

```rust
struct Println;

impl lep::Fun for Println {
    fn invoke(&self, args: Vec<Rc<dyn Any>>) -> Option<Rc<dyn Any>> {
        for x in args {
            print!("{}", lep::stringify(x));
        }
        println!("");
        Some(Rc::new(()))
    }
}
```


## Types

Lep has a dynamic and open-ended type system.  Type `Rc<dyn Any>` is used to
pass immutable values to and from functions.  Extension functions may return
and accept custom types, but they cannot be used with built-in arithmetic
functions, and logic functions will treat all values as truthful.

Fully supported types:

- `()`
- `bool`
- `i64`
- `String`
- `lep::Ref` (function)

The following values are considered untrue:

- `()`
- `false`
- `0` (only i64)
- `""` (only String)


## Evaluation

Extension functions are bound to a `lep::Env` object:

```rust
let my_println = Println {};
let mut env = lep::Env::new();
lep::builtin::register_all(&mut env);
env.register("println", &my_println);
```

An evaluation iteration takes an existing `lep::State` and replaces it with a
new one:

```rust
let mut state = lep::State::new();
loop {
    if let Some(new_state) = lep::eval_stmt(read_line(), state.clone(), &mut env) {
        state = new_state;
    }
}
```
