Your job for this assignment is to implement a compiler that maps
MLish, a subset of ML, down to Scish.  To do so, you must complete two
tasks: (1) type-checking (including inference) for MLish, and (2) a
translation from MLish AST to Scish AST (which, you can compile to
Cish, which you can compile to Mips.)

The file mlish_ast.ml defines the abstract syntax for the ML subset
that we will be using, and the files ml_lex.mll and ml_parse.mly
provide the lexer and parser for the language.  The language is really
very cut down --- there's no support for modules, references, pattern
matching, type declarations, type annotations, or even recursive
functions. Thus, the bulk of the work is in implementing type
inference.

To test out your ML code, instead of providing an interpreter, you can
simply evaluate the code in OCaml toplevel to see what value you get
back.  You should get back an equivalent value when you compile the
code to Scish and run it in the Scish interpreter. When testing your
compilation code, we will be running it on closed programs of type
int, so it's up to you to decide about how other types of values are
represented.

To run MLish code directly in OCaml, you will need to add a few
definitions to the initial basis such as:

   let isnil x = match x with [] -> true | _ -> false

Make sure to test your code on all of the language forms.  Take a look
at mlish_ast.ml carefully to understand the primitives and the types
that need to be supported.

To construct the type-checker for MLish, modify the definition in
mlish_type_check.ml. You should follow (roughly) the notes presented
in class for doing ML-style type inference.  You do not need to worry
about side-effects (since the language doesn't have any!) or
refinements/sub-typing (because the language hast Int_ but not the
more refined types such as Pos_t or Neg_t that we discussed in class).
The function type_check_exp should return the type of the input (if it
has one), and otherwise should raise the exception TypeError if the
program is not well typed.

To implement compilation, edit the definition in mlish_compile.ml.  I
will leave it up to you how to compile code to Scish, but it's
relatively easy to do compared to the type checking part of the assignment.

To submit your work, upload both mlish_type_check.ml and
mlish_compile.ml to the autograder on GradeScope when it goes live.

Running make generates an executable called ./ps6_mlish. You can
invoke this one of two ways by passing either the argument "typecheck"
or "compile" to the executable.  For example, running

./ps6_mlish typecheck tests/test5.ml

Runs just your typechecker on the test file tests/test5.ml and prints
out the inferred type for the expression, or prints "Type Error" if
the program does not type check. Types are printed in format similar to OCaml,
with -> representing functions, and ' representing a type variable. For example,
on the example tests/idtest2.ml, the reference solution produces the type:

(int) * (('ptvar0) list)

Whereas if I copy and paste the same example into ocaml or utop REPL, OCaml prints

int * 'a list 

for the type, which you can see is the same up to extra parentheses and a different
name for the type variable.

For testing compilation, you can run

./ps6_mlish compile tests/test5.ml

which first typechecks the program, then if there are no type errors,
it compiles it to Scish, runs the Scish evaluator, and prints the
answer. Again, when testing your compilation code, we will be running
it on closed programs of type int, so it's up to you to pick a
convention for how you represent other types of values.

Hint: Getting the ML style let polymorphism that we described in class
to work is the most conceptually difficult part of the
assignment. Thus, if you're just trying to get the bulk of credit, we
suggest delaying that and just trying to get non-polymorphic examples
working first.
