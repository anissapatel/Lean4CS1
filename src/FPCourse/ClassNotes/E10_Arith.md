# A Language of Arithmetic, in Lean
```lean
namespace Arith
```

## Syntax
```lean
inductive ArithExpr where
| lit (n : Nat) : ArithExpr
| add (e1 e2 : ArithExpr) : ArithExpr
open ArithExpr

-- examples expressions using our syntax
def e1 : ArithExpr := lit 1
def e7 : ArithExpr := lit 7
def e3 : ArithExpr := add e1 e7
def e4 : ArithExpr :=   -- 7 + (6 + 9)
  add
    (lit 7)
    (add
      (lit 6)
      (lit 9)
    )
```

# Operational Semantics
```lean
def arithEval : ArithExpr → Nat
| lit n => n
| add e1 e2 => (arithEval e1) + (arithEval e2)

-- and here's what it means: 22
#eval arithEval e4
```

## To Prepare For Next Class

To be prepared to participate in the
conversation in next class, which I do
strongly recommend to you all, please
do the following before next class.

(1) add support for the following forms
- inc (n : Nat)   -- will mean *add 1*
- mul (n m : Nat) -- will mean n * m
- exp (n m : Nat) -- will mean n ^ m
- tet (n m : Nat) -- n^n^n... m times
- var (v : Var)   -- needs *interpretation*

(2) To handle `var` you will need
to add a `Var` type. Go study how
we did this for variable exprssions
in propositional logic. It's okay,
as in that code, to define a Var
type with just a few instances, such
as X, Y, Z, and W (four constructors
with these names) A better design is
one with a single Var constructor that
takes a Nat "index" to distinguish one
variable from another. Then you can do
this: `def X := Var.mk 0`, then define
`Y := Var.mk 1`, and so forth. You'll
then have a `Var` type supporting an
infinite set of variables, *indexed by
natural numbers*, and you can bind nice
names to any finite number of them you
plan to use in a given application. An
*interpretation* is then a function from
Nat-indexed variable objects to Nat values.
NB: The index is *not* the value of the
variable, it's what makes one variable
distinct from another. Again, you will
define a separate interpretation function
to model the binding of these `Var` objects
to different Nat values.

It will look something like this:

```lean
define varInterp : Var → Nat
| Var.mk 0 => 6   -- evaluate X (Var 0) to 6
| Var.mk 1 => 2   -- evaluate Y to 2
| Var.mk 2 => 11  -- evaluate Z to 11
| Var.mk 3 => 1   -- evaluate W to 1
| Var.mk _ => 0   -- otherwise 0
```

Note that you need that last case to
make the varInterp function total, as
there is now an infinitude of distinct
`Var` values.

Then just as we did with propositional
logic as we embedded it in Lean, you'll
need to update the `arithEval` semantic
evaluator to take not only an expression
but also a variable interpretation as its
arguments. Evaluating an arithmetic expr
then produces different answers in general
for different interpretations. To be very
concrete about it, evaluating *X + Y* under
an interpretation, *{ X => 1, Y => 2}* will
in general produce different value under
different interpretations. Here it's 3, but
evaluating *X + Y* under *{ X => 3, Y => 2}*
will give *5* as its meaning under this new
interpretation.
```lean
end Arith
```


<div class="issue-box">📝 <a href="https://github.com/kevinsullivan/Lean4CS1/issues/new">Report an issue</a> with this section</div>

