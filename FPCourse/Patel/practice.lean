namespace KNat

/- @@@
### KNat type

Our `KNat` (from scratch) type just mimics Nat.
@@@ -/

inductive KNat where
| zero
| succ (n : KNat)


/- @@@
### Special Values

The `KNat` type provides not only the visible
constructors but also a recursor that enables
definitions of total functions from this type.
As a start, we can bind mnemonic identifiers
to special values of type type, which include
terms representing zero (`KNat.zero`) and one
(`KNat.succ KNat.zero`).
@@@ -/

def kzero := KNat.zero
def kone := KNat.succ kzero
def ktwo := KNat.succ kone
def kthree := KNat.succ ktwo


/- @@@
### Operations

We implement arithmetic operations on our
custom representation of natural numbers as
total functions in Lean. Total functions are
ultimately supported by the basic induction
principle for the `KNat` type. But applying
these functions directly is something almost
no one would do, as Lean provides supportive
notations. You'd thus see definitions such
as those that follow here. Look for the step
functions when you study this material (hint:
as defined in non-base cases).

@@@ -/

-- Increment: no need to destructure argument
def inc (n: KNat) := n.succ   -- Notation for KNat.succ n

-- Decrement: must destructure (pattern match) argument
-- So the argument must be to the right of the colon
def dec : KNat → KNat
| KNat.zero => kzero          -- decrement zero is zero (truncation)
| KNat.succ n' => n'          -- decrement *one more than any n'* is n'

/- @@@
Recursive Arithmetic Functions
@@@ -/

/- @@@
We start on the recursive functions with
addition implemented, by case analysis on
its second argument and use of induction.
If the second argument is zero, we return
the first argument. If it's one more than
`n'` we return the successor of the sum of
the first argument and n'. This maneuver just
rewrites `a +  (b + 1)` as `1 + (a + b)` and
then evaluates `a + b` by recursion. At the
end of the day, the add function increments
the first argument `a`, `b` times for any `b`.
@@@ -/
def add : KNat → KNat → KNat                -- Addition function
  | a, KNat.zero   => a
  | a, KNat.succ b => inc (add a b)

/- @@@
Whereas addition is interated incrementing,
multiplication is iterated addition. To get
`a * b` just add `a` to itself `b` *times*.
Adding `a` to itself zero times is defined
to be zero, which is exactly what is needed
to make our library faithful to the actual
math.
@@@ -/
def mul : KNat → KNat → KNat
| _a, KNat.zero => KNat.zero
| a, KNat.succ b => add a (mul a b)

/- @@@
Exponentiation is iterated multiplication in
just the same way. `a ^ b` is `a` *multiplied*
by itself `b` times.
@@@ -/
def exp : KNat → KNat → KNat
| _, KNat.zero => kone      -- kone is defined above
| a, KNat.succ b' =>  mul (exp a b') a

/- @@@
EXERCISE: define the tetration, call it `tet`.
Lean has no special notation for it. What it
does have is a way to take advantage of the
pattern you're seeing here. Call the `identity`
funciton the 0th hyperoperation, increment the
1st hyperop, add the 2nd, multiplication, the
3rd, and tetration the fourth. First write `tet`
following the pattern above. Second, harder,
see if you can define `hyperop`, taking three
arguments, the first being the `hyper-depth`,
in which case `tet a b` is `hyperop 4 a b`.
@@@ -/

/- @@@
### Classes
@@@ -/

/- @@@
Here's the `Zero` typeclass in Lean. An
instance associates a value, given by the
value of the field, `Add.zero`, with any
type given by `α`. We will necxt create an
instance of this class *for the KNat type*,
to define what we mean by zero for *KNat*.
```lean
class Zero (α : Type u) where
  zero : α
```
@@@ -/
instance : Zero KNat where
zero := KNat.zero

-- Among other things, `0` is now notation
#check (0 : KNat)

instance : One KNat where
one := kone
#check (1 : KNat)

instance : Add KNat where
  add := KNat.add      -- class field name on left, add function on right

instance : Mul KNat where
mul := mul

instance : Pow KNat KNat where
pow := exp

#eval (1 + 1 : KNat)
#eval ktwo * kthree
#eval ktwo ^ kthree

/- @@@
Not only do we get these notations, but
they also come (thank you Lean library)
with the right associativity, precedence,
etc.
@@@ -/

#eval ktwo *  ktwo + ktwo    -- six
#eval ktwo * (ktwo + ktwo)   -- eight!
#eval ktwo +  ktwo * ktwo    -- six
#eval ktwo + (ktwo * ktwo)   -- six

/- @@@

@@@ -/


def addAnyTypeAsLongItsAddable {α : Type} [Add α] : α → α → α
| a, b => a + b

-- add for Nat, Add Nat instance provided by library
#eval addAnyTypeAsLongItsAddable 3 4

-- add for rationals (instance defined in Lean library)
#eval (3/4: Rat) + 1/2

-- add for String? NOPE, no instance in library
-- #eval addAnyTypeAsLongItsAddable "Hi" "There"

-- -- add for KNat
#eval addAnyTypeAsLongItsAddable (1 : KNat) 1

/- @@@
EXERCISES

1. Extend KNat algebra with operations for
unary Negation and Subtraction, and instances
to provide notations and more. Use your search
engine or agent to find the names of the right
classes in Lean's libraries for these operations.

2. Replace Nat with KNat in the following
definition of the syntax and semantics of
our little language of arithmetic. Extend
the language to support the subtraction and
negation operations you've just defined.

3. Extend your language of arithmetic with
*variable* expressions, so you can write not
just, say, two plus three, but X plus 3. See
how we handled propositional variables in our
formalization of propositional logic and use
the same pattern here.

4. Provide a few examples similar to those
above, testing and showing that expressions
using subtraction, negation, and variables
work with usual precedence and associativity.
@@@ -/

def sub : KNat → KNat → KNat
| a, KNat.zero => a
| a, KNat.succ b => dec (sub a b)

-- Sub KNat is the type class here that is available to use
-- allows us to go from #eval KNat.add ktwo kthree to #eval ktwo + kthree

instance : Sub KNat where
  sub := KNat.sub

#eval sub ktwo ktwo

def KNat.eq : KNat → KNat → Bool
  | KNat.zero, KNat.zero => true
  | KNat.succ a, KNat.succ b => KNat.eq a b
  | _, _ => false

def le : KNat → KNat → Bool
  | (KNat.succ a), (KNat.succ b) => le a b
  | KNat.succ _, KNat.zero => false
  | KNat.zero, _ => true

def gt : KNat → KNat → Bool :=
  fun a b => !le a b

-- Since KNat represents only natural numbers, unary negation is implemented as truncated subtraction from zero.
--Therefore, the result is zero for every KNat value
def neg (a : KNat) : KNat :=
  sub KNat.zero a

instance : Neg KNat where
  neg := KNat.neg


#eval -kthree
#eval -ktwo
#eval -(kone + ktwo)

end KNat

namespace Arith
open KNat


inductive ArithVariable where
  | XVar
  | YVar
  | ZVar



--syntax (constructor so lit 7 is a term of this type ArithExpr)
inductive ArithExpr where
| lit (n : KNat) --this is a constructor for a literal number
| add (e1 e2 : ArithExpr) : ArithExpr --this is a constructor for addition of two arithmetic expressions
| sub (e1 e2 : ArithExpr) : ArithExpr --this is a constructor for subtraction of two arithmetic expressions
| neg (e : ArithExpr) : ArithExpr --this is a constructor for unary negation of an arithmetic expression
| var (v : ArithVariable) : ArithExpr

instance : Add ArithExpr where
  add := ArithExpr.add

instance : Sub ArithExpr where
  sub := ArithExpr.sub

instance : Neg ArithExpr where
  neg := ArithExpr.neg

def arithInterp : Type := ArithVariable → KNat
def X : ArithExpr := ArithExpr.var ArithVariable.XVar
def Y : ArithExpr := ArithExpr.var ArithVariable.YVar
def Z : ArithExpr := ArithExpr.var ArithVariable.ZVar

-- Assign numerical values to variables
def i1 : arithInterp :=
  fun (v : ArithVariable) =>
    match v with
    | ArithVariable.XVar => ktwo
    | ArithVariable.YVar => kthree
    | ArithVariable.ZVar => kone

open ArithExpr



--expressions using our syntax
def a1 : ArithExpr := lit 1
-- def a7 : ArithExpr := lit 7
def e1 : ArithExpr := lit 1
-- def e7 : ArithExpr := lit 7
-- def e3 : ArithExpr := add e1 e7
-- def a1Pa7 : ArithExpr := add a1 a7



-- operational semantics
--the 2 functions are the same in this case, just written in different styles
-- def arithEval (t : ArithExpr) : Nat
-- | lit n => n

-- Evaluate arithmetic expressions
def arithEval : ArithExpr → arithInterp → KNat
  | lit n, _ => n
  | ArithExpr.add e1 e2, i => KNat.add (arithEval e1 i) (arithEval e2 i)
  | ArithExpr.sub e1 e2, i=> KNat.sub (arithEval e1 i) (arithEval e2 i)
  | ArithExpr.neg e, i => KNat.neg (arithEval e i)
  | ArithExpr.var v, i => i v

--#eval a1Pa7 : ArithExpr := plus (lit 7) plus()
--look at what we did for prop logic
-- Addition: left associative

def xPlusThree : ArithExpr :=
  ArithExpr.add
    (ArithExpr.var ArithVariable.XVar)
    (ArithExpr.lit kthree)

def testSub : ArithExpr :=
  ArithExpr.sub
    (ArithExpr.lit kthree)
    (ArithExpr.lit kone)

#eval arithEval testSub i1
-- 2

def testNeg : ArithExpr :=
  ArithExpr.neg (ArithExpr.lit kthree)

#eval arithEval testNeg i1
-- 0

def testVars : ArithExpr :=
  X + Y

#eval arithEval testVars i1
-- 5

def testPrecedence : ArithExpr :=
  -X + Y

#eval arithEval testPrecedence i1
-- 3

def testParentheses : ArithExpr :=
  -(X + Y)

#eval arithEval testParentheses i1
-- 0

end Arith
