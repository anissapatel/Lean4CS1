namespace Arith

--syntax (constructor so lit 7 is a term of this type ArithExpr)
inductive ArithExpr where
| lit (n : Nat)
| plus (e1 e2 : ArithExpr) : ArithExpr

open ArithExpr

--expressions using our syntax
def a1 : ArithExpr := lit 1
def a7 : ArithExpr := lit 7
def a1Pa7 : ArithExpr :=

-- operational semantics
--the 2 functions are the same in this case, just written in different styles
def arithEval (t : ArithExpr) : Nat
| lit n => n

def arithEval' : ArithExpr → Nat :=
  match t with
  | lit n => n
  |plus e1 e2 => Nat.add (arithEval e1) (arithEval e2)

def arithEval : ArithExpr → Nat
| lit n => n

--#eval a1Pa7 : ArithExpr := plus (lit 7) plus()
--look at what we did for prop logic and create times in here

end Arith
