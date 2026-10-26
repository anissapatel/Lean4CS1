namespace Arith

--syntax (constructor so lit 7 is a term of this type ArithExpr)
inductive ArithExpr where
| lit (n : Nat) --this is a constructor for a literal number
| add (e1 e2 : ArithExpr) : ArithExpr --this is a constructor for addition of two arithmetic expressions

open ArithExpr



--expressions using our syntax
def a1 : ArithExpr := lit 1
def a7 : ArithExpr := lit 7
def e1 : ArithExpr := lit 1
def e7 : ArithExpr := lit 7
def e3 : ArithExpr := add e1 e7
def a1Pa7 : ArithExpr := add a1 a7

-- operational semantics
--the 2 functions are the same in this case, just written in different styles
-- def arithEval (t : ArithExpr) : Nat
-- | lit n => n

def arithEval : ArithExpr → Nat
  | lit n => n
  | add e1 e2 => Nat.add (arithEval e1) (arithEval e2)


--#eval a1Pa7 : ArithExpr := plus (lit 7) plus()
--look at what we did for prop logic and create times in here




end Arith

-- #############################################################################
namespace KNat

inductive KNat where
  | zero : KNat
  | succ (n : KNat) : KNat


def inc (n : KNat) := n.succ

def add : KNat → KNat → KNat
  | a, KNat.zero => a
  | a, KNat.succ b => inc (add a b)

-- 1. These must be defined INSIDE the namespace
def kzero : KNat := KNat.zero
def kone : KNat := KNat.succ kzero

--the notation zero for the zero of our type bc there is a type class for zero
instance : Zero KNat where
  zero := KNat.zero

instance : One KNat where
  one := kone

def mul : KNat → KNat → KNat
  | _, 0 => 0
  | a, KNat.succ b => add a (mul a b)

-- 2. Register '+' for KNat
instance : Add KNat where
  add := add

-- 3. Run #check inside the namespace block
#check 1 + 1
#check kone + kone
#reduce kone + kone

def exp : KNat → KNat → KNat
| _, 0 => 1
| a, KNat.succ b' => mul (exp a b') a

instance: Pow KNat KNat where
  pow := exp

def kthree := KNat.succ (KNat.succ kone)

#eval kthree ^ kthree
#eval kone + kone

end KNat
