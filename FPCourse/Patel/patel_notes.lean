-- INTRODUCTION RULES
def n : Nat := Nat.zero
def m : Nat := Nat.succ n

def b : Bool := Bool.true
def c : Bool := Bool.false

def nb : Nat × Bool :=
  Prod.mk n b

def nb' : Nat × Bool :=
  (
    Nat.zero,
    Bool.false
  )

--ELIMINATION RULES

def NB2Nat : (Nat × Bool) → Nat :=
  fun (p : Nat × Bool) =>
    Prod.fst p

def NB2Nat' : (Nat × Bool) → Nat :=
  fun (p : Nat × Bool) =>
    p.1

def NB2Bool : (Nat × Bool) → Bool :=
  fun (p : Nat × Bool) =>
    p.2

-- → function is totaled, so even if you dont give the input, you can still get the output
-- let is an expression that allows you to bind a name to a value in a local scope


def swap_nat_bool' : (Nat × Bool) → (Bool × Nat) :=
  fun (n, b) => (b, n)

--takes any type alpha and beta, but you want a polymorphic function, so you want to use type variables
-- dont want to pigeonhole yourself into a specific type Nat Bool, so you want to use type variables


def swap'' :
∀
  {α : Type u}       -- for any type α
  {β : Type v},      -- for any type β
  (α × β) → (β × α)  -- from any α - β pair, derive a β - α pair
-- now omit explicit α and β arguments; the're inferred
  := fun (a, b) => (b,a)

--elimination is the destructuring of a type, take it's pieces apart to use
--intro pieces put together to use wholly

--infers that alpha is Nat and beta is Bool


-- Declare α and β together, bund both of them early, ∀ implicit
def swap {α β : Type u} : α × β → β × α := fun (a, b) => (b, a)

#eval swap (0, false)
#eval swap ("No", "Way")

--works but cannot print function values

--propositions are types


def swap_comm {α β : Type u} (a : α) (b : β) :
  swap (swap (x, y)) = (x, y) :=
rfl

-- swap (swap (a, b)) is a type, it is an equality type, if we can prove it
-- rfl is a proof of equality, it is a constructor of the equality type, it is a witness of the equality type
-- rfl forces the lean kernel to reduce the left hand side to the right hand side, and if it does, then it is a proof of equality
--Eq.refl(x,y)

def swap_comm' {α β : Type u} (a : α) (b : β) :
  Eq (swap (swap (x, y))) (x, y) := Eq.refl (x, y)

inductive Variable where
| Xvar
| Yvar
| Zvar

open Variable

def varInterp : Type := Variable → Bool

inductive PropLogicSyntax where
| T
| F
| And (left right : PropLogicSyntax) : PropLogicSyntax
| Or (left right : PropLogicSyntax) : PropLogicSyntax
| Not (p : PropLogicSyntax)
| Var (v : Variable)

open PropLogicSyntax

def X := PropLogicSyntax.Var Variable.Xvar
def Y:= PropLogicSyntax.Var Variable.Yvar
def Z := PropLogicSyntax.Var Variable.Zvar

--something in this might not be right
def i : varInterp := fun (v : Variable) =>
    match v with
    | .Xvar => true
    | .Yvar => false
    | .Zvar => true

def eval : PropLogicSyntax → Bool
| .T => true
| .F => false
| PropLogicSyntax.And p1 p2 => (eval p1) && (eval p2)
| PropLogicSyntax.Or p1 p2 => (eval p1) || (eval p2)
| PropLogicSyntax.Not p1 => !(eval p1)
| PropLogicSyntax.Var v => i v


-- _ =>  says default to whatever you write, so false here

--eval turns a piece of syntax in a bool and so you use eval in the function

def e1 := PropLogicSyntax.F
def e2 := PropLogicSyntax.T
def e3 := PropLogicSyntax.And e1 e2



-- def e1 :=F
-- def e2 := T
-- this is all predicate logic


#eval eval e1
#eval eval e2
#eval eval e3

--===================================================
--Propositional Logic
--===================================================
-- fun PQ =>   --for all intro
--  fun i =>   --for all intro
--    fun h => -- --> into (--> == for all)
--      case P is true and
          -- Qt Qf

--h is a proof of not p and q
-- h: !(P ^ q)
  -- not (P ^ Q) --> (P ^ Q) --> false implies
-- and.intro will construct a proof of the conjunction so if you have a proof of p hp and a proof of q hq, you can construct a proof of p ^ q
--h (And.intro hp hq) creates this conjunction since h only takes one argument that is

-- theorem DM1 :
--   ∀ (P Q : PropLogicSyntax),
--   ∀ (i : varInterp),
--   ¬(P ∧ Q) ⇒ ¬P ∨ ¬Q :=

-- the idea is that you dont know whether p is false or if q is false just because the whole comes back false, only p needs to be false or only q
--logically, the proof works, but youre at a standstill when you dont know the individual value
theorem DM1 : ∀ (P Q : Prop), ¬(P ∧ Q) → ¬P ∨ ¬Q :=
  fun P Q => _
    fun h => _

--prove a negation by assuming something is true and proving its false
theorem DM2 : ∀ (P Q : Prop), ¬P ∨ ¬Q → ¬(P ∧ Q) :=
  fun P Q =>
    fun h =>
      fun pandq =>
        let p : P := And.left pandq
        let q : Q := And.right pandq
        match h with
        | Or.inl np => np p
        | Or.inr nq => nq q
