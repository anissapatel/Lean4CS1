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
