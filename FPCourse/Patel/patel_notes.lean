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
-- theorem DM1 : ∀ (P Q : Prop), ¬(P ∧ Q) → ¬P ∨ ¬Q :=
--   fun P Q =>
--     fun h =>
--       Or.inl _ => _

--prove a negation by assuming something is true and proving its false
-- theorem DM2 : ∀ (P Q : Prop), ¬P ∨ ¬Q → ¬(P ∧ Q) :=
--   fun P Q =>
--     fun h =>
--       fun pandq =>
--         let p : P := And.left pandq
--         let q : Q := And.right pandq
--         match h with
--         | Or.inl np => np p
--         | Or.inr nq => nq q

--as a note, there is _Q to say you're not explicitly using it in the body of the code

theorem DM2 : ∀ (P Q : Prop), ¬P ∨ ¬Q → ¬(P ∧ Q) :=

  fun P _Q =>                               -- ∀ intro (twice)
    fun h =>                                -- ∀ intro
      fun pandq =>                          -- → intro
        let p : P := And.left pandq         -- And.elim on left
        let q := pandq.right                -- And.elim on right
        match h with                        -- Or elim (by cases)
        | Or.inl np => np p                 -- → elim (fn application)
        | Or.inr nq => nq q                -- → elim (fn application)


  /- @@@ Mandatory homework: State and prove the two remaining variants of DeMorgan's laws, involving distribution of nation over disjunction (not over or). @@@ -/


theorem DM3 : ∀ (P Q : Prop), ¬(P ∨ Q) → ¬P ∧ ¬Q :=
  fun P Q =>                  -- ∀ intro (twice)
  fun h : ¬(P ∨ Q) =>         -- → intro (h : (P ∨ Q) → False)
    -- We need to construct a conjunction (And.intro) of ¬P and ¬Q
    let np : ¬P :=            -- To prove ¬P, assume p : P, derive False
      fun p : P =>            --to prove ¬P we assume we have a proof of p of P and goal is False
        h (Or.inl p)          -- Or.inl p constructs (P ∨ Q); apply h to get False
    let nq : ¬Q :=            -- To prove ¬Q, assume q : Q, derive False
      fun q : Q =>
        h (Or.inr q)          -- Or.inr q constructs (P ∨ Q); apply h to get False
    And.intro np nq           -- And intro

theorem DM4 : ∀ (P Q : Prop), ¬P ∧ ¬Q → ¬(P ∨ Q) :=
  fun P Q =>                  -- ∀ intro (twice)
  fun h : ¬P ∧ ¬Q =>          -- → intro
  fun porq : P ∨ Q =>         -- → intro contains either a proof of p or proof of q(assume P ∨ Q, derive False)
    let np : ¬P := h.left     -- And.elim on left (np : P → False)
    let nq : ¬Q := h.right    -- And.elim on right (nq : Q → False)
    match porq with           -- Or elim (case analysis on P ∨ Q) tear open porq to see which case is inside
    | Or.inl p => np p        -- If P is true, apply np to p to get False
    | Or.inr q => nq q        -- If Q is true, apply nq to q to get False

theorem notContradiction {P : Prop} : ¬(P ∧ ¬P) :=
  fun pandNotP =>
    let p : P := pandNotP.left
    let np : ¬P := pandNotP.right
    np p          -- np is a function because it is a proof of a negation that takes in P


theorem noContradiction2 {P : Prop} : ¬(P ∧ ¬P) :=
  fun pandNotP => pandNotP.right pandNotP.left

--use the strategy of proof by negation: assume true, prove not P

example {P : Prop} : ¬(P ∧ ¬P) :=
  fun{pnp : P ∧ ¬P} =>
    pnp.right pnp.left


inductive Dog : Type where
  | Iris
  | Fido
  | Sargent

  open Dog

  inductive Friendly : Dog → Prop where
    | irisFriendly : Friendly Iris
    | fidoFriendly : Friendly Fido

  inductive Furry : Dog → Prop where
    | irisFurry : Furry Iris
    | sargentFurry : Furry Sargent

-- friendly is a proposition/predicate

-- example : Friendly Iris ∧ Furry Iris := sorry

--define this predicate, a predicate is a function
-- → Prop is what signals you are working with a predicate
--takes a dog a returns a proposition
-- the function returns a Prop is what also signals the proposition when no →
--moving the d : Dog to the left of the colon makes it globally available
def Suitable (d : Dog) : Prop := Friendly d ∧ Furry d
def Suitable' : Dog → Prop := fun d => (Friendly d ∧ Furry d)

--order of friendly and furry matters
example : Suitable Iris :=
  And.intro Friendly.irisFriendly Furry.irisFurry

#check (Suitable)
#check (Friendly)

#check (∀ (d : Dog), Friendly d)
#check ∀ (d : Dog), Friendly d

-- example : ∀ (d : Dog), Friendly d :=
--   fun d =>
--   match d with
--     | Iris => Friendly.irisFriendly
--     | Fido => Friendly.fidoFriendly
--     | Sargent => _    -- not possible, not friendly


example : ¬(∀ (d : Dog), Friendly d):=
  fun allDogsFriendly =>
    let sf := allDogsFriendly Sargent
    nomatch sf


-- Recursors give you total functions in Lean
-- ex. match and def are friendlier notations
--Nobody uses them directly, but useful to know
-- every type has it's own recursor


example : Empty → String := λ e => nomatch e

-- noncomputable means you cant run something, no compiled code, #reduce doesn't need that
noncomputable def fromUnit (u : Unit) : String :=
  PUnit.rec "the one and only" u

--reduce uses the kernel evaluator rather than
--{} means you don't have to specify the type, Lean will infer it

def sumUp : Nat → Nat
    | Nat.zero => 0
    | Nat.succ n' => (n' + 1) + sumUp n'

def fac : Nat → Nat
    | 0 => 1
    | (n' +  1) => (n' + 1) * fac n'

#eval fac 5

--base case and step function

def factorial (n : Nat) : Nat :=
  Nat.rec 1 (fun n ih => (n + 1) * ih) n

#eval factorial 0   -- 1
#eval factorial 5   -- 120


--syntactic symbol interpreted to semantic meaning
--ex. + is just Nat.add
--ex. * is just Nat.mul

-- type class is a special one-constructor inductive
-- Instance (α:Type)
-- an instance of a type class applies to a type (like Nat, String, etc.)
-- you should only have one instance per type
-- you have foo, to add foo you create an instance of addfoo (can only have one addfoo instance)
-- one instance per type that you want to add
-- add is a type class, add Nat/addfoo is the instance of that type class
-- once type class called add applied to the different types, the corresponding instances are used
-- this is how Lean resolves overloaded functions like + and * for different types


--LISTS:
  -- a list can be nill
  -- a list can be a cons of an element and another list
  -- cons take a single number a smaller list, can think of like a stack
  -- it is LIFO
  -- the base case needs to be right in order to multiply all the elements in the list
  --

  -- option/maybe
  -- a value of type Option α is either none or some a, where a : α
  -- useful for representing values that may or may not exist
  -- either none or some value of that type
  def dec : Nat → Option Nat
   | 0 => none
   | (n' + 1) => Option.some n'

  -- List α
  -- | nil
  -- | cons (h : α) (l : List α)
  -- cons is construct a list with a head element and a tail list (rest of the list)
  -- if the list is empty there is no head
  -- same as the decrement of 0, return none

-- describe a custom list type called MyList
inductive MyList (α : Type) : Type where
  | nil
  | cons (h : α) (t : MyList α)

--polymorphic function called head that returns the first element of a list, if one exists
def head {α : Type} : List α → Option α
  | List.nil => none
  | List.cons h _ => some h

def head' {α : Type} : List α → Option α
  | [] => none
  | h :: _ => some h


--recursive fold function! The main idea is that it takes a list and combines all its elements into one final value using a function you provide
def myfold {α : Type} (f : α → α → α) (id : α) : List α → α
  | [] => id
  | h :: t => f h (myfold f id t)

#eval myfold Nat.add 0 []
#eval myfold Nat.add 0 [1]
#eval myfold Nat.add 0 [1, 2]

#eval myfold Nat.mul 1 []
#eval myfold Nat.mul 1 [1]
#eval myfold Nat.mul 1 [1, 2, 3, 4, 5]

def myfold2
  {α : Type }
  (f : α → α → α)
  (f_assoc : ∀ (a b c : α ), f (f a b) c = f a (f b c))
  (id : α)
  (fid : ∀ a, f id a = a ∧ f a id = a)
  : List α → α
  | [] => id
  | h :: t => f h (myfold f id t)


-- tree objects
-- a tree is either a leaf or a node with a value and two subtrees
inductive MyTree (α : Type) : Type where
  | leaf
  | node (v : α) (l r : MyTree α)


-- every monoid we've written is parameterized by a concrete type, monoid Nat is about Nat,
-- when talking about container types, talking about type builders, the type of option is type → type
-- list nat yields list nat, etc
-- tree nat is the type of

class Foldable (F : Type → Type) where
  foldr {α β : Type} : (α → β → β) → β → F α → β

def treeFoldr {α β : Type} (f : α → β → β) (z : β) : MyTree α → β
  | MyTree.leaf => z
  | MyTree.node v l r => f v (treeFoldr f (treeFoldr f z r) l)

  --container type F in toList{F : Type → Type} (α : Type) (xs : F α) : List α
  --alpha is the element type
  --xs can be a list of alpha values, or a tree of alpha values, as long as it satisfies the container of values

-- multiplication is just many additions
-- exponentiation is just many multiplications
-- tetration is just many exponentiations

/-! @@@
# November 2 Notes:
@@@ -/


  --Monoid: a collection with an associative binary operation and an identity element
  --Examples of monoids include:
  -- Nat with addition and 0
  -- Nat with multiplication and 1
  -- List with concatenation and the empty list

  -- class monoid (α : Type) where
  --   op: α → α → α
  --   id: α
  --   assoc: ∀ a b c : α, op (op a b) c = op a (op b c)
  --   left_id: ∀ a, op id a = a
  --   right_id: ∀ a, op a id = a


--To be a Monoid, a type just needs:A Set of Items: A bucket of stuff you're working with (like numbers, lists, or strings).
--A "Glue" Operation · : A way to take two items and combine them into one item of the same type.
--A "Do Nothing" Item ($e$): A special identity element that changes nothing when you glue it to something else.


--if we have a clock, the action is to move the time along 12pm + 4 hours is 4pm
--the identity is like a self loop on itself, time doesnt change
-- it points are pairs of rationals and vectors as pairs of rationals
-- you cant add points to each other, cant add 3pm + 5pm, it doesnt make sense
-- you can say say 12 → 2 but not 0 → .5, but if you say diregard that, then it's no longer a vector space
  -- to have a vector space, you need to be able to take the multiplicative inverse
  -- the scalers need to be more than a monoid
-- b-a is b × additive inverse of a
-- this is similar to how subtraction is defined in terms of addition and the additive inverse
-- field, ring, group, monoid
-- a field is a ring where every non-zero element has a multiplicative inverse
-- a ring is a set with two operations, addition and multiplication, where addition forms an abelian group, multiplication is associative, and multiplication distributes over addition
  -- can have a ring for matrices, polynomials, etc. can have some actions on it but not all matrices are invertible for example
-- a group is a monoid where every element has an inverse
  -- a group is symmentry preserving actions
  -- sets of actions that preserve a structure, actions, that can be undone
  -- can use that to solve equations
-- a monoid is a set with an associative binary operation and an identity element


--A group: a monoid where you can undo actions (essentially)
-- inverse/cancel the action
-- inverse of 0 is 0 (do nothing identity)
-- inverse of 2 is 1
-- think of a group as a collections of actions, like addition, where you can also undo


-- torsor over a group
-- given a group G, a torsor over G is a set X with a free and transitive action of G on X
-- given our clock example, the set of times on the clock is a torsor over the group of hour increments
-- can only have three elements in the torsor if the group has three elements

/-! @@@
# November 4 Notes:
@@@ -/

--idRight is a proof of for all a integers where after the := comes the proof term
-- the inverse field of this group is the definition of the regular invere function
-- Fin 3 is the finite natural number from 0, 1, 2
-- if you have fin 5 and add 3 + 3 you get 1 (mod n = 5)  it rolls over
-- instance : Group (Fin 3) where
--   op : Fin 3 → Fin 3 → Fin 3 → Fin 3 := (· + ·)
-- for a group you need addition, additive inverse, associativity, identity, operator?
-- when you think of a vector space, think of a collection of actions
-- points on the clock are torsors and the vectors are the differences between points
-- a torsor can take 2 type arguments, where G is a group and T is your torsor, what the group of vectors act on
-- class Torsor (G T : Type) where
--   [groupG : Group G]
--   act : G → T → T
--   actId : ∀ t : T, act groupG.id t = t
-- the group determines the underlying structure of the torsor
-- if your group is clock then you have to have 12 torsors
-- T is the set of points plus a group action on those points which is the G and T which is a torsor
--

/-! @@@
# November 9 Notes:
@@@ -/

-- Affine space is a set of points with a vector space acting on it in a free and transitive manner
-- essentially, it is a torsor over a vector space
