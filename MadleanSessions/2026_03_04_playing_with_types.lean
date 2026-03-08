/-
Type Systems, Lambda Calculus and CIC
04-03-2026, Faculty of Mathematics of UCM
Jorge Mayoral
-/

/-
===============================================================
Type Systems, Lambda Calculus and CIC (Calculus of Inductive
Constructions)
===============================================================

Lean implements the Calculus of Inductive Constructions (CIC):
  • dependent types
  • universes
  • inductive types with generated eliminators/recursors

Curry–Howard:
  Types  ↔  Propositions
  Terms  ↔  Proofs
  Reduction  ↔  Proof normalization (evaluation model of the kernel)
-/


/-
===============================================================
  "Untyped" λ-Calculus
===============================================================

Term

 x y z (var)

 fun x => t (abs)

 MN (app)
-/

namespace untypedLambda

-- α conversion (Variable renaming)
variable (B : Type)
variable (a b : B)

example: (fun x => x + 1) = (fun y => y + 1) := rfl

-- β reduction (App - Substitution)

example: (fun x => x + 1) 1 = 1 + 1 := rfl

end untypedLambda

/-
===============================================================
  Simply Typed Lambda Calculus
===============================================================

  A type system defines a formal language with the primitive notion of Type.

  The typing judgment

      Γ ⊢ t : T

  relates a term t with a type T under a context Γ
  (a list of term : type assumptions).

  Every type is characterized by two fundamental rules:

    - Introduction rule  — how to construct a term of that type
    - Elimination rule   — how to use (or consume) a term of that type

  ---------------------------------------------------------------
  Function Types
  ---------------------------------------------------------------

  Introduction Rule (→-Intro)

      Γ, x : A ⊢ t : B
      -----------------------
      Γ ⊢ (fun x => t) : A → B

  Elimination Rule (→-Elim)  (Application)

      Γ ⊢ f : A → B   Γ ⊢ a : A
      --------------------------------
              Γ ⊢ f a : B

  Key Idea: any type must be equipped with introduction and elimination rules
-/

-- Product  A × B

namespace simplyTyped

variable (A B : Type)
variable (a : A) (b: B)

-- introduction
#check @Prod.mk A B
example: A × B := Prod.mk a b


#check @Prod.fst A B
-- elimination 1
example (p : A × B): A := Prod.fst p

#check @Prod.snd A B
-- elimination 2
example (p : A × B): B := Prod.snd p


-- ι-reduction
example: Prod.fst (Prod.mk a b) = a := rfl

-- η-reduction
example (p: A × B): Prod.mk (Prod.fst p) (Prod.snd p) = p := rfl

-- Sum  A + B
def sumEx : Sum Nat String := Sum.inl 5

def sumElim (s : Sum Nat String) : String :=
  match s with
  | Sum.inl n => toString n
  | Sum.inr s => s

  -- True Type

  -- intro
  example: True := True.intro

  -- elim (stupid)

  def elim_true : A → True → A := fun a => fun _ => a

  -- False Type

  -- intro : None

  -- elim
  def elim_false (S: Type) : False → S := False.rec (motive := fun _ => S)


  -- Curry Howard (STLC ↔ Intuitionistic Prpositional Logic)


/-
  Natural numbers as a Type
-/

-- intro
#check Nat.zero
#check Nat.succ

--elim: primitive recursion
def elimNat: K → (Nat → K → K) → Nat → K :=
  fun a f n => match n with
  | Nat.zero => a
  | Nat.succ k => f k (elimNat a f k)

#check @Nat.rec (motive := fun _ => A)


def ys: Nat → String := elimNat "" (fun _ => fun m => "y" ++ m)

#eval ys 5

end simplyTyped

/-
===============================================================
 Dependency on Types
===============================================================

Types depending on Types
-/

namespace dependencyOnTypes

variable (A B C: Type)

#check @List

--intro
#check @List.nil
#check @List.cons

--elimination
#check @List.rec (motive := fun _ => A) B

/-
Terms depending on Types
-/

#check @id
#check @id Nat
#eval @id Nat 2

/-
Types depending on Terms
-/

def dep: Bool → Type
| true => Nat
| false => String


/-
Dependent function:

  ∀ x : A, B x

Generalizes A → B.
-/
-- elim
def depExample
  (A : Type)
  (B : A → Type)
  (f : ∀ x : A, B x)
  (a : A) : B a := f a

/-
===============================================================
 Inductive Types Generate Recursors (CIC Pattern)
===============================================================

General CIC principle:

For an inductive type

  inductive T where
  | c₁ : ...
  | c₂ : ...

Lean automatically generates:

  T.rec

with type:

  T.rec :
    (motive : T → Sort u) →
    (case_c₁ : ...) →
    (case_c₂ : ...) →
    (t : T) →
    motive t

T.rec motive case_c₁ case_c₂ ... (ci args) =
case_ci args (recursive calls on recursive arguments)

So every inductive type gives:

  - constructors      (introduction rules)
  - automatic generated recursor     (elimination rule)
  - ι-reduction rules (computation rules)

This is the computational heart of CIC.
-/

inductive MyProd (A B : Type) where
| mk : A → B → MyProd A B

#check @MyProd.rec A B (motive := fun _ => C)

-- defining fst via pattern matching
def fst {A B} (p : MyProd A B) : A :=
  match p with
  | MyProd.mk a _ => a

-- ι-reduction
example {A B} (a : A) (b : B) :
  fst (MyProd.mk a b) = a :=
rfl

end dependencyOnTypes

/-
===============================================================
4. Natural Numbers (Dependent version)
===============================================================
-/

def dep_nat_elim: (B : Nat → Prop) →
(B 0) →
((n : Nat) → B n → B (n + 1)) →
∀ n : Nat, B n := fun B a f n =>
  match n with
  | Nat.zero   => a
  | Nat.succ k => f k (dep_nat_elim B a f k)

variable (B : Nat → Prop)
#check @Nat.rec B

def n_ge_0: ∀ n: Nat, 0 ≤ n := @Nat.rec
(motive := fun n => 0 ≤ n)
(Nat.le_refl 0)
(fun n ih => @Nat.le_succ_of_le 0 n ih)

#check ∀ n: Nat, 0 ≤ n
#check fun n => 0 ≤ n
/-
===============================================================
 Universes (Avoiding Paradoxes)
===============================================================

If Type : Type, we get paradoxical system (same flavor as Russses's paradox).

Lean instead has a hierarchy:

  Type 0 : Type 1 : Type 2 : ...

More generally:

  Type u : Type (u+1)

and also:

  Sort u

This prevents self-reference inconsistencies.

Universe polymorphism:
-/

universe u v

def uprod (A : Type u) (B : Type v) :=
  A × B

#check uprod


/-
===============================================================
 Dependent Induction (Full CIC Strength)
===============================================================

Dependent eliminator for Nat:

  Nat.rec :
    (motive : Nat → Sort u) →
    motive 0 →
    ((n : Nat) → motive n → motive (Nat.succ n)) →
    (n : Nat) →
    motive n

This is stronger than simple recursion:
it encodes mathematical induction.
-/


variable (B : Nat → Type)
#check @Nat.rec (motive := B)


/-
Principle of induction is given "for free" with inductive types.
-/
