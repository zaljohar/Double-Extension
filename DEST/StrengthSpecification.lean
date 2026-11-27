import DEST.ReferenceTheory
import DEST.ReferenceLogic
import Mathlib.Data.Set.Countable

set_option autoImplicit false
set_option maxHeartbeats 0

universe u

namespace DESTStrength
open DESTReference

abbrev Unary := Σ n : ℕ, Formula (n+1)

def Uniform {X : Type u} (m r : X → X → Prop) (a : X) : Prop :=
  ∀ y, m y a ↔ r y a

def Trace {X : Type u} (m : X → X → Prop) (a : X) : Set X := {y | m y a}

def Extension {X : Type u} (m : X → X → Prop) (q : Unary)
    (v : Fin q.1 → X) : Set X := {y | q.2.eval m m (push y v)}

def Protected {X : Type u} (m : X → X → Prop) (U : Set X)
    (qs : List Unary) (B : Set X) : Prop :=
  ∃ q ∈ qs, ∃ v : Fin q.1 → X, (∀ i, v i ∈ U) ∧ Extension m q v = B

/-- The finite list controls only comprehension and uniformity. We retain
    every induction instance, infinity, and both extensionalities. -/
inductive Fragment (qs : List Unary) : Sentence → Prop where
  | ext1 : Fragment qs (extensionality false)
  | ext2 : Fragment qs (extensionality true)
  | comp (q : Unary) : q ∈ qs → q.2.firstOnly → Fragment qs (comprehension q.2)
  | unif (q : Unary) : q ∈ qs → q.2.firstOnly → Fragment qs (DESTReference.uniformity q.2)
  | inf : Fragment qs infinity
  | natInd {n : ℕ} (p : Formula (n+1)) : Fragment qs (naturalInduction p)
  | setInd {n : ℕ} (p : Formula (n+1)) : Fragment qs (setInduction p)

/-- The corrected base theory, without first-membership set induction.
    Infinity and the full natural-number induction schema are retained. -/
inductive BaseAxiom : Sentence → Prop where
  | ext1 : BaseAxiom (extensionality false)
  | ext2 : BaseAxiom (extensionality true)
  | comp {n : ℕ} (p : Formula (n+1)) : p.firstOnly → BaseAxiom (comprehension p)
  | unif {n : ℕ} (p : Formula (n+1)) : p.firstOnly → BaseAxiom (DESTReference.uniformity p)
  | inf : BaseAxiom infinity
  | natInd {n : ℕ} (p : Formula (n+1)) : BaseAxiom (naturalInduction p)

def BaseSatisfies {X : Type u} (m r : X → X → Prop) : Prop :=
  ∀ s, BaseAxiom s → s.eval m r Fin.elim0

def SatisfiesFragment {X : Type u} (m r : X → X → Prop) (qs : List Unary) : Prop :=
  ∀ s, Fragment qs s → s.eval m r Fin.elim0

/-- Exactly the combinatorial obligations from the finite reflection argument.
    These are inputs, NOT theorems about a weak set-theoretic universe. -/
structure HullData {X : Type u} (m : X → X → Prop) (U : Set X)
    (qs : List Unary) (D : Set (Set X)) : Prop where
  ext : Function.Injective (Trace m)
  countable : D.Countable
  trace_mem : ∀ a, a ∈ U → Trace m a ∈ D
  singleton_mem : ∀ b, b ∉ U → ({b} : Set X) ∈ D
  requested_mem : ∀ q ∈ qs, ∀ v : Fin q.1 → X, Extension m q v ∈ D
  outside_fresh : ∀ l : List X, ∃ a, a ∉ U ∧ a ∉ l
  protected_trace : ∀ a B, Protected m U qs B → Trace m a = B → a ∈ U
  singleton_not_fixed : ∀ b, b ∉ U → ¬ ∃ a, a ∈ U ∧ Trace m a = {b}
  singleton_unprotected : ∀ b, b ∉ U → ¬ Protected m U qs {b}
  protected_fresh : ∀ B ∈ D, Protected m U qs B →
    (¬ ∃ a, a ∈ U ∧ Trace m a = B) →
    ∀ l : List X, ∃ a, a ∉ U ∧ a ∉ l ∧ a ∈ B

def Inductive {X : Type u} (m : X → X → Prop) (z a : X) : Prop :=
  m z a ∧ ∀ n, m n a → ∃ s, m s a ∧ (∀ y, m y s ↔ y = n ∨ m y n)

def LeastInductive {X : Type u} (m : X → X → Prop) (z w : X) : Prop :=
  Inductive m z w ∧ ∀ a, Inductive m z a → ∀ y, m y w → m y a

/-- The standard numeral frame is an input to the fragment construction.
    In the set-theoretic argument it comes from the ambient model's omega. -/
structure NatFrame {X : Type u} (m : X → X → Prop) (U : Set X)
    (num : ℕ → X) (w : X) : Prop where
  wf : WellFounded m
  injective : Function.Injective num
  zero : ∀ a, ¬ m a (num 0)
  succ : ∀ a n, m a (num (n+1)) ↔ a = num n ∨ m a (num n)
  omega : ∀ a, m a w ↔ ∃ n, num n = a
  num_mem : ∀ n, num n ∈ U
  omega_mem : w ∈ U

/-- Lower-bound statement: all first-language definable collections of
    uniform objects with uniform parameters have a uniform representative. -/
def UniformComprehension {X : Type u} (m r : X → X → Prop) : Prop :=
  ∀ {n : ℕ} (p : Formula (n+1)), p.firstOnly → ∀ v : Fin n → X,
    (∀ i, Uniform m r (v i)) →
    (∀ y, p.eval m r (push y v) → Uniform m r y) →
    ∃ a, Uniform m r a ∧ ∀ y, m y a ↔ p.eval m r (push y v)

end DESTStrength
