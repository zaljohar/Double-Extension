import DEST.ReferenceTheory

/-! Independent semantic specifications for the focused extension.
The old, verified reference theory is not modified. In particular, the new
Original specification contains NO existence axiom for an inductive set. -/
set_option autoImplicit false
universe u
namespace DESTOriginal
open DESTReference

abbrev Uniform {X : Type u} (m r : X → X → Prop) (a : X) : Prop :=
  ∀ y, m y a ↔ r y a
abbrev Zero {X : Type u} (m : X → X → Prop) (z : X) : Prop := ∀ y, ¬ m y z
abbrev Succ {X : Type u} (m : X → X → Prop) (a b : X) : Prop :=
  ∀ y, m y b ↔ y = a ∨ m y a
abbrev Sub {X : Type u} (m : X → X → Prop) (a b : X) : Prop := ∀ y, m y a → m y b
abbrev InductiveSet {X : Type u} (m : X → X → Prop) (z a : X) : Prop :=
  m z a ∧ ∀ n, m n a → ∃ s, m s a ∧ Succ m n s
abbrev Natural {X : Type u} (m : X → X → Prop) (z n : X) : Prop :=
  ∀ a, InductiveSet m z a → m n a
abbrev LeastInductive {X : Type u} (m : X → X → Prop) (z w : X) : Prop :=
  InductiveSet m z w ∧ ∀ a, InductiveSet m z a → Sub m w a

/-- Relational induction on the intersection of all inductive sets, whether
or not there is an inductive set. This is a scheme over actual first-order
formulas with arbitrary parameters, not over arbitrary Lean predicates. -/
structure Original {X : Type u} (m r : X → X → Prop) : Prop where
  ext1 : ∀ a b, (∀ y, m y a ↔ m y b) → a = b
  ext2 : ∀ a b, (∀ y, r y a ↔ r y b) → a = b
  comp : ∀ {n : ℕ} (p : Formula (n+1)), p.firstOnly → ∀ v : Fin n → X,
    ∃ a, ∀ y, r y a ↔ p.eval m r (push y v)
  unif : ∀ {n : ℕ} (p : Formula (n+1)), p.firstOnly → ∀ v : Fin n → X,
    (∀ i, Uniform m r (v i)) → ∀ a,
    (∀ y, r y a ↔ p.eval m r (push y v)) → ¬ p.eval m r (push a v) → Uniform m r a
  natInd : ∀ z, Zero m z → ∀ {n : ℕ} (p : Formula (n+1)) (v : Fin n → X),
    p.eval m r (push z v) →
    (∀ a, Natural m z a → ∀ b, Succ m a b →
      p.eval m r (push a v) → p.eval m r (push b v)) →
    ∀ a, Natural m z a → p.eval m r (push a v)

abbrev SU1 {X : Type u} (m r : X → X → Prop) : Prop :=
  ∀ x y, Uniform m r x → Sub m y x → Uniform m r y

abbrev TI1 {X : Type u} (m r : X → X → Prop) : Prop :=
  ∀ {n : ℕ} (p : Formula (n+1)) (v : Fin n → X),
    (∀ a, (∀ y, m y a → p.eval m r (push y v)) → p.eval m r (push a v)) →
    ∀ a, p.eval m r (push a v)

abbrev Transitive {X : Type u} (m : X → X → Prop) (a : X) : Prop :=
  ∀ y x, m x y → m y a → m x a
abbrev Power {X : Type u} (m : X → X → Prop) (a b : X) : Prop :=
  ∀ y, m y b ↔ Sub m y a
abbrev AllUniform {X : Type u} (m r : X → X → Prop) (a : X) : Prop :=
  Uniform m r a ∧ ∀ y, m y a → Uniform m r y
abbrev HereditarilyUniform {X : Type u} (m r : X → X → Prop) (a : X) : Prop :=
  Uniform m r a ∧ ∃ t, Transitive m t ∧ Sub m a t ∧ ∀ y, m y t → Uniform m r y

/-- Zermelo set theory (no Choice, no Replacement), interpreted on the first
members of W. The separation schema ranges over every first-language formula,
with quantifiers interpreted on the subtype of first members of W.
This is a semantic scheme, not an arithmetized internal truth predicate. -/
abbrev Inside {X : Type u} (m : X → X → Prop) (W : X) := {x : X // m x W}

abbrev insideMem {X : Type u} (m : X → X → Prop) (W : X) : Inside m W → Inside m W → Prop :=
  fun a b => m a.val b.val

structure ZermeloModel {X : Type u} (m : X → X → Prop) (W : X) : Prop where
  ext : ∀ a b, m a W → m b W → (∀ y, m y W → (m y a ↔ m y b)) → a = b
  empty : ∃ z, m z W ∧ Zero m z
  pair : ∀ a b, m a W → m b W → ∃ c, m c W ∧ ∀ y, m y c ↔ y = a ∨ y = b
  union : ∀ a, m a W → ∃ b, m b W ∧ ∀ y, m y b ↔ ∃ z, m z a ∧ m y z
  power : ∀ a, m a W → ∃ b, m b W ∧ ∀ y, m y W → (m y b ↔ Sub m y a)
  infinity : ∃ z w, m z W ∧ m w W ∧ Zero m z ∧ InductiveSet m z w
  foundation : ∀ a, m a W → (∃ y, m y a) → ∃ y, m y a ∧ ∀ z, m z a → ¬ m z y
  separation : ∀ {n : ℕ} (p : Formula (n+1)), p.firstOnly →
    ∀ (v : Fin n → Inside m W) (a : Inside m W),
    ∃ b : Inside m W, ∀ y : Inside m W, insideMem m W y b ↔
      insideMem m W y a ∧ p.eval (insideMem m W) (insideMem m W) (push y v)

end DESTOriginal
