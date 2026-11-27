import DEST.Syntax

set_option autoImplicit false

namespace DESTVerification

/-- The challenge uses no definitions of the model construction. The first
    membership is actual ZFSet membership restricted to the proposed domain. -/
def first (D : Set DEST.A) (x a : D) : Prop := x.val ∈ a.val

def uniform (D : Set DEST.A) (r : D → D → Prop) (a : D) : Prop :=
  ∀ y : D, first D y a ↔ r y a

/-- Extensionality for both memberships, comprehension for every first-language
    formula with parameters, and corrected uniformity. -/
def axioms (D : Set DEST.A) (r : D → D → Prop) : Prop :=
  (∀ a b : D, (∀ y, first D y a ↔ first D y b) → a = b) ∧
  (∀ a b : D, (∀ y, r y a ↔ r y b) → a = b) ∧
  (∀ (p : DEST.Formula) (l : List D), ∃ a : D,
    ∀ y : D, r y a ↔ p.eval D (y.val :: l.map Subtype.val)) ∧
  (∀ (p : DEST.Formula) (l : List D), (∀ b ∈ l, uniform D r b) →
    ∀ a : D, (∀ y : D, r y a ↔ p.eval D (y.val :: l.map Subtype.val)) →
      ¬ r a a → uniform D r a)

def inductiveSet (D : Set DEST.A) (zero a : D) : Prop :=
  first D zero a ∧ ∀ n : D, first D n a →
    ∃ s : D, first D s a ∧ ∀ z : D, first D z s ↔ z = n ∨ first D z n

/-- A single endpoint with all axioms and induction in the same model.
    The predicate quantifiers are stronger than first-order induction schemes. -/
def ModelSpec (D : Set DEST.A) (r : D → D → Prop)
    (num : ℕ → D) (w : D) : Prop :=
  axioms D r ∧
  WellFounded (first D) ∧
  uniform D r w ∧
  (∀ n : ℕ, uniform D r (num n)) ∧
  Function.Injective num ∧
  (∀ a : D, ¬ first D a (num 0)) ∧
  (∀ (a : D) (n : ℕ), first D a (num (n+1)) ↔ a = num n ∨ first D a (num n)) ∧
  (∀ a : D, first D a w ↔ ∃ n : ℕ, num n = a) ∧
  inductiveSet D (num 0) w ∧
  (∀ a : D, inductiveSet D (num 0) a → ∀ z : D, first D z w → first D z a) ∧
  (∀ P : D → Prop, P (num 0) → (∀ n : ℕ, P (num n) → P (num (n+1))) →
    ∀ a : D, first D a w → P a) ∧
  (∀ P : D → Prop, (∀ a : D, (∀ y : D, first D y a → P y) → P a) → ∀ a : D, P a)

end DESTVerification
