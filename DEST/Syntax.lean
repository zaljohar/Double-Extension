import Mathlib.SetTheory.ZFC.Basic
import Mathlib.Data.Set.Countable
import Mathlib.Tactic.DeriveCountable

set_option autoImplicit false
set_option maxHeartbeats 0

namespace DEST

abbrev A := ZFSet.{0}

/-- First-order equality/membership syntax, with de Bruijn indices. A binder
    puts its variable at the head of the environment. Out-of-scope atoms are
    false; this harmless totalization also covers every well-scoped formula. -/
inductive Formula where
  | bot : Formula
  | eq : ℕ → ℕ → Formula
  | mem : ℕ → ℕ → Formula
  | imp : Formula → Formula → Formula
  | all : Formula → Formula
  deriving Countable

/-- Relativized first-order semantics on the actual domain `D`. -/
def Formula.eval (D : Set A) : Formula → List A → Prop
  | .bot, _ => False
  | .eq i j, l => ∃ a : A, l[i]? = some a ∧ l[j]? = some a
  | .mem i j, l => ∃ a b : A, l[i]? = some a ∧ l[j]? = some b ∧ a ∈ b
  | .imp p q, l => p.eval D l → q.eval D l
  | .all p, l => ∀ a ∈ D, p.eval D (a :: l)

abbrev truth (p : Formula) (l : List A) : Prop := p.eval Set.univ l

end DEST
