import DEST.Specification

set_option autoImplicit false

namespace DESTVerification

-- Comparator challenge only. This hole is never imported by the solution.
theorem exists_model : ∃ (D : Set DEST.A) (r : D → D → Prop)
    (num : ℕ → D) (w : D), ModelSpec D r num w := by
  sorry

end DESTVerification
