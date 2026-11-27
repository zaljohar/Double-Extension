import DEST.Specification
import DEST.ReferenceLogic

set_option autoImplicit false

namespace DESTVerification

-- Comparator challenge only. This hole is never imported by the solution.
theorem exists_model : ∃ (D : Set DEST.A) (r : D → D → Prop)
    (num : ℕ → D) (w : D), ModelSpec D r num w := by
  sorry

end DESTVerification

namespace DESTSemantic

-- Statement fixtures only; never imported into the solution.
theorem exists_audited_model : ∃ (D : Set DEST.A) (r : D → D → Prop)
    (num : ℕ → D) (w : D),
    DESTVerification.ModelSpec D r num w ∧
    DESTReference.Satisfies (DESTVerification.first D) r := by
  sorry

theorem exists_reference_model : ∃ (X : Type 1) (m1 m2 : X → X → Prop),
    Nonempty X ∧ DESTReference.Satisfies m1 m2 ∧ WellFounded m1 := by
  sorry

theorem reference_consistent : DESTReference.Consistent := by
  sorry

end DESTSemantic
