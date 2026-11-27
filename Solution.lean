import DEST.Model
import DEST.Specification

set_option autoImplicit false
set_option maxHeartbeats 0

namespace DESTVerification

/-- Bridge from the actual construction to the independently stated challenge. -/
theorem exists_model : ∃ (D : Set DEST.A) (r : D → D → Prop)
    (num : ℕ → D) (w : D), ModelSpec D r num w := by
  obtain ⟨r, hax, hwf, hw, hn⟩ := DEST.exists_DEST_model
  refine ⟨DEST.M, r, DEST.numeral, DEST.omegaObj, ?_⟩
  exact ⟨hax, hwf, hw, hn, DEST.numeral_injective, DEST.numeral_zero,
    DEST.numeral_succ, DEST.omega_exact, DEST.omega_inductive,
    DEST.omega_least_inductive, DEST.natural_induction, DEST.full_set_induction⟩

end DESTVerification
