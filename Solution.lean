import DEST.OriginalClosed
import DEST.RankModel
import DEST.ZermeloModel
import DEST.Model
import DEST.Specification
import DEST.SemanticAudit
import DEST.ReferenceLogic

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

namespace DESTSemantic

/-- The old endpoint and the independent closed-sentence reference theory
    hold in exactly the same model. The consistency proof is a consequence. -/
theorem exists_audited_model : ∃ (D : Set DEST.A) (r : D → D → Prop)
    (num : ℕ → D) (w : D),
    DESTVerification.ModelSpec D r num w ∧
    DESTReference.Satisfies (DESTVerification.first D) r := by
  obtain ⟨D, r, num, w, h⟩ := DESTVerification.exists_model
  exact ⟨D, r, num, w, h, model_satisfies_reference D r num w h⟩

/-- The reference theory has a nonempty ordinary first-order model. -/
theorem exists_reference_model : ∃ (X : Type 1) (m1 m2 : X → X → Prop),
    Nonempty X ∧ DESTReference.Satisfies m1 m2 ∧ WellFounded m1 := by
  obtain ⟨D, r, num, w, h, hsat⟩ := exists_audited_model
  exact ⟨D, DESTVerification.first D, r, ⟨w⟩, hsat, h.2.1⟩

/-- No derivation of falsity in the declared classical first-order calculus. -/
theorem reference_consistent : DESTReference.Consistent := by
  obtain ⟨X, m1, m2, _, hsat, _⟩ := exists_reference_model
  exact DESTReference.consistent_of_model m1 m2 hsat

end DESTSemantic

namespace DESTOriginal

/-- The previously verified model satisfies the Infinity-free formulation. -/
theorem exists_original_model : ∃ (X : Type 1) (m r : X → X → Prop),
    Nonempty X ∧ Original m r := by
  obtain ⟨X,m,r,hX,h,_⟩ := DESTSemantic.exists_reference_model
  exact ⟨X,m,r,hX,original_of_reference m r h⟩

end DESTOriginal

namespace DESTOriginalClosed

theorem original_consistent : Consistent := by
  obtain ⟨X,m,r,_,h⟩ := DESTOriginal.exists_original_model
  exact consistent_of_original_model m r h

end DESTOriginalClosed
