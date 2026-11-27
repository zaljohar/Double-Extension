import DEST.OriginalClosedSpecification
import DEST.OriginalStrength

set_option autoImplicit false
set_option maxHeartbeats 0
universe u
namespace DESTOriginalClosed
open DESTReference

@[simp] theorem natural_correct {X : Type u} (m r : X → X → Prop)
    {n : ℕ} (v : Fin n → X) (z a : Fin n) :
    (naturalF z a).eval m r v ↔ DESTOriginal.Natural m (v z) (v a) := by
  exact DESTOriginal.naturalF_correct m r v z a

theorem induction_correct {X : Type u} (m r : X → X → Prop)
    {n : ℕ} (p : Formula (n+1)) :
    (naturalInduction p).eval m r Fin.elim0 ↔
      ∀ v : Fin n → X, ∀ z, DESTOriginal.Zero m z →
        p.eval m r (push z v) →
        (∀ a, DESTOriginal.Natural m z a → ∀ b, DESTOriginal.Succ m a b →
          p.eval m r (push a v) → p.eval m r (push b v)) →
        ∀ a, DESTOriginal.Natural m z a → p.eval m r (push a v) := by
  simp only [naturalInduction, eval_close, Formula.eval, natBody,
    DESTSemantic.zero_correct, DESTSemantic.succ_correct, natural_correct,
    eval_atVar, push_zero, push_succ]

theorem satisfies_iff_original {X : Type u} (m r : X → X → Prop) :
    Satisfies m r ↔ DESTOriginal.Original m r := by
  constructor
  · intro h
    refine ⟨(DESTSemantic.first_extensionality_correct m r).mp (h _ Axiom.ext1),
      (DESTSemantic.second_extensionality_correct m r).mp (h _ Axiom.ext2),?_,?_,?_⟩
    · intro n p hp v
      exact (DESTSemantic.comprehension_correct m r p).mp (h _ (Axiom.comp p hp)) v
    · intro n p hp v
      exact (DESTSemantic.uniformity_correct m r p).mp (h _ (Axiom.unif p hp)) v
    · intro z hz n p v
      exact (induction_correct m r p).mp (h _ (Axiom.natInd p)) v z hz
  · intro h s hs
    cases hs with
    | ext1 => exact (DESTSemantic.first_extensionality_correct m r).mpr h.ext1
    | ext2 => exact (DESTSemantic.second_extensionality_correct m r).mpr h.ext2
    | comp p hp => exact (DESTSemantic.comprehension_correct m r p).mpr (h.comp p hp)
    | unif p hp => exact (DESTSemantic.uniformity_correct m r p).mpr (h.unif p hp)
    | natInd p =>
      apply (induction_correct m r p).mpr
      intro v z hz
      exact h.natInd z hz p v

/-- Closed axioms, with no existence axiom, have precisely the same models as
    the older base theory. Completeness of ordinary first-order logic then
    gives the corresponding external deductive equivalence. -/
theorem satisfies_iff_base {X : Type u} (m r : X → X → Prop) :
    Satisfies m r ↔ DESTStrength.BaseSatisfies m r :=
  (satisfies_iff_original m r).trans (DESTOriginal.original_iff_base m r)

theorem consistent_of_original_model {X : Type u} (m r : X → X → Prop)
    (h : DESTOriginal.Original m r) : Consistent := by
  intro hd
  exact DESTReference.soundness m r Axiom ((satisfies_iff_original m r).mpr h) hd Fin.elim0

end DESTOriginalClosed
