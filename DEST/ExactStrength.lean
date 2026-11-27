import DEST.ExactStrengthSpecification
import DEST.SetCompactness
import DEST.OriginalClosed

set_option autoImplicit false
set_option maxHeartbeats 0

namespace DESTExact

open DESTArithmetic DESTReference

private def interpreted {X : Type} {m : X → X → Prop} {z w : X}
    (o : NumberOperations m z w) : Arithmetic (Number m w) (RealObject m w) :=
  ⟨o.zero,o.succ,o.add,o.mul,fun a b => m a.val b.val⟩

private theorem interpreted_term {X : Type} {m : X → X → Prop} {z w : X}
    (o : NumberOperations m z w) {n : ℕ} (t : NumTerm n) (v : Fin n → Number m w) :
    (interpreted o).term t v = t.eval o v := by
  induction t with
  | var i => simp only [Arithmetic.term, NumTerm.eval]
  | zero => simp only [Arithmetic.term, NumTerm.eval, interpreted]
  | succ t ih => simp only [Arithmetic.term, NumTerm.eval, ih]; rfl
  | add a b ha hb => simp only [Arithmetic.term, NumTerm.eval, ha, hb]; rfl
  | mul a b ha hb => simp only [Arithmetic.term, NumTerm.eval, ha, hb]; rfl

private theorem interpreted_truth {X : Type} {m : X → X → Prop} {z w : X}
    (o : NumberOperations m z w) {n k : ℕ} (p : StandardFormula n k)
    (v : Fin n → Number m w) (e : Fin k → RealObject m w) :
    (interpreted o).truth p v e ↔ p.eval o v e := by
  induction p with
  | bot => rfl
  | numEq t s => simp only [Arithmetic.truth, StandardFormula.eval, interpreted_term]
  | realEq i j => rfl
  | mem t i => simp only [Arithmetic.truth, StandardFormula.eval, interpreted_term]; rfl
  | imp p q hp hq => simp only [Arithmetic.truth, StandardFormula.eval, hp, hq]
  | allNum p ih => simp only [Arithmetic.truth, StandardFormula.eval, ih]
  | allReal p ih => simp only [Arithmetic.truth, StandardFormula.eval, ih]

theorem parameter_free_from_original (h : OriginalSatisfiable) : ParameterFreeSatisfiable := by
  obtain ⟨X,m,r,_,hB⟩ := h
  obtain ⟨z,w,_,_,o,ho⟩ := DESTOriginal.original_interprets_standard_arithmetic m r
    ((DESTOriginalClosed.satisfies_iff_original m r).mp hB)
  refine ⟨Number m w,RealObject m w,interpreted o,⟨?_,?_⟩⟩
  · refine ⟨ho.succ_ne_zero,ho.succ_injective,ho.add_zero,ho.add_succ,ho.mul_zero,ho.mul_succ,
      ho.real_ext,?_⟩
    intro n k p v e
    simp only [interpreted_truth]
    exact ho.induction_schema p v e
  · intro n p v
    obtain ⟨A,hA⟩ := ho.comprehension p v
    exact ⟨A,fun a => (hA a).trans (interpreted_truth o p (push a v) Fin.elim0).symm⟩

theorem inductive_from_z2 (kl : ConstructibleInterpretation) (h : Z2Satisfiable) :
    InductiveSatisfiable := by
  obtain ⟨X,M,hr,hc⟩ := kl h
  obtain ⟨Y,m,r,hy,hs,_⟩ := DESTSet.reference_model_from_set_model hr hc (.imp .bot .bot)
    ⟨trivial,trivial⟩ (fun h => h)
  obtain ⟨hb,ht⟩ := (DESTOriginal.original_TI_iff_reference m r).mpr hs
  exact ⟨Y,m,r,hy,(DESTOriginalClosed.satisfies_iff_original m r).mpr hb,ht⟩

theorem original_from_inductive (h : InductiveSatisfiable) : OriginalSatisfiable := by
  obtain ⟨X,m,r,hn,hb,_⟩ := h
  exact ⟨X,m,r,hn,hb⟩

/-- The full model-existence equivalence, conditional on the two published
reductions. Ordinary first-order completeness gives external equiconsistency. -/
theorem z2_equiconsistency (friedman : FriedmanRestriction) (kl : ConstructibleInterpretation) :
    (Z2Satisfiable ↔ OriginalSatisfiable) ∧ (Z2Satisfiable ↔ InductiveSatisfiable) := by
  have fromZ2 := inductive_from_z2 kl
  have toZ2 := fun h => friedman (parameter_free_from_original h)
  exact ⟨⟨fun h => original_from_inductive (fromZ2 h),toZ2⟩,
    ⟨fromZ2,fun h => toZ2 (original_from_inductive h)⟩⟩

/-- The upper-bound implication also gives syntactic consistency directly,
using the kernel-checked soundness of both DEST calculi. -/
theorem consistency_from_z2_model (kl : ConstructibleInterpretation) (h : Z2Satisfiable) :
    DESTOriginalClosed.Consistent ∧ DESTReference.Consistent := by
  obtain ⟨X,M,hr,hc⟩ := kl h
  have hT : DESTReference.Consistent := by
    intro hd
    exact DESTSet.first_sentence_of_internal_model hr hc (by trivial) hd
  obtain ⟨Y,m,r,_,hs,_⟩ := DESTSet.reference_model_from_set_model hr hc (.imp .bot .bot)
    ⟨trivial,trivial⟩ (fun f => f)
  exact ⟨DESTOriginalClosed.consistent_of_original_model m r
    (DESTOriginal.original_of_reference m r hs),hT⟩

end DESTExact
