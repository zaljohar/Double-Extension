import DEST.Original
import DEST.StandardArithmetic

/-! Bridge between the Infinity-free original theory and the earlier
closed-sentence arithmetic-strength specification. No transfinite induction
or subset uniformity is used in the base-theory bridge. -/
set_option autoImplicit false
set_option maxHeartbeats 0
universe u
namespace DESTOriginal
open DESTReference

/-- The old explicit Infinity axiom and conditional induction are consequences
of original DEST, not extra assumptions. -/
theorem base_of_original {X : Type u} (m r : X → X → Prop)
    (h : Original m r) : DESTStrength.BaseSatisfies m r := by
  intro s hs
  cases hs with
  | ext1 => exact (DESTSemantic.first_extensionality_correct m r).mpr h.ext1
  | ext2 => exact (DESTSemantic.second_extensionality_correct m r).mpr h.ext2
  | comp p hp => exact (DESTSemantic.comprehension_correct m r p).mpr (h.comp p hp)
  | unif p hp => exact (DESTSemantic.uniformity_correct m r p).mpr (h.unif p hp)
  | inf =>
    obtain ⟨z,w,hz,hw,_⟩ := exists_uniform_omega m r h
    simp only [infinity, eval_ex, eval_conj, DESTSemantic.zero_correct,
      DESTSemantic.omega_correct, push_zero, push_succ]
    exact ⟨w,z,hz,hw.1,hw.2⟩
  | natInd p =>
    simp only [naturalInduction, eval_close, Formula.eval, natBody, eval_conj,
      DESTSemantic.zero_correct, DESTSemantic.omega_correct, DESTSemantic.succ_correct,
      eval_atVar, push_zero, push_succ]
    intro v w z hzw hb hstep a ha
    have hn : ∀ x, Natural m z x → m x w := fun x hx => hx w hzw.2.1
    exact h.natInd z hzw.1 p v hb
      (fun x hx b hxb hp => hstep x (hn x hx) b hxb hp)
      a (fun t ht => hzw.2.2 t ht a ha)

/-- The converse uses explicit Infinity only on the OLD specification's side. -/
theorem original_of_base {X : Type u} (m r : X → X → Prop)
    (h : DESTStrength.BaseSatisfies m r) : Original m r := by
  have he := (DESTSemantic.first_extensionality_correct m r).mp
    (h _ DESTStrength.BaseAxiom.ext1)
  refine ⟨he,(DESTSemantic.second_extensionality_correct m r).mp
    (h _ DESTStrength.BaseAxiom.ext2),?_,?_,?_⟩
  · intro n p hp v
    exact (DESTSemantic.comprehension_correct m r p).mp
      (h _ (DESTStrength.BaseAxiom.comp p hp)) v
  · intro n p hp v hv a ha hs
    exact (DESTSemantic.uniformity_correct m r p).mp
      (h _ (DESTStrength.BaseAxiom.unif p hp)) v hv a ha hs
  · intro z hz n p v hb hs a ha
    have hi := h _ DESTStrength.BaseAxiom.inf
    simp only [infinity,eval_ex,eval_conj,DESTSemantic.zero_correct,
      DESTSemantic.omega_correct,push_zero,push_succ] at hi
    obtain ⟨w,z',hz',hw,hleast⟩ := hi
    have ez : z' = z := he _ _ (fun y => ⟨fun hy => (hz' y hy).elim,fun hy => (hz y hy).elim⟩)
    subst z'
    have hn := h _ (DESTStrength.BaseAxiom.natInd p)
    simp only [naturalInduction,eval_close,Formula.eval,natBody,eval_conj,
      DESTSemantic.zero_correct,DESTSemantic.omega_correct,DESTSemantic.succ_correct,
      eval_atVar,push_zero,push_succ] at hn
    exact hn v w z ⟨hz,hw,hleast⟩ hb
      (fun x hx b hxb hp => hs x (fun t ht => hleast t ht x hx) b hxb hp) a (ha w hw)

/-- Same carrier and relations, in arbitrary models, including nonstandard
arithmetic. This is a semantic equivalence, not equiconsistency with Z2. -/
theorem original_iff_base {X : Type u} (m r : X → X → Prop) :
    Original m r ↔ DESTStrength.BaseSatisfies m r :=
  ⟨base_of_original m r, original_of_base m r⟩

/-- Also identify the exact stronger theory used in the upper-bound argument. -/
theorem original_TI_iff_reference {X : Type u} (m r : X → X → Prop) :
    (Original m r ∧ TI1 m r) ↔ DESTReference.Satisfies m r := by
  constructor
  · rintro ⟨h,ht⟩
    have hb := base_of_original m r h
    intro s hs
    cases hs with
    | ext1 => exact hb _ DESTStrength.BaseAxiom.ext1
    | ext2 => exact hb _ DESTStrength.BaseAxiom.ext2
    | comp p hp => exact hb _ (DESTStrength.BaseAxiom.comp p hp)
    | unif p hp => exact hb _ (DESTStrength.BaseAxiom.unif p hp)
    | inf => exact hb _ DESTStrength.BaseAxiom.inf
    | natInd p => exact hb _ (DESTStrength.BaseAxiom.natInd p)
    | setInd p => exact (DESTSemantic.setInduction_correct m r p).mpr (ht p)
  · intro h
    refine ⟨original_of_reference m r h,?_⟩
    intro n p v
    exact (DESTSemantic.setInduction_correct m r p).mp (h _ (Axiom.setInd p)) v

/-- Lower-bound arithmetic model for the original Infinity-free theory.
Full parameter-free impredicative comprehension and full induction; no SU. -/
theorem original_interprets_standard_arithmetic {X : Type u} (m r : X → X → Prop)
    (h : Original m r) : ∃ z w, Zero m z ∧ LeastInductive m z w ∧
      ∃ o : DESTArithmetic.NumberOperations m z w, DESTArithmetic.StandardArithmeticModel o := by
  exact DESTArithmetic.base_interprets_standard_arithmetic m r (base_of_original m r h)

end DESTOriginal
