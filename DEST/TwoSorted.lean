import DEST.TwoSortedSpecification
import DEST.InternalRecursion

set_option autoImplicit false
set_option maxHeartbeats 0
universe u
namespace DESTArithmetic
open DESTReference DESTStrength

theorem arithmetic_firstOnly {n d : ℕ} (p : ArithFormula n)
    (z w : Fin d) (f : Fin n → Fin d) : (p.translate z w f).firstOnly := by
  induction p generalizing d with
  | bot => trivial
  | eq a b => trivial
  | mem a b => trivial
  | zero a => trivial
  | succ a b => simp [ArithFormula.translate, succF, iffF, conj, disj, neg, Formula.firstOnly]
  | add a b c => exact addF_firstOnly z w (f a) (f b) (f c)
  | mul a b c => exact mulF_firstOnly z w (f a) (f b) (f c)
  | imp p q ihp ihq => exact ⟨ihp z w f,ihq z w f⟩
  | allNum p ih => exact ⟨True.intro,ih z.succ w.succ (liftRen f)⟩
  | allReal p ih => exact ⟨⟨True.intro,True.intro⟩,ih z.succ w.succ (liftRen f)⟩

/-- The independent arithmetic semantics is preserved by the translation,
including arbitrary number and set quantifier alternation. -/
theorem arithmetic_translation_correct {X : Type u} (m r : X → X → Prop)
    {n d : ℕ} (p : ArithFormula n) (z w : Fin d) (f : Fin n → Fin d) (v : Fin d → X) :
    (p.translate z w f).eval m r v ↔ p.eval m (v z) (v w) (fun j => v (f j)) := by
  induction p generalizing d with
  | bot => rfl
  | eq a b => rfl
  | mem a b => rfl
  | zero a => rfl
  | succ a b => exact DESTSemantic.succ_correct m r (f a) (f b) v
  | add a b c => exact addF_correct m r v z w (f a) (f b) (f c)
  | mul a b c => exact mulF_correct m r v z w (f a) (f b) (f c)
  | imp p q ihp ihq => simp only [ArithFormula.translate, ArithFormula.eval, Formula.eval, ihp, ihq]
  | allNum p ih =>
    have he (a : X) : (fun j => push a v (liftRen f j)) = push a (fun j => v (f j)) := by
      funext j
      refine Fin.cases ?_ (fun k => ?_) j <;> simp
    simp only [ArithFormula.translate, ArithFormula.eval, Formula.eval, ih, push_zero, push_succ, he]
  | allReal p ih =>
    have he (a : X) : (fun j => push a v (liftRen f j)) = push a (fun j => v (f j)) := by
      funext j
      refine Fin.cases ?_ (fun k => ?_) j <;> simp
    simp only [ArithFormula.translate, ArithFormula.eval, Formula.eval, subsetF_correct,
      ih, push_zero, push_succ, he]

private def arithParams {n : ℕ} : Fin (n+1) → Fin (n+3) :=
  Fin.cases 0 (fun j => j.succ.succ.succ)

private theorem arithParams_eval {X : Type u} {n : ℕ} (k z w : X) (v : Fin n → X) :
    (fun j => push k (push w (push z v)) (arithParams j)) = push k v := by
  funext j
  refine Fin.cases ?_ (fun i => ?_) j <;> simp [arithParams]

/-- Fixed first-language numerical comprehension plus the translated grammar
proves unrestricted impredicative comprehension without free real parameters. -/
theorem parameter_free_arithmetic {X : Type u} (m r : X → X → Prop)
    (h : BaseSatisfies m r) (z w : X) (hz : ∀ a, ¬ m a z)
    (hw : LeastInductive m z w) : ParamFreeArithmetic m z w := by
  have laws := internal_successor_laws m r h z w hz hw
  have ext1 := (DESTSemantic.first_extensionality_correct m r).mp (h _ BaseAxiom.ext1)
  refine ⟨laws,internal_arithmetic_laws m r h z w hz hw,?_,?_,?_⟩
  · intro a b ha hb he
    apply ext1 a b
    intro k
    exact ⟨fun hk => (he k (ha k hk)).mp hk,fun hk => (he k (hb k hk)).mpr hk⟩
  · intro n p v hv
    let q : Formula (n+3) := p.translate (Fin.succ (Fin.succ 0)) (Fin.succ 0) arithParams
    let v' : Fin (n+1) → X := push z v
    have hv' : ∀ j, m (v' j) w := by
      intro j
      refine Fin.cases ?_ (fun i => ?_) j
      · simpa [v'] using laws.zero_mem
      · simpa [v'] using hv i
    have hq : q.firstOnly := arithmetic_firstOnly p _ _ _
    have he (k : X) : q.eval m r (push k (push w v')) ↔ p.eval m z w (push k v) := by
      simp only [q, v', arithmetic_translation_correct, push_zero, push_succ, arithParams_eval]
    obtain ⟨A,_,hA⟩ := number_comprehension_of_model m r h z w hz hw q hq v' hv'
    refine ⟨A,fun k hk => ((hA k).mp hk).1,?_⟩
    intro k hk
    exact ⟨fun ha => (he k).mp ((hA k).mp ha).2,fun ha => (hA k).mpr ⟨hk,(he k).mpr ha⟩⟩
  · intro n p v hb hs
    let q : Formula (n+3) := p.translate (Fin.succ (Fin.succ 0)) (Fin.succ 0) arithParams
    let v' : Fin (n+2) → X := push w (push z v)
    have he (k : X) : q.eval m r (push k v') ↔ p.eval m z w (push k v) := by
      simp only [q, v', arithmetic_translation_correct, push_zero, push_succ, arithParams_eval]
    have hi := internal_induction m r h z w hz hw q v' ((he z).mpr hb)
      (fun a ha b hab hp => (he b).mpr (hs a ha b hab ((he a).mp hp)))
    exact fun a ha => (he a).mp (hi a ha)

/-- The base axioms themselves provide both arithmetic-domain witnesses. -/
theorem base_interprets_arithmetic {X : Type u} (m r : X → X → Prop)
    (h : BaseSatisfies m r) : ∃ z w, (∀ a, ¬ m a z) ∧
      LeastInductive m z w ∧ ParamFreeArithmetic m z w := by
  have hi := h _ BaseAxiom.inf
  simp only [DESTReference.infinity, eval_ex, eval_conj, DESTSemantic.zero_correct,
    DESTSemantic.omega_correct, push_zero, push_succ] at hi
  obtain ⟨w,z,hz,hw⟩ := hi
  exact ⟨z,w,hz,hw,parameter_free_arithmetic m r h z w hz hw⟩

end DESTArithmetic
