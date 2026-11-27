import DEST.ArithmeticSpecification
import DEST.Strength

set_option autoImplicit false
set_option maxHeartbeats 0

universe u
namespace DESTArithmetic
open DESTReference DESTStrength

theorem firstOnly_rename {n k : ℕ} (p : Formula n) (f : Fin n → Fin k)
    (h : p.firstOnly) : (p.rename f).firstOnly := by
  induction p generalizing k with
  | bot => trivial
  | eq i j => trivial
  | mem1 i j => trivial
  | mem2 i j => exact False.elim h
  | imp p q ihp ihq => exact ⟨ihp f h.1, ihq f h.2⟩
  | all p ih => exact ih (liftRen f) h

/-- The explicit permutation has exactly the intended effect on assignments. -/
theorem eval_swapHead {X : Type u} (m r : X → X → Prop) {n : ℕ}
    (p : Formula (n+2)) (a w : X) (v : Fin n → X) :
    (p.rename swapHead).eval m r (push a (push w v)) ↔
      p.eval m r (push w (push a v)) := by
  rw [eval_rename]
  have he : (fun i => push a (push w v) (swapHead i)) = push w (push a v) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [swapHead, Fin.cases_zero, push_succ, push_zero]
    · refine Fin.cases ?_ (fun k => ?_) j
      · simp only [swapHead, Fin.cases_succ, Fin.cases_zero, push_zero, push_succ]
      · simp only [swapHead, Fin.cases_succ, push_succ]
  rw [he]

@[simp] theorem subsetF_correct {X : Type u} (m r : X → X → Prop) {n : ℕ}
    (i j : Fin n) (v : Fin n → X) :
    (subsetF i j).eval m r v ↔ IsReal m (v j) (v i) := by
  simp [subsetF, IsReal, Formula.eval]

/-- Even arbitrarily nested real quantifiers introduce no second membership. -/
theorem guarded_firstOnly {n : ℕ} (p : Guarded n) : p.translate.firstOnly := by
  induction p with
  | atom p hp => exact hp
  | bot => trivial
  | imp p q ihp ihq => exact ⟨ihp, ihq⟩
  | allNum p ih => exact ⟨True.intro, firstOnly_rename p.translate swapHead ih⟩
  | allReal p ih =>
    exact ⟨⟨True.intro, True.intro⟩, firstOnly_rename p.translate swapHead ih⟩

/-- The real guard is deliberately not uniformity. The equivalence holds
in arbitrary models, including models whose internal omega is nonstandard. -/
theorem guarded_translation_correct {X : Type u} (m r : X → X → Prop)
    (w : X) {n : ℕ} (p : Guarded n) (v : Fin n → X) :
    p.translate.eval m r (push w v) ↔ p.eval m w v := by
  induction p with
  | atom p hp => exact first_only_eval m r m p hp (push w v)
  | bot => rfl
  | imp p q ihp ihq =>
    simp only [Guarded.translate, Guarded.eval, Formula.eval, ihp, ihq]
  | allNum p ih =>
    simp only [Guarded.translate, Guarded.eval, Formula.eval,
      push_zero, push_succ, eval_swapHead, ih]
  | allReal p ih =>
    simp only [Guarded.translate, Guarded.eval, Formula.eval,
      subsetF_correct, push_zero, push_succ, eval_swapHead, ih]

/-- Parameter-free real comprehension for the entire guarded language.
The free parameters must be numbers; bound real variables are unrestricted. -/
theorem guarded_number_comprehension {X : Type u} (m r : X → X → Prop)
    (h : BaseSatisfies m r) (z w : X) (hz : ∀ a, ¬ m a z)
    (hw : LeastInductive m z w) {n : ℕ} (p : Guarded (n+1))
    (v : Fin n → X) (hv : ∀ i, m (v i) w) :
    ∃ A, Uniform m r A ∧ IsReal m w A ∧
      ∀ a, m a w → (m a A ↔ p.eval m w (push a v)) := by
  let q : Formula (n+2) := p.translate.rename swapHead
  have hq : q.firstOnly := firstOnly_rename p.translate swapHead (guarded_firstOnly p)
  obtain ⟨A,hA,he⟩ := number_comprehension_of_model m r h z w hz hw q hq v hv
  have hval (a : X) : q.eval m r (push a (push w v)) ↔ p.eval m w (push a v) :=
    (eval_swapHead m r p.translate a w v).trans
      (guarded_translation_correct m r w p (push a v))
  refine ⟨A,hA,?_,?_⟩
  · intro a ha
    exact ((he a).mp ha).1
  · intro a ha
    constructor
    · intro hm
      exact (hval a).mp ((he a).mp hm).2
    · intro hp
      exact (he a).mpr ⟨ha,(hval a).mpr hp⟩

/-- Extract the actual induction scheme from the base theory. The predicate
must have first-order syntax; no unrestricted external induction is assumed. -/
theorem internal_induction {X : Type u} (m r : X → X → Prop)
    (h : BaseSatisfies m r) (z w : X) (hz : ∀ a, ¬ m a z)
    (hw : LeastInductive m z w) {n : ℕ} (p : Formula (n+1))
    (v : Fin n → X) (hb : p.eval m r (push z v))
    (hs : ∀ a, m a w → ∀ b, (∀ y, m y b ↔ y = a ∨ m y a) →
      p.eval m r (push a v) → p.eval m r (push b v)) :
    ∀ a, m a w → p.eval m r (push a v) := by
  have hInd := h _ (BaseAxiom.natInd p)
  simp only [naturalInduction, eval_close, Formula.eval, natBody, eval_conj,
    DESTSemantic.zero_correct, DESTSemantic.omega_correct, DESTSemantic.succ_correct,
    eval_atVar, push_zero, push_succ] at hInd
  exact hInd v w z ⟨hz,hw⟩ hb hs

/-- Full induction for the guarded language, including arbitrary real
parameters. No uniformity hypothesis is imposed on those parameters. -/
theorem guarded_induction {X : Type u} (m r : X → X → Prop)
    (h : BaseSatisfies m r) (z w : X) (hz : ∀ a, ¬ m a z)
    (hw : LeastInductive m z w) {n : ℕ} (p : Guarded (n+1))
    (v : Fin n → X) (hb : p.eval m w (push z v))
    (hs : ∀ a, m a w → ∀ b, (∀ y, m y b ↔ y = a ∨ m y a) →
      p.eval m w (push a v) → p.eval m w (push b v)) :
    ∀ a, m a w → p.eval m w (push a v) := by
  let q : Formula (n+2) := p.translate.rename swapHead
  have hval (a : X) : q.eval m r (push a (push w v)) ↔ p.eval m w (push a v) :=
    (eval_swapHead m r p.translate a w v).trans
      (guarded_translation_correct m r w p (push a v))
  have hi := internal_induction m r h z w hz hw q (push w v) ((hval z).mpr hb)
    (fun a ha b he hp => (hval b).mpr (hs a ha b he ((hval a).mp hp)))
  exact fun a ha => (hval a).mp (hi a ha)

/-- The internal naturals satisfy the successor part of PA even in
nonstandard models of the base theory. -/
theorem internal_successor_laws {X : Type u} (m r : X → X → Prop)
    (h : BaseSatisfies m r) (z w : X) (hz : ∀ a, ¬ m a z)
    (hw : LeastInductive m z w) : SuccessorLaws m z w := by
  classical
  have ext1 := (DESTSemantic.first_extensionality_correct m r).mp (h _ BaseAxiom.ext1)
  let p : Formula 1 := conj
    (.all (.all (.imp (.mem1 0 (Fin.succ 0))
      (.imp (.mem1 (Fin.succ 0) (Fin.succ (Fin.succ 0)))
        (.mem1 0 (Fin.succ (Fin.succ 0)))))))
    (neg (.mem1 0 0))
  have hp (a : X) : p.eval m r (push a Fin.elim0) ↔
      TransitiveObject m a ∧ ¬ m a a := by
    simp only [p, TransitiveObject, eval_conj, eval_neg, Formula.eval, push_zero, push_succ]
  have hcore : ∀ a, m a w → TransitiveObject m a ∧ ¬ m a a := by
    have hb : p.eval m r (push z Fin.elim0) :=
      (hp z).mpr ⟨fun y x _ hy => (hz y hy).elim, hz z⟩
    have hs (a : X) (_ : m a w) (b : X) (he : SuccRel m a b)
        (ha : p.eval m r (push a Fin.elim0)) : p.eval m r (push b Fin.elim0) := by
      obtain ⟨ht,hi⟩ := (hp a).mp ha
      apply (hp b).mpr
      constructor
      · intro y x hxy hy
        rcases (he y).mp hy with hya | hya
        · subst y
          exact (he x).mpr (Or.inr hxy)
        · exact (he x).mpr (Or.inr (ht y x hxy hya))
      · intro hbb
        have hab := (he a).mpr (Or.inl rfl)
        rcases (he b).mp hbb with hba | hba
        · subst b
          exact hi hbb
        · exact hi (ht b a hab hba)
    have hall := internal_induction m r h z w hz hw p Fin.elim0 hb hs
    exact fun a ha => (hp a).mp (hall a ha)
  let q : Formula 2 := .all (.imp (.mem1 0 (Fin.succ 0))
    (.mem1 0 (Fin.succ (Fin.succ 0))))
  let v : Fin 1 → X := push w Fin.elim0
  have hq (a : X) : q.eval m r (push a v) ↔ ∀ y, m y a → m y w := by
    simp only [q, v, Formula.eval, push_zero, push_succ]
  have hclosed : ∀ a, m a w → ∀ y, m y a → m y w := by
    have hb := (hq z).mpr (fun y hy => (hz y hy).elim)
    have hs (a : X) (ha : m a w) (b : X) (he : SuccRel m a b)
        (hp : q.eval m r (push a v)) : q.eval m r (push b v) := by
      apply (hq b).mpr
      intro y hy
      rcases (he y).mp hy with e | hy
      · exact e.symm ▸ ha
      · exact (hq a).mp hp y hy
    have hall := internal_induction m r h z w hz hw q v hb hs
    exact fun a ha => (hq a).mp (hall a ha)
  let t : Formula 3 := disj (.eq 0 (Fin.succ 0))
    (ex (conj (.mem1 0 (Fin.succ (Fin.succ (Fin.succ 0)))) (succF 0 (Fin.succ 0))))
  let e : Fin 2 → X := push z (push w Fin.elim0)
  have ht (a : X) : t.eval m r (push a e) ↔
      a = z ∨ ∃ b, m b w ∧ SuccRel m b a := by
    simp only [t, e, eval_disj, eval_ex, eval_conj, Formula.eval,
      DESTSemantic.succ_correct, push_zero, push_succ, SuccRel]
  have hpred : ∀ a, m a w → a = z ∨ ∃ b, m b w ∧ SuccRel m b a := by
    have hb := (ht z).mpr (Or.inl rfl)
    have hs (a : X) (ha : m a w) (b : X) (he : SuccRel m a b)
        (_ : t.eval m r (push a e)) : t.eval m r (push b e) :=
      (ht b).mpr (Or.inr ⟨a,ha,he⟩)
    have hall := internal_induction m r h z w hz hw t e hb hs
    exact fun a ha => (ht a).mp (hall a ha)
  refine ⟨hw.1.1,hw.1.2,?_,?_,?_,hpred,?_,?_,hclosed⟩
  · intro a b c hb hc
    exact ext1 b c (fun y => (hb y).trans (hc y).symm)
  · intro a b he eqz
    exact hz a (eqz ▸ (he a).mpr (Or.inl rfl))
  · intro a b c ha hb hca hcb
    by_contra hne
    have hab : m a b := ((hcb a).mp ((hca a).mpr (Or.inl rfl))).resolve_left hne
    have hba : m b a := ((hca b).mp ((hcb b).mpr (Or.inl rfl))).resolve_left (Ne.symm hne)
    exact (hcore a ha).2 ((hcore a ha).1 b a hab hba)
  · exact fun a ha => (hcore a ha).1
  · exact fun a ha => (hcore a ha).2

end DESTArithmetic
