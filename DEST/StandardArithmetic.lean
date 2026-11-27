import DEST.StandardArithmeticSpecification
import DEST.TwoSorted

set_option autoImplicit false
set_option maxHeartbeats 0
universe u
namespace DESTArithmetic
open DESTReference DESTStrength

@[simp] theorem arNeg_eval {X : Type u} (m : X → X → Prop) (z w : X)
    {n : ℕ} (p : ArithFormula n) (v : Fin n → X) :
    (arNeg p).eval m z w v ↔ ¬ p.eval m z w v := Iff.rfl

@[simp] theorem arAnd_eval {X : Type u} (m : X → X → Prop) (z w : X)
    {n : ℕ} (p q : ArithFormula n) (v : Fin n → X) :
    (arAnd p q).eval m z w v ↔ p.eval m z w v ∧ q.eval m z w v := by
  classical
  simp only [arAnd, arNeg_eval, ArithFormula.eval]
  tauto

@[simp] theorem arExNum_eval {X : Type u} (m : X → X → Prop) (z w : X)
    {n : ℕ} (p : ArithFormula (n+1)) (v : Fin n → X) :
    (arExNum p).eval m z w v ↔ ∃ a, m a w ∧ p.eval m z w (push a v) := by
  classical
  simp only [arExNum, arNeg_eval, ArithFormula.eval]
  push_neg <;> rfl

noncomputable def chooseOperations {X : Type u} (m : X → X → Prop) (z w : X)
    (h : ParamFreeArithmetic m z w) : NumberOperations m z w := by
  classical
  let s (a : Number m w) := h.successor.total a.val a.property
  let add (a b : Number m w) := h.arithmetic.add_total a.val b.val a.property b.property
  let mul (a b : Number m w) := h.arithmetic.mul_total a.val b.val a.property b.property
  exact {
    zero := ⟨z,h.successor.zero_mem⟩
    succ := fun a => ⟨Classical.choose (s a),(Classical.choose_spec (s a)).1⟩
    add := fun a b => ⟨Classical.choose (add a b),(Classical.choose_spec (add a b)).1⟩
    mul := fun a b => ⟨Classical.choose (mul a b),(Classical.choose_spec (mul a b)).1⟩
    zero_ok := rfl
    succ_ok := fun a => (Classical.choose_spec (s a)).2
    add_ok := fun a b => (Classical.choose_spec (add a b)).2
    mul_ok := fun a b => (Classical.choose_spec (mul a b)).2 }

/-- Flattening a term into a relational formula preserves its actual value. -/
theorem term_graph_correct {X : Type u} {m : X → X → Prop} {z w : X}
    (h : ParamFreeArithmetic m z w) (o : NumberOperations m z w)
    {n d : ℕ} (t : NumTerm n) (f : Fin n → Fin d) (b : Fin d)
    (v : Fin d → X) (e : Fin n → Number m w) (he : ∀ i, v (f i) = (e i).val) :
    (t.graph f b).eval m z w v ↔ v b = (t.eval o e).val := by
  induction t generalizing d with
  | var a => simpa only [NumTerm.graph, NumTerm.eval, ArithFormula.eval, he]
  | zero => simpa only [NumTerm.graph, NumTerm.eval, ArithFormula.eval, o.zero_ok]
  | succ t ih =>
    simp only [NumTerm.graph, arExNum_eval, arAnd_eval, ArithFormula.eval, push_zero, push_succ, NumTerm.eval]
    constructor
    · rintro ⟨a,_,ha,hs⟩
      have eq := (ih (fun i => (f i).succ) 0 (push a v) (fun i => by simpa using he i)).mp ha
      have eq' : a = (t.eval o e).val := by simpa using eq
      subst a
      exact h.successor.functional _ _ _ hs (o.succ_ok (t.eval o e))
    · intro hb
      let a := t.eval o e
      refine ⟨a.val,a.property,?_,?_⟩
      · exact (ih (fun i => (f i).succ) 0 (push a.val v)
          (fun i => by simpa using he i)).mpr (by simp [a])
      · rw [hb]
        exact o.succ_ok a
  | add t s iht ihs =>
    simp only [NumTerm.graph, arExNum_eval, arAnd_eval, ArithFormula.eval, push_zero, push_succ, NumTerm.eval]
    constructor
    · rintro ⟨a,_,c,_,ha,hc,hadd⟩
      have ea := (iht (fun i => (f i).succ.succ) (Fin.succ 0) (push c (push a v))
        (fun i => by simpa using he i)).mp ha
      have ec := (ihs (fun i => (f i).succ.succ) 0 (push c (push a v))
        (fun i => by simpa using he i)).mp hc
      have ea' : a = (t.eval o e).val := by simpa using ea
      have ec' : c = (s.eval o e).val := by simpa using ec
      subst a
      subst c
      exact h.arithmetic.add_unique _ _ _ _ (s.eval o e).property hadd (o.add_ok (t.eval o e) (s.eval o e))
    · intro hb
      let a := t.eval o e
      let c := s.eval o e
      refine ⟨a.val,a.property,c.val,c.property,?_,?_,?_⟩
      · exact (iht (fun i => (f i).succ.succ) (Fin.succ 0) (push c.val (push a.val v))
          (fun i => by simpa using he i)).mpr (by simp [a])
      · exact (ihs (fun i => (f i).succ.succ) 0 (push c.val (push a.val v))
          (fun i => by simpa using he i)).mpr (by simp [c])
      · rw [hb]
        exact o.add_ok a c
  | mul t s iht ihs =>
    simp only [NumTerm.graph, arExNum_eval, arAnd_eval, ArithFormula.eval, push_zero, push_succ, NumTerm.eval]
    constructor
    · rintro ⟨a,_,c,_,ha,hc,hmul⟩
      have ea := (iht (fun i => (f i).succ.succ) (Fin.succ 0) (push c (push a v))
        (fun i => by simpa using he i)).mp ha
      have ec := (ihs (fun i => (f i).succ.succ) 0 (push c (push a v))
        (fun i => by simpa using he i)).mp hc
      have ea' : a = (t.eval o e).val := by simpa using ea
      have ec' : c = (s.eval o e).val := by simpa using ec
      subst a
      subst c
      exact h.arithmetic.mul_unique _ _ _ _ (t.eval o e).property (s.eval o e).property hmul
        (o.mul_ok (t.eval o e) (s.eval o e))
    · intro hb
      let a := t.eval o e
      let c := s.eval o e
      refine ⟨a.val,a.property,c.val,c.property,?_,?_,?_⟩
      · exact (iht (fun i => (f i).succ.succ) (Fin.succ 0) (push c.val (push a.val v))
          (fun i => by simpa using he i)).mpr (by simp [a])
      · exact (ihs (fun i => (f i).succ.succ) 0 (push c.val (push a.val v))
          (fun i => by simpa using he i)).mpr (by simp [c])
      · rw [hb]
        exact o.mul_ok a c

/-- Relationalization is truth preserving for the complete independently
scoped two-sorted functional language, with no standardness assumption. -/
theorem standard_translation_correct {X : Type u} {m : X → X → Prop} {z w : X}
    (h : ParamFreeArithmetic m z w) (o : NumberOperations m z w)
    {n k d : ℕ} (p : StandardFormula n k) (f : Fin n → Fin d) (g : Fin k → Fin d)
    (v : Fin d → X) (e : Fin n → Number m w) (a : Fin k → RealObject m w)
    (he : ∀ i, v (f i) = (e i).val) (ha : ∀ i, v (g i) = (a i).val) :
    (p.relationalize f g).eval m z w v ↔ p.eval o e a := by
  induction p generalizing d with
  | bot => rfl
  | numEq t s =>
    simp only [StandardFormula.relationalize, StandardFormula.eval, arExNum_eval, arAnd_eval,
      ArithFormula.eval, push_zero, push_succ]
    constructor
    · rintro ⟨b,_,c,_,hb,hc,eq⟩
      have eb := (term_graph_correct h o t (fun i => (f i).succ.succ) (Fin.succ 0)
        (push c (push b v)) e (fun i => by simpa using he i)).mp hb
      have ec := (term_graph_correct h o s (fun i => (f i).succ.succ) 0
        (push c (push b v)) e (fun i => by simpa using he i)).mp hc
      apply Subtype.ext
      have eb' : b = (t.eval o e).val := by simpa using eb
      have ec' : c = (s.eval o e).val := by simpa using ec
      exact eb'.symm.trans (eq.trans ec')
    · intro eq
      let b := t.eval o e
      let c := s.eval o e
      refine ⟨b.val,b.property,c.val,c.property,?_,?_,congrArg (fun x : Number m w => x.val) eq⟩
      · apply (term_graph_correct h o t (fun i => (f i).succ.succ) (Fin.succ 0)
          (push c.val (push b.val v)) e (fun i => by simpa using he i)).mpr
        simp [b]
      · apply (term_graph_correct h o s (fun i => (f i).succ.succ) 0
          (push c.val (push b.val v)) e (fun i => by simpa using he i)).mpr
        simp [c]
  | realEq i j =>
    simp only [StandardFormula.relationalize, StandardFormula.eval, ArithFormula.eval, ha]
    exact ⟨Subtype.ext,fun h => congrArg (fun x : RealObject m w => x.val) h⟩
  | mem t i =>
    simp only [StandardFormula.relationalize, StandardFormula.eval, arExNum_eval, arAnd_eval,
      ArithFormula.eval, push_zero, push_succ, ha]
    constructor
    · rintro ⟨b,_,hb,hm⟩
      have eb := (term_graph_correct h o t (fun i => (f i).succ) 0 (push b v) e
        (fun i => by simpa using he i)).mp hb
      have eb' : b = (t.eval o e).val := by simpa using eb
      exact eb' ▸ hm
    · intro hm
      let b := t.eval o e
      refine ⟨b.val,b.property,?_,hm⟩
      apply (term_graph_correct h o t (fun i => (f i).succ) 0 (push b.val v) e
        (fun i => by simpa using he i)).mpr
      simp [b]
  | imp p q ihp ihq =>
    simp only [StandardFormula.relationalize, StandardFormula.eval, ArithFormula.eval,
      ihp f g v e a he ha, ihq f g v e a he ha]
  | allNum p ih =>
    simp only [StandardFormula.relationalize, StandardFormula.eval, ArithFormula.eval]
    have bridge (b : Number m w) :
        (p.relationalize (liftRen f) (fun j => (g j).succ)).eval m z w (push b.val v) ↔
          p.eval o (push b e) a := by
      apply ih (liftRen f) (fun j => (g j).succ) (push b.val v) (push b e) a
      · intro j
        refine Fin.cases ?_ (fun i => ?_) j <;> simp [he]
      · intro j
        simp [ha]
    exact ⟨fun ht b => (bridge b).mp (ht b.val b.property),
      fun ht b hb => (bridge ⟨b,hb⟩).mpr (ht ⟨b,hb⟩)⟩
  | allReal p ih =>
    simp only [StandardFormula.relationalize, StandardFormula.eval, ArithFormula.eval]
    have bridge (b : RealObject m w) :
        (p.relationalize (fun j => (f j).succ) (liftRen g)).eval m z w (push b.val v) ↔
          p.eval o e (push b a) := by
      apply ih (fun j => (f j).succ) (liftRen g) (push b.val v) e (push b a)
      · intro j
        simp [he]
      · intro j
        refine Fin.cases ?_ (fun i => ?_) j <;> simp [ha]
    exact ⟨fun ht b => (bridge b).mp (ht b.val b.property),
      fun ht b hb => (bridge ⟨b,hb⟩).mpr (ht ⟨b,hb⟩)⟩

/-- Each relational model constructed from DEST satisfies the usual
functional-language PA equations and the full two-sorted parameter-free
comprehension and induction schemes. -/
theorem standard_arithmetic_model {X : Type u} {m : X → X → Prop} {z w : X}
    (h : ParamFreeArithmetic m z w) (o : NumberOperations m z w) : StandardArithmeticModel o := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro a eq
    exact h.successor.not_zero a.val (o.succ a).val (o.succ_ok a)
      ((congrArg (fun x : Number m w => x.val) eq).trans o.zero_ok)
  · intro a b eq
    apply Subtype.ext
    exact h.successor.injective a.val b.val (o.succ a).val a.property b.property (o.succ_ok a)
      (by rw [eq]; exact o.succ_ok b)
  · intro a
    apply Subtype.ext
    apply h.arithmetic.add_unique a.val o.zero.val _ _ o.zero.property (o.add_ok a o.zero)
    rw [o.zero_ok]
    exact h.arithmetic.add_zero a.val a.property
  · intro a b
    apply Subtype.ext
    apply h.arithmetic.add_unique a.val (o.succ b).val _ _ (o.succ b).property (o.add_ok a (o.succ b))
    exact h.arithmetic.add_succ _ _ _ _ _ b.property (o.succ b).property (o.add_ok a b)
      (o.succ_ok b) (o.succ_ok (o.add a b)) (o.succ (o.add a b)).property
  · intro a
    apply Subtype.ext
    apply h.arithmetic.mul_unique a.val o.zero.val _ _ a.property o.zero.property (o.mul_ok a o.zero)
    rw [o.zero_ok]
    exact h.arithmetic.mul_zero a.val a.property
  · intro a b
    apply Subtype.ext
    apply h.arithmetic.mul_unique a.val (o.succ b).val _ _ a.property (o.succ b).property (o.mul_ok a (o.succ b))
    exact h.arithmetic.mul_succ _ _ _ _ _ a.property b.property (o.succ b).property (o.mul_ok a b)
      (o.succ_ok b) (o.add_ok (o.mul a b) a) (o.add (o.mul a b) a).property
  · intro a b he
    apply Subtype.ext
    exact h.real_ext a.val b.val a.property b.property (fun k hk => he ⟨k,hk⟩)
  · intro n p e
    let q : ArithFormula (n+1) := p.relationalize id Fin.elim0
    let v : Fin n → X := fun j => (e j).val
    obtain ⟨A,hA,hcomp⟩ := h.comprehension q v (fun j => (e j).property)
    refine ⟨⟨A,hA⟩,?_⟩
    intro k
    apply (hcomp k.val k.property).trans
    apply standard_translation_correct h o p id Fin.elim0 (push k.val v) (push k e) Fin.elim0
    · intro j
      refine Fin.cases ?_ (fun i => ?_) j <;> simp [v]
    · intro j
      exact Fin.elim0 j
  · intro n k p e a hb hs
    let v : Fin (n+k) → X := Fin.append (fun j => (e j).val) (fun j => (a j).val)
    let f : Fin (n+1) → Fin (n+k+1) := liftRen (fun i => i.castAdd k)
    let g : Fin k → Fin (n+k+1) := fun i => (Fin.natAdd n i).succ
    let q : ArithFormula (n+k+1) := p.relationalize f g
    have bridge (b : Number m w) : q.eval m z w (push b.val v) ↔ p.eval o (push b e) a := by
      apply standard_translation_correct h o p f g (push b.val v) (push b e) a
      · intro j
        refine Fin.cases ?_ (fun i => ?_) j <;> simp [f, v]
      · intro j
        simp [g, v]
    have hbase : q.eval m z w (push z v) := by
      simpa only [o.zero_ok] using (bridge o.zero).mpr hb
    have hstep (b : X) (hb' : m b w) (c : X) (he : SuccRel m b c)
        (hp : q.eval m z w (push b v)) : q.eval m z w (push c v) := by
      let b' : Number m w := ⟨b,hb'⟩
      have eq : c = (o.succ b').val := h.successor.functional _ _ _ he (o.succ_ok b')
      rw [eq]
      exact (bridge (o.succ b')).mpr (hs b' ((bridge b').mp hp))
    have hall := h.induction_schema q v hbase hstep
    exact fun b => (bridge b).mp (hall b.val b.property)

/-- Every model of corrected base DEST, with its explicit infinity axiom,
has a two-sorted functional model of parameter-free full arithmetic on
its own internal natural numbers. -/
theorem base_interprets_standard_arithmetic {X : Type u} (m r : X → X → Prop)
    (h : BaseSatisfies m r) : ∃ z w, (∀ a, ¬ m a z) ∧ LeastInductive m z w ∧
      ∃ o : NumberOperations m z w, StandardArithmeticModel o := by
  obtain ⟨z,w,hz,hw,hp⟩ := base_interprets_arithmetic m r h
  let o := chooseOperations m z w hp
  exact ⟨z,w,hz,hw,o,standard_arithmetic_model hp o⟩

end DESTArithmetic
