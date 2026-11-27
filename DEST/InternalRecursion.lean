import DEST.RecursionSpecification
import DEST.ArithmeticBridge

set_option autoImplicit false
set_option maxHeartbeats 0

universe u
namespace DESTArithmetic
open DESTReference DESTStrength

@[simp] theorem pairF_correct {X : Type u} (m r : X → X → Prop) {n : ℕ}
    (v : Fin n → X) (p a b : Fin n) :
    (pairF p a b).eval m r v ↔ PairCode m (v p) (v a) (v b) := by
  simp only [pairF, PairCode, eval_ex, eval_conj, eval_disj, eval_iffF,
    Formula.eval, push_zero, push_succ]

@[simp] theorem valueF_correct {X : Type u} (m r : X → X → Prop) {n : ℕ}
    (v : Fin n → X) (g k b : Fin n) :
    (valueF g k b).eval m r v ↔ GraphValue m (v g) (v k) (v b) := by
  simp only [valueF, GraphValue, eval_ex, eval_conj, pairF_correct,
    Formula.eval, push_zero, push_succ]

@[simp] theorem indexF_correct {X : Type u} (m r : X → X → Prop) {n : ℕ}
    (v : Fin n → X) (k t : Fin n) :
    (indexF k t).eval m r v ↔ Index m (v k) (v t) := by
  simp only [indexF, Index, eval_disj, Formula.eval]

theorem graphF_correct {X : Type u} (m r : X → X → Prop) (step : StepSyntax)
    (H : X → X → X → X → X → Prop) (hs : StepCorrect m r step H)
    {n : ℕ} (v : Fin n → X) (z w a i t g : Fin n) :
    (graphF step z w a i t g).eval m r v ↔
      RecGraph m (H (v z) (v w) (v a)) (v z) (v w) (v i) (v t) (v g) := by
  have he {k : ℕ} (v' : Fin k → X) (z' w' a' b' c' : Fin k) :
      (step z' w' a' b' c').eval m r v' ↔ H (v' z') (v' w') (v' a') (v' b') (v' c') :=
    hs v' z' w' a' b' c'
  simp only [graphF, eval_conj, valueF_correct, indexF_correct,
    DESTSemantic.succ_correct, Formula.eval, eval_ex, he, push_zero, push_succ]
  constructor
  · rintro ⟨hr, ht, hf, hb, hn⟩
    exact ⟨hr, ht, hf, hb, hn⟩
  · intro h
    exact ⟨h.range, h.total, h.functional, h.base, h.next⟩

theorem graphExistsF_correct {X : Type u} (m r : X → X → Prop) (step : StepSyntax)
    (H : X → X → X → X → X → Prop) (hs : StepCorrect m r step H)
    {n : ℕ} (v : Fin n → X) (z w a i t : Fin n) :
    (graphExistsF step z w a i t).eval m r v ↔
      ∃ g, Uniform m r g ∧ (∀ p, m p g → Uniform m r p) ∧
        RecGraph m (H (v z) (v w) (v a)) (v z) (v w) (v i) (v t) g := by
  simp only [graphExistsF, eval_ex, eval_conj, DESTSemantic.uniformF_correct,
    graphF_correct m r step H hs, Formula.eval, push_zero, push_succ, Uniform]

@[simp] theorem agreeF_correct {X : Type u} (m r : X → X → Prop) {n : ℕ}
    (v : Fin n → X) (g h k : Fin n) :
    (agreeF g h k).eval m r v ↔
      ∀ b c, GraphValue m (v g) (v k) b → GraphValue m (v h) (v k) c → b = c := by
  simp only [agreeF, valueF_correct, Formula.eval, push_zero, push_succ]

theorem outputF_correct {X : Type u} (m r : X → X → Prop) (step : StepSyntax)
    (H : X → X → X → X → X → Prop) (hs : StepCorrect m r step H)
    {n : ℕ} (v : Fin n → X) (z w a i t b : Fin n) :
    (outputF step z w a i t b).eval m r v ↔
      RecOutput m (H (v z) (v w) (v a)) (v z) (v w) (v i) (v t) (v b) := by
  simp only [outputF, RecOutput, eval_ex, eval_conj, graphF_correct m r step H hs,
    valueF_correct, push_zero, push_succ]

theorem succStep_correct {X : Type u} (m r : X → X → Prop) :
    StepCorrect m r succStep (fun _ _ _ b c => SuccRel m b c) := by
  intro n v z w a b c
  exact DESTSemantic.succ_correct m r b c v

@[simp] theorem addF_correct {X : Type u} (m r : X → X → Prop) {n : ℕ}
    (v : Fin n → X) (z w a b c : Fin n) :
    (addF z w a b c).eval m r v ↔ AddRel m (v z) (v w) (v a) (v b) (v c) := by
  exact outputF_correct m r succStep (fun _ _ _ x y => SuccRel m x y)
    (succStep_correct m r) v z w a a b c

theorem mulStep_correct {X : Type u} (m r : X → X → Prop) :
    StepCorrect m r mulStep (fun z w a b c => AddRel m z w b a c) := by
  intro n v z w a b c
  exact addF_correct m r v z w b a c

@[simp] theorem mulF_correct {X : Type u} (m r : X → X → Prop) {n : ℕ}
    (v : Fin n → X) (z w a b c : Fin n) :
    (mulF z w a b c).eval m r v ↔ MulRel m (v z) (v w) (v a) (v b) (v c) := by
  exact outputF_correct m r mulStep (fun z w a x y => AddRel m z w x a y)
    (mulStep_correct m r) v z w a z b c

private theorem pairF_firstOnly {n : ℕ} (p a b : Fin n) : (pairF p a b).firstOnly := by
  simp [pairF, ex, conj, iffF, disj, neg, Formula.firstOnly]

private theorem valueF_firstOnly {n : ℕ} (g k b : Fin n) : (valueF g k b).firstOnly := by
  simp [valueF, ex, conj, neg, Formula.firstOnly, pairF_firstOnly]

private theorem graphF_firstOnly (step : StepSyntax)
    (h : ∀ {n : ℕ} (z w a b c : Fin n), (step z w a b c).firstOnly)
    {n : ℕ} (z w a i t g : Fin n) : (graphF step z w a i t g).firstOnly := by
  simp [graphF, indexF, succF, valueF_firstOnly, ex, conj, iffF, disj, neg, Formula.firstOnly, h]

private theorem outputF_firstOnly (step : StepSyntax)
    (h : ∀ {n : ℕ} (z w a b c : Fin n), (step z w a b c).firstOnly)
    {n : ℕ} (z w a i t b : Fin n) : (outputF step z w a i t b).firstOnly := by
  simp [outputF, ex, conj, neg, Formula.firstOnly, graphF_firstOnly step h, valueF_firstOnly]

theorem addF_firstOnly {n : ℕ} (z w a b c : Fin n) : (addF z w a b c).firstOnly := by
  apply outputF_firstOnly succStep
  intro k z' w' a' b' c'
  simp [succStep, succF, iffF, conj, disj, neg, Formula.firstOnly]

theorem mulF_firstOnly {n : ℕ} (z w a b c : Fin n) : (mulF z w a b c).firstOnly := by
  apply outputF_firstOnly mulStep
  intro k z' w' a' b' c'
  exact addF_firstOnly z' w' b' a' c'

section UniformConstructions
variable {X : Type u} (m r : X → X → Prop) (h : BaseSatisfies m r)
include h

theorem uniform_unordered_pair (a b : X) (ha : Uniform m r a) (hb : Uniform m r b) :
    ∃ p, Uniform m r p ∧ ∀ y, m y p ↔ y = a ∨ y = b := by
  let q : Formula 3 := disj (.eq 0 (Fin.succ 0)) (.eq 0 (Fin.succ (Fin.succ 0)))
  let v : Fin 2 → X := push a (push b Fin.elim0)
  have hv : ∀ j, Uniform m r (v j) := by
    intro j
    refine Fin.cases ?_ (fun k => ?_) j
    · simpa [v] using ha
    · refine Fin.cases ?_ (fun l => Fin.elim0 l) k
      simpa [v] using hb
  have he (y : X) : q.eval m r (push y v) ↔ y = a ∨ y = b := by
    simp only [q, v, eval_disj, Formula.eval, push_zero, push_succ]
  obtain ⟨p,hp,hmem⟩ := uniform_comprehension_of_model m r h q
    (by simp [q, disj, neg, Formula.firstOnly]) v hv (by
      intro y hy
      rcases (he y).mp hy with e | e
      · exact e.symm ▸ ha
      · exact e.symm ▸ hb)
  exact ⟨p,hp,fun y => (hmem y).trans (he y)⟩

theorem uniform_singleton (a : X) (ha : Uniform m r a) :
    ∃ p, Uniform m r p ∧ ∀ y, m y p ↔ y = a := by
  obtain ⟨p,hp,hmem⟩ := uniform_unordered_pair m r h a a ha ha
  exact ⟨p,hp,fun y => ⟨fun hy => ((hmem y).mp hy).elim id id,
    fun hy => (hmem y).mpr (Or.inl hy)⟩⟩

theorem uniform_ordered_pair (a b : X) (ha : Uniform m r a) (hb : Uniform m r b) :
    ∃ p, Uniform m r p ∧ PairCode m p a b := by
  obtain ⟨s,hs,hes⟩ := uniform_singleton m r h a ha
  obtain ⟨t,ht,het⟩ := uniform_unordered_pair m r h a b ha hb
  obtain ⟨p,hp,hep⟩ := uniform_unordered_pair m r h s t hs ht
  exact ⟨p,hp,s,t,hes,het,hep⟩

theorem uniform_adjoin (g p : X) (hg : Uniform m r g) (hp : Uniform m r p)
    (hmem : ∀ y, m y g → Uniform m r y) :
    ∃ g', Uniform m r g' ∧ (∀ y, m y g' → Uniform m r y) ∧
      ∀ y, m y g' ↔ y = p ∨ m y g := by
  let q : Formula 3 := disj (.eq 0 (Fin.succ 0)) (.mem1 0 (Fin.succ (Fin.succ 0)))
  let v : Fin 2 → X := push p (push g Fin.elim0)
  have hv : ∀ j, Uniform m r (v j) := by
    intro j
    refine Fin.cases ?_ (fun k => ?_) j
    · simpa [v] using hp
    · refine Fin.cases ?_ (fun l => Fin.elim0 l) k
      simpa [v] using hg
  have he (y : X) : q.eval m r (push y v) ↔ y = p ∨ m y g := by
    simp only [q, v, eval_disj, Formula.eval, push_zero, push_succ]
  have hu (y : X) (hy : y = p ∨ m y g) : Uniform m r y := by
    rcases hy with e | hy
    · exact e.symm ▸ hp
    · exact hmem y hy
  obtain ⟨g',hg',hge⟩ := uniform_comprehension_of_model m r h q
    (by simp [q, disj, neg, Formula.firstOnly]) v hv (fun y hy => hu y ((he y).mp hy))
  have hg'' (y : X) : m y g' ↔ y = p ∨ m y g := (hge y).trans (he y)
  exact ⟨g',hg',fun y hy => hu y ((hg'' y).mp hy),hg''⟩

end UniformConstructions

/-- Ordered-pair injectivity for arbitrary membership structures. The
intersection of the members of the pair identifies the first coordinate;
their union identifies the two-element set of coordinates. -/
theorem pair_coordinates {X : Type u} (m : X → X → Prop) {p a b c d : X}
    (h : PairCode m p a b) (h' : PairCode m p c d) : a = c ∧ b = d := by
  have intersect (x y : X) (hc : PairCode m p x y) (v : X) :
      (∀ t, m t p → m v t) ↔ v = x := by
    obtain ⟨s,t,hs,ht,hp⟩ := hc
    constructor
    · intro hv
      exact (hs v).mp (hv s ((hp s).mpr (Or.inl rfl)))
    · intro hv q hq
      rcases (hp q).mp hq with e | e
      · subst q
        exact (hs v).mpr hv
      · subst q
        exact (ht v).mpr (Or.inl hv)
  have union (x y : X) (hc : PairCode m p x y) (v : X) :
      (∃ t, m t p ∧ m v t) ↔ v = x ∨ v = y := by
    obtain ⟨s,t,hs,ht,hp⟩ := hc
    constructor
    · rintro ⟨q,hq,hv⟩
      rcases (hp q).mp hq with e | e
      · subst q
        exact Or.inl ((hs v).mp hv)
      · subst q
        exact (ht v).mp hv
    · intro hv
      exact ⟨t,(hp t).mpr (Or.inr rfl),(ht v).mpr hv⟩
  have e : a = c := (intersect c d h' a).mp ((intersect a b h a).mpr rfl)
  subst c
  refine ⟨rfl,?_⟩
  have hb : b = a ∨ b = d := (union a d h' b).mp ((union a b h b).mpr (Or.inr rfl))
  have hd : d = a ∨ d = b := (union a b h d).mp ((union a d h' d).mpr (Or.inr rfl))
  rcases hb with hb | hb
  · rcases hd with hd | hd
    · exact hb.trans hd.symm
    · exact hd.symm
  · exact hb

section Recursion
variable {X : Type u} (m r : X → X → Prop) (h : BaseSatisfies m r)
    (z w : X) (hz : ∀ a, ¬ m a z) (hw : LeastInductive m z w)

private theorem index_mem_number (laws : SuccessorLaws m z w) {k n : X}
    (hn : m n w) (hk : Index m k n) : m k w := by
  rcases hk with e | hk
  · exact e.symm ▸ hn
  · exact laws.members n hn k hk

private theorem index_pred (laws : SuccessorLaws m z w) {k l n : X}
    (hn : m n w) (hl : Index m l n) (he : SuccRel m k l) : Index m k n := by
  have hk : m k l := (he k).mpr (Or.inl rfl)
  rcases hl with e | hl
  · exact Or.inr (e ▸ hk)
  · exact Or.inr (laws.transitive n hn l k hk hl)

include h hz hw

private theorem singleton_graph (H : X → X → Prop) (i : X) (hi : m i w) :
    ∃ g, Uniform m r g ∧ (∀ p, m p g → Uniform m r p) ∧
      RecGraph m H z w i z g := by
  have laws := internal_successor_laws m r h z w hz hw
  have hu := (uniform_omega_of_model m r h z w hz hw).2
  obtain ⟨p,hp,hpair⟩ := uniform_ordered_pair m r h z i (hu z laws.zero_mem) (hu i hi)
  obtain ⟨g,hg,hge⟩ := uniform_singleton m r h p hp
  have hv (k b : X) : GraphValue m g k b ↔ k = z ∧ b = i := by
    constructor
    · rintro ⟨q,hq,hc⟩
      have e := (hge q).mp hq
      subst q
      exact pair_coordinates m hc hpair
    · rintro ⟨rfl,rfl⟩
      exact ⟨p,(hge p).mpr rfl,hpair⟩
  refine ⟨g,hg,?_,?_⟩
  · intro q hq
    exact ((hge q).mp hq).symm ▸ hp
  · constructor
    · intro k b hk
      obtain ⟨e,f⟩ := (hv k b).mp hk
      exact ⟨Or.inl e,f.symm ▸ hi⟩
    · intro k hk
      rcases hk with e | hk
      · exact ⟨i,(hv k i).mpr ⟨e,rfl⟩⟩
      · exact (hz k hk).elim
    · intro k b c hb hc
      exact ((hv k b).mp hb).2.trans ((hv k c).mp hc).2.symm
    · exact (hv z i).mpr ⟨rfl,rfl⟩
    · intro k l b c _ hl he
      exact (laws.not_zero k l he ((hv l c).mp hl).1).elim

/-- Adjoin one new pair to an existing internal graph. The proof uses
only uniform comprehension and the internal Peano successor laws. -/
private theorem extend_graph (H : X → X → Prop) (i n s g b c : X)
    (hn : m n w) (hs : m s w) (he : SuccRel m n s)
    (hg : Uniform m r g) (hgm : ∀ p, m p g → Uniform m r p)
    (hr : RecGraph m H z w i n g) (hb : GraphValue m g n b) (hc : m c w)
    (hbc : H b c) :
    ∃ g', Uniform m r g' ∧ (∀ p, m p g' → Uniform m r p) ∧
      RecGraph m H z w i s g' ∧ GraphValue m g' s c := by
  have laws := internal_successor_laws m r h z w hz hw
  have hu := (uniform_omega_of_model m r h z w hz hw).2
  obtain ⟨p,hp,hpair⟩ := uniform_ordered_pair m r h s c (hu s hs) (hu c hc)
  obtain ⟨g',hg',hgm',hge⟩ := uniform_adjoin m r h g p hg hp hgm
  have hv (k v : X) : GraphValue m g' k v ↔ (k = s ∧ v = c) ∨ GraphValue m g k v := by
    constructor
    · rintro ⟨q,hq,hc'⟩
      rcases (hge q).mp hq with e | hq
      · subst q
        exact Or.inl (pair_coordinates m hc' hpair)
      · exact Or.inr ⟨q,hq,hc'⟩
    · rintro (⟨rfl,rfl⟩ | ⟨q,hq,hc'⟩)
      · exact ⟨p,(hge p).mpr (Or.inl rfl),hpair⟩
      · exact ⟨q,(hge q).mpr (Or.inr hq),hc'⟩
  have old_mem (k : X) (hk : Index m k n) : m k s := (he k).mpr hk
  have old_ne (k : X) (hk : Index m k n) : k ≠ s := by
    intro e
    exact laws.irreflexive s hs (e ▸ old_mem k hk)
  refine ⟨g',hg',hgm',?_,(hv s c).mpr (Or.inl ⟨rfl,rfl⟩)⟩
  constructor
  · intro k v hk
    rcases (hv k v).mp hk with ⟨e,f⟩ | hk
    · exact ⟨Or.inl e,f.symm ▸ hc⟩
    · obtain ⟨hkn,hvw⟩ := hr.range k v hk
      exact ⟨Or.inr (old_mem k hkn),hvw⟩
  · intro k hk
    rcases hk with e | hk
    · exact ⟨c,(hv k c).mpr (Or.inl ⟨e,rfl⟩)⟩
    · obtain ⟨v,hv'⟩ := hr.total k ((he k).mp hk)
      exact ⟨v,(hv k v).mpr (Or.inr hv')⟩
  · intro k v v' hk hk'
    rcases (hv k v).mp hk with ⟨e,f⟩ | hk
    · rcases (hv k v').mp hk' with ⟨_,f'⟩ | hk'
      · exact f.trans f'.symm
      · exact (old_ne k (hr.range k v' hk').1 e).elim
    · rcases (hv k v').mp hk' with ⟨e,_⟩ | hk'
      · exact (old_ne k (hr.range k v hk).1 e).elim
      · exact hr.functional k v v' hk hk'
  · exact (hv z i).mpr (Or.inr hr.base)
  · intro k l v v' hk hl hkl
    rcases (hv k v).mp hk with ⟨e,f⟩ | hk
    · subst k
      have hsl : m s l := (hkl s).mpr (Or.inl rfl)
      rcases (hv l v').mp hl with ⟨e',_⟩ | hl
      · subst l
        exact (laws.irreflexive s hs hsl).elim
      · exact (laws.irreflexive s hs
          (laws.transitive s hs l s hsl (old_mem l (hr.range l v' hl).1))).elim
    · rcases (hv l v').mp hl with ⟨e,f⟩ | hl
      · subst l
        subst v'
        have hkN := index_mem_number m z w laws hn (hr.range k v hk).1
        have ekn := laws.injective k n s hkN hn hkl he
        subst k
        have ev := hr.functional n v b hk hb
        exact ev.symm ▸ hbc
      · exact hr.next k l v v' hk hl hkl

/-- Internal recursion for any syntactically defined total numerical step.
The induction formula asserts existence of a uniform graph; it is a genuine
instance of DEST induction, not an induction over the ambient Lean Nat. -/
theorem internal_recursion_graph (step : StepSyntax) (H : X → X → X → X → X → Prop)
    (hstep : StepCorrect m r step H) (a i : X) (hi : m i w)
    (htotal : ∀ b, m b w → ∃ c, m c w ∧ H z w a b c) :
    ∀ n, m n w → ∃ g, Uniform m r g ∧ (∀ p, m p g → Uniform m r p) ∧
      RecGraph m (H z w a) z w i n g := by
  have laws := internal_successor_laws m r h z w hz hw
  let p : Formula 5 := graphExistsF step (Fin.succ 0) (Fin.succ (Fin.succ 0))
    (Fin.succ (Fin.succ (Fin.succ 0))) (Fin.succ (Fin.succ (Fin.succ (Fin.succ 0)))) 0
  let v : Fin 4 → X := push z (push w (push a (push i Fin.elim0)))
  have hp (n : X) : p.eval m r (push n v) ↔
      ∃ g, Uniform m r g ∧ (∀ q, m q g → Uniform m r q) ∧ RecGraph m (H z w a) z w i n g := by
    simp only [p, v, graphExistsF_correct m r step H hstep, push_zero, push_succ]
  have hb := (hp z).mpr (singleton_graph m r h z w hz hw (H z w a) i hi)
  have hs (n : X) (hn : m n w) (s : X) (he : SuccRel m n s)
      (hprev : p.eval m r (push n v)) : p.eval m r (push s v) := by
    obtain ⟨g,hg,hgm,hr⟩ := (hp n).mp hprev
    obtain ⟨s',hs',he'⟩ := laws.total n hn
    have es := laws.functional n s' s he' he
    have hsN : m s w := es ▸ hs'
    obtain ⟨b,hb⟩ := hr.total n (Or.inl rfl)
    obtain ⟨c,hc,hbc⟩ := htotal b (hr.range n b hb).2
    obtain ⟨g',hg',hgm',hr',_⟩ := extend_graph m r h z w hz hw (H z w a) i n s g b c
      hn hsN he hg hgm hr hb hc hbc
    exact (hp s).mpr ⟨g',hg',hgm',hr'⟩
  have hall := internal_induction m r h z w hz hw p v hb hs
  exact fun n hn => (hp n).mp (hall n hn)

/-- Values in two internal graphs with the same input and numerical step
agree, even when the graphs themselves are not uniform. -/
theorem internal_recursion_unique (H : X → X → Prop) (i n : X) (hn : m n w)
    (hfun : ∀ b c d, m b w → H b c → H b d → c = d)
    {b c : X} (hb : RecOutput m H z w i n b) (hc : RecOutput m H z w i n c) : b = c := by
  obtain ⟨g,hg,hb⟩ := hb
  obtain ⟨f,hf,hc⟩ := hc
  have laws := internal_successor_laws m r h z w hz hw
  let p : Formula 3 := agreeF (Fin.succ 0) (Fin.succ (Fin.succ 0)) 0
  let v : Fin 2 → X := push g (push f Fin.elim0)
  have hp (k : X) : p.eval m r (push k v) ↔
      ∀ b c, GraphValue m g k b → GraphValue m f k c → b = c := by
    simp only [p, v, agreeF_correct, push_zero, push_succ]
  have hbase := (hp z).mpr (fun x y hx hy =>
    (hg.functional z x i hx hg.base).trans (hf.functional z i y hf.base hy))
  have hs (k : X) (_ : m k w) (l : X) (he : SuccRel m k l)
      (hprev : p.eval m r (push k v)) : p.eval m r (push l v) := by
    apply (hp l).mpr
    intro x y hx hy
    have hkn := index_pred m z w laws hn (hg.range l x hx).1 he
    obtain ⟨x',hx'⟩ := hg.total k hkn
    obtain ⟨y',hy'⟩ := hf.total k hkn
    have e := (hp k).mp hprev x' y' hx' hy'
    subst y'
    exact hfun x' x y (hg.range k x' hx').2 (hg.next k l x' x hx' hx he)
      (hf.next k l x' y hy' hy he)
  have hall := internal_induction m r h z w hz hw p v hbase hs
  exact (hp n).mp (hall n hn) b c hb hc

private theorem internal_recursion_total (step : StepSyntax) (H : X → X → X → X → X → Prop)
    (hstep : StepCorrect m r step H) (a i : X) (hi : m i w)
    (htotal : ∀ b, m b w → ∃ c, m c w ∧ H z w a b c) (n : X) (hn : m n w) :
    ∃ b, m b w ∧ RecOutput m (H z w a) z w i n b := by
  obtain ⟨g,_,_,hg⟩ := internal_recursion_graph m r h z w hz hw step H hstep a i hi htotal n hn
  obtain ⟨b,hb⟩ := hg.total n (Or.inl rfl)
  exact ⟨b,(hg.range n b hb).2,g,hg,hb⟩

private theorem internal_recursion_zero (H : X → X → Prop) (i : X) (hi : m i w) :
    RecOutput m H z w i z i := by
  obtain ⟨g,_,_,hg⟩ := singleton_graph m r h z w hz hw H i hi
  exact ⟨g,hg,hg.base⟩

private theorem internal_recursion_succ (step : StepSyntax) (H : X → X → X → X → X → Prop)
    (hstep : StepCorrect m r step H) (a i n s b c : X) (hn : m n w) (hs : m s w)
    (he : SuccRel m n s) (hb : RecOutput m (H z w a) z w i n b) (hc : m c w)
    (hbc : H z w a b c) (hi : m i w)
    (htotal : ∀ v, m v w → ∃ y, m y w ∧ H z w a v y)
    (hfun : ∀ v x y, m v w → H z w a v x → H z w a v y → x = y) :
    RecOutput m (H z w a) z w i s c := by
  obtain ⟨g,hg,hgm,hr⟩ := internal_recursion_graph m r h z w hz hw step H hstep a i hi htotal n hn
  obtain ⟨b',hb'⟩ := hr.total n (Or.inl rfl)
  have e := internal_recursion_unique m r h z w hz hw (H z w a) i n hn hfun hb ⟨g,hr,hb'⟩
  subst b'
  obtain ⟨g',_,_,hr',hv⟩ := extend_graph m r h z w hz hw (H z w a) i n s g b c
    hn hs he hg hgm hr hb' hc hbc
  exact ⟨g',hr',hv⟩

/-- All recursive PA operation equations in arbitrary models of base DEST.
No standard numeral frame, second-order choice or set induction is used. -/
theorem internal_arithmetic_laws : ArithmeticLaws m z w := by
  have laws := internal_successor_laws m r h z w hz hw
  let H : X → X → X → X → X → Prop := fun _ _ _ b c => SuccRel m b c
  have htotal (a b : X) (ha : m a w) (hb : m b w) :
      ∃ c, m c w ∧ AddRel m z w a b c :=
    internal_recursion_total m r h z w hz hw succStep H (succStep_correct m r)
      a a ha laws.total b hb
  have hfun (a b c d : X) (hb : m b w) (hc : AddRel m z w a b c) (hd : AddRel m z w a b d) : c = d :=
    internal_recursion_unique m r h z w hz hw (SuccRel m) a b hb
      (fun v x y _ hx hy => laws.functional v x y hx hy) hc hd
  have hrange (a b c : X) (hc : AddRel m z w a b c) : m c w := by
    obtain ⟨g,hg,hv⟩ := hc
    exact (hg.range b c hv).2
  let J : X → X → X → X → X → Prop := fun z' w' a b c => AddRel m z' w' b a c
  have jtotal (a : X) (ha : m a w) (v : X) (hv : m v w) : ∃ c, m c w ∧ J z w a v c :=
    htotal v a hv ha
  have jfun (a : X) (ha : m a w) (v x y : X) (_ : m v w) (hx : J z w a v x) (hy : J z w a v y) : x = y :=
    hfun v a x y ha hx hy
  refine ⟨htotal,hfun,hrange,?_,?_,?_,?_,?_,?_,?_⟩
  · intro a ha
    exact internal_recursion_zero m r h z w hz hw (SuccRel m) a ha
  · intro a b c b' c' hb hb' hc he hc' hcN
    obtain ⟨g,hg,hv⟩ := hc
    have ha : m a w := (hg.range z a hg.base).2
    exact internal_recursion_succ m r h z w hz hw succStep H (succStep_correct m r)
      a a b b' c c' hb hb' he ⟨g,hg,hv⟩ hcN hc' ha laws.total
      (fun v x y _ hx hy => laws.functional v x y hx hy)
  · intro a b ha hb
    exact internal_recursion_total m r h z w hz hw mulStep J (mulStep_correct m r)
      a z laws.zero_mem (jtotal a ha) b hb
  · intro a b c d ha hb hc hd
    exact internal_recursion_unique m r h z w hz hw (J z w a) z b hb (jfun a ha) hc hd
  · intro a b c hc
    obtain ⟨g,hg,hv⟩ := hc
    exact (hg.range b c hv).2
  · intro a _
    exact internal_recursion_zero m r h z w hz hw (J z w a) z laws.zero_mem
  · intro a b c b' c' ha hb hb' hc he hc' hcN
    exact internal_recursion_succ m r h z w hz hw mulStep J (mulStep_correct m r)
      a z b b' c c' hb hb' he hc hcN hc' laws.zero_mem (jtotal a ha) (jfun a ha)

end Recursion
end DESTArithmetic
