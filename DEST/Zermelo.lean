import DEST.ZermeloSyntax

/-! A set-coded Zermelo domain in every original DEST + SU1 model.
The induction arguments below always use an explicit formula of the reference
language. The external Lean natural numbers are used only as syntax indices. -/
set_option autoImplicit false
set_option maxHeartbeats 0
universe u
namespace DESTOriginal
open DESTReference

section Elementary
variable {X : Type u} (m r : X → X → Prop) (h : Original m r)
include h

theorem induction_on (z w : X) (hz : Zero m z) (hw : LeastInductive m z w)
    {n : ℕ} (p : Formula (n+1)) (v : Fin n → X) (P : X → Prop)
    (he : ∀ a, p.eval m r (push a v) ↔ P a) (hb : P z)
    (hs : ∀ a b, m a w → Succ m a b → P a → P b) : ∀ a, m a w → P a := by
  intro a ha
  apply (he a).mp
  exact h.natInd z hz p v ((he z).mpr hb)
    (fun x hx b hxb hp => (he b).mpr (hs x b (hx w hw.1) hxb ((he x).mp hp)))
    a (fun t ht => hw.2 t ht a ha)

theorem successor_functional (a b c : X) (hb : Succ m a b) (hc : Succ m a c) : b = c :=
  h.ext1 b c (fun y => (hb y).trans (hc y).symm)

theorem successor_mem (z w a b : X) (hw : LeastInductive m z w)
    (ha : m a w) (hb : Succ m a b) : m b w := by
  obtain ⟨c,hc,hs⟩ := hw.1.2 a ha
  exact (successor_functional m r h a c b hs hb) ▸ hc

theorem successor_ne_zero (z a b : X) (hz : Zero m z) (hb : Succ m a b) : b ≠ z := by
  intro e
  exact hz a (e ▸ (hb a).mpr (Or.inl rfl))

end Elementary

private theorem uniform_push {X : Type u} {m r : X → X → Prop} {n : ℕ}
    (a : X) (v : Fin n → X) (ha : Uniform m r a) (hv : ∀ i, Uniform m r (v i)) :
    ∀ i, Uniform m r (push a v i) := by
  intro i; refine Fin.cases ?_ (fun j => ?_) i
  · simpa using ha
  · simpa using hv j

section Constructions
variable {X : Type u} (m r : X → X → Prop) (h : Original m r)
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
  obtain ⟨p,hp,hmem⟩ := uniform_collection m r h q
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
  obtain ⟨g',hg',hge⟩ := uniform_collection m r h q
    (by simp [q, disj, neg, Formula.firstOnly]) v hv (fun y hy => hu y ((he y).mp hy))
  have hg'' (y : X) : m y g' ↔ y = p ∨ m y g := (hge y).trans (he y)
  exact ⟨g',hg',fun y hy => hu y ((hg'' y).mp hy),hg''⟩


end Constructions

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

section MoreConstructions
variable {X : Type u} (m r : X → X → Prop) (h : Original m r)
include h

theorem uniform_power (su : SU1 m r) (a : X) (ha : Uniform m r a) :
    ∃ b, AllUniform m r b ∧ Power m a b := by
  let v : Fin 1 → X := push a Fin.elim0
  let p : Formula 2 := subF 0 (Fin.succ 0)
  have hv := uniform_push a Fin.elim0 ha (fun i => Fin.elim0 i)
  have he (y : X) : p.eval m r (push y v) ↔ Sub m y a := by
    simp only [p,v,subF_correct,push_zero,push_succ]
  obtain ⟨b,hb,hm⟩ := collect m r h p (subF_first _ _) v hv _ he (fun y hy => su a y ha hy)
  exact ⟨b,⟨hb,fun y hy => su a y ha ((hm y).mp hy)⟩,hm⟩

theorem uniform_intersection (a b : X) (ha : Uniform m r a) (hb : Uniform m r b)
    (hu : ∀ y, m y a → Uniform m r y) : ∃ c, Uniform m r c ∧ ∀ y, m y c ↔ m y a ∧ m y b := by
  let v : Fin 2 → X := push a (push b Fin.elim0)
  let p : Formula 3 := conj (.mem1 0 (Fin.succ 0)) (.mem1 0 (Fin.succ (Fin.succ 0)))
  have hv : ∀ i, Uniform m r (v i) := uniform_push a _ ha (uniform_push b _ hb (fun i => Fin.elim0 i))
  have he (y : X) : p.eval m r (push y v) ↔ m y a ∧ m y b := by
    simp only [p,v,eval_conj,Formula.eval,push_zero,push_succ]
  exact collect m r h p (by simp [p,conj,neg,Formula.firstOnly]) v hv _ he (fun y hy => hu y hy.1)

theorem uniform_union (a : X) (ha : Uniform m r a)
    (hu : ∀ y z, m z a → m y z → Uniform m r y) :
    ∃ b, Uniform m r b ∧ ∀ y, m y b ↔ ∃ z, m z a ∧ m y z := by
  let v : Fin 1 → X := push a Fin.elim0
  let p : Formula 2 := ex (conj (.mem1 0 (Fin.succ (Fin.succ 0))) (.mem1 (Fin.succ 0) 0))
  have hv : ∀ i, Uniform m r (v i) := uniform_push a _ ha (fun i => Fin.elim0 i)
  have he (y : X) : p.eval m r (push y v) ↔ ∃ z, m z a ∧ m y z := by
    simp only [p,v,eval_ex,eval_conj,Formula.eval,push_zero,push_succ]
  exact collect m r h p (by simp [p,ex,conj,neg,Formula.firstOnly]) v hv _ he
    (fun y ⟨z,hz,hy⟩ => hu y z hz hy)

theorem power_good (su : SU1 m r) (a b : X) (ha : GoodStage m r a) (hp : Power m a b) : GoodStage m r b := by
  classical
  obtain ⟨c,hc,hpc⟩ := uniform_power m r h su a ha.1.1
  have e : c = b := h.ext1 _ _ (fun y => (hpc y).trans (hp y).symm)
  have hb : AllUniform m r b := e ▸ hc
  have htrans : Transitive m b := by
    intro y x hxy hy
    apply (hp x).mpr
    intro z hz
    exact ha.2.1 x z hz ((hp y).mp hy x hxy)
  refine ⟨hb,htrans,?_⟩
  intro d hd
  obtain ⟨hdb,x,hxd⟩ := hd
  by_cases hex : ∃ y, m y d ∧ m y a
  · have hdu := su b d hb.1 hdb
    obtain ⟨i,hi,he⟩ := uniform_intersection m r h a d ha.1.1 hdu ha.1.2
    obtain ⟨y,hy,hm⟩ := hex
    obtain ⟨q,hq,hmin⟩ := ha.2.2 i ⟨fun v hv => ((he v).mp hv).1, y,(he y).mpr ⟨hm,hy⟩⟩
    refine ⟨q,((he q).mp hq).2,?_⟩
    intro v hvd hvq
    exact hmin v ((he v).mpr ⟨ha.2.1 q v hvq ((he q).mp hq).1,hvd⟩) hvq
  · refine ⟨x,hxd,?_⟩
    intro v hvd hvx
    exact hex ⟨v,hvd,(hp x).mp (hdb x hxd) v hvx⟩

end MoreConstructions

section Numbers
variable {X : Type u} (m r : X → X → Prop) (h : Original m r)
variable (z w : X) (hz : Zero m z) (hw : LeastInductive m z w)
include h hz hw

theorem number_core : ∀ a, m a w → NumCore m a w := by
  let p : Formula 2 := numCoreF 0 (Fin.succ 0)
  let v : Fin 1 → X := push w Fin.elim0
  have he (a : X) : p.eval m r (push a v) ↔ NumCore m a w := by
    simp only [p,v,numCoreF_correct,push_zero,push_succ]
  apply induction_on m r h z w hz hw p v _ he
  · exact ⟨fun y x _ hy => (hz y hy).elim,hz z,fun y hy => (hz y hy).elim⟩
  · intro a b ha hs hc
    obtain ⟨ht,hir,hsub⟩ := hc
    refine ⟨?_,?_,?_⟩
    · intro y x hxy hy
      rcases (hs y).mp hy with e | hy
      · subst y; exact (hs x).mpr (Or.inr hxy)
      · exact (hs x).mpr (Or.inr (ht y x hxy hy))
    · intro hbb
      rcases (hs b).mp hbb with e | hba
      · subst b; exact hir hbb
      · exact hir (ht b a ((hs a).mpr (Or.inl rfl)) hba)
    · intro y hy
      rcases (hs y).mp hy with e | hy
      · exact e.symm ▸ ha
      · exact hsub y hy

theorem successor_injective (a b c : X) (ha : m a w) (hb : m b w)
    (hac : Succ m a c) (hbc : Succ m b c) : a = b := by
  classical
  by_contra hn
  have hab := ((hbc a).mp ((hac a).mpr (Or.inl rfl))).resolve_left hn
  have hba := ((hac b).mp ((hbc b).mpr (Or.inl rfl))).resolve_left (Ne.symm hn)
  have hc := number_core m r h z w hz hw a ha
  exact hc.2.1 (hc.1 b a hab hba)

theorem zero_or_contains_zero : ∀ a, m a w → a = z ∨ m z a := by
  let p : Formula 2 := disj (.eq 0 (Fin.succ 0)) (.mem1 (Fin.succ 0) 0)
  let v : Fin 1 → X := push z Fin.elim0
  have he (a : X) : p.eval m r (push a v) ↔ a = z ∨ m z a := by
    simp only [p,v,eval_disj,Formula.eval,push_zero,push_succ]
  apply induction_on m r h z w hz hw p v _ he (Or.inl rfl)
  intro a b _ hs ha
  exact Or.inr ((hs z).mpr (ha.elim (fun e => Or.inl e.symm) Or.inr))

theorem successor_below (a s : X) (hs : Succ m a s) :
    ∀ k, m k w → Earlier m a s k := by
  let p : Formula 3 := earlierF (Fin.succ 0) (Fin.succ (Fin.succ 0)) 0
  let v : Fin 2 → X := push a (push s Fin.elim0)
  have he (k : X) : p.eval m r (push k v) ↔ Earlier m a s k := by
    simp only [p,v,earlierF_correct,push_zero,push_succ]
  apply induction_on m r h z w hz hw p v _ he
  · exact fun ha => (hz a ha).elim
  · intro k l _ hkl ih hak
    rcases (hkl a).mp hak with e | hak
    · subst k
      exact Or.inl (successor_functional m r h a s l hs hkl)
    · exact Or.inr ((hkl s).mpr (ih hak))

theorem number_compare (a : X) (ha : m a w) : ∀ b, m b w → Compare m a b := by
  let p : Formula 2 := compareF (Fin.succ 0) 0
  let v : Fin 1 → X := push a Fin.elim0
  have he (b : X) : p.eval m r (push b v) ↔ Compare m a b := by
    simp only [p,v,compareF_correct,push_zero,push_succ]
  apply induction_on m r h z w hz hw p v _ he
  · rcases zero_or_contains_zero m r h z w hz hw a ha with e | he'
    · exact Or.inl e
    · exact Or.inr (Or.inr he')
  · intro b s _ hbs ih
    rcases ih with e | hab | hba
    · exact Or.inr (Or.inl ((hbs a).mpr (Or.inl e)))
    · exact Or.inr (Or.inl ((hbs a).mpr (Or.inr hab)))
    · rcases successor_below m r h z w hz hw b s hbs a ha hba with e | hsa
      · exact Or.inl e.symm
      · exact Or.inr (Or.inr hsa)

theorem omega_good (hu : AllUniform m r w) : GoodStage m r w := by
  classical
  refine ⟨hu,fun y x hxy hy => (number_core m r h z w hz hw y hy).2.2 x hxy,?_⟩
  intro b hb
  obtain ⟨hsub,a,ha⟩ := hb
  by_contra hn
  let p : Formula 2 := avoidF 0 (Fin.succ 0)
  let v : Fin 1 → X := push b Fin.elim0
  have he (k : X) : p.eval m r (push k v) ↔ Avoid m k b := by
    simp only [p,v,avoidF_correct,push_zero,push_succ]
  have hi : ∀ k, m k w → Avoid m k b := by
    apply induction_on m r h z w hz hw p v _ he
    · refine ⟨?_,fun y hy => (hz y hy).elim⟩
      intro hzb
      exact hn ⟨z,hzb,fun y _ hy => hz y hy⟩
    · intro k l _ hkl ih
      have hall : ∀ y, m y l → ¬ m y b := by
        intro y hy
        rcases (hkl y).mp hy with e | hy
        · subst y; exact ih.1
        · exact ih.2 y hy
      exact ⟨fun hl => hn ⟨l,hl,fun y hy hb' => hall y hb' hy⟩,hall⟩
  exact (hi a (hsub a ha)).1 ha

end Numbers

section Towers
variable {X : Type u} (m r : X → X → Prop) (h : Original m r) (su : SU1 m r)
variable (z w : X) (hz : Zero m z) (hw : LeastInductive m z w) (hu : AllUniform m r w)
include h su hz hw hu


/-- Every internally natural index has an internally coded graph, all of
whose entries are uniform. The graph need not be externally finite. -/
theorem stages_exist : ∀ k, m k w → StageExists m r z w k := by
  let p : Formula 3 := stageExistsF (Fin.succ 0) (Fin.succ (Fin.succ 0)) 0
  let v : Fin 2 → X := push z (push w Fin.elim0)
  have he (k : X) : p.eval m r (push k v) ↔ StageExists m r z w k := by
    simp only [p,v,stageExistsF_correct,push_zero,push_succ]
  apply induction_on m r h z w hz hw p v _ he
  · obtain ⟨q,hq,hpair⟩ := uniform_ordered_pair m r h z w (hu.2 z hw.1.1) hu.1
    obtain ⟨g,hg,hmem⟩ := uniform_singleton m r h q hq
    have hv (k a : X) (hh : Value m g k a) : k = z ∧ a = w := by
      obtain ⟨b,hb,hbpair⟩ := hh
      have e : b = q := (hmem b).mp hb
      subst b
      exact pair_coordinates m hbpair hpair
    refine ⟨g,w,⟨hg,fun y hy => ((hmem y).mp hy).symm ▸ hq⟩,hu.1,?_,q,(hmem q).mpr rfl,hpair⟩
    intro k a hka
    obtain ⟨e,f⟩ := hv k a hka
    subst k; subst a
    exact ⟨hw.1.1,fun _ => rfl,fun hn => (hn rfl).elim⟩
  · intro k s hk hs ih
    obtain ⟨g,a,hg,ha,hgraph,hvalue⟩ := ih
    have hsN := successor_mem m r h z w k s hw hk hs
    obtain ⟨b,hb,hpower⟩ := uniform_power m r h su a ha
    obtain ⟨q,hq,hpair⟩ := uniform_ordered_pair m r h s b (hu.2 s hsN) hb.1
    obtain ⟨g',hg',hgu,hmem⟩ := uniform_adjoin m r h g q hg.1 hq hg.2
    have old (i x : X) (hh : Value m g i x) : Value m g' i x := by
      obtain ⟨q',hq',hp⟩ := hh
      exact ⟨q',(hmem q').mpr (Or.inr hq'),hp⟩
    have hv (i x : X) (hh : Value m g' i x) : (i = s ∧ x = b) ∨ Value m g i x := by
      obtain ⟨q',hq',hp⟩ := hh
      rcases (hmem q').mp hq' with e | he'
      · subst q'; exact Or.inl (pair_coordinates m hp hpair)
      · exact Or.inr ⟨q',he',hp⟩
    refine ⟨g',b,⟨hg',hgu⟩,hb.1,?_,q,(hmem q).mpr (Or.inl rfl),hpair⟩
    intro i x hi
    rcases hv i x hi with ⟨e,f⟩ | hv'
    · subst i; subst x
      exact ⟨hsN,fun e => (successor_ne_zero m r h z k s hz hs e).elim,
        fun _ => ⟨k,a,hs,old k a hvalue,hpower⟩⟩
    · obtain ⟨hn,hbase,hstep⟩ := hgraph i x hv'
      exact ⟨hn,hbase,fun hnz => by
        obtain ⟨j,b',hjs,hjb,hpb⟩ := hstep hnz
        exact ⟨j,b',hjs,old j b' hjb,hpb⟩⟩

theorem stage_total (k : X) (hk : m k w) : ∃ a, Stage m z w k a := by
  obtain ⟨g,a,_,_,hg,hv⟩ := stages_exist m r h su z w hz hw hu k hk
  exact ⟨a,g,hg,hv⟩

theorem stage_zero (a : X) (ha : Stage m z w z a) : a = w := by
  obtain ⟨g,hg,hv⟩ := ha
  exact (hg z a hv).2.1 rfl

private theorem stage_prev (k s b : X) (hk : m k w) (hs : Succ m k s)
    (hb : Stage m z w s b) : ∃ a, Stage m z w k a ∧ Power m a b := by
  obtain ⟨g,hg,hv⟩ := hb
  obtain ⟨j,a,hjs,hja,hp⟩ := (hg s b hv).2.2 (successor_ne_zero m r h z k s hz hs)
  have hj := (hg j a hja).1
  have e := successor_injective m r h z w hz hw j k s hj hk hjs hs
  subst j
  exact ⟨a,⟨g,hg,hja⟩,hp⟩

theorem all_stages_good : ∀ k, m k w → StageGood m r z w k := by
  let p : Formula 3 := stageGoodF (Fin.succ 0) (Fin.succ (Fin.succ 0)) 0
  let v : Fin 2 → X := push z (push w Fin.elim0)
  have he (k : X) : p.eval m r (push k v) ↔ StageGood m r z w k := by
    simp only [p,v,stageGoodF_correct,push_zero,push_succ]
  apply induction_on m r h z w hz hw p v _ he
  · intro a ha
    have e := stage_zero m r h su z w hz hw hu a ha
    exact e.symm ▸ omega_good m r h z w hz hw hu
  · intro k s hk hs ih b hb
    obtain ⟨a,ha,hp⟩ := stage_prev m r h su z w hz hw hu k s b hk hs hb
    exact power_good m r h su a b (ih a ha) hp

theorem stages_unique : ∀ k, m k w → StageUnique m z w k := by
  let p : Formula 3 := stageUniqueF (Fin.succ 0) (Fin.succ (Fin.succ 0)) 0
  let v : Fin 2 → X := push z (push w Fin.elim0)
  have he (k : X) : p.eval m r (push k v) ↔ StageUnique m z w k := by
    simp only [p,v,stageUniqueF_correct,push_zero,push_succ]
  apply induction_on m r h z w hz hw p v _ he
  · intro a b ha hb
    exact (stage_zero m r h su z w hz hw hu a ha).trans (stage_zero m r h su z w hz hw hu b hb).symm
  · intro k s hk hs ih a b ha hb
    obtain ⟨a',ha',hpa⟩ := stage_prev m r h su z w hz hw hu k s a hk hs ha
    obtain ⟨b',hb',hpb⟩ := stage_prev m r h su z w hz hw hu k s b hk hs hb
    have e := ih a' b' ha' hb'
    subst b'
    exact h.ext1 a b (fun y => (hpa y).trans (hpb y).symm)

theorem stages_nested : ∀ k, m k w → StageNest m z w k := by
  let p : Formula 3 := stageNestF (Fin.succ 0) (Fin.succ (Fin.succ 0)) 0
  let v : Fin 2 → X := push z (push w Fin.elim0)
  have he (k : X) : p.eval m r (push k v) ↔ StageNest m z w k := by
    simp only [p,v,stageNestF_correct,push_zero,push_succ]
  apply induction_on m r h z w hz hw p v _ he
  · intro j a b hj; exact (hz j hj).elim
  · intro k s hk hs ih j a b hj ha hb
    obtain ⟨c,hc,hp⟩ := stage_prev m r h su z w hz hw hu k s b hk hs hb
    have hg := all_stages_good m r h su z w hz hw hu k hk c hc
    have hcb : Sub m c b := fun y hy => (hp y).mpr (fun x hx => hg.2.1 y x hx hy)
    rcases (hs j).mp hj with e | hj'
    · subst j
      have e := stages_unique m r h su z w hz hw hu k hk a c ha hc
      exact e.symm ▸ hcb
    · exact fun y hy => hcb y (ih j a c hj' ha hc y hy)

theorem stage_advance (k a : X) (ha : Stage m z w k a) :
    ∃ s b, m s w ∧ Stage m z w s b ∧ Power m a b := by
  obtain ⟨g,hg,hv⟩ := ha
  have hk := (hg k a hv).1
  obtain ⟨s,hs,hks⟩ := hw.1.2 k hk
  obtain ⟨b,hb⟩ := stage_total m r h su z w hz hw hu s hs
  obtain ⟨c,hc,hp⟩ := stage_prev m r h su z w hz hw hu k s b hk hks hb
  have e := stages_unique m r h su z w hz hw hu k hk a c ⟨g,hg,hv⟩ hc
  exact ⟨s,b,hs,hb,e.symm ▸ hp⟩

theorem tower_uniform (a : X) (ha : InTower m z w a) : Uniform m r a := by
  obtain ⟨k,b,⟨g,hg,hv⟩,hab⟩ := ha
  exact (all_stages_good m r h su z w hz hw hu k (hg k b hv).1 b ⟨g,hg,hv⟩).1.2 a hab

theorem tower_trans (a b : X) (ha : InTower m z w a) (hb : m b a) : InTower m z w b := by
  obtain ⟨k,c,⟨g,hg,hv⟩,hac⟩ := ha
  have good := all_stages_good m r h su z w hz hw hu k (hg k c hv).1 c ⟨g,hg,hv⟩
  exact ⟨k,c,⟨g,hg,hv⟩,good.2.1 a b hb hac⟩

theorem tower_subset (a b : X) (ha : InTower m z w a) (hb : Sub m b a) : InTower m z w b := by
  obtain ⟨k,c,⟨g,hg,hv⟩,hac⟩ := ha
  have good := all_stages_good m r h su z w hz hw hu k (hg k c hv).1 c ⟨g,hg,hv⟩
  obtain ⟨s,d,_,hd,hp⟩ := stage_advance m r h su z w hz hw hu k c ⟨g,hg,hv⟩
  exact ⟨s,d,hd,(hp b).mpr (fun y hy => good.2.1 a y (hb y hy) hac)⟩

/-- Pairing two elements of the union uses a common internal stage, whose
existence follows from comparison of the internal natural indices. -/
theorem common_stage (a b : X) (ha : InTower m z w a) (hb : InTower m z w b) :
    ∃ k c, Stage m z w k c ∧ m a c ∧ m b c := by
  obtain ⟨i,c,⟨g,hg,hv⟩,hac⟩ := ha
  obtain ⟨j,d,⟨f,hf,hv'⟩,hbd⟩ := hb
  have hi := (hg i c hv).1
  have hj := (hf j d hv').1
  rcases number_compare m r h z w hz hw i hi j hj with e | hij | hji
  · subst j
    have e := stages_unique m r h su z w hz hw hu i hi c d ⟨g,hg,hv⟩ ⟨f,hf,hv'⟩
    exact ⟨i,c,⟨g,hg,hv⟩,hac,e.symm ▸ hbd⟩
  · exact ⟨j,d,⟨f,hf,hv'⟩,stages_nested m r h su z w hz hw hu j hj i c d hij ⟨g,hg,hv⟩ ⟨f,hf,hv'⟩ a hac,hbd⟩
  · exact ⟨i,c,⟨g,hg,hv⟩,hac,stages_nested m r h su z w hz hw hu i hi j d c hji ⟨f,hf,hv'⟩ ⟨g,hg,hv⟩ b hbd⟩

end Towers
end DESTOriginal
