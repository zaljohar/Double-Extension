import DEST.WeakHull
import DEST.WeakSpecification

set_option autoImplicit false
set_option maxHeartbeats 0

namespace DESTWeak
open DEST

abbrev First := DESTVerification.first
abbrev Unary := DESTStrength.Unary

/-- The only query formulas besides the fixed fragment are a fixed finite
    list of formulas whose ambient truth is to be preserved. -/
def formulas (qs : List Unary) (extra : List DEST.Formula) : List DEST.Formula :=
  qs.map (fun q => DESTSemantic.erase q.2) ++ extra

private theorem requested_formula (qs : List Unary) (extra : List DEST.Formula)
    (q : Unary) (hq : q ∈ qs) : DESTSemantic.erase q.2 ∈ formulas qs extra :=
  List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨q,hq,rfl⟩))

/-- Start with the actual set of all finite von Neumann ordinals and omega. -/
noncomputable def seedCode : A := insert omegaSet omegaSet

private theorem seed_exact : (seedCode : Set A) = DEST.seed := by
  ext a
  change a ∈ insert omegaSet omegaSet ↔ a ∈ DEST.seed
  rw [ZFSet.mem_insert_iff]
  change a = omegaSet ∨ a ∈ omegaSet ↔ a ∈ Set.range vn ∨ a ∈ ({omegaSet} : Set A)
  simp only [omegaSet, ZFSet.mem_range, Set.mem_range, Set.mem_singleton_iff]
  tauto

section Fixed
variable (ps : List DEST.Formula)

noncomputable def uCode : A := code (queries ps) ∅ seedCode
noncomputable def mCode : A := code (queries ps) (uCode ps) (uCode ps)
noncomputable abbrev U : Set A := (uCode ps : Set A)
noncomputable abbrev M : Set A := (mCode ps : Set A)
abbrev Carrier := ↥(M ps)

def uniformDomain : Set (Carrier ps) := {a | a.val ∈ U ps}

theorem u_sub_m : U ps ⊆ M ps := seed_dom (queries ps) (uCode ps) (uCode ps)

theorem seed_sub_u : DEST.seed ⊆ U ps := by
  rw [← seed_exact]
  exact seed_dom (queries ps) ∅ seedCode

theorem m_countable : (M ps).Countable := by
  have hs : (seedCode : Set A).Countable := seed_exact.symm ▸ DEST.seed_countable
  exact code_countable (queries ps) (uCode ps) (uCode ps)
    (code_countable (queries ps) ∅ seedCode hs)

private theorem qrep {p : DEST.Formula} (hp : p ∈ ps) : Query.rep p ∈ queries ps :=
  local_mem hp (by simp [localQueries])
private theorem qdiff {p : DEST.Formula} (hp : p ∈ ps) : Query.diff p ∈ queries ps :=
  local_mem hp (by simp [localQueries])
private theorem qexists {p : DEST.Formula} (hp : p ∈ ps) : Query.counter (.imp p .bot) ∈ queries ps :=
  local_mem hp (by simp [localQueries])
private theorem qoutside {p : DEST.Formula} (hp : p ∈ ps) : Query.outside p ∈ queries ps :=
  local_mem hp (by simp [localQueries])

theorem reflect_M (p : DEST.Formula) (hp : p ∈ ps) (l : List A)
    (hl : Supported (M ps) l) : p.eval (M ps) l ↔ truth p l := by
  apply reflect (queries ps) (uCode ps) (uCode ps) p _ l hl
  intro q hq
  exact local_mem hp (List.mem_append.mpr (Or.inr hq))

/-- An extension is defined by one of the fixed formulas and a finite list
    of parameters. Ambient evaluation is valid by finite reflection. -/
def extn (p : DEST.Formula) (l : List (Carrier ps)) : Set (Carrier ps) :=
  {y | truth p (y.val :: l.map Subtype.val)}

private theorem trace_mem (a : Carrier ps) :
    extn ps (.mem 0 1) [a] = DESTStrength.Trace (First (M ps)) a := by
  ext y
  change (∃ z w : A, some y.val = some z ∧ some a.val = some w ∧ z ∈ w) ↔ y.val ∈ a.val
  simp

/-- Trace equality is reflected into the ambient set universe by the
    single disagreement-witness test for p. -/
theorem trace_rep (a : Carrier ps) (p : DEST.Formula) (l : List (Carrier ps))
    (hp : Query.diff p ∈ queries ps)
    (h : DESTStrength.Trace (First (M ps)) a = extn ps p l) :
    ∀ y : A, y ∈ a.val ↔ truth p (y::l.map Subtype.val) := by
  classical
  intro y
  by_contra hn
  obtain ⟨z,hz,hd⟩ := witness (queries ps) (uCode ps) (uCode ps) (.diff p) hp
    (a.val :: l.map Subtype.val) []
    (supported_cons a.property (supported_map (M ps) l)) (by simp [Supported]) ⟨y,hn⟩
  have hz' : (⟨z,hz⟩ : Carrier ps) ∈ DESTStrength.Trace (First (M ps)) a ↔
      (⟨z,hz⟩ : Carrier ps) ∈ extn ps p l := by rw [h]
  exact hd hz'

theorem trace_injective : Function.Injective (DESTStrength.Trace (First (M ps))) := by
  intro a b h
  apply Subtype.ext
  apply ZFSet.ext
  intro y
  have ht := trace_rep ps a (.mem 0 1) [b]
    (by simp [queries]) (h.trans (trace_mem ps b).symm) y
  change (y ∈ a.val ↔ ∃ z w : A, some y = some z ∧ some b.val = some w ∧ z ∈ w) at ht
  simpa using ht

private theorem represented_in_u (p : DEST.Formula) (hp : p ∈ ps)
    (l : List (Carrier ps)) (hl : Supported (U ps) (l.map Subtype.val))
    (h : ∃ a : A, ∀ y : A, y ∈ a ↔ truth p (y::l.map Subtype.val)) :
    ∃ a : Carrier ps, a ∈ uniformDomain ps ∧ DESTStrength.Trace (First (M ps)) a = extn ps p l := by
  obtain ⟨a,ha,hr⟩ := witness (queries ps) ∅ seedCode (.rep p) (qrep ps hp)
    (l.map Subtype.val) [] hl (by simp [Supported]) h
  refine ⟨⟨a,u_sub_m ps ha⟩,ha,?_⟩
  ext y
  exact hr y.val

private theorem outside_fresh (l : List (Carrier ps)) :
    ∃ a : Carrier ps, a ∉ uniformDomain ps ∧ a ∉ l := by
  have hn : ¬ ∃ a : A, ∀ y : A, y ∈ a ↔ truth (.eq 0 0) [y] := by
    rintro ⟨a,ha⟩
    exact ZFSet.mem_irrefl a ((ha a).mpr (by simp [truth, DEST.Formula.eval]))
  obtain ⟨a,ha,h⟩ := witness (queries ps) (uCode ps) (uCode ps) (.outside (.eq 0 0))
    (by simp [queries]) [] (l.map Subtype.val) (by simp [Supported])
    (supported_map (M ps) l) (unrepresented_fresh (uCode ps) (.eq 0 0) [] _ hn)
  change truth (.eq 0 0) [a] ∧ a ∉ U ps ∧ a ∉ l.map Subtype.val at h
  exact ⟨⟨a,ha⟩,h.2.1,fun hm => h.2.2 (List.mem_map.mpr ⟨_,hm,rfl⟩)⟩

private theorem singleton_not_fixed (b : Carrier ps) (hb : b ∉ uniformDomain ps) :
    ¬ ∃ a : Carrier ps, a ∈ uniformDomain ps ∧ DESTStrength.Trace (First (M ps)) a = {b} := by
  classical
  rintro ⟨a,ha,he⟩
  have hbmem : b ∈ DESTStrength.Trace (First (M ps)) a := by rw [he]; simp
  have hexis : truth (.mem 0 1) [b.val,a.val] := by
    change b.val ∈ a.val at hbmem
    simpa [truth, DEST.Formula.eval] using hbmem
  obtain ⟨z,hz,ht⟩ := witness (queries ps) ∅ seedCode (.counter (.imp (.mem 0 1) .bot))
    (by simp [queries]) [a.val] [] (supported_cons (show a.val ∈ U ps from ha) (by simp [Supported]))
    (by simp [Supported]) ⟨b.val,by simpa [test,truth,DEST.Formula.eval] using hexis⟩
  have hmem : z ∈ a.val := by simpa [test,truth,DEST.Formula.eval] using ht
  let z' : Carrier ps := ⟨z,u_sub_m ps hz⟩
  have hm : z' ∈ DESTStrength.Trace (First (M ps)) a := hmem
  rw [he] at hm
  have eq' : z' = b := Set.mem_singleton_iff.mp hm
  exact hb (eq' ▸ (show z' ∈ uniformDomain ps from hz))

private theorem extension_eq (q : Unary) (hp : q.2.firstOnly)
    (hq : DESTSemantic.erase q.2 ∈ ps) (v : Fin q.1 → Carrier ps) :
    DESTStrength.Extension (First (M ps)) q v = extn ps (DESTSemantic.erase q.2) (DESTSemantic.params v) := by
  ext y
  change q.2.eval (First (M ps)) (First (M ps)) (DESTReference.push y v) ↔
    truth (DESTSemantic.erase q.2) (y.val :: (DESTSemantic.params v).map Subtype.val)
  exact (DESTSemantic.unary_translation (M ps) (First (M ps)) q.2 hp v y).trans
    (reflect_M ps _ hq _ (supported_cons y.property (supported_map (M ps) _)))

private theorem params_uniform {q : Unary} {v : Fin q.1 → Carrier ps}
    (hv : ∀ i, v i ∈ uniformDomain ps) : Supported (U ps) ((DESTSemantic.params v).map Subtype.val) := by
  intro a ha
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
  exact DESTSemantic.params_all (fun b : Carrier ps => b ∈ uniformDomain ps) v hv b hb

/-- The extension family is a finite-formula indexed image, not P(M). -/
def extensionFamily : Set (Set (Carrier ps)) :=
  Set.range (fun a : {a : Carrier ps // a ∈ uniformDomain ps} => DESTStrength.Trace (First (M ps)) a.val) ∪
  Set.range (fun a : {a : Carrier ps // a ∉ uniformDomain ps} => ({a.val} : Set (Carrier ps))) ∪
  Set.range (fun t : {p : DEST.Formula // p ∈ ps} × List (Carrier ps) => extn ps t.1.val t.2)

private theorem family_countable : (extensionFamily ps).Countable := by
  letI : Countable (Carrier ps) := m_countable ps
  unfold extensionFamily
  exact ((Set.countable_range _).union (Set.countable_range _)).union (Set.countable_range _)

/-- Every hypothesis of the previously conditional finite matching theorem
    is now supplied by the two constructed hulls. -/
theorem hull_data (qs : List Unary) (extra : List DEST.Formula)
    (hfirst : ∀ q ∈ qs, q.2.firstOnly) :
    DESTStrength.HullData (First (M (formulas qs extra))) (uniformDomain (formulas qs extra)) qs
      (extensionFamily (formulas qs extra)) := by
  classical
  let ps := formulas qs extra
  change DESTStrength.HullData (First (M ps)) (uniformDomain ps) qs (extensionFamily ps)
  have ex_eq (q : Unary) (hq : q ∈ qs) (v : Fin q.1 → Carrier ps) :=
    extension_eq ps q (hfirst q hq) (requested_formula qs extra q hq) v
  have rep_protected (B : Set (Carrier ps)) (hp : DESTStrength.Protected (First (M ps)) (uniformDomain ps) qs B) :
      ∃ p ∈ ps, ∃ l : List (Carrier ps), Supported (U ps) (l.map Subtype.val) ∧ extn ps p l = B := by
    obtain ⟨q,hq,v,hv,he⟩ := hp
    exact ⟨DESTSemantic.erase q.2,requested_formula qs extra q hq,DESTSemantic.params v,
      params_uniform ps (q := q) hv,(ex_eq q hq v).symm.trans he⟩
  refine ⟨trace_injective ps,family_countable ps,?_,?_,?_,outside_fresh ps,?_,singleton_not_fixed ps,?_,?_⟩
  · intro a ha
    exact Or.inl (Or.inl ⟨⟨a,ha⟩,rfl⟩)
  · intro b hb
    exact Or.inl (Or.inr ⟨⟨b,hb⟩,rfl⟩)
  · intro q hq v
    exact Or.inr ⟨(⟨DESTSemantic.erase q.2,requested_formula qs extra q hq⟩,DESTSemantic.params v),(ex_eq q hq v).symm⟩
  · intro a B hp he
    obtain ⟨p,hp',l,hl,hs⟩ := rep_protected B hp
    obtain ⟨b,hb,hr⟩ := represented_in_u ps p hp' l hl
      ⟨a.val,trace_rep ps a p l (qdiff ps hp') (he.trans hs.symm)⟩
    have e : a = b := trace_injective ps (he.trans (hs.symm.trans hr.symm))
    exact e.symm ▸ hb
  · intro b hb hp
    obtain ⟨p,hp',l,hl,hs⟩ := rep_protected {b} hp
    have ht : truth p (b.val :: l.map Subtype.val) := by
      change b ∈ extn ps p l
      rw [hs]; simp
    obtain ⟨z,hz,h⟩ := witness (queries ps) ∅ seedCode (.counter (.imp p .bot)) (qexists ps hp')
      (l.map Subtype.val) [] hl (by simp [Supported]) ⟨b.val,by simpa [test,truth,DEST.Formula.eval] using ht⟩
    have ht' : truth p (z::l.map Subtype.val) := by simpa [test,truth,DEST.Formula.eval] using h
    let z' : Carrier ps := ⟨z,u_sub_m ps hz⟩
    have hm : z' ∈ extn ps p l := ht'
    rw [hs] at hm
    have e : z' = b := Set.mem_singleton_iff.mp hm
    exact hb (e ▸ (show z' ∈ uniformDomain ps from hz))
  · intro B _ hp hn lban
    obtain ⟨p,hp',l,hl,hs⟩ := rep_protected B hp
    have hno : ¬ ∃ a : A, ∀ y : A, y ∈ a ↔ truth p (y::l.map Subtype.val) := by
      intro he
      obtain ⟨a,ha,hr⟩ := represented_in_u ps p hp' l hl he
      exact hn ⟨a,ha,hr.trans hs⟩
    obtain ⟨a,ha,hh⟩ := witness (queries ps) (uCode ps) (uCode ps) (.outside p) (qoutside ps hp')
      (l.map Subtype.val) (lban.map Subtype.val) (supported_map (M ps) l) (supported_map (M ps) lban)
      (unrepresented_fresh (uCode ps) p _ _ hno)
    change truth p (a::l.map Subtype.val) ∧ a ∉ U ps ∧ a ∉ lban.map Subtype.val at hh
    refine ⟨⟨a,ha⟩,hh.2.1,fun hmem => hh.2.2 (List.mem_map.mpr ⟨_,hmem,rfl⟩),?_⟩
    rw [← hs]
    exact hh.1

private theorem vn_in_u (n : ℕ) : vn n ∈ U ps := seed_sub_u ps (Or.inl ⟨n,rfl⟩)
private theorem omega_in_u : omegaSet ∈ U ps := seed_sub_u ps (Or.inr (by simp))
noncomputable def numeral (n : ℕ) : Carrier ps := ⟨vn n,u_sub_m ps (vn_in_u ps n)⟩
noncomputable def omegaObj : Carrier ps := ⟨omegaSet,u_sub_m ps (omega_in_u ps)⟩

theorem nat_frame : DESTStrength.NatFrame (First (M ps)) (uniformDomain ps) (numeral ps) (omegaObj ps) := by
  refine ⟨InvImage.wf (fun x : Carrier ps => x.val) ZFSet.mem_wf,?_,?_,?_,?_,vn_in_u ps,omega_in_u ps⟩
  · intro n m h
    have he : vn n = vn m := congrArg Subtype.val h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hn | hm
    · have hh := DEST.vn_mem_of_lt hn
      rw [he] at hh
      exact ZFSet.mem_irrefl _ hh
    · have hh := DEST.vn_mem_of_lt hm
      rw [← he] at hh
      exact ZFSet.mem_irrefl _ hh
  · intro a
    exact ZFSet.notMem_empty a.val
  · intro a n
    change a.val ∈ insert (vn n) (vn n) ↔ a = numeral ps n ∨ a.val ∈ vn n
    rw [ZFSet.mem_insert_iff]
    constructor
    · rintro (h|h)
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr h
    · rintro (h|h)
      · exact Or.inl (congrArg Subtype.val h)
      · exact Or.inr h
  · intro a
    change a.val ∈ ZFSet.range vn ↔ _
    rw [ZFSet.mem_range]
    constructor
    · rintro ⟨n,h⟩; exact ⟨n,Subtype.ext h⟩
    · rintro ⟨n,h⟩; exact ⟨n,congrArg Subtype.val h⟩

end Fixed

/-- Independent endpoint: finite fragments have a model reflecting any
    supplied finite family of first-membership formulas. This is an ordinary
    Lean theorem; the proof in the weak metatheory is the accompanying
    fixed-formula resource derivation, not an inference from this theorem. -/
theorem exists_reflecting_fragment (qs : List DESTStrength.Unary) (extra : List DEST.Formula)
    (hfirst : ∀ q ∈ qs, q.2.firstOnly) :
    ∃ (D : Set DEST.A) (r : D → D → Prop), D.Countable ∧ Nonempty D ∧
      DESTStrength.SatisfiesFragment (DESTVerification.first D) r qs ∧
      WellFounded (DESTVerification.first D) ∧
      (∀ n : ℕ, ambientNumeral n ∈ D) ∧ ambientOmega ∈ D ∧
      ∀ p ∈ extra, ∀ l : List DEST.A, (∀ x ∈ l, x ∈ D) → (p.eval D l ↔ DEST.truth p l) := by
  let ps := formulas qs extra
  letI : Countable (Carrier ps) := m_countable ps
  obtain ⟨r,hs,_,hwf⟩ := DESTStrength.finite_model_of_hull
    (First (M ps)) (uniformDomain ps) qs (extensionFamily ps) (numeral ps) (omegaObj ps)
    (hull_data qs extra hfirst) (nat_frame ps)
  have hvn (n : ℕ) : ambientNumeral n = DEST.vn n := by
    induction n with
    | zero => rfl
    | succ n ih => simp only [ambientNumeral,DEST.vn,ih]
  have hw : ambientOmega = DEST.omegaSet := by
    unfold ambientOmega DEST.omegaSet
    rw [show ambientNumeral = DEST.vn from funext hvn]
  refine ⟨M ps,r,m_countable ps,⟨omegaObj ps⟩,hs,hwf,fun n => ?_,?_,?_⟩
  · rw [hvn]
    exact u_sub_m ps (vn_in_u ps n)
  · rw [hw]
    exact u_sub_m ps (omega_in_u ps)
  · intro p hp l hl
    exact reflect_M ps p (List.mem_append.mpr (Or.inr hp)) l hl

private theorem eraseFirst_eq {n : ℕ} (p : DESTReference.Formula n) :
    eraseFirst p = DESTSemantic.erase p := by
  induction p with
  | bot => rfl
  | eq i j => rfl
  | mem1 i j => rfl
  | mem2 i j => rfl
  | imp p q ihp ihq => simp only [eraseFirst,DESTSemantic.erase,ihp,ihq]
  | all p ih => simp only [eraseFirst,DESTSemantic.erase,ih]

/-- The syntactic fragment reduction and the actual reflecting hulls give
    ambient truth for a first-language theorem. No HullData assumption remains. -/
theorem first_sentence_ambient {s : DESTReference.Sentence} (hfirst : s.firstOnly)
    (hd : DESTReference.Derives DESTReference.Axiom s) : DEST.truth (eraseFirst s) [] := by
  rw [eraseFirst_eq]
  classical
  obtain ⟨qs,hqs⟩ := DESTStrength.finite_proof_support hd
  let ts := qs.filter (fun q => decide q.2.firstOnly)
  have ht : ∀ q ∈ ts, q.2.firstOnly := by
    intro q hq
    exact of_decide_eq_true ((List.mem_filter.mp hq).2)
  have hin (q : Unary) (hq : q ∈ qs) (hp : q.2.firstOnly) : q ∈ ts :=
    List.mem_filter.mpr ⟨hq,decide_eq_true hp⟩
  obtain ⟨D,r,_,_,hmodel,_,_,_,href⟩ := exists_reflecting_fragment ts [DESTSemantic.erase s] ht
  have hs : DESTStrength.SatisfiesFragment (DESTVerification.first D) r qs := by
    intro p hp
    apply hmodel p
    cases hp with
    | ext1 => exact DESTStrength.Fragment.ext1
    | ext2 => exact DESTStrength.Fragment.ext2
    | comp q hq hp => exact DESTStrength.Fragment.comp q (hin q hq hp) hp
    | unif q hq hp => exact DESTStrength.Fragment.unif q (hin q hq hp) hp
    | inf => exact DESTStrength.Fragment.inf
    | natInd p => exact DESTStrength.Fragment.natInd p
    | setInd p => exact DESTStrength.Fragment.setInd p
  have he := DESTReference.soundness (DESTVerification.first D) r (DESTStrength.Fragment qs) hs hqs Fin.elim0
  have htrans := DESTSemantic.first_language_translation D r s hfirst Fin.elim0 [] (fun i => Fin.elim0 i)
  exact (href _ (by simp) [] (by simp)).mp (htrans.mp he)

end DESTWeak
