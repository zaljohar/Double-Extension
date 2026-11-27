import DEST.SetAssignment

set_option autoImplicit false
set_option maxHeartbeats 0

universe u

namespace DESTSet

open DESTReference DESTStrength

variable {X : Type u} {M : Model X} {qs : List DESTStrength.Unary} {s : Sentence}
variable {C : Regions M qs s} (F : Assignment C)
local infix:50 " ∈ₛ " => M.mem

abbrev firstRel (a b : Carrier M C.d) : Prop := a.val ∈ₛ b.val
abbrev secondRel (a b : Carrier M C.d) : Prop := second F a.val b.val

theorem first_ext {a b : Carrier M C.d}
    (h : ∀ y : Carrier M C.d, firstRel y a ↔ firstRel y b) : a = b := by
  apply Subtype.ext
  apply M.extensionality
  intro y
  constructor
  · intro hy
    exact (h ⟨y,C.trans_d _ _ hy a.property⟩).mp hy
  · intro hy
    exact (h ⟨y,C.trans_d _ _ hy b.property⟩).mpr hy

theorem graph_ext {a b B D : X} (ha : F.graph a B) (hb : F.graph b D)
    (h : ∀ y : Carrier M C.d, second F y.val a ↔ second F y.val b) : B = D := by
  apply M.extensionality
  intro x
  constructor
  · intro hx
    exact (second_of_graph F hb x).mp
      ((h ⟨x,F.output_subset _ _ ha x hx⟩).mp ((second_of_graph F ha x).mpr hx))
  · intro hx
    exact (second_of_graph F ha x).mp
      ((h ⟨x,F.output_subset _ _ hb x hx⟩).mpr ((second_of_graph F hb x).mpr hx))

theorem uniform_iff (a : Carrier M C.d) :
    Uniform firstRel (secondRel F) a ↔ a.val ∈ₛ C.u := by
  constructor
  · intro h
    obtain ⟨b,hb⟩ := F.total _ a.property
    have e : b = a.val := by
      apply M.extensionality
      intro x
      constructor
      · intro hx
        exact (h ⟨x,F.output_subset _ _ hb x hx⟩).mpr ((second_of_graph F hb x).mpr hx)
      · intro hx
        exact (second_of_graph F hb x).mp
          ((h ⟨x,C.trans_d _ _ hx a.property⟩).mp hx)
    exact (F.fixed a.val).mp (e ▸ hb)
  · intro h y
    exact (second_of_graph F ((F.fixed a.val).mpr h) y.val).symm

theorem extension_eval {n : ℕ} {p : DESTReference.Formula (n+1)} (hp : p.firstOnly)
    (v : Fin n → Carrier M C.d) (y : Carrier M C.d) :
    Relativized (fun a => a ∈ₛ C.d) M.mem M.mem p (push y.val (fun i => (v i).val)) ↔
      p.eval firstRel (secondRel F) (push y v) := by
  have h : (fun i => (push y v i).val) = push y.val (fun i => (v i).val) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  rw [← h]
  exact (relativized_subtype _ _ _ p (push y v)).trans
    (first_only_eval firstRel firstRel (secondRel F) p hp _)

def LocalTruth {n : ℕ} (p : DESTReference.Formula (n+1)) (v : Fin n → Carrier M C.d)
    (a : X) : Prop :=
  Relativized (fun x => x ∈ₛ C.d) M.mem (second F) p (push a (fun i => (v i).val))

theorem def_local_truth {n : ℕ} (p : DESTReference.Formula (n+1)) (v : Fin n → Carrier M C.d) :
    UnaryDef M.toOperations (LocalTruth F p v) := by
  unfold UnaryDef LocalTruth
  let w := fun i (env : Unit → X) => push (env ()) (fun j => (v j).val) i
  apply relativized_def M (D := fun a => a ∈ₛ C.d)
    (Def.mem (.var ()) (.param C.d)) (def_second F) p w
  intro i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp only [w,push_zero,push_succ]
  · exact TermDef.var ()
  · exact TermDef.param (v j).val

theorem local_truth {n : ℕ} (p : DESTReference.Formula (n+1)) (v : Fin n → Carrier M C.d)
    (a : Carrier M C.d) : LocalTruth F p v a.val ↔ p.eval firstRel (secondRel F) (push a v) := by
  have he : (fun i => (push a v i).val) = push a.val (fun i => (v i).val) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  unfold LocalTruth
  rw [← he]
  exact relativized_subtype _ _ _ p (push a v)

abbrev zeroObj (C : Regions M qs s) : Carrier M C.d := ⟨M.zero,C.zero_in⟩
abbrev omegaObj (C : Regions M qs s) : Carrier M C.d := ⟨M.omega,C.u_sub C.omega_in⟩

def succObj (C : Regions M qs s) (a : Carrier M C.d) : Carrier M C.d :=
  ⟨succ M a.val,C.insert_d _ _ a.property a.property⟩

theorem succ_obj {a y : Carrier M C.d} :
    firstRel y (succObj C a) ↔ y = a ∨ firstRel y a := by
  change M.mem y.val (succ M a.val) ↔ _
  rw [mem_succ]
  simp only [Subtype.ext_iff,firstRel]

theorem least_omega : LeastInductive (firstRel (C := C)) (zeroObj C) (omegaObj C) := by
  refine ⟨⟨M.zero_mem,?_⟩,?_⟩
  · intro a ha
    exact ⟨succObj C a,M.succ_mem _ ha,fun y => succ_obj⟩
  · intro a ha x hx
    have hstep : ∀ n, n ∈ₛ a.val → succ M n ∈ₛ a.val := by
      intro n hn
      let n' : Carrier M C.d := ⟨n,C.trans_d _ _ hn a.property⟩
      obtain ⟨b,hb,he⟩ := ha.2 n' hn
      have h : b = succObj C n' := first_ext (fun y => (he y).trans succ_obj.symm)
      rw [h] at hb
      exact hb
    exact M.omega_least _ ha.1 hstep x.val hx

theorem satisfies_fragment :
    DESTStrength.SatisfiesFragment (firstRel (C := C)) (secondRel F) qs := by
  classical
  intro phi hphi
  cases hphi with
  | ext1 =>
    exact (DESTSemantic.first_extensionality_correct firstRel (secondRel F)).mpr
      (fun _ _ h => first_ext h)
  | ext2 =>
    apply (DESTSemantic.second_extensionality_correct firstRel (secondRel F)).mpr
    intro a b h
    obtain ⟨A,ha⟩ := F.total _ a.property
    obtain ⟨B,hb⟩ := F.total _ b.property
    have eq := graph_ext F ha hb h
    exact Subtype.ext (F.injective _ _ _ ha (eq.symm ▸ hb))
  | comp q hq hp =>
    apply (DESTSemantic.comprehension_correct firstRel (secondRel F) q.2).mpr
    intro v
    obtain ⟨B,hB⟩ := extension_exists M C.d q.2 (fun i => (v i).val)
    have hg : ∃ a, F.graph a B := by
      by_cases hb : B ∈ₛ C.u
      · exact ⟨B,(F.fixed B).mpr hb⟩
      · exact F.onto_right _ ⟨hb, Or.inr ⟨q,hq,fun i => (v i).val,fun i => (v i).property,hB⟩⟩
    obtain ⟨a,ha⟩ := hg
    refine ⟨⟨a,F.input _ _ ha⟩,fun y => (second_of_graph F ha y.val).trans ?_⟩
    rw [hB]
    exact ⟨fun h => (extension_eval F hp v y).mp h.2,
      fun h => ⟨y.property,(extension_eval F hp v y).mpr h⟩⟩
  | unif q hq hp =>
    apply (DESTSemantic.uniformity_correct firstRel (secondRel F) q.2).mpr
    intro v huv a ha hself
    obtain ⟨b,hb⟩ := F.total _ a.property
    apply (uniform_iff F a).mpr
    by_contra hu
    have hExt : Extension M C.d q.2 (fun i => (v i).val) b := by
      intro x
      constructor
      · intro hx
        have hd := F.output_subset _ _ hb x hx
        let x' : Carrier M C.d := ⟨x,hd⟩
        exact ⟨hd,(extension_eval F hp v x').mpr ((ha x').mp ((second_of_graph F hb x).mpr hx))⟩
      · rintro ⟨hd,hr⟩
        let x' : Carrier M C.d := ⟨x,hd⟩
        exact (second_of_graph F hb x).mp ((ha x').mpr ((extension_eval F hp v x').mp hr))
    have hP : Protected C b :=
      ⟨q,hq,fun i => (v i).val,fun i => (uniform_iff F (v i)).mp (huv i),hExt⟩
    exact hself ((ha a).mp ((second_of_graph F hb a.val).mpr (F.protected_match _ _ hb hP hu)))
  | inf =>
    simp only [infinity, eval_ex, eval_conj, DESTSemantic.zero_correct,
      DESTSemantic.omega_correct, push_zero, push_succ]
    exact ⟨omegaObj C,zeroObj C,(fun a => M.empty a.val),least_omega.1,least_omega.2⟩
  | natInd p =>
    simp only [naturalInduction, eval_close, DESTReference.Formula.eval, natBody, eval_conj,
      DESTSemantic.zero_correct, DESTSemantic.omega_correct, DESTSemantic.succ_correct,
      eval_atVar, push_zero, push_succ]
    intro v w z hzw hb hstep a ha
    have ez : z = zeroObj C := first_ext
      (fun y => ⟨fun h => (hzw.1 y h).elim,fun h => (M.empty _ h).elim⟩)
    subst z
    have hw : LeastInductive firstRel (zeroObj C) w := hzw.2
    have ew : w = omegaObj C := first_ext
      (fun y => ⟨hw.2 _ least_omega.1 y, least_omega.2 _ hw.1 y⟩)
    subst w
    have hbase := (local_truth F p v (zeroObj C)).mpr hb
    have hall := nat_induction M _ (def_local_truth F p v) hbase (by
      intro x hx hp
      let x' : Carrier M C.d := ⟨x,C.trans_d _ _ hx (omegaObj C).property⟩
      apply (local_truth F p v (succObj C x')).mpr
      exact hstep x' hx (succObj C x') (fun _ => succ_obj) ((local_truth F p v x').mp hp))
    exact (local_truth F p v a).mp (hall a.val ha)
  | setInd p =>
    apply (DESTSemantic.setInduction_correct firstRel (secondRel F) p).mpr
    intro v hs a
    apply (local_truth F p v a).mp
    by_contra ha
    obtain ⟨b,hb⟩ := M.separation C.d (fun y => ¬ LocalTruth F p v y) (def_local_truth F p v).not
    obtain ⟨y,hy,hm⟩ := M.foundation b ⟨a.val,(hb _).mpr ⟨a.property,ha⟩⟩
    obtain ⟨hd,hno⟩ := (hb y).mp hy
    let y' : Carrier M C.d := ⟨y,hd⟩
    apply hno
    apply (local_truth F p v y').mpr
    apply hs y'
    intro x hx
    apply (local_truth F p v x).mp
    by_contra hbad
    exact hm x.val ((hb _).mpr ⟨x.property,hbad⟩) hx

theorem code_relation (hr : CofinalReflection M) (d : X) (hz : M.zero ∈ₛ d)
    {r : X → X → Prop} (dr : BinaryDef M.toOperations r) :
    ∃ g, ∀ x y, entry M g x y ↔ x ∈ₛ d ∧ y ∈ₛ d ∧ r x y := by
  obtain ⟨b,hb,ht,hi,_⟩ := hr d []
  have hzero : M.zero ∈ₛ b := ht _ _ hz hb
  have hpair (x y : X) (hx : x ∈ₛ d) (hy : y ∈ₛ d) :
      pair M.toOperations M.zero x y ∈ₛ b := by
    have hx' : x ∈ₛ b := ht _ _ hx hb
    have hy' : y ∈ₛ b := ht _ _ hy hb
    exact hi _ _ (hi _ _ hx' hzero) (hi _ _ (hi _ _ hx' (hi _ _ hy' hzero)) hzero)
  let P := fun p => ∃ x y, x ∈ₛ d ∧ y ∈ₛ d ∧ p = pair M.toOperations M.zero x y ∧ r x y
  have dP : UnaryDef M.toOperations P := by
    unfold UnaryDef P
    apply Def.ex
    apply Def.ex
    exact (Def.mem (.var (some none)) (.param d)).and
      ((Def.mem (.var none) (.param d)).and
      ((Def.eq (.var (some (some ()))) (defPair M (.var (some none)) (.var none))).and
      (Def.app₂ dr (.var (some none)) (.var none))))
  obtain ⟨g,hg⟩ := M.separation b P dP
  refine ⟨g,fun x y => ?_⟩
  change pair M.toOperations M.zero x y ∈ₛ g ↔ _
  rw [hg]
  constructor
  · rintro ⟨_,a,c,ha,hc,he,hr⟩
    obtain ⟨rfl,rfl⟩ := pair_inj M he
    exact ⟨ha,hc,hr⟩
  · rintro ⟨hx,hy,hxy⟩
    exact ⟨hpair x y hx hy,x,y,hx,hy,rfl,hxy⟩

/-- Both the domain and the graph of second membership are sets of the weak
model. The first relation is inherited from its membership. -/
theorem finite_fragment_inside (hr : CofinalReflection M) (hc : InternallyCountable M)
    (qs : List DESTStrength.Unary) (s : Sentence) (hs : s.firstOnly) :
    ∃ d g : X, Nonempty (Carrier M d) ∧
      DESTStrength.SatisfiesFragment (first M d)
        (fun a b : Carrier M d => entry M g a.val b.val) qs ∧
      (s.eval (first M d) (fun a b : Carrier M d => entry M g a.val b.val) Fin.elim0 ↔
        s.eval M.mem M.mem Fin.elim0) := by
  obtain ⟨C⟩ := regions M hr qs s
  obtain ⟨F⟩ := assignment C hr hc
  obtain ⟨g,hg⟩ := code_relation hr C.d C.zero_in (def_second F)
  have he : (fun a b : Carrier M C.d => entry M g a.val b.val) = secondRel F := by
    funext a b
    exact propext ⟨fun h => ((hg _ _).mp h).2.2,fun h => (hg _ _).mpr ⟨a.property,b.property,h⟩⟩
  refine ⟨C.d,g,⟨zeroObj C⟩,?_⟩
  rw [he]
  refine ⟨satisfies_fragment F,?_⟩
  exact (first_only_eval (first M C.d) (secondRel F) (first M C.d) s hs _).trans
    ((reflect M C.closed_d s (fun q hq => List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inl hq)))
      Fin.elim0).trans (by
        have h : (fun i : Fin 0 => ((Fin.elim0 i : Carrier M C.d)).val) = Fin.elim0 := by
          funext i
          exact Fin.elim0 i
        rw [h]))

/-- Every first-membership conclusion of the reference calculus holds in
the weak set model itself. The construction needs only the formulas used
in that derivation. -/
theorem first_sentence_of_internal_model (hr : CofinalReflection M) (hc : InternallyCountable M)
    {s : Sentence} (hs : s.firstOnly) (hd : Derives Axiom s) : s.eval M.mem M.mem Fin.elim0 := by
  obtain ⟨qs,hqs⟩ := finite_proof_support hd
  obtain ⟨d,g,_,hfragment,hreflect⟩ := finite_fragment_inside hr hc qs s hs
  exact hreflect.mp (soundness (first M d) (fun a b => entry M g a.val b.val)
    (Fragment qs) hfragment hqs Fin.elim0)

end DESTSet
