import DEST.StrengthSpecification
import DEST.SemanticAudit
import DEST.Model

set_option autoImplicit false
set_option maxHeartbeats 0

universe u

namespace DESTStrength
open DESTReference

/-- Evaluation of a first-language formula is independent of the second relation. -/
theorem first_only_eval {X : Type u} (m r r' : X → X → Prop)
    {n : ℕ} (p : Formula n) (h : p.firstOnly) (v : Fin n → X) :
    p.eval m r v ↔ p.eval m r' v := by
  induction p with
  | bot => rfl
  | eq i j => rfl
  | mem1 i j => rfl
  | mem2 i j => exact False.elim h
  | imp p q ihp ihq =>
    change p.firstOnly ∧ q.firstOnly at h
    simp only [Formula.eval, ihp h.1, ihq h.2]
  | all p ih =>
    change p.firstOnly at h
    simp only [Formula.eval, ih h]

section Matching
variable {X : Type u} [Countable X] (m : X → X → Prop) (U : Set X)
  (qs : List Unary) (D : Set (Set X))

def Fixed (B : Set X) : Prop := ∃ a, a ∈ U ∧ Trace m a = B
abbrev Outside := {a : X // a ∉ U}
abbrev Free := {B : Set X // B ∈ D ∧ ¬ Fixed m U B}

def Allowed (a : Outside U) (B : Free m U D) : Prop :=
  Trace m a.val ≠ B.val ∧ (Protected m U qs B.val → a.val ∈ B.val)

/-- The finite-fragment back-and-forth step, independent of the ambient
    cumulative hierarchy and of any truth predicate for a proper class. -/
theorem finite_assignment (h : HullData m U qs D) :
    ∃ F : X → Set X, Function.Injective F ∧
      (∀ B ∈ D, ∃ a, F a = B) ∧
      (∀ a, F a = Trace m a ↔ a ∈ U) ∧
      (∀ a, Protected m U qs (F a) → a ∉ U → a ∈ F a) := by
  classical
  have fresh (l : List (Outside U)) : ∃ b : Outside U, b ∉ l := by
    obtain ⟨b,hbu,hbl⟩ := h.outside_fresh (l.map Subtype.val)
    exact ⟨⟨b,hbu⟩,fun hb => hbl (List.mem_map.mpr ⟨_,hb,rfl⟩)⟩
  have single_fixed (b : Outside U) : ¬ Fixed m U {b.val} := by
    intro hb
    exact h.singleton_not_fixed b.val b.property hb
  let single (b : Outside U) : Free m U D :=
    ⟨{b.val},h.singleton_mem b.val b.property,single_fixed b⟩
  letI : Countable ↥D := h.countable
  letI : Countable (Free m U D) :=
    Function.Injective.countable (f := fun b : Free m U D => (⟨b.val,b.property.1⟩ : ↥D))
      (by intro a b he; apply Subtype.ext; exact congrArg (fun t : ↥D => t.val) he)
  obtain ⟨b,_⟩ := fresh []
  letI : Nonempty (Outside U) := ⟨b⟩
  letI : Nonempty (Free m U D) := ⟨single b⟩
  have left (a : Outside U) (l : List (Free m U D)) :
      ∃ B, B ∉ l ∧ Allowed m U qs D a B := by
    let f : Outside U → Set X := fun b => {b.val}
    have hf : Function.Injective f := by
      intro b c he
      apply Subtype.ext
      have hm : b.val ∈ f c := by rw [← he]; simp [f]
      exact Set.mem_singleton_iff.mp hm
    obtain ⟨k,hk⟩ := DEST.pullback_list hf (Trace m a.val :: l.map Subtype.val)
    obtain ⟨c,hc⟩ := fresh k
    refine ⟨single c,?_,?_,?_⟩
    · intro hm
      apply hc
      apply hk
      exact List.mem_cons.mpr (Or.inr (List.mem_map.mpr ⟨single c,hm,rfl⟩))
    · intro he
      apply hc
      apply hk
      exact List.mem_cons.mpr (Or.inl he.symm)
    · intro hp
      exact (h.singleton_unprotected c.val c.property hp).elim
  have right (B : Free m U D) (l : List (Outside U)) :
      ∃ a, a ∉ l ∧ Allowed m U qs D a B := by
    by_cases hp : Protected m U qs B.val
    · obtain ⟨a,ha,hl,hm⟩ := h.protected_fresh B.val B.property.1 hp B.property.2 (l.map Subtype.val)
      refine ⟨⟨a,ha⟩,?_,?_,fun _ => hm⟩
      · intro he
        exact hl (List.mem_map.mpr ⟨_,he,rfl⟩)
      · intro he
        exact ha (h.protected_trace a B.val hp he)
    · let f : Outside U → Set X := fun a => Trace m a.val
      have hf : Function.Injective f := fun _ _ he => Subtype.ext (h.ext he)
      obtain ⟨k,hk⟩ := DEST.pullback_list hf [B.val]
      obtain ⟨a,ha⟩ := fresh (l ++ k)
      refine ⟨a,fun he => ha (List.mem_append.mpr (Or.inl he)),?_,fun he => (hp he).elim⟩
      intro he
      exact ha (List.mem_append.mpr (Or.inr (hk a (by simpa using he))))
  obtain ⟨e,he⟩ := DEST.countable_matching (Allowed m U qs D) left right
  let F (a : X) : Set X := if ha : a ∈ U then Trace m a else (e ⟨a,ha⟩).val
  have pos (a : X) (ha : a ∈ U) : F a = Trace m a := by simp [F,ha]
  have neg' (a : X) (ha : a ∉ U) : F a = (e ⟨a,ha⟩).val := by simp [F,ha]
  refine ⟨F,?_,?_,?_,?_⟩
  · intro a c hac
    by_cases ha : a ∈ U <;> by_cases hc : c ∈ U
    · exact h.ext ((pos a ha).symm.trans (hac.trans (pos c hc)))
    · exact ((e ⟨c,hc⟩).property.2 ⟨a,ha,((pos a ha).symm.trans hac).trans (neg' c hc)⟩).elim
    · exact ((e ⟨a,ha⟩).property.2 ⟨c,hc,((pos c hc).symm.trans hac.symm).trans (neg' a ha)⟩).elim
    · have heq : e ⟨a,ha⟩ = e ⟨c,hc⟩ :=
        Subtype.ext ((neg' a ha).symm.trans (hac.trans (neg' c hc)))
      exact congrArg Subtype.val (e.injective heq)
  · intro B hB
    by_cases hf : Fixed m U B
    · obtain ⟨a,ha,heq⟩ := hf
      exact ⟨a,(pos a ha).trans heq⟩
    · obtain ⟨a,ha⟩ := e.surjective ⟨B,hB,hf⟩
      exact ⟨a.val,(neg' a.val a.property).trans (congrArg Subtype.val ha)⟩
  · intro a
    constructor
    · intro hf
      by_contra hn
      exact (he ⟨a,hn⟩).1 (hf.symm.trans (neg' a hn))
    · exact pos a
  · intro a hp hn
    have hh := neg' a hn
    rw [hh] at hp ⊢
    exact (he ⟨a,hn⟩).2 hp

end Matching

/-- The exact finite list of comprehension/uniformity formulas is retained;
    the model also satisfies all instances of both induction schemes. -/
theorem finite_model_of_hull {X : Type u} [Countable X] (m : X → X → Prop)
    (U : Set X) (qs : List Unary) (D : Set (Set X)) (num : ℕ → X) (w : X)
    (h : HullData m U qs D) (hn : NatFrame m U num w) :
    ∃ r : X → X → Prop, SatisfiesFragment m r qs ∧
      (∀ a, Uniform m r a ↔ a ∈ U) ∧ WellFounded m := by
  classical
  obtain ⟨F,hF,honto,hfix,hself⟩ := finite_assignment m U qs D h
  let r (y a : X) : Prop := y ∈ F a
  have hu (a : X) : Uniform m r a ↔ a ∈ U := by
    rw [← hfix a]
    constructor
    · intro he
      ext y
      exact (he y).symm
    · intro he y
      change y ∈ Trace m a ↔ y ∈ F a
      rw [he]
  have ext1 : ∀ a b : X, (∀ y, m y a ↔ m y b) → a = b := by
    intro a b he
    apply h.ext
    ext y
    exact he y
  have ext2 : ∀ a b : X, (∀ y, r y a ↔ r y b) → a = b := by
    intro a b he
    apply hF
    ext y
    exact he y
  have natInd (P : X → Prop) (h0 : P (num 0))
      (hs : ∀ n : ℕ, P (num n) → P (num (n+1))) :
      ∀ a, m a w → P a := by
    have hall : ∀ n : ℕ, P (num n) := by
      intro n
      induction n with
      | zero => exact h0
      | succ n ih => exact hs n ih
    intro a ha
    obtain ⟨n,rfl⟩ := (hn.omega a).mp ha
    exact hall n
  have hind : Inductive m (num 0) w := by
    refine ⟨(hn.omega _).mpr ⟨0,rfl⟩,?_⟩
    intro a ha
    obtain ⟨n,rfl⟩ := (hn.omega a).mp ha
    exact ⟨num (n+1),(hn.omega _).mpr ⟨n+1,rfl⟩,fun y => hn.succ y n⟩
  have hleast : ∀ a, Inductive m (num 0) a → ∀ y, m y w → m y a := by
    intro a ha
    apply natInd (fun y => m y a) ha.1
    intro n hmem
    obtain ⟨s,hs,he⟩ := ha.2 (num n) hmem
    have eqs : s = num (n+1) := ext1 _ _ (fun y => (he y).trans (hn.succ y n).symm)
    exact eqs ▸ hs
  refine ⟨r,?_,hu,hn.wf⟩
  intro s ax
  cases ax with
  | ext1 => exact (DESTSemantic.first_extensionality_correct m r).mpr ext1
  | ext2 => exact (DESTSemantic.second_extensionality_correct m r).mpr ext2
  | comp q hq hp =>
    apply (DESTSemantic.comprehension_correct m r q.2).mpr
    intro v
    obtain ⟨a,ha⟩ := honto (Extension m q v) (h.requested_mem q hq v)
    refine ⟨a,fun y => ?_⟩
    change y ∈ F a ↔ q.2.eval m r (push y v)
    rw [ha]
    exact (first_only_eval m r m q.2 hp (push y v)).symm
  | unif q hq hp =>
    apply (DESTSemantic.uniformity_correct m r q.2).mpr
    intro v hv a ha hna
    have he : Extension m q v = F a := by
      ext y
      exact (first_only_eval m r m q.2 hp (push y v)).symm.trans (ha y).symm
    have hprot : Protected m U qs (F a) :=
      ⟨q,hq,v,fun i => (hu (v i)).mp (hv i),he⟩
    apply (hu a).mpr
    by_contra hnot
    exact hna ((ha a).mp (hself a hprot hnot))
  | inf =>
    simp only [infinity, eval_ex, eval_conj, DESTSemantic.zero_correct,
      DESTSemantic.omega_correct, push_zero, push_succ]
    exact ⟨w,num 0,hn.zero,hind,hleast⟩
  | natInd p =>
    simp only [naturalInduction, eval_close, Formula.eval, natBody, eval_conj,
      DESTSemantic.zero_correct, DESTSemantic.omega_correct, DESTSemantic.succ_correct,
      eval_atVar, push_zero, push_succ]
    intro v w' z hzw hb hstep a ha
    obtain ⟨hz',hw'⟩ := hzw
    have ez : z = num 0 := ext1 _ _ (fun y => ⟨fun hy => (hz' y hy).elim,fun hy => (hn.zero y hy).elim⟩)
    subst z
    have ew : w' = w := ext1 _ _ (fun y => ⟨hw'.2 w hind y,hleast w' hw'.1 y⟩)
    subst w'
    apply natInd (fun y => p.eval m r (push y v)) hb _ a ha
    intro k hk
    exact hstep (num k) ((hn.omega _).mpr ⟨k,rfl⟩) (num (k+1)) (fun y => hn.succ y k) hk
  | setInd p =>
    apply (DESTSemantic.setInduction_correct m r p).mpr
    intro v hstep a
    exact hn.wf.induction a hstep

/-- The independent base specification is a subtheory of the full reference. -/
theorem base_of_full {X : Type u} (m r : X → X → Prop)
    (h : Satisfies m r) : BaseSatisfies m r := by
  intro s hs
  apply h s
  cases hs with
  | ext1 => exact Axiom.ext1
  | ext2 => exact Axiom.ext2
  | comp p hp => exact Axiom.comp p hp
  | unif p hp => exact Axiom.unif p hp
  | inf => exact Axiom.inf
  | natInd p => exact Axiom.natInd p

/-- All base-theory models, not just the constructed model, satisfy the
    uniform-comprehension principle. This is the lower-bound mechanism. -/
theorem uniform_comprehension_of_model {X : Type u} (m r : X → X → Prop)
    (h : BaseSatisfies m r) : UniformComprehension m r := by
  classical
  intro n p hp v hv hvalues
  obtain ⟨a,ha⟩ := (DESTSemantic.comprehension_correct m r p).mp
    (h _ (BaseAxiom.comp p hp)) v
  have hU : Uniform m r a := by
    by_contra hnot
    have hself : p.eval m r (push a v) := by
      by_contra hno
      exact hnot ((DESTSemantic.uniformity_correct m r p).mp
        (h _ (BaseAxiom.unif p hp)) v hv a ha hno)
    exact hnot (hvalues a hself)
  exact ⟨a,hU,fun y => (hU y).trans (ha y)⟩

/-- Monotonicity of the exact fragment selection. -/
theorem fragment_mono {qs ts : List Unary} (h : ∀ q ∈ qs, q ∈ ts)
    {s : Sentence} (hs : Fragment qs s) : Fragment ts s := by
  cases hs with
  | ext1 => exact Fragment.ext1
  | ext2 => exact Fragment.ext2
  | comp q hq hp => exact Fragment.comp q (h q hq) hp
  | unif q hq hp => exact Fragment.unif q (h q hq) hp
  | inf => exact Fragment.inf
  | natInd p => exact Fragment.natInd p
  | setInd p => exact Fragment.setInd p

theorem axiom_in_fragment {s : Sentence} (h : Axiom s) :
    ∃ qs : List Unary, Fragment qs s := by
  cases h with
  | ext1 => exact ⟨[],Fragment.ext1⟩
  | ext2 => exact ⟨[],Fragment.ext2⟩
  | comp p hp => exact ⟨[⟨_,p⟩],Fragment.comp ⟨_,p⟩ (by simp) hp⟩
  | unif p hp => exact ⟨[⟨_,p⟩],Fragment.unif ⟨_,p⟩ (by simp) hp⟩
  | inf => exact ⟨[],Fragment.inf⟩
  | natInd p => exact ⟨[],Fragment.natInd p⟩
  | setInd p => exact ⟨[],Fragment.setInd p⟩

/-- Structural proof transformation, with no model-theoretic assumptions. -/
theorem derives_mono {T T' : Sentence → Prop} (h : ∀ s, T s → T' s)
    {n : ℕ} {p : Formula n} (hd : Derives T p) : Derives T' p := by
  induction hd with
  | closedTheory p hp => exact Derives.closedTheory p (h p hp)
  | theory p hp => exact Derives.theory p (h p hp)
  | k p q => exact Derives.k p q
  | s p q r => exact Derives.s p q r
  | classicalRule p => exact Derives.classicalRule p
  | mp h1 h2 ih1 ih2 => exact Derives.mp ih1 ih2
  | gen h ih => exact Derives.gen ih
  | inst p i => exact Derives.inst p i
  | dist p q => exact Derives.dist p q
  | vac p => exact Derives.vac p
  | eqRefl i => exact Derives.eqRefl i
  | eqSubst p i j => exact Derives.eqSubst p i j

/-- Every derivation uses a finite list of the comprehension/uniformity
    schemas. This proves the exact proof-support reduction, not a uniform
    reflection principle inside second-order arithmetic. -/
theorem finite_proof_support {n : ℕ} {p : Formula n} (hd : Derives Axiom p) :
    ∃ qs : List Unary, Derives (Fragment qs) p := by
  induction hd with
  | closedTheory p hp =>
    obtain ⟨qs,hq⟩ := axiom_in_fragment hp
    exact ⟨qs,Derives.closedTheory p hq⟩
  | theory p hp =>
    obtain ⟨qs,hq⟩ := axiom_in_fragment hp
    exact ⟨qs,Derives.theory p hq⟩
  | k p q => exact ⟨[],Derives.k p q⟩
  | s p q r => exact ⟨[],Derives.s p q r⟩
  | classicalRule p => exact ⟨[],Derives.classicalRule p⟩
  | mp h1 h2 ih1 ih2 =>
    obtain ⟨qs,hq⟩ := ih1
    obtain ⟨ts,ht⟩ := ih2
    have l : ∀ s, Fragment qs s → Fragment (qs ++ ts) s :=
      fun _ h => fragment_mono (fun q hq => List.mem_append.mpr (Or.inl hq)) h
    have r : ∀ s, Fragment ts s → Fragment (qs ++ ts) s :=
      fun _ h => fragment_mono (fun q hq => List.mem_append.mpr (Or.inr hq)) h
    exact ⟨qs ++ ts,Derives.mp (derives_mono l hq) (derives_mono r ht)⟩
  | gen h ih =>
    obtain ⟨qs,hq⟩ := ih
    exact ⟨qs,Derives.gen hq⟩
  | inst p i => exact ⟨[],Derives.inst p i⟩
  | dist p q => exact ⟨[],Derives.dist p q⟩
  | vac p => exact ⟨[],Derives.vac p⟩
  | eqRefl i => exact ⟨[],Derives.eqRefl i⟩
  | eqSubst p i j => exact ⟨[],Derives.eqSubst p i j⟩

/-- A model for every requested finite fragment entails consistency in the
    declared calculus. This is the formal reduction, not a proof of its
    antecedent in Z2. -/
theorem consistent_of_fragments (h : ∀ qs : List Unary,
    ∃ (X : Type u) (m r : X → X → Prop), Nonempty X ∧ SatisfiesFragment m r qs) :
    DESTReference.Consistent := by
  intro hd
  obtain ⟨qs,hq⟩ := finite_proof_support hd
  obtain ⟨X,m,r,_,hm⟩ := h qs
  exact soundness m r (Fragment qs) hm hq Fin.elim0

/-- In any reference model, its internal least inductive set has uniform
    members and is itself uniform. This does not assume standard omega. -/
theorem uniform_omega_of_model {X : Type u} (m r : X → X → Prop)
    (h : BaseSatisfies m r) (z w : X) (hz : ∀ a, ¬ m a z)
    (hw : LeastInductive m z w) : Uniform m r w ∧ ∀ a, m a w → Uniform m r a := by
  classical
  have ext1 := (DESTSemantic.first_extensionality_correct m r).mp (h _ BaseAxiom.ext1)
  have hc : UniformComprehension m r := @uniform_comprehension_of_model X m r h
  have hzU : Uniform m r z := by
    obtain ⟨a,ha,he⟩ := hc (.bot : Formula 1) (by trivial) Fin.elim0
      (fun i => Fin.elim0 i) (fun _ hbad => False.elim hbad)
    have eqz : a = z := ext1 a z (fun y =>
      ⟨fun hy => False.elim ((he y).mp hy), fun hy => (hz y hy).elim⟩)
    exact eqz ▸ ha
  let p : Formula 1 := conj (uniformF 0)
    (.all (.imp (.mem1 0 (Fin.succ 0)) (uniformF 0)))
  have hp (a : X) : p.eval m r (push a Fin.elim0) ↔
      Uniform m r a ∧ ∀ y, m y a → Uniform m r y := by
    simp [p, Uniform, Formula.eval]
  have hbase : p.eval m r (push z Fin.elim0) :=
    (hp z).mpr ⟨hzU, fun y hy => (hz y hy).elim⟩
  have hstep (a : X) (_ : m a w) (b : X) (hs : ∀ y, m y b ↔ y = a ∨ m y a)
      (ha : p.eval m r (push a Fin.elim0)) : p.eval m r (push b Fin.elim0) := by
    obtain ⟨haU,haMem⟩ := (hp a).mp ha
    have hmem (y : X) (hy : y = a ∨ m y a) : Uniform m r y := by
      rcases hy with rfl | hy
      · exact haU
      · exact haMem y hy
    let q : Formula 2 := disj (.eq 0 (Fin.succ 0)) (.mem1 0 (Fin.succ 0))
    let v : Fin 1 → X := push a Fin.elim0
    have hq (y : X) : q.eval m r (push y v) ↔ y = a ∨ m y a := by
      simp [q, v, Formula.eval, DESTSemantic.push_push_one]
    have hv : ∀ i : Fin 1, Uniform m r (v i) := by
      intro i
      refine Fin.cases ?_ (fun j => Fin.elim0 j) i
      simpa [v] using haU
    obtain ⟨c,hcU,hce⟩ := hc q (by simp [q, disj, neg, Formula.firstOnly]) v hv
      (fun y hy => hmem y ((hq y).mp hy))
    have eqb : c = b := ext1 c b (fun y => (hce y).trans ((hq y).trans (hs y).symm))
    exact (hp b).mpr ⟨eqb ▸ hcU,fun y hy => hmem y ((hs y).mp hy)⟩
  have hInd := h _ (BaseAxiom.natInd p)
  simp only [naturalInduction, eval_close, Formula.eval, natBody, eval_conj,
    DESTSemantic.zero_correct, DESTSemantic.omega_correct, DESTSemantic.succ_correct,
    eval_atVar, push_zero, push_succ] at hInd
  have hall : ∀ a, m a w → Uniform m r a := by
    intro a ha
    exact ((hp a).mp (hInd Fin.elim0 w z ⟨hz,hw⟩ hbase hstep a ha)).1
  -- Define the internal naturals with NO free set parameters, to avoid
  -- assuming the uniformity of omega before proving it.
  let q : Formula 1 := ex (ex (conj (conj (zeroF 0) (omegaF 0 (Fin.succ 0)))
    (.mem1 (Fin.succ (Fin.succ 0)) (Fin.succ 0))))
  have hq (a : X) : q.eval m r (push a Fin.elim0) ↔ m a w := by
    have heval : q.eval m r (push a Fin.elim0) ↔
        ∃ w' z', (∀ y, ¬ m y z') ∧ LeastInductive m z' w' ∧ m a w' := by
      have htwo (x y : X) (v : Fin 1 → X) : push x (push y v) (2 : Fin 3) = v 0 := by
        rw [show (2 : Fin 3) = (0 : Fin 1).succ.succ by decide, push_succ, push_succ]
      simp [q, Formula.eval, LeastInductive, Inductive, and_assoc, htwo]
    rw [heval]
    constructor
    · rintro ⟨w',z',hz',hw',ha⟩
      have ez : z' = z := ext1 _ _ (fun y => ⟨fun hy => (hz' y hy).elim,fun hy => (hz y hy).elim⟩)
      subst z'
      exact hw'.2 w hw.1 a ha
    · intro ha
      exact ⟨w,z,hz,hw,ha⟩
  have qfirst : q.firstOnly := by
    simp [q, ex, conj, neg, zeroF, omegaF, inductiveF, succF, iffF, disj, Formula.firstOnly]
  obtain ⟨c,hcU,hce⟩ := hc q qfirst Fin.elim0 (fun i => Fin.elim0 i)
    (fun y hy => hall y ((hq y).mp hy))
  have ew : c = w := ext1 c w (fun y => (hce y).trans (hq y))
  exact ⟨ew ▸ hcU,hall⟩

/-- Numeric parameters and omega are the only free parameters here. The
    formula itself may contain arbitrary first-language quantifiers. This
    is the exact separation/comprehension lemma used in the lower bound. -/
theorem number_comprehension_of_model {X : Type u} (m r : X → X → Prop)
    (h : BaseSatisfies m r) (z w : X) (hz : ∀ a, ¬ m a z)
    (hw : LeastInductive m z w) {n : ℕ} (p : Formula (n+2)) (hp : p.firstOnly)
    (v : Fin n → X) (hv : ∀ i, m (v i) w) :
    ∃ a, Uniform m r a ∧ ∀ y, m y a ↔ m y w ∧ p.eval m r (push y (push w v)) := by
  obtain ⟨hwU,hnum⟩ := uniform_omega_of_model m r h z w hz hw
  let q : Formula (n+2) := conj (.mem1 0 (Fin.succ 0)) p
  have hq (y : X) : q.eval m r (push y (push w v)) ↔
      m y w ∧ p.eval m r (push y (push w v)) := by
    simp [q, Formula.eval, DESTSemantic.push_push_one]
  have hparams : ∀ i : Fin (n+1), Uniform m r (push w v i) := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using hwU
    · simpa using hnum (v j) (hv j)
  obtain ⟨a,ha,he⟩ := uniform_comprehension_of_model m r h q
    (by simp [q, conj, neg, Formula.firstOnly, hp]) (push w v) hparams
    (fun y hy => hnum y ((hq y).mp hy).1)
  exact ⟨a,ha,fun y => (he y).trans (hq y)⟩

end DESTStrength
