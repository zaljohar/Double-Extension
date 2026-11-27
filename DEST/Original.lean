import DEST.OriginalSpecification
import DEST.SemanticAudit

set_option autoImplicit false
set_option maxHeartbeats 0
universe u
namespace DESTOriginal
open DESTReference

/-- The uniformity consequence, in an arbitrary original DEST model. -/
theorem uniform_collection {X : Type u} (m r : X → X → Prop) (h : Original m r)
    {n : ℕ} (p : Formula (n+1)) (hp : p.firstOnly) (v : Fin n → X)
    (hv : ∀ i, Uniform m r (v i)) (hy : ∀ y, p.eval m r (push y v) → Uniform m r y) :
    ∃ a, Uniform m r a ∧ ∀ y, m y a ↔ p.eval m r (push y v) := by
  classical
  obtain ⟨a,ha⟩ := h.comp p hp v
  have hu : Uniform m r a := by
    by_contra hn
    have hs : p.eval m r (push a v) := by
      by_contra hf
      exact hn (h.unif p hp v hv a ha hf)
    exact hn (hy a hs)
  exact ⟨a,hu,fun y => (hu y).trans (ha y)⟩

/-- Generic convenient wrapper around the preceding theorem. The explicit
formula and its semantic equivalence are mandatory inputs. -/
theorem collect {X : Type u} (m r : X → X → Prop) (h : Original m r)
    {n : ℕ} (p : Formula (n+1)) (hp : p.firstOnly) (v : Fin n → X)
    (hv : ∀ i, Uniform m r (v i)) (P : X → Prop)
    (he : ∀ y, p.eval m r (push y v) ↔ P y) (hu : ∀ y, P y → Uniform m r y) :
    ∃ a, Uniform m r a ∧ ∀ y, m y a ↔ P y := by
  obtain ⟨a,ha,hm⟩ := uniform_collection m r h p hp v hv (fun y hy => hu y ((he y).mp hy))
  exact ⟨a,ha,fun y => (hm y).trans (he y)⟩

theorem empty_exists {X : Type u} (m r : X → X → Prop) (h : Original m r) :
    ∃ z, Zero m z ∧ Uniform m r z := by
  obtain ⟨z,hu,he⟩ := uniform_collection m r h (.bot : Formula 1) True.intro Fin.elim0
    (fun i => Fin.elim0 i) (fun y hy => False.elim hy)
  exact ⟨z,fun y hy => (he y).mp hy,hu⟩

theorem successor_exists {X : Type u} (m r : X → X → Prop) (h : Original m r)
    (a : X) (ha : AllUniform m r a) : ∃ b, Succ m a b ∧ AllUniform m r b := by
  let p : Formula 2 := disj (.eq 0 (Fin.succ 0)) (.mem1 0 (Fin.succ 0))
  let v : Fin 1 → X := push a Fin.elim0
  have hv : ∀ i, Uniform m r (v i) := by
    intro i; refine Fin.cases ?_ (fun j => Fin.elim0 j) i; simpa [v] using ha.1
  have he (y : X) : p.eval m r (push y v) ↔ y = a ∨ m y a := by
    simp only [p,v,eval_disj,Formula.eval,push_zero,push_succ]
  have hu (y : X) (hy : y = a ∨ m y a) : Uniform m r y := by
    rcases hy with rfl | hy
    · exact ha.1
    · exact ha.2 y hy
  obtain ⟨b,hb,hm⟩ := collect m r h p (by simp [p,disj,neg,Formula.firstOnly]) v hv _ he hu
  exact ⟨b,hm,hb,fun y hy => hu y ((hm y).mp hy)⟩

/-- First-only formula for membership in every inductive set, with no
presupposition that such a set exists. -/
def naturalF {n : ℕ} (z a : Fin n) : Formula n :=
  .all (.imp (inductiveF z.succ 0) (.mem1 a.succ 0))

@[simp] theorem naturalF_correct {X : Type u} (m r : X → X → Prop)
    {n : ℕ} (v : Fin n → X) (z a : Fin n) :
    (naturalF z a).eval m r v ↔ Natural m (v z) (v a) := by
  simp only [naturalF, Natural, Formula.eval, DESTSemantic.inductive_correct, push_zero,push_succ]

theorem naturalF_firstOnly {n : ℕ} (z a : Fin n) : (naturalF z a).firstOnly := by
  simp [naturalF,inductiveF,succF,conj,disj,iffF,neg,ex,Formula.firstOnly]

def allUniformF {n : ℕ} (a : Fin n) : Formula n :=
  conj (uniformF a) (.all (.imp (.mem1 0 a.succ) (uniformF 0)))

@[simp] theorem allUniformF_correct {X : Type u} (m r : X → X → Prop)
    {n : ℕ} (v : Fin n → X) (a : Fin n) :
    (allUniformF a).eval m r v ↔ AllUniform m r (v a) := by
  simp only [allUniformF,AllUniform,eval_conj,DESTSemantic.uniformF_correct,
    Formula.eval,push_zero,push_succ]

/-- Main requested theorem: Infinity and uniformity of omega follow from
original DEST, with no Infinity axiom, no SU, no TI, no standard Nat frame. -/
theorem exists_uniform_omega {X : Type u} (m r : X → X → Prop) (h : Original m r) :
    ∃ z w, Zero m z ∧ LeastInductive m z w ∧ AllUniform m r w := by
  obtain ⟨z,hz,hzu⟩ := empty_exists m r h
  let p : Formula 1 := allUniformF 0
  have he (a : X) : p.eval m r (push a Fin.elim0) ↔ AllUniform m r a := by
    simp only [p,allUniformF_correct,push_zero]
  have hb : p.eval m r (push z Fin.elim0) := (he z).mpr ⟨hzu,fun y hy => (hz y hy).elim⟩
  have hs (a : X) (_ : Natural m z a) (b : X) (hab : Succ m a b)
      (ha : p.eval m r (push a Fin.elim0)) : p.eval m r (push b Fin.elim0) := by
    obtain ⟨c,hc,hcu⟩ := successor_exists m r h a ((he a).mp ha)
    have e : c = b := h.ext1 c b (fun y => (hc y).trans (hab y).symm)
    exact (he b).mpr (e ▸ hcu)
  have hN : ∀ a, Natural m z a → AllUniform m r a :=
    fun a ha => (he a).mp (h.natInd z hz p Fin.elim0 hb hs a ha)
  let q : Formula 2 := naturalF (Fin.succ 0) 0
  let v : Fin 1 → X := push z Fin.elim0
  have hv : ∀ i, Uniform m r (v i) := by
    intro i; refine Fin.cases ?_ (fun j => Fin.elim0 j) i; simpa [v] using hzu
  have hq (a : X) : q.eval m r (push a v) ↔ Natural m z a := by
    simp only [q,v,naturalF_correct,push_zero,push_succ]
  obtain ⟨w,hwu,hw⟩ := collect m r h q (naturalF_firstOnly _ _) v hv _ hq
    (fun a ha => (hN a ha).1)
  have hind : InductiveSet m z w := by
    refine ⟨(hw z).mpr (fun a ha => ha.1),?_⟩
    intro a ha
    have hn := (hw a).mp ha
    obtain ⟨b,hab,_⟩ := successor_exists m r h a (hN a hn)
    refine ⟨b,(hw b).mpr ?_,hab⟩
    intro c hc
    obtain ⟨s,hs,hsa⟩ := hc.2 a (hn c hc)
    have e : s = b := h.ext1 s b (fun y => (hsa y).trans (hab y).symm)
    exact e ▸ hs
  exact ⟨z,w,hz,⟨hind,fun a ha y hy => (hw y).mp hy a ha⟩,hwu,
    fun y hy => (hN y ((hw y).mp hy)).1⟩

/-- Bridge from the previously verified specification. Infinity is NOT used
in the proof above; it is used here only as a property of the old model. -/
theorem original_of_reference {X : Type u} (m r : X → X → Prop) (h : Satisfies m r) : Original m r := by
  have he := (DESTSemantic.first_extensionality_correct m r).mp (h _ Axiom.ext1)
  refine ⟨he,(DESTSemantic.second_extensionality_correct m r).mp (h _ Axiom.ext2),?_,?_,?_⟩
  · intro n p hp v
    exact (DESTSemantic.comprehension_correct m r p).mp (h _ (Axiom.comp p hp)) v
  · intro n p hp v hv a ha hs
    exact (DESTSemantic.uniformity_correct m r p).mp (h _ (Axiom.unif p hp)) v hv a ha hs
  · intro z hz n p v hb hs a ha
    have hi := h _ Axiom.inf
    simp only [infinity,eval_ex,eval_conj,DESTSemantic.zero_correct,
      DESTSemantic.omega_correct,push_zero,push_succ] at hi
    obtain ⟨w,z',hz',hw,hleast⟩ := hi
    have ez : z' = z := he _ _ (fun y => ⟨fun hy => (hz' y hy).elim,fun hy => (hz y hy).elim⟩)
    subst z'
    have hn := h _ (Axiom.natInd p)
    simp only [naturalInduction,eval_close,Formula.eval,natBody,eval_conj,
      DESTSemantic.zero_correct,DESTSemantic.omega_correct,DESTSemantic.succ_correct,
      eval_atVar,push_zero,push_succ] at hn
    exact hn v w z ⟨hz,hw,hleast⟩ hb
      (fun x hx b hxb hp => hs x (fun t ht => hleast t ht x hx) b hxb hp) a (ha w hw)

end DESTOriginal
