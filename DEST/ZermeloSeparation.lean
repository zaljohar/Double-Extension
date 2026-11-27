import DEST.Zermelo

set_option autoImplicit false
set_option maxHeartbeats 0
universe u
namespace DESTOriginal
open DESTReference

/-- The extra free variable is the set-coded domain, at the head of the context. -/
def swapHead {n : ℕ} : Fin (n+2) → Fin (n+2) :=
  Fin.cases (Fin.succ 0) (Fin.cases 0 (fun i => i.succ.succ))

theorem firstOnly_rename {n k : ℕ} (p : Formula n) (f : Fin n → Fin k)
    (hp : p.firstOnly) : (p.rename f).firstOnly := by
  induction p generalizing k with
  | bot => trivial
  | eq i j => trivial
  | mem1 i j => trivial
  | mem2 i j => exact False.elim hp
  | imp p q ihp ihq => exact ⟨ihp f hp.1,ihq f hp.2⟩
  | all p ih => exact ih (liftRen f) hp

theorem eval_swapHead {X : Type u} (m r : X → X → Prop) {n : ℕ}
    (p : Formula (n+2)) (a W : X) (v : Fin n → X) :
    (p.rename swapHead).eval m r (push a (push W v)) ↔
      p.eval m r (push W (push a v)) := by
  rw [eval_rename]
  have he : (fun i => push a (push W v) (swapHead i)) = push W (push a v) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [swapHead,DESTSemantic.push_push_one]
    · refine Fin.cases ?_ (fun k => ?_) j
      · simp [swapHead,DESTSemantic.push_push_one]
      · simp [swapHead,DESTSemantic.push_push_one]
  rw [he]

def relativize : {n : ℕ} → Formula n → Formula (n+1)
  | _, .bot => .bot
  | _, .eq i j => .eq i.succ j.succ
  | _, .mem1 i j => .mem1 i.succ j.succ
  | _, .mem2 _ _ => .bot
  | _, .imp p q => .imp (relativize p) (relativize q)
  | _, .all p => .all (.imp (.mem1 0 (Fin.succ 0)) ((relativize p).rename swapHead))

theorem relativize_first {n : ℕ} (p : Formula n) (hp : p.firstOnly) : (relativize p).firstOnly := by
  induction p with
  | bot => trivial
  | eq i j => trivial
  | mem1 i j => trivial
  | mem2 i j => trivial
  | imp p q ihp ihq => exact ⟨ihp hp.1,ihq hp.2⟩
  | all p ih => exact ⟨True.intro,firstOnly_rename _ swapHead (ih hp)⟩

/-- Full first-order relativization, including arbitrary unbounded quantifiers. -/
theorem relativize_correct {X : Type u} (m r : X → X → Prop) (W : X)
    {n : ℕ} (p : Formula n) (hp : p.firstOnly) (v : Fin n → Inside m W) :
    (relativize p).eval m r (push W (fun i => (v i).val)) ↔
      p.eval (insideMem m W) (insideMem m W) v := by
  induction p with
  | bot => rfl
  | eq i j =>
    simp only [relativize,Formula.eval,push_succ,Subtype.ext_iff]
  | mem1 i j => simp [relativize,Formula.eval,insideMem]
  | mem2 i j => exact False.elim hp
  | imp p q ihp ihq => simp only [relativize,Formula.eval,ihp hp.1 v,ihq hp.2 v]
  | all p ih =>
    simp only [relativize,Formula.eval,push_zero,push_succ,eval_swapHead]
    have hv (a : Inside m W) : (fun i => (push a v i).val) = push a.val (fun i => (v i).val) := by
      funext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
    constructor
    · intro h a
      apply (ih hp (push a v)).mp
      rw [hv]
      exact h a.val a.property
    · intro h a ha
      let a' : Inside m W := ⟨a,ha⟩
      have hh := (ih hp (push a' v)).mpr (h a')
      rw [hv] at hh
      exact hh

/-- Separation on a uniform transitive domain with uniform elements and
closure under existing subsets of its elements. No restriction on the
complexity of the separating formula. -/
theorem separation_in_domain {X : Type u} (m r : X → X → Prop) (h : Original m r)
    (W : X) (hW : AllUniform m r W) (ht : Transitive m W)
    (hsub : ∀ a b, m a W → Sub m b a → m b W)
    {n : ℕ} (p : Formula (n+1)) (hp : p.firstOnly)
    (v : Fin n → Inside m W) (a : Inside m W) :
    ∃ b : Inside m W, ∀ y : Inside m W, insideMem m W y b ↔
      insideMem m W y a ∧ p.eval (insideMem m W) (insideMem m W) (push y v) := by
  let ren : Fin (n+2) → Fin (n+3) :=
    Fin.cases (Fin.succ (Fin.succ 0)) (Fin.cases 0 (fun i => i.succ.succ.succ))
  let q : Formula (n+3) := conj (.mem1 0 (Fin.succ 0)) ((relativize p).rename ren)
  let vs : Fin (n+2) → X := push a.val (push W (fun i => (v i).val))
  have hv : ∀ i, Uniform m r (vs i) := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [vs] using hW.2 a.val a.property
    · refine Fin.cases ?_ (fun k => ?_) j
      · simpa [vs] using hW.1
      · simpa [vs] using hW.2 (v k).val (v k).property
  have hq : q.firstOnly := by
    change (conj (.mem1 0 (Fin.succ 0)) ((relativize p).rename ren)).firstOnly
    simp [conj,neg,Formula.firstOnly,firstOnly_rename _ ren (relativize_first p hp)]
  have guard (y : X) : q.eval m r (push y vs) → m y a.val := by
    intro hy
    have hguard := ((eval_conj m r (push y vs) (.mem1 0 (Fin.succ 0))
      ((relativize p).rename ren)).mp hy).1
    simpa only [Formula.eval,push_zero,push_succ,vs] using hguard
  obtain ⟨b,hb,he⟩ := uniform_collection m r h q hq vs hv
    (fun y hy => hW.2 y (ht a.val y (guard y hy) a.property))
  have hba : Sub m b a.val := fun y hy => guard y ((he y).mp hy)
  refine ⟨⟨b,hsub a.val b a.property hba⟩,?_⟩
  intro y
  have hre : (fun i => push y.val vs (ren i)) = push W (fun i => (push y v i).val) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [ren,vs,DESTSemantic.push_push_one]
    · refine Fin.cases ?_ (fun k => ?_) j
      · simp [ren,vs,DESTSemantic.push_push_one]
      · simp [ren,vs,DESTSemantic.push_push_one]
  change m y.val b ↔ m y.val a.val ∧ _
  rw [he y]
  -- The assignment identity aligns the domain and the distinguished element.
  -- Keeping vs folded here prevents simp from changing the left-hand side.
  have hrel : ((relativize p).rename ren).eval m r (push y.val vs) ↔
      p.eval (insideMem m W) (insideMem m W) (push y v) := by
    rw [eval_rename,hre]
    exact relativize_correct m r W p hp (push y v)
  -- Re-express the unfolded conjunction using the original environment.
  rw [q,eval_conj]
  change (m y.val a.val ∧ ((relativize p).rename ren).eval m r (push y.val vs)) ↔ _
  rw [hrel]

end DESTOriginal
