import DEST.ReferenceTheory

set_option autoImplicit false
set_option maxHeartbeats 0

universe u

namespace DESTReference

/-- Classical first-order Hilbert derivations with equality. The context size
    records the available free variables; all nonlogical axioms are sentences.
    Universal generalization is unrestricted because hypotheses are closed. -/
inductive Derives (T : Sentence → Prop) : {n : ℕ} → Formula n → Prop where
  | closedTheory (p : Sentence) : T p → Derives T p
  | theory {n : ℕ} (p : Sentence) : T p → Derives T (p.rename (Fin.elim0 : Fin 0 → Fin n))
  | k {n : ℕ} (p q : Formula n) : Derives T (.imp p (.imp q p))
  | s {n : ℕ} (p q r : Formula n) :
      Derives T (.imp (.imp p (.imp q r)) (.imp (.imp p q) (.imp p r)))
  | classicalRule {n : ℕ} (p : Formula n) : Derives T (.imp (neg (neg p)) p)
  | mp {n : ℕ} {p q : Formula n} : Derives T (.imp p q) → Derives T p → Derives T q
  | gen {n : ℕ} {p : Formula (n+1)} : Derives T p → Derives T (.all p)
  | inst {n : ℕ} (p : Formula (n+1)) (i : Fin n) :
      Derives T (.imp (.all p) (atVar p i id))
  | dist {n : ℕ} (p : Formula n) (q : Formula (n+1)) :
      Derives T (.imp (.all (.imp (p.rename Fin.succ) q)) (.imp p (.all q)))
  | vac {n : ℕ} (p : Formula n) : Derives T (.imp p (.all (p.rename Fin.succ)))
  | eqRefl {n : ℕ} (i : Fin n) : Derives T (.eq i i)
  | eqSubst {n : ℕ} (p : Formula (n+1)) (i j : Fin n) :
      Derives T (.imp (.eq i j) (.imp (atVar p i id) (atVar p j id)))

/-- Soundness for this explicitly declared proof calculus. -/
theorem soundness {X : Type u} (m1 m2 : X → X → Prop)
    (T : Sentence → Prop) (hT : ∀ s, T s → s.eval m1 m2 Fin.elim0)
    {n : ℕ} {p : Formula n} (h : Derives T p) : ∀ v : Fin n → X, p.eval m1 m2 v := by
  classical
  induction h with
  | closedTheory p hp =>
    intro v
    have he : v = (Fin.elim0 : Fin 0 → X) := by funext i; exact Fin.elim0 i
    rw [he]
    exact hT p hp
  | theory p hp =>
    intro v
    rw [eval_rename]
    have he : (fun i => v (Fin.elim0 i)) = (Fin.elim0 : Fin 0 → X) := by
      funext i; exact Fin.elim0 i
    rw [he]
    exact hT p hp
  | k p q => intro v; exact fun hp _ => hp
  | s p q r => intro v; exact fun h1 h2 hp => h1 hp (h2 hp)
  | classicalRule p => intro v; exact Classical.byContradiction
  | mp h1 h2 ih1 ih2 => intro v; exact ih1 v (ih2 v)
  | gen h ih => intro v x; exact ih (push x v)
  | inst p i =>
    intro v h
    exact (eval_atVar m1 m2 p i id v).mpr (h (v i))
  | dist p q =>
    intro v
    simp only [Formula.eval, eval_rename, push_succ]
    exact fun h hp x => h x hp
  | vac p =>
    intro v
    simp only [Formula.eval, eval_rename, push_succ]
    exact fun hp _ => hp
  | eqRefl i => intro v; rfl
  | eqSubst p i j =>
    intro v
    simp only [Formula.eval, eval_atVar, id_eq]
    intro he hp
    rwa [← he]

def Consistent : Prop := ¬ Derives Axiom (.bot : Sentence)

/-- The model-to-syntactic-consistency bridge, proved within Lean. -/
theorem consistent_of_model {X : Type u} (m1 m2 : X → X → Prop)
    (h : Satisfies m1 m2) : Consistent := by
  intro hd
  exact soundness m1 m2 Axiom h hd Fin.elim0

end DESTReference
