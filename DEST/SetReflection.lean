import DEST.SetRecursion

set_option autoImplicit false
set_option maxHeartbeats 0

universe u

namespace DESTSet

open DESTReference

variable {X : Type u} (M : Model X)
local infix:50 " ∈ₛ " => M.mem

def Relativized (D : X → Prop) (m r : X → X → Prop) :
    {n : ℕ} → DESTReference.Formula n → (Fin n → X) → Prop
  | _, .bot, _ => False
  | _, .eq i j, v => v i = v j
  | _, .mem1 i j, v => m (v i) (v j)
  | _, .mem2 i j, v => r (v i) (v j)
  | _, .imp p q, v => Relativized D m r p v → Relativized D m r q v
  | _, .all p, v => ∀ x, D x → Relativized D m r p (push x v)

theorem relativized_all (m r : X → X → Prop) {n : ℕ} (p : DESTReference.Formula n)
    (v : Fin n → X) : Relativized (fun _ => True) m r p v ↔ p.eval m r v := by
  induction p with
  | bot => rfl
  | eq i j => rfl
  | mem1 i j => rfl
  | mem2 i j => rfl
  | imp p q hp hq => simp only [Relativized, DESTReference.Formula.eval, hp, hq]
  | all p ih => simp only [Relativized, DESTReference.Formula.eval, ih, true_implies]

theorem relativized_subtype (D : X → Prop) (m r : X → X → Prop)
    {n : ℕ} (p : DESTReference.Formula n) (v : Fin n → Subtype D) :
    Relativized D m r p (fun i => (v i).val) ↔
      p.eval (fun x y : Subtype D => m x.val y.val) (fun x y : Subtype D => r x.val y.val) v := by
  induction p with
  | bot => rfl
  | eq i j => simp only [Relativized, DESTReference.Formula.eval, Subtype.ext_iff]
  | mem1 i j => rfl
  | mem2 i j => rfl
  | imp p q hp hq => simp only [Relativized, DESTReference.Formula.eval, hp, hq]
  | all p ih =>
    change (∀ a, D a → Relativized D m r p (push a (fun i => (v i).val))) ↔
      ∀ a : Subtype D, p.eval (fun x y : Subtype D => m x.val y.val)
        (fun x y : Subtype D => r x.val y.val) (push a v)
    have henv (a : Subtype D) :
        (fun i => (push a v i).val) = push a.val (fun i => (v i).val) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp
    constructor
    · intro h a
      apply (ih (push a v)).mp
      rw [henv]
      exact h a.val a.property
    · intro h a ha
      have hh := (ih (push (⟨a,ha⟩ : Subtype D) v)).mpr (h ⟨a,ha⟩)
      rw [henv] at hh
      exact hh

namespace TermDef

variable {o : Operations X}

theorem relabel {ι κ : Type} {f : (ι → X) → X} (h : TermDef o f) (g : ι → κ) :
    TermDef o (fun v => f (fun i => v (g i))) := by
  obtain ⟨t,ht⟩ := h
  refine ⟨t.subst (fun i => .var (g i)),fun v => ?_⟩
  rw [Term.eval_subst]
  exact ht _

end TermDef

theorem relativized_def {D : X → Prop} (dD : UnaryDef M.toOperations D)
    {r : X → X → Prop} (dr : BinaryDef M.toOperations r) {n : ℕ}
    (p : DESTReference.Formula n) {ι : Type} (f : Fin n → (ι → X) → X)
    (hf : ∀ i, TermDef M.toOperations (f i)) :
    Def M.toOperations (fun v => Relativized D M.mem r p (fun i => f i v)) := by
  induction p generalizing ι with
  | bot => exact Def.bot
  | eq i j => exact Def.eq (hf i) (hf j)
  | mem1 i j => exact Def.mem (hf i) (hf j)
  | mem2 i j => exact Def.app₂ dr (hf i) (hf j)
  | imp p q hp hq => exact Def.imp (hp f hf) (hq f hf)
  | all p ih =>
    change Def M.toOperations (fun v => ∀ x, D x → Relativized D M.mem r p (push x (fun i => f i v)))
    apply Def.all
    apply Def.imp (Def.app₁ dD (.var none))
    let f' := fun i (v : Option ι → X) => push (v none) (fun j => f j (fun k => v (some k))) i
    apply ih f'
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [f', push_zero] using
        (TermDef.var (o := M.toOperations) (none : Option ι))
    · simpa only [f', push_succ] using (hf j).relabel some

theorem eval_def {r : X → X → Prop} (dr : BinaryDef M.toOperations r) {n : ℕ}
    (p : DESTReference.Formula n) {ι : Type} (f : Fin n → (ι → X) → X)
    (hf : ∀ i, TermDef M.toOperations (f i)) :
    Def M.toOperations (fun v => p.eval M.mem r (fun i => f i v)) :=
  (relativized_def M Def.top dr p f hf).congr (fun v => relativized_all _ _ _ _)

structure Query where
  arity : ℕ
  test : (Fin arity → X) → X → Prop
  definable : Def M.toOperations (fun v : Option (Fin arity) → X => test (fun i => v (some i)) (v none))

def Closed (d : X) (qs : List (Query M)) : Prop :=
  ∀ q ∈ qs, ∀ v : Fin q.arity → X, (∀ i, v i ∈ₛ d) → (∃ a, q.test v a) →
    ∃ a, a ∈ₛ d ∧ q.test v a

/-- The constructible reflection consequence of Kanovei–Lyubetsky, Corollary
8.4 and Lemma 8.5, for a finite family of first-order witness requests.
Adjunction closure follows by including the adjunction operation. -/
def CofinalReflection : Prop :=
  ∀ a (qs : List (Query M)), ∃ d, a ∈ₛ d ∧ Transitive M d ∧
    (∀ x y, x ∈ₛ d → y ∈ₛ d → M.insert x y ∈ₛ d) ∧ Closed M d qs

def counter {n : ℕ} (p : DESTReference.Formula (n+1)) : Query M where
  arity := n
  test := fun v a => ¬ p.eval M.mem M.mem (push a v)
  definable := by
    apply Def.not
    let f := fun i (v : Option (Fin n) → X) => push (v none) (fun j => v (some j)) i
    apply eval_def M (Def.mem (.var false) (.var true)) p f
    intro i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp only [f, push_zero, push_succ]
    · exact TermDef.var none
    · exact TermDef.var (some j)

def counters : {n : ℕ} → DESTReference.Formula n → List (Query M)
  | _, .all p => counter M p :: counters p
  | _, .imp p q => counters p ++ counters q
  | _, _ => []

abbrev Carrier (d : X) := {a : X // a ∈ₛ d}
abbrev first (d : X) (a b : Carrier M d) : Prop := a.val ∈ₛ b.val

theorem reflect {d : X} {qs : List (Query M)} (hc : Closed M d qs) {n : ℕ}
    (p : DESTReference.Formula n) (hQ : ∀ q ∈ counters M p, q ∈ qs)
    (v : Fin n → Carrier M d) :
    p.eval (first M d) (first M d) v ↔ p.eval M.mem M.mem (fun i => (v i).val) := by
  classical
  induction p with
  | bot => rfl
  | eq i j => simp only [DESTReference.Formula.eval, Subtype.ext_iff]
  | mem1 i j => rfl
  | mem2 i j => rfl
  | imp p q hp hq =>
    change (p.eval _ _ v → q.eval _ _ v) ↔ (p.eval _ _ _ → q.eval _ _ _)
    rw [hp (fun r hr => hQ r (List.mem_append.mpr (Or.inl hr))) v,
      hq (fun r hr => hQ r (List.mem_append.mpr (Or.inr hr))) v]
  | all p ih =>
    have hsub : ∀ r ∈ counters M p, r ∈ qs :=
      fun r hr => hQ r (List.mem_cons.mpr (Or.inr hr))
    have henv (a : Carrier M d) :
        (fun i => (push a v i).val) = push a.val (fun i => (v i).val) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp
    constructor
    · intro hp a
      by_contra hn
      obtain ⟨b,hb,hbad⟩ := hc (counter M p) (hQ _ (List.mem_cons.mpr (Or.inl rfl)))
        (fun i => (v i).val) (fun i => (v i).property) ⟨a,hn⟩
      let b' : Carrier M d := ⟨b,hb⟩
      have ht := (ih hsub (push b' v)).mp (hp b')
      rw [henv] at ht
      exact hbad ht
    · intro hp a
      apply (ih hsub (push a v)).mpr
      rw [henv]
      exact hp a.val

end DESTSet
