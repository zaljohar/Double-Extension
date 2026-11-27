import DEST.SetReflection

set_option autoImplicit false
set_option maxHeartbeats 0

universe u

namespace DESTSet

open DESTReference

variable {X : Type u} {o : Operations X}

theorem Def.all_fin {ι : Type} {n : ℕ} {P : (ι → X) → Fin n → Prop}
    (h : ∀ i, Def o (fun v => P v i)) : Def o (fun v => ∀ i, P v i) := by
  induction n with
  | zero => exact Def.top.congr (fun _ => by simp)
  | succ n ih =>
    exact (Def.and (h 0) (ih (P := fun v i => P v i.succ) (fun i => h i.succ))).congr
      (fun _ => Fin.forall_fin_succ.symm)

theorem Def.all_values {n : ℕ} {ι : Type} {P : (ι → X) → (Fin n → X) → Prop}
    (h : Def o (fun v : ι ⊕ Fin n → X => P (fun i => v (.inl i)) (fun i => v (.inr i)))) :
    Def o (fun v => ∀ a, P v a) := by
  induction n generalizing ι with
  | zero =>
    have h' := h.relabel (Sum.elim id Fin.elim0)
    have h0 : Def o (fun v : ι → X => P v Fin.elim0) := by
      apply h'.congr
      intro v
      have e : (fun i : Fin 0 => v (Fin.elim0 i)) = Fin.elim0 := by
        funext i
        exact Fin.elim0 i
      change P v (fun i => v (Fin.elim0 i)) ↔ P v Fin.elim0
      rw [e]
    apply h0.congr
    intro v
    have he (a : Fin 0 → X) : a = Fin.elim0 := by funext i; exact Fin.elim0 i
    constructor
    · intro hp a
      rw [he a]
      exact hp
    · intro hp
      exact hp _
  | succ n ih =>
    have h' := h.relabel (fun i : ι ⊕ Fin (n+1) =>
      match i with
      | .inl i => Sum.inl (some i)
      | .inr j => Fin.cases (Sum.inl none) Sum.inr j)
    have hd : Def o (fun w : Option ι ⊕ Fin n → X =>
        P (fun i => w (.inl (some i))) (push (w (.inl none)) (fun j => w (.inr j)))) := by
      apply h'.congr
      intro w
      have he : (fun j : Fin (n+1) => w (Fin.cases (Sum.inl none) Sum.inr j)) =
          push (w (.inl none)) (fun j => w (.inr j)) := by
        funext j
        refine Fin.cases ?_ (fun k => ?_) j <;> simp only [Fin.cases_zero,Fin.cases_succ,push_zero,push_succ]
      rw [he]
    apply (Def.all (R := fun v x => ∀ a, P v (push x a))
      (ih (P := fun v a => P (fun i => v (some i)) (push (v none) a)) hd)).congr
    intro v
    constructor
    · intro hh a
      rw [← push_eta a]
      exact hh _ _
    · intro hh a b
      exact hh _

theorem Def.ex_values {n : ℕ} {ι : Type} {P : (ι → X) → (Fin n → X) → Prop}
    (h : Def o (fun v : ι ⊕ Fin n → X => P (fun i => v (.inl i)) (fun i => v (.inr i)))) :
    Def o (fun v => ∃ a, P v a) := by
  have ha : Def o (fun v => ∀ a, ¬ P v a) := Def.all_values (P := fun v a => ¬ P v a) h.not
  exact ha.not.congr (fun _ => by classical push Not; rfl)

theorem Def.ex_list {ι α : Type} {P : (ι → X) → α → Prop} (l : List α)
    (h : ∀ a ∈ l, Def o (fun v => P v a)) : Def o (fun v => ∃ a ∈ l, P v a) := by
  induction l with
  | nil => exact Def.bot.congr (fun _ => by simp)
  | cons a l ih =>
    apply (Def.or (h a (by simp)) (ih (fun b hb => h b (List.mem_cons_of_mem a hb)))).congr
    intro v
    simp only [List.mem_cons]
    constructor
    · rintro (ha | ⟨b,hb,hp⟩)
      · exact ⟨a,Or.inl rfl,ha⟩
      · exact ⟨b,Or.inr hb,hp⟩
    · rintro ⟨b, (rfl | hb), hp⟩
      · exact Or.inl hp
      · exact Or.inr ⟨b,hb,hp⟩

variable (M : Model X)
local infix:50 " ∈ₛ " => M.mem

def Extension {n : ℕ} (d : X) (p : DESTReference.Formula (n+1)) (v : Fin n → X) (B : X) : Prop :=
  ∀ x, x ∈ₛ B ↔ x ∈ₛ d ∧ Relativized (fun y => y ∈ₛ d) M.mem M.mem p (push x v)

theorem defExtension {n : ℕ} (d : X) (p : DESTReference.Formula (n+1)) {ι : Type}
    {f : (ι → X) → X} (hf : TermDef M.toOperations f)
    (g : Fin n → (ι → X) → X) (hg : ∀ i, TermDef M.toOperations (g i)) :
    Def M.toOperations (fun v => Extension M d p (fun i => g i v) (f v)) := by
  unfold Extension
  apply Def.all
  apply Def.iff (Def.mem (.var none) (hf.relabel some))
  apply Def.and (Def.mem (.var none) (.param d))
  let vals := fun i (v : Option ι → X) => push (v none) (fun j => g j (fun k => v (some k))) i
  apply relativized_def M (D := fun x => x ∈ₛ d)
    (Def.mem (.var ()) (.param d)) (Def.mem (.var false) (.var true)) p vals
  intro i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp only [vals,push_zero,push_succ]
  · exact TermDef.var none
  · exact (hg j).relabel some

theorem extension_exists {n : ℕ} (d : X) (p : DESTReference.Formula (n+1)) (v : Fin n → X) :
    ∃ B, Extension M d p v B := by
  let f := fun i (env : Unit → X) => push (env ()) v i
  have hf (i : Fin (n+1)) : TermDef M.toOperations (f i) := by
    refine Fin.cases ?_ (fun j => ?_) i <;> simp only [f,push_zero,push_succ]
    · exact TermDef.var ()
    · exact TermDef.param (v j)
  exact M.separation d (fun x => Relativized (fun y => y ∈ₛ d) M.mem M.mem p (push x v))
    (relativized_def M (D := fun x => x ∈ₛ d) (Def.mem (.var ()) (.param d))
      (Def.mem (.var false) (.var true)) p f hf)

def extensionQuery {n : ℕ} (d : X) (p : DESTReference.Formula (n+1)) : Query M where
  arity := n
  test := Extension M d p
  definable := defExtension M d p (.var none) (fun i v => v (some i)) (fun i => TermDef.var (some i))

theorem extension_subset {d B : X} {n : ℕ} {p : DESTReference.Formula (n+1)}
    {v : Fin n → X} (h : Extension M d p v B) : ∀ x, x ∈ₛ B → x ∈ₛ d :=
  fun x hx => ((h x).mp hx).1

theorem extension_unique {d B C : X} {n : ℕ} {p : DESTReference.Formula (n+1)}
    {v : Fin n → X} (hB : Extension M d p v B) (hC : Extension M d p v C) : B = C :=
  M.extensionality _ _ (fun x => (hB x).trans (hC x).symm)

def positive {n : ℕ} (p : DESTReference.Formula (n+1)) : Query M where
  arity := n
  test := fun v a => p.eval M.mem M.mem (push a v)
  definable := by
    let f := fun i (v : Option (Fin n) → X) => push (v none) (fun j => v (some j)) i
    apply eval_def M (Def.mem (.var false) (.var true)) p f
    intro i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp only [f,push_zero,push_succ]
    · exact TermDef.var none
    · exact TermDef.var (some j)

def represents {n : ℕ} (p : DESTReference.Formula (n+1)) (v : Fin n → X) (a : X) : Prop :=
  ∀ y, y ∈ₛ a ↔ p.eval M.mem M.mem (push y v)

def representative {n : ℕ} (p : DESTReference.Formula (n+1)) : Query M where
  arity := n
  test := represents M p
  definable := by
    unfold represents
    apply Def.all
    apply Def.iff (Def.mem (.var none) (.var (some none)))
    let f := fun i (v : Option (Option (Fin n)) → X) => push (v none) (fun j => v (some (some j))) i
    apply eval_def M (Def.mem (.var false) (.var true)) p f
    intro i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp only [f,push_zero,push_succ]
    · exact TermDef.var none
    · exact TermDef.var (some (some j))

def outsideVal {n : ℕ} (u b : X) (v : Fin n → X) : Fin (n+2) → X :=
  push u (push b v)

def outside {n : ℕ} (p : DESTReference.Formula (n+1)) : Query M where
  arity := n+2
  test := fun v a =>
    p.eval M.mem M.mem (push a (fun i => v i.succ.succ)) ∧
      ¬ a ∈ₛ v 0 ∧ ¬ a ∈ₛ v (0 : Fin (n+1)).succ
  definable := by
    apply Def.and
    · let f := fun i (v : Option (Fin (n+2)) → X) => push (v none) (fun j => v (some j.succ.succ)) i
      apply eval_def M (Def.mem (.var false) (.var true)) p f
      intro i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp only [f,push_zero,push_succ]
      · exact TermDef.var none
      · exact TermDef.var (some j.succ.succ)
    · exact Def.and (Def.mem (.var none) (.var (some 0))).not
        (Def.mem (.var none) (.var (some (0 : Fin (n+1)).succ))).not

theorem outside_eval {n : ℕ} (p : DESTReference.Formula (n+1)) (u b a : X) (v : Fin n → X) :
    (outside M p).test (outsideVal u b v) a ↔
      p.eval M.mem M.mem (push a v) ∧ ¬ a ∈ₛ u ∧ ¬ a ∈ₛ b := by
  simp only [outside, outsideVal, push_succ, push_zero]

theorem union_two (a b : X) : ∃ c, ∀ x, x ∈ₛ c ↔ x ∈ₛ a ∨ x ∈ₛ b := by
  obtain ⟨c,hc⟩ := M.union_set (M.insert a (single M b))
  refine ⟨c, ?_⟩
  intro x
  rw [hc]
  constructor
  · rintro ⟨v,hv,hx⟩
    rcases (M.mem_insert _ _ _).mp hv with rfl | hv
    · exact Or.inl hx
    · obtain rfl := (mem_single M _ _).mp hv
      exact Or.inr hx
  · rintro (h | h)
    · exact ⟨a,(M.mem_insert _ _ _).mpr (Or.inl rfl),h⟩
    · exact ⟨b,(M.mem_insert _ _ _).mpr (Or.inr ((mem_single M _ _).mpr rfl)),h⟩

theorem outside_exists {n : ℕ} (p : DESTReference.Formula (n+1)) (u b : X) (v : Fin n → X)
    (h : ¬ ∃ a, represents M p v a) :
    ∃ a, (outside M p).test (outsideVal u b v) a := by
  classical
  by_contra he
  apply h
  obtain ⟨u',hu'⟩ := union_two M u b
  let f := fun i (env : Unit → X) => push (env ()) v i
  have hf (i : Fin (n+1)) : TermDef M.toOperations (f i) := by
    refine Fin.cases ?_ (fun j => ?_) i <;> simp only [f,push_zero,push_succ]
    · exact TermDef.var ()
    · exact TermDef.param (v j)
  obtain ⟨a,ha⟩ := M.separation u' (fun y => p.eval M.mem M.mem (push y v))
    (eval_def M (Def.mem (.var false) (.var true)) p f hf)
  refine ⟨a,fun y => ⟨fun hy => ((ha y).mp hy).2, ?_⟩⟩
  intro hy
  have hbound : y ∈ₛ u' := by
    by_contra hn
    apply he
    refine ⟨y, (outside_eval M p u b y v).mpr ⟨hy, ?_, ?_⟩⟩
    · exact fun h => hn ((hu' y).mpr (Or.inl h))
    · exact fun h => hn ((hu' y).mpr (Or.inr h))
  exact (ha y).mpr ⟨hbound,hy⟩

end DESTSet
