import DEST.Syntax
import Mathlib.Data.Set.Countable
import Mathlib.Logic.Equiv.List

set_option autoImplicit false
set_option maxHeartbeats 0

namespace DEST

def Supported (D : Set A) (l : List A) : Prop := ∀ x ∈ l, x ∈ D

theorem supported_cons {D : Set A} {a : A} {l : List A}
    (ha : a ∈ D) (hl : Supported D l) : Supported D (a::l) := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact ha
  · exact hl x hx

theorem supported_map (D : Set A) (l : List D) : Supported D (l.map Subtype.val) := by
  intro x hx
  obtain ⟨y,_,rfl⟩ := List.mem_map.mp hx
  exact y.property

theorem lift_list {D : Set A} (l : List A) (h : Supported D l) :
    ∃ k : List D, k.map Subtype.val = l := by
  induction l with
  | nil => exact ⟨[],rfl⟩
  | cons a l ih =>
    have ha : a ∈ D := h a (by simp)
    obtain ⟨k,hk⟩ := ih (fun x hx => h x (List.mem_cons.mpr (Or.inr hx)))
    exact ⟨⟨a,ha⟩::k,by simp [hk]⟩

/-- The additional tests make the representation and trace arguments explicit,
    avoiding any reliance on an informal elementary-submodel hypothesis. -/
inductive Query where
  | counter (p : Formula) : Query
  | rep (p : Formula) : Query
  | diff (p : Formula) : Query
  | outside (p : Formula) : Query
  deriving Countable

def test (avoid : Set A) (q : Query) (l banned : List A) (x : A) : Prop :=
  match q with
  | .counter p => ¬ truth p (x::l)
  | .rep p => ∀ y : A, y ∈ x ↔ truth p (y::l)
  | .diff p => match l with
    | [] => False
    | a::k => ¬ (x ∈ a ↔ truth p (x::k))
  | .outside p => truth p (x::l) ∧ x ∉ avoid ∧ x ∉ banned

noncomputable def pick (P : A → Prop) : A := by
  classical
  exact if h : ∃ x, P x then Classical.choose h else ∅

theorem pick_spec {P : A → Prop} (h : ∃ x, P x) : P (pick P) := by
  classical
  rw [pick, dif_pos h]
  exact Classical.choose_spec h

noncomputable def step (avoid D : Set A) : Set A :=
  D ∪ Set.range (fun t : Query × List D × List D =>
    pick (test avoid t.1 (t.2.1.map Subtype.val) (t.2.2.map Subtype.val)))

theorem step_countable {avoid D : Set A} (h : D.Countable) : (step avoid D).Countable := by
  letI : Countable D := h
  exact h.union (Set.countable_range _)

theorem subset_step (avoid D : Set A) : D ⊆ step avoid D := by
  intro x hx
  exact Or.inl hx

noncomputable def stage (avoid seed : Set A) : ℕ → Set A
  | 0 => seed
  | n+1 => step avoid (stage avoid seed n)

noncomputable def hull (avoid seed : Set A) : Set A := ⋃ n, stage avoid seed n

theorem stage_countable {avoid seed : Set A} (h : seed.Countable) (n : ℕ) :
    (stage avoid seed n).Countable := by
  induction n with
  | zero => exact h
  | succ n ih => exact step_countable ih

theorem hull_countable {avoid seed : Set A} (h : seed.Countable) :
    (hull avoid seed).Countable :=
  Set.countable_iUnion (stage_countable h)

theorem stage_mono (avoid seed : Set A) {n m : ℕ} (h : n ≤ m) :
    stage avoid seed n ⊆ stage avoid seed m := by
  induction m with
  | zero =>
    have h' : n = 0 := by omega
    subst n
    exact fun _ hx => hx
  | succ m ih =>
    by_cases h' : n ≤ m
    · exact fun _ hx => subset_step avoid _ (ih h' hx)
    · have h'' : n = m+1 := by omega
      subst n
      exact fun _ hx => hx

theorem seed_subset_hull (avoid seed : Set A) : seed ⊆ hull avoid seed := by
  intro x hx
  exact Set.mem_iUnion.mpr ⟨0,hx⟩

theorem stage_subset_hull (avoid seed : Set A) (n : ℕ) :
    stage avoid seed n ⊆ hull avoid seed := by
  intro x hx
  exact Set.mem_iUnion.mpr ⟨n,hx⟩

theorem list_stage {avoid seed : Set A} (l : List A)
    (h : Supported (hull avoid seed) l) : ∃ n, Supported (stage avoid seed n) l := by
  induction l with
  | nil => exact ⟨0,by simp [Supported]⟩
  | cons a l ih =>
    obtain ⟨n,hn⟩ := Set.mem_iUnion.mp (h a (by simp))
    obtain ⟨m,hm⟩ := ih (fun x hx => h x (List.mem_cons.mpr (Or.inr hx)))
    refine ⟨max n m,supported_cons (stage_mono avoid seed (le_max_left n m) hn) ?_⟩
    intro x hx
    exact stage_mono avoid seed (le_max_right n m) (hm x hx)

/-- Every successful test over finitely many hull parameters has a witness in
    that same hull. -/
theorem hull_witness {avoid seed : Set A} (q : Query) (l banned : List A)
    (hl : Supported (hull avoid seed) l) (hb : Supported (hull avoid seed) banned)
    (hex : ∃ x, test avoid q l banned x) :
    ∃ x ∈ hull avoid seed, test avoid q l banned x := by
  obtain ⟨n,hn⟩ := list_stage l hl
  obtain ⟨m,hm⟩ := list_stage banned hb
  let d := max n m
  have hn' : Supported (stage avoid seed d) l := fun x hx =>
    stage_mono avoid seed (le_max_left n m) (hn x hx)
  have hm' : Supported (stage avoid seed d) banned := fun x hx =>
    stage_mono avoid seed (le_max_right n m) (hm x hx)
  obtain ⟨l',hl'⟩ := lift_list l hn'
  obtain ⟨b',hb'⟩ := lift_list banned hm'
  refine ⟨pick (test avoid q l banned),?_,pick_spec hex⟩
  apply stage_subset_hull avoid seed (d+1)
  change pick (test avoid q l banned) ∈ step avoid (stage avoid seed d)
  right
  exact ⟨(q,l',b'),by simp [hl',hb']⟩

/-- Tarski–Vaught, proved directly for the chosen syntax. -/
theorem hull_elementary (avoid seed : Set A) (p : Formula) (l : List A)
    (hl : Supported (hull avoid seed) l) :
    p.eval (hull avoid seed) l ↔ truth p l := by
  classical
  induction p generalizing l with
  | bot => rfl
  | eq i j => rfl
  | mem i j => rfl
  | imp p q ihp ihq =>
    change (p.eval (hull avoid seed) l → q.eval (hull avoid seed) l) ↔
      (truth p l → truth q l)
    rw [ihp l hl,ihq l hl]
  | all p ih =>
    change (∀ a ∈ hull avoid seed, p.eval (hull avoid seed) (a::l)) ↔
      (∀ a ∈ (Set.univ : Set A), truth p (a::l))
    constructor
    · intro h a _
      by_contra hn
      obtain ⟨b,hb,hbad⟩ := hull_witness (.counter p) l [] hl
        (by simp [Supported]) ⟨a,hn⟩
      exact hbad ((ih (b::l) (supported_cons hb hl)).mp (h b hb))
    · intro h a ha
      exact (ih (a::l) (supported_cons ha hl)).mpr (h a (by simp))

/-- Any countable family of ambient sets has an ambient set as its extension. -/
theorem countable_represented (S : Set A) (h : S.Countable) :
    ∃ a : A, ∀ y : A, y ∈ a ↔ y ∈ S := by
  classical
  by_cases hs : S.Nonempty
  · obtain ⟨f,hf⟩ := h.exists_eq_range hs
    refine ⟨ZFSet.range f,?_⟩
    intro y
    rw [hf,ZFSet.mem_range] <;> rfl
  · refine ⟨∅,?_⟩
    intro y
    constructor
    · intro hy
      exact (ZFSet.notMem_empty y hy).elim
    · intro hy
      exact (hs ⟨y,hy⟩).elim

private theorem list_countable (l : List A) : ({x : A | x ∈ l} : Set A).Countable := by
  induction l with
  | nil => simpa using (Set.countable_empty : (∅ : Set A).Countable)
  | cons a l ih =>
    have he : ({x : A | x ∈ a::l} : Set A) = insert a {x : A | x ∈ l} := by
      ext x
      simp
    rw [he]
    exact ih.insert a

/-- Unrepresented definable collections cannot be countable. Hence after
    excluding a countable hull and finitely many further objects, one remains. -/
theorem unrepresented_fresh (U : Set A) (hc : U.Countable) (p : Formula) (l banned : List A)
    (hn : ¬ ∃ a : A, ∀ y : A, y ∈ a ↔ truth p (y::l)) :
    ∃ x, test U (.outside p) l banned x := by
  classical
  by_contra h
  apply hn
  let S : Set A := {x | truth p (x::l)}
  have hsub : S ⊆ U ∪ {x : A | x ∈ banned} := by
    intro x hx
    by_cases hu : x ∈ U
    · exact Or.inl hu
    · right
      have hb : x ∈ banned := by
        by_contra hb
        exact h ⟨x,hx,hu,hb⟩
      exact hb
  exact countable_represented S ((hc.union (list_countable banned)).mono hsub)

end DEST
