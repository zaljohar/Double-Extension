import Mathlib.Data.Set.Countable

set_option autoImplicit false
set_option maxHeartbeats 0

namespace DEST

universe u v

/-- Finite partial matching, represented by a list of edges. -/
def Good {A : Type u} {B : Type v} (R : A → B → Prop) (l : List (A × B)) : Prop :=
  (∀ p ∈ l, R p.1 p.2) ∧
  (∀ p ∈ l, ∀ q ∈ l, p.1 = q.1 ↔ p.2 = q.2)

private theorem add_edge {A : Type u} {B : Type v} {R : A → B → Prop}
    {l : List (A × B)} (hl : Good R l) {a : A} {b : B}
    (hab : R a b) (ha : a ∉ l.map Prod.fst) (hb : b ∉ l.map Prod.snd) :
    Good R ((a,b) :: l) := by
  constructor
  · intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hab
    · exact hl.1 p hp
  · intro p hp q hq
    rcases List.mem_cons.mp hp with rfl | hp <;>
      rcases List.mem_cons.mp hq with rfl | hq
    · simp
    · have h₁ : a ≠ q.1 := by
        intro h
        apply ha
        exact List.mem_map.mpr ⟨q, hq, h.symm⟩
      have h₂ : b ≠ q.2 := by
        intro h
        apply hb
        exact List.mem_map.mpr ⟨q, hq, h.symm⟩
      exact ⟨fun h => (h₁ h).elim, fun h => (h₂ h).elim⟩
    · have h₁ : p.1 ≠ a := by
        intro h
        exact ha (List.mem_map.mpr ⟨p, hp, h⟩)
      have h₂ : p.2 ≠ b := by
        intro h
        exact hb (List.mem_map.mpr ⟨p, hp, h⟩)
      exact ⟨fun h => (h₁ h).elim, fun h => (h₂ h).elim⟩
    · exact hl.2 p hp q hq

private theorem extend_left {A : Type u} {B : Type v} {R : A → B → Prop}
    (fresh : ∀ a : A, ∀ l : List B, ∃ b, b ∉ l ∧ R a b)
    (l : List (A × B)) (hl : Good R l) (a : A) :
    ∃ k : List (A × B), Good R k ∧ (∀ p ∈ l, p ∈ k) ∧ ∃ b, (a,b) ∈ k := by
  classical
  by_cases ha : a ∈ l.map Prod.fst
  · obtain ⟨p,hp,he⟩ := List.mem_map.mp ha
    rcases p with ⟨x,y⟩
    change x = a at he
    subst x
    exact ⟨l,hl,fun _ h => h,y,hp⟩
  · obtain ⟨b,hb,hr⟩ := fresh a (l.map Prod.snd)
    exact ⟨(a,b)::l,add_edge hl hr ha hb,
      fun p hp => List.mem_cons.mpr (Or.inr hp),b,List.mem_cons.mpr (Or.inl rfl)⟩

private theorem extend_right {A : Type u} {B : Type v} {R : A → B → Prop}
    (fresh : ∀ b : B, ∀ l : List A, ∃ a, a ∉ l ∧ R a b)
    (l : List (A × B)) (hl : Good R l) (b : B) :
    ∃ k : List (A × B), Good R k ∧ (∀ p ∈ l, p ∈ k) ∧ ∃ a, (a,b) ∈ k := by
  classical
  by_cases hb : b ∈ l.map Prod.snd
  · obtain ⟨p,hp,he⟩ := List.mem_map.mp hb
    rcases p with ⟨x,y⟩
    change y = b at he
    subst y
    exact ⟨l,hl,fun _ h => h,x,hp⟩
  · obtain ⟨a,ha,hr⟩ := fresh b (l.map Prod.fst)
    exact ⟨(a,b)::l,add_edge hl hr ha hb,
      fun p hp => List.mem_cons.mpr (Or.inr hp),a,List.mem_cons.mpr (Or.inl rfl)⟩

/-- A countable back-and-forth construction with finite avoidance on both sides. -/
theorem countable_matching {A : Type u} {B : Type v} [Countable A] [Countable B]
    [Nonempty A] [Nonempty B] (R : A → B → Prop)
    (left : ∀ a : A, ∀ l : List B, ∃ b, b ∉ l ∧ R a b)
    (right : ∀ b : B, ∀ l : List A, ∃ a, a ∉ l ∧ R a b) :
    ∃ e : A ≃ B, ∀ a, R a (e a) := by
  classical
  obtain ⟨ea, hea⟩ := exists_surjective_nat A
  obtain ⟨eb, heb⟩ := exists_surjective_nat B
  let P := {l : List (A × B) // Good R l}
  have step (n : ℕ) (l : P) : ∃ k : P,
      (∀ p ∈ l.val, p ∈ k.val) ∧ (∃ b, (ea n,b) ∈ k.val) ∧ (∃ a, (a,eb n) ∈ k.val) := by
    obtain ⟨k,hk,hsub,b,hb⟩ := extend_left left l.val l.property (ea n)
    obtain ⟨j,hj,hsub',a,ha⟩ := extend_right right k hk (eb n)
    exact ⟨⟨j,hj⟩,fun p hp => hsub' p (hsub p hp),⟨b,hsub' _ hb⟩,⟨a,ha⟩⟩
  let next (n : ℕ) (l : P) : P := Classical.choose (step n l)
  have hn (n : ℕ) (l : P) := Classical.choose_spec (step n l)
  let start : P := ⟨[], by simp [Good]⟩
  let c : ℕ → P := Nat.rec start (fun n l => next n l)
  have succ (n : ℕ) : c (n+1) = next n (c n) := rfl
  have inc (n : ℕ) : ∀ p ∈ (c n).val, p ∈ (c (n+1)).val := by
    rw [succ]
    exact (hn n (c n)).1
  have mono (n m : ℕ) (h : n ≤ m) : ∀ p ∈ (c n).val, p ∈ (c m).val := by
    induction m with
    | zero =>
      have h' : n = 0 := by omega
      subst n
      exact fun _ hp => hp
    | succ m ih =>
      by_cases h' : n ≤ m
      · exact fun p hp => inc m p (ih h' p hp)
      · have h'' : n = m+1 := by omega
        subst n
        exact fun _ hp => hp
  let G (a : A) (b : B) : Prop := ∃ n, (a,b) ∈ (c n).val
  have total (a : A) : ∃ b, G a b := by
    obtain ⟨n,rfl⟩ := hea a
    obtain ⟨b,hb⟩ := (hn n (c n)).2.1
    exact ⟨b,n+1,by rw [succ]; exact hb⟩
  have onto (b : B) : ∃ a, G a b := by
    obtain ⟨n,rfl⟩ := heb b
    obtain ⟨a,ha⟩ := (hn n (c n)).2.2
    exact ⟨a,n+1,by rw [succ]; exact ha⟩
  have functional {a a' : A} {b b' : B} (h : G a b) (h' : G a' b') :
      a = a' ↔ b = b' := by
    obtain ⟨n,hn'⟩ := h
    obtain ⟨m,hm'⟩ := h'
    exact (c (max n m)).property.2 (a,b) (mono n _ (le_max_left _ _) _ hn')
      (a',b') (mono m _ (le_max_right _ _) _ hm')
  let f : A → B := fun a => Classical.choose (total a)
  have hf (a : A) : G a (f a) := Classical.choose_spec (total a)
  have bij : Function.Bijective f := by
    constructor
    · intro a a' h
      exact (functional (hf a) (hf a')).2 h
    · intro b
      obtain ⟨a,ha⟩ := onto b
      exact ⟨a,(functional (hf a) ha).1 rfl⟩
  refine ⟨Equiv.ofBijective f bij,?_⟩
  intro a
  obtain ⟨n,h⟩ := hf a
  exact (c n).property.1 (a,f a) h

end DEST
