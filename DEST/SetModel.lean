import DEST.SetLanguage

/-! The set operations and schemes used by the internal argument. All
separation, collection and induction refer to first-order definability. -/
set_option autoImplicit false
set_option maxHeartbeats 0

universe u

namespace DESTSet

variable {X : Type u}

def pair (o : Operations X) (z a b : X) : X :=
  o.insert (o.insert a z) (o.insert (o.insert a (o.insert b z)) z)

def Entry (o : Operations X) (z g a b : X) : Prop := o.mem (pair o z a b) g

structure Model (X : Type u) extends Operations X where
  zero : X
  omega : X
  empty : ∀ x, ¬ mem x zero
  mem_insert : ∀ x a b, mem x (insert a b) ↔ x = a ∨ mem x b
  extensionality : ∀ a b, (∀ x, mem x a ↔ mem x b) → a = b
  foundation : ∀ a, (∃ x, mem x a) → ∃ x, mem x a ∧ ∀ y, mem y a → ¬ mem y x
  zero_mem : mem zero omega
  succ_mem : ∀ n, mem n omega → mem (insert n n) omega
  omega_least : ∀ a, mem zero a → (∀ n, mem n a → mem (insert n n) a) →
    ∀ n, mem n omega → mem n a
  union_set : ∀ a, ∃ b, ∀ x, mem x b ↔ ∃ c, mem c a ∧ mem x c
  separation : ∀ (a : X) (P : X → Prop), UnaryDef toOperations P →
    ∃ b, ∀ x, mem x b ↔ mem x a ∧ P x
  collection : ∀ (a : X) (R : X → X → Prop), BinaryDef toOperations R →
    (∀ x, mem x a → ∃ y, R x y) → ∃ b, ∀ x, mem x a → ∃ y, mem y b ∧ R x y
  lt_asymm : ∀ a b, lt a b → ¬ lt b a
  least_def : ∀ (P : X → Prop), UnaryDef toOperations P → (∃ a, P a) →
    ∃ a, P a ∧ ∀ b, P b → a = b ∨ lt a b

section Model

variable (M : Model X)
local infix:50 " ∈ₛ " => M.mem

abbrev succ (a : X) : X := M.insert a a
abbrev single (a : X) : X := M.insert a M.zero
abbrev entry (g a b : X) : Prop := Entry M.toOperations M.zero g a b

@[simp] theorem mem_single (a b : X) : a ∈ₛ single M b ↔ a = b := by
  rw [M.mem_insert]
  simp [M.empty]

@[simp] theorem mem_succ (a b : X) : a ∈ₛ succ M b ↔ a = b ∨ a ∈ₛ b :=
  M.mem_insert a b b

theorem mem_irrefl (a : X) : ¬ a ∈ₛ a := by
  intro ha
  obtain ⟨x,hx,h⟩ := M.foundation (single M a) ⟨a,(mem_single M _ _).mpr rfl⟩
  obtain rfl : x = a := (mem_single M _ _).mp hx
  exact h _ hx ha

theorem mem_asymm {a b : X} (hab : a ∈ₛ b) : ¬ b ∈ₛ a := by
  intro hba
  let d := M.insert a (single M b)
  have ha : a ∈ₛ d := (M.mem_insert _ _ _).mpr (Or.inl rfl)
  have hb : b ∈ₛ d := (M.mem_insert _ _ _).mpr (Or.inr ((mem_single M _ _).mpr rfl))
  obtain ⟨x,hx,h⟩ := M.foundation d ⟨a,ha⟩
  rcases (M.mem_insert _ _ _).mp hx with hxa | hxb
  · subst x
    exact h b hb hba
  · obtain rfl : x = b := (mem_single M _ _).mp hxb
    exact h a ha hab

theorem succ_injective : Function.Injective (succ M) := by
  intro a b e
  by_contra ne
  have ha : a ∈ₛ succ M b := e ▸ (mem_succ M a a).mpr (Or.inl rfl)
  have hb : b ∈ₛ succ M a := e.symm ▸ (mem_succ M b b).mpr (Or.inl rfl)
  exact mem_asymm M ((mem_succ M _ _).mp ha |>.resolve_left ne)
    ((mem_succ M _ _).mp hb |>.resolve_left (Ne.symm ne))

theorem succ_ne_zero (a : X) : succ M a ≠ M.zero := by
  intro h
  exact M.empty a (h ▸ (mem_succ M a a).mpr (Or.inl rfl))

theorem pair_inj {a b c d : X}
    (h : pair M.toOperations M.zero a b = pair M.toOperations M.zero c d) :
    a = c ∧ b = d := by
  have common (x y t : X) :
      (∀ q, q ∈ₛ pair M.toOperations M.zero x y → t ∈ₛ q) ↔ t = x := by
    constructor
    · intro hq
      exact (mem_single M _ _).mp (hq (single M x) ((M.mem_insert _ _ _).mpr (Or.inl rfl)))
    · intro et q hq
      subst t
      change q ∈ₛ M.insert (single M x) (single M (M.insert x (single M y))) at hq
      rcases (M.mem_insert _ _ _).mp hq with e | e
      · exact e.symm ▸ (mem_single M _ _).mpr rfl
      · have e' := (mem_single M _ _).mp e
        exact e'.symm ▸ (M.mem_insert _ _ _).mpr (Or.inl rfl)
  have e : a = c := (common c d a).mp (h ▸ (common a b a).mpr rfl)
  subst c
  have contains (x y t : X) :
      (∃ q, q ∈ₛ pair M.toOperations M.zero x y ∧ t ∈ₛ q) ↔ t = x ∨ t = y := by
    constructor
    · rintro ⟨q,hq,ht⟩
      change q ∈ₛ M.insert (single M x) (single M (M.insert x (single M y))) at hq
      rcases (M.mem_insert _ _ _).mp hq with rfl | e
      · exact Or.inl ((mem_single M _ _).mp ht)
      · rw [(mem_single M _ _).mp e] at ht
        simpa only [M.mem_insert, M.empty, or_false] using ht
    · intro ht
      refine ⟨M.insert x (single M y), (M.mem_insert _ _ _).mpr
        (Or.inr ((mem_single M _ _).mpr rfl)), ?_⟩
      simpa only [M.mem_insert, M.empty, or_false] using ht
  refine ⟨rfl, ?_⟩
  have hb := (contains a d b).mp (h ▸ (contains a b b).mpr (Or.inr rfl))
  have hd := (contains a b d).mp (h.symm ▸ (contains a d d).mpr (Or.inr rfl))
  by_cases he : b = a
  · exact hd.elim (fun ha => he.trans ha.symm) Eq.symm
  · exact hb.resolve_left he

theorem pair_eq_iff {a b c d : X} :
    pair M.toOperations M.zero a b = pair M.toOperations M.zero c d ↔ a = c ∧ b = d := by
  constructor
  · exact pair_inj M
  · rintro ⟨rfl,rfl⟩
    rfl

theorem defPair {ι : Type} {f g : (ι → X) → X}
    (hf : TermDef M.toOperations f) (hg : TermDef M.toOperations g) :
    TermDef M.toOperations (fun v => pair M.toOperations M.zero (f v) (g v)) := by
  unfold pair
  exact (hf.insert (.param _)).insert
    ((hf.insert (hg.insert (.param _))).insert (.param _))

theorem defEntry {ι : Type} {f g h : (ι → X) → X}
    (hf : TermDef M.toOperations f) (hg : TermDef M.toOperations g)
    (hh : TermDef M.toOperations h) :
    Def M.toOperations (fun v => entry M (f v) (g v) (h v)) :=
  Def.mem (defPair M hg hh) hf

theorem nat_induction (P : X → Prop) (hP : UnaryDef M.toOperations P)
    (hz : P M.zero) (hs : ∀ n, n ∈ₛ M.omega → P n → P (succ M n)) :
    ∀ n, n ∈ₛ M.omega → P n := by
  obtain ⟨b,hb⟩ := M.separation M.omega P hP
  have hz' : M.zero ∈ₛ b := (hb _).mpr ⟨M.zero_mem,hz⟩
  have hs' : ∀ n, n ∈ₛ b → succ M n ∈ₛ b := by
    intro n hn
    obtain ⟨hom,hn⟩ := (hb _).mp hn
    exact (hb _).mpr ⟨M.succ_mem _ hom,hs _ hom hn⟩
  exact fun n hn => ((hb n).mp (M.omega_least b hz' hs' n hn)).2

def Transitive (a : X) : Prop := ∀ x y, x ∈ₛ y → y ∈ₛ a → x ∈ₛ a

theorem nat_transitive (n : X) (hn : n ∈ₛ M.omega) : Transitive M n := by
  apply nat_induction M (Transitive M) _ _ _ n hn
  · unfold Transitive UnaryDef
    apply Def.all
    apply Def.all
    apply Def.imp
    · exact Def.mem (.var (some none)) (.var none)
    · apply Def.imp
      · exact Def.mem (.var none) (.var (some (some ())))
      · exact Def.mem (.var (some none)) (.var (some (some ())))
  · exact fun _ y _ hy => (M.empty y hy).elim
  · intro a _ ha x y hxy hy
    rcases (mem_succ M _ _).mp hy with rfl | hy
    · exact (mem_succ M _ _).mpr (Or.inr hxy)
    · exact (mem_succ M _ _).mpr (Or.inr (ha _ _ hxy hy))

theorem nat_elements (n : X) (hn : n ∈ₛ M.omega) : ∀ a, a ∈ₛ n → a ∈ₛ M.omega := by
  apply nat_induction M (fun n => ∀ a, a ∈ₛ n → a ∈ₛ M.omega) _ _ _ n hn
  · apply Def.all
    exact Def.imp (Def.mem (.var none) (.var (some ()))) (Def.mem (.var none) (.param _))
  · exact fun a ha => (M.empty a ha).elim
  · intro a ha ih b hb
    rcases (mem_succ M _ _).mp hb with rfl | hb
    · exact ha
    · exact ih _ hb

theorem nat_pred (n : X) (hn : n ∈ₛ M.omega) : n = M.zero ∨ ∃ a, a ∈ₛ M.omega ∧ n = succ M a := by
  apply nat_induction M (fun n => n = M.zero ∨ ∃ a, a ∈ₛ M.omega ∧ n = succ M a) _ _ _ n hn
  · apply Def.or (Def.eq (.var ()) (.param _))
    apply Def.ex
    exact Def.and (Def.mem (.var none) (.param _))
      (Def.eq (.var (some ())) ((TermDef.var none).insert (.var none)))
  · exact Or.inl rfl
  · exact fun a ha _ => Or.inr ⟨a,ha,rfl⟩

theorem nat_eq_zero_or_zero_mem (n : X) (hn : n ∈ₛ M.omega) : n = M.zero ∨ M.zero ∈ₛ n := by
  apply nat_induction M (fun n => n = M.zero ∨ M.zero ∈ₛ n) _ _ _ n hn
  · exact Def.or (Def.eq (.var ()) (.param _)) (Def.mem (.param _) (.var ()))
  · exact Or.inl rfl
  · exact fun a _ ha => Or.inr ((mem_succ M _ _).mpr (ha.imp Eq.symm id))

theorem nat_succ_le_of_mem (b : X) (hb : b ∈ₛ M.omega) :
    ∀ a, a ∈ₛ b → succ M a = b ∨ succ M a ∈ₛ b := by
  apply nat_induction M (fun b => ∀ a, a ∈ₛ b → succ M a = b ∨ succ M a ∈ₛ b) _ _ _ b hb
  · apply Def.all
    apply Def.imp (Def.mem (.var none) (.var (some ())))
    exact Def.or
      (Def.eq ((TermDef.var none).insert (.var none)) (.var (some ())))
      (Def.mem ((TermDef.var none).insert (.var none)) (.var (some ())))
  · exact fun a ha => (M.empty a ha).elim
  · intro b _ ih a ha
    rcases (mem_succ M _ _).mp ha with rfl | ha
    · exact Or.inl rfl
    · exact Or.inr ((mem_succ M _ _).mpr (ih a ha))

theorem nat_compare (a b : X) (ha : a ∈ₛ M.omega) (hb : b ∈ₛ M.omega) :
    a ∈ₛ b ∨ a = b ∨ b ∈ₛ a := by
  apply nat_induction M (fun a => a ∈ₛ b ∨ a = b ∨ b ∈ₛ a) _ _ _ a ha
  · exact Def.or (Def.mem (.var ()) (.param b))
      (Def.or (Def.eq (.var ()) (.param b)) (Def.mem (.param b) (.var ())))
  · rcases nat_eq_zero_or_zero_mem M b hb with h | h
    · exact Or.inr (Or.inl h.symm)
    · exact Or.inl h
  · intro a _ ih
    rcases ih with h | h | h
    · rcases nat_succ_le_of_mem M b hb a h with e | e
      · exact Or.inr (Or.inl e)
      · exact Or.inl e
    · exact Or.inr (Or.inr ((mem_succ M _ _).mpr (Or.inl h.symm)))
    · exact Or.inr (Or.inr ((mem_succ M _ _).mpr (Or.inr h)))

theorem least_number (P : X → Prop) (hP : UnaryDef M.toOperations P)
    (h : ∃ n, n ∈ₛ M.omega ∧ P n) :
    ∃ n, n ∈ₛ M.omega ∧ P n ∧ ∀ k, k ∈ₛ M.omega → P k → ¬ k ∈ₛ n := by
  obtain ⟨a,ha⟩ := M.separation M.omega P hP
  obtain ⟨n,hn⟩ := h
  obtain ⟨k,hk,hmin⟩ := M.foundation a ⟨n,(ha n).mpr hn⟩
  obtain ⟨hw,hp⟩ := (ha k).mp hk
  exact ⟨k,hw,hp,fun i hi hp => hmin i ((ha i).mpr ⟨hi,hp⟩)⟩

theorem def_image (a : X) (R : X → X → Prop) (hR : BinaryDef M.toOperations R)
    (h : ∀ x, x ∈ₛ a → ∃! y, R x y) :
    ∃ b, ∀ y, y ∈ₛ b ↔ ∃ x, x ∈ₛ a ∧ R x y := by
  obtain ⟨c,hc⟩ := M.collection a R hR (fun x hx => (h x hx).exists)
  have hdef : UnaryDef M.toOperations (fun y => ∃ x, x ∈ₛ a ∧ R x y) := by
    apply Def.ex
    exact Def.and (Def.mem (.var none) (.param a))
      (Def.app₂ hR (.var none) (.var (some ())))
  obtain ⟨b,hb⟩ := M.separation c _ hdef
  refine ⟨b,fun y => ⟨fun hy => ((hb y).mp hy).2,?_⟩⟩
  rintro ⟨x,hx,hy⟩
  obtain ⟨z,hzc,hz⟩ := hc x hx
  obtain ⟨w,_,hu⟩ := h x hx
  have e : z = y := (hu _ hz).trans (hu _ hy).symm
  exact (hb y).mpr ⟨e ▸ hzc, ⟨x,hx,hy⟩⟩

end Model

end DESTSet
