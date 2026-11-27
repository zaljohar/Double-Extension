import DEST.SetModel

/-! Definable recursion through the internal natural numbers of a set model.
A history is an actual set of the model. The result is a definable class graph. -/
set_option autoImplicit false
set_option maxHeartbeats 0

universe u

namespace DESTSet

variable {X : Type u} (M : Model X)
local infix:50 " ∈ₛ " => M.mem

macro "set_logic" : tactic => `(tactic|
  repeat' (first
    | assumption
    | apply Def.all
    | apply Def.ex
    | apply Def.iff
    | apply Def.and
    | apply Def.or
    | apply Def.imp
    | apply Def.eq
    | apply defEntry
    | apply Def.mem
    | apply Def.lt
    | apply Def.top
    | apply Def.bot
    | apply defPair
    | apply TermDef.insert
    | apply TermDef.var
    | apply TermDef.param))

theorem entry_insert {g a b x y : X} :
    entry M (M.insert (pair M.toOperations M.zero a b) g) x y ↔
      (x = a ∧ y = b) ∨ entry M g x y := by
  unfold entry Entry
  rw [M.mem_insert, pair_eq_iff M]

theorem entry_single {a b x y : X} :
    entry M (single M (pair M.toOperations M.zero a b)) x y ↔ x = a ∧ y = b := by
  unfold entry Entry
  rw [mem_single M, pair_eq_iff M]

def History (Good : X → Prop) (Step : X → X → X → Prop) (start n g : X) : Prop :=
  entry M g M.zero start ∧
  (∀ k, k ∈ₛ succ M n → ∃ a, entry M g k a) ∧
  (∀ k a, entry M g k a → k ∈ₛ succ M n ∧ Good a) ∧
  (∀ k a b, entry M g k a → entry M g k b → a = b) ∧
  (∀ k, k ∈ₛ n → ∀ a b, entry M g k a → entry M g (succ M k) b → Step k a b)

def Run (Good : X → Prop) (Step : X → X → X → Prop) (start n a : X) : Prop :=
  n ∈ₛ M.omega ∧ ∃ g, History M Good Step start n g ∧ entry M g n a

variable {Good : X → Prop} {Step : X → X → X → Prop} {start : X}

theorem def_history (hG : UnaryDef M.toOperations Good) (hS : TernaryDef M.toOperations Step) :
    BinaryDef M.toOperations (History M Good Step start) := by
  unfold BinaryDef History
  set_logic
  · apply Def.app₁ hG
    set_logic
  · apply Def.app₃ hS
    set_logic

theorem def_run (hG : UnaryDef M.toOperations Good) (hS : TernaryDef M.toOperations Step) :
    BinaryDef M.toOperations (Run M Good Step start) := by
  unfold BinaryDef Run
  apply Def.and (Def.mem (.var false) (.param _))
  apply Def.ex
  apply Def.and
  · exact Def.app₂ (def_history M (start := start) hG hS) (.var (some false)) (.var none)
  · exact defEntry M (.var none) (.var (some false)) (.var (some true))

theorem history_zero (hz : Good start) :
    History M Good Step start M.zero (single M (pair M.toOperations M.zero M.zero start)) := by
  refine ⟨(entry_single M).mpr ⟨rfl,rfl⟩, ?_, ?_, ?_, ?_⟩
  · intro k hk
    have h : k = M.zero := ((mem_succ M _ _).mp hk).resolve_right (M.empty k)
    exact ⟨start,(entry_single M).mpr ⟨h,rfl⟩⟩
  · intro k a h
    obtain ⟨rfl,rfl⟩ := (entry_single M).mp h
    exact ⟨(mem_succ M _ _).mpr (Or.inl rfl), hz⟩
  · intro k a b h₁ h₂
    exact ((entry_single M).mp h₁).2.trans ((entry_single M).mp h₂).2.symm
  · intro k hk
    exact (M.empty k hk).elim

theorem history_succ {n g a b : X} (hn : n ∈ₛ M.omega)
    (h : History M Good Step start n g) (ha : entry M g n a)
    (hb : Step n a b) (hGood : Good b) :
    History M Good Step start (succ M n)
      (M.insert (pair M.toOperations M.zero (succ M n) b) g) := by
  obtain ⟨hz,htotal,hcover,hfun,hstep⟩ := h
  have hnew : ¬ succ M n ∈ₛ succ M n := mem_irrefl M _
  have old_ne {k : X} (hk : k ∈ₛ succ M n) : k ≠ succ M n := by
    rintro rfl
    exact hnew hk
  refine ⟨(entry_insert M).mpr (Or.inr hz), ?_, ?_, ?_, ?_⟩
  · intro k hk
    rcases (mem_succ M _ _).mp hk with rfl | hk
    · exact ⟨b, (entry_insert M).mpr (Or.inl ⟨rfl,rfl⟩)⟩
    · obtain ⟨v,hv⟩ := htotal k hk
      exact ⟨v,(entry_insert M).mpr (Or.inr hv)⟩
  · intro k v hv
    rcases (entry_insert M).mp hv with ⟨rfl,rfl⟩ | hv
    · exact ⟨(mem_succ M _ _).mpr (Or.inl rfl), hGood⟩
    · obtain ⟨hk,hv⟩ := hcover k v hv
      exact ⟨(mem_succ M _ _).mpr (Or.inr hk),hv⟩
  · intro k v w hv hw
    rcases (entry_insert M).mp hv with ⟨rfl,rfl⟩ | hv
    · rcases (entry_insert M).mp hw with h | hw
      · exact h.2.symm
      · exact (hnew (hcover _ _ hw).1).elim
    · rcases (entry_insert M).mp hw with h | hw
      · exact (old_ne (hcover _ _ hv).1 h.1).elim
      · exact hfun _ _ _ hv hw
  · intro k hk v w hv hw
    have hv' : entry M g k v := ((entry_insert M).mp hv).resolve_left
      (fun e => old_ne hk e.1)
    rcases (mem_succ M _ _).mp hk with rfl | hk
    · have hw' := ((entry_insert M).mp hw).resolve_right (fun e => hnew (hcover _ _ e).1)
      rw [hfun _ v a hv' ha, hw'.2]
      exact hb
    · have hs : succ M k ∈ₛ succ M n := (mem_succ M _ _).mpr (nat_succ_le_of_mem M _ hn _ hk)
      have hw' := ((entry_insert M).mp hw).resolve_left (fun e => old_ne hs e.1)
      exact hstep _ hk _ _ hv' hw'

theorem histories_agree (hG : UnaryDef M.toOperations Good) (hS : TernaryDef M.toOperations Step)
    (det : ∀ n a b c, n ∈ₛ M.omega → Good a → Step n a b → Step n a c → b = c)
    {n k g h : X} (hn : n ∈ₛ M.omega) (hk : k ∈ₛ M.omega)
    (hg : History M Good Step start n g) (hh : History M Good Step start k h) :
    ∀ i, i ∈ₛ M.omega → ∀ a b, entry M g i a → entry M h i b → a = b := by
  let P (i : X) := ∀ a b, entry M g i a → entry M h i b → a = b
  have hP : UnaryDef M.toOperations P := by
    unfold UnaryDef P
    set_logic
  apply nat_induction M P hP
  · intro a b ha hb
    exact (hg.2.2.2.1 _ _ _ ha hg.1).trans (hh.2.2.2.1 _ _ _ hb hh.1).symm
  · intro i hi ih a b ha hb
    have prev {j : X} (hj : j ∈ₛ M.omega) (hij : succ M i ∈ₛ succ M j) : i ∈ₛ j := by
      rcases (mem_succ M _ _).mp hij with e | hm
      · exact e ▸ (mem_succ M i i).mpr (Or.inl rfl)
      · exact nat_transitive M _ hj _ _ ((mem_succ M i i).mpr (Or.inl rfl)) hm
    have hin := prev hn (hg.2.2.1 _ _ ha).1
    have hik := prev hk (hh.2.2.1 _ _ hb).1
    obtain ⟨v,hv⟩ := hg.2.1 i ((mem_succ M _ _).mpr (Or.inr hin))
    obtain ⟨w,hw⟩ := hh.2.1 i ((mem_succ M _ _).mpr (Or.inr hik))
    have hEq := ih v w hv hw
    subst w
    exact det i v a b hi (hg.2.2.1 _ _ hv).2
      (hg.2.2.2.2 i hin _ _ hv ha) (hh.2.2.2.2 i hik _ _ hw hb)

theorem run_good {n a : X} (ha : Run M Good Step start n a) : Good a := by
  obtain ⟨_,g,hg,ha⟩ := ha
  exact (hg.2.2.1 _ _ ha).2

theorem run_total (hG : UnaryDef M.toOperations Good) (hS : TernaryDef M.toOperations Step)
    (hz : Good start)
    (ht : ∀ n a, n ∈ₛ M.omega → Good a → ∃ b, Step n a b ∧ Good b) :
    ∀ n, n ∈ₛ M.omega → ∃ a, Run M Good Step start n a := by
  have hdef : UnaryDef M.toOperations (fun n => ∃ g, History M Good Step start n g) := by
    apply Def.ex
    exact Def.app₂ (def_history M (start := start) hG hS) (.var (some ())) (.var none)
  have hh : ∀ n, n ∈ₛ M.omega → ∃ g, History M Good Step start n g := by
    apply nat_induction M _ hdef
    · exact ⟨_,history_zero M hz⟩
    · intro n hn h
      obtain ⟨g,hg⟩ := h
      obtain ⟨a,ha⟩ := hg.2.1 n ((mem_succ M _ _).mpr (Or.inl rfl))
      obtain ⟨b,hb,hbG⟩ := ht n a hn (hg.2.2.1 _ _ ha).2
      exact ⟨_,history_succ M hn hg ha hb hbG⟩
  intro n hn
  obtain ⟨g,hg⟩ := hh n hn
  obtain ⟨a,ha⟩ := hg.2.1 n ((mem_succ M _ _).mpr (Or.inl rfl))
  exact ⟨a,hn,g,hg,ha⟩

theorem run_unique (hG : UnaryDef M.toOperations Good) (hS : TernaryDef M.toOperations Step)
    (det : ∀ n a b c, n ∈ₛ M.omega → Good a → Step n a b → Step n a c → b = c)
    {n a b : X} (ha : Run M Good Step start n a) (hb : Run M Good Step start n b) : a = b := by
  obtain ⟨hn,g,hg,ha⟩ := ha
  obtain ⟨_,h,hh,hb⟩ := hb
  exact histories_agree M hG hS det hn hn hg hh n hn a b ha hb

theorem run_step {n a b : X} (ha : Run M Good Step start n a) (hb : Step n a b) (hB : Good b) :
    Run M Good Step start (succ M n) b := by
  obtain ⟨hn,g,hg,ha⟩ := ha
  exact ⟨M.succ_mem _ hn,_,history_succ M hn hg ha hb hB,(entry_insert M).mpr (Or.inl ⟨rfl,rfl⟩)⟩

end DESTSet
