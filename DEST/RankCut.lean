import DEST.Model
import Mathlib.Logic.Small.List
import Mathlib.SetTheory.ZFC.VonNeumann

/-! The rank-bounded analogue of the verified countable hull. In Lean,
ZFSet admits collection indexed by small types. The construction below
collects witnesses for the actual first-order syntax. For the ZFC
finite-fragment argument, only finitely many queries are needed. -/
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DESTRank
open DEST

noncomputable def boundNext (o : Ordinal.{0}) : Ordinal.{0} :=
  let C := ZFSet.vonNeumann o
  letI : Small.{0} ↥(C : Set A) := ZFSet.small_coe C
  let f := fun t : Query × List (↥(C : Set A)) =>
    pick (test ∅ t.1 (t.2.map Subtype.val) [])
  Order.succ (max o (ZFSet.rank (ZFSet.range f)))

noncomputable def bound : ℕ → Ordinal.{0}
  | 0 => Order.succ (ZFSet.rank omegaSet)
  | n+1 => boundNext (bound n)

noncomputable def cutSet : A := ZFSet.iUnion (fun n : ℕ => ZFSet.vonNeumann (bound n))
def Cut : Set A := {x | x ∈ cutSet}

theorem bound_le_next (o : Ordinal.{0}) : o ≤ boundNext o := by
  unfold boundNext
  exact (le_max_left _ _).trans (Order.le_succ _)

theorem bound_mono : Monotone bound := by
  apply monotone_nat_of_le_succ
  intro n
  exact bound_le_next (bound n)

theorem mem_cut (x : A) : x ∈ Cut ↔ ∃ n : ℕ, ZFSet.rank x < bound n := by
  change x ∈ cutSet ↔ _
  simp only [cutSet,ZFSet.mem_iUnion,ZFSet.mem_vonNeumann]

theorem cut_subset_closed {x y : A} (hx : x ∈ Cut) (h : y ⊆ x) : y ∈ Cut := by
  obtain ⟨n,hn⟩ := (mem_cut x).mp hx
  exact (mem_cut y).mpr ⟨n,(ZFSet.rank_mono h).trans_lt hn⟩

theorem cut_transitive {x y : A} (hx : x ∈ Cut) (h : y ∈ x) : y ∈ Cut := by
  obtain ⟨n,hn⟩ := (mem_cut x).mp hx
  exact (mem_cut y).mpr ⟨n,(ZFSet.rank_lt_of_mem h).trans hn⟩

theorem omega_in_cut : omegaSet ∈ Cut :=
  (mem_cut _).mpr ⟨0,Order.lt_succ _⟩

theorem seed_in_cut : DEST.seed ⊆ Cut := by
  intro a ha
  rcases ha with ⟨n,rfl⟩ | ha
  · exact cut_transitive omega_in_cut (ZFSet.mem_range_self (f := vn) n)
  · have e : a = omegaSet := Set.mem_singleton_iff.mp ha
    exact e.symm ▸ omega_in_cut

private theorem cut_list_stage (l : List A) (hl : Supported Cut l) :
    ∃ n : ℕ, Supported (ZFSet.vonNeumann (bound n) : Set A) l := by
  induction l with
  | nil => exact ⟨0,by simp [Supported]⟩
  | cons a l ih =>
    obtain ⟨n,hn⟩ := (mem_cut a).mp (hl a (by simp))
    obtain ⟨m,hm⟩ := ih (fun x hx => hl x (List.mem_cons.mpr (Or.inr hx)))
    refine ⟨max n m, supported_cons ?_ ?_⟩
    · exact ZFSet.mem_vonNeumann.mpr (hn.trans_le (bound_mono (le_max_left n m)))
    · intro x hx
      exact ZFSet.mem_vonNeumann.mpr
        ((ZFSet.mem_vonNeumann.mp (hm x hx)).trans_le (bound_mono (le_max_right n m)))

/-- Witness closure of the rank cut, not a postulated reflection hypothesis. -/
theorem cut_witness (q : Query) (l : List A) (hl : Supported Cut l)
    (hex : ∃ x, test ∅ q l [] x) : ∃ x ∈ Cut, test ∅ q l [] x := by
  obtain ⟨n,hn⟩ := cut_list_stage l hl
  obtain ⟨l',hl'⟩ := lift_list l hn
  let C := ZFSet.vonNeumann (bound n)
  letI : Small.{0} ↥(C : Set A) := ZFSet.small_coe C
  let f := fun t : Query × List (↥(C : Set A)) =>
    pick (test ∅ t.1 (t.2.map Subtype.val) [])
  let x := pick (test ∅ q l [])
  have hx : x ∈ ZFSet.range f := by
    refine ZFSet.mem_range.mpr ⟨(q,l'),?_⟩
    change pick (test ∅ q (l'.map Subtype.val) []) = x
    rw [hl']
  refine ⟨x,(mem_cut x).mpr ⟨n+1,?_⟩,pick_spec hex⟩
  change ZFSet.rank x < Order.succ (max (bound n) (ZFSet.rank (ZFSet.range f)))
  exact ((ZFSet.rank_lt_of_mem hx).trans_le (le_max_right _ _)).trans (Order.lt_succ _)

/-- The freshness argument needs boundedness of the cut, not countability.
A definable class confined to a set plus finitely many points has a set
representative by Separation. -/
private noncomputable def listSet : List A → A
  | [] => ∅
  | a::l => insert a (listSet l)

private theorem mem_listSet (a : A) (l : List A) : a ∈ listSet l ↔ a ∈ l := by
  induction l with
  | nil => simp [listSet]
  | cons b l ih => simp [listSet,ZFSet.mem_insert_iff,ih]

theorem cut_unrepresented_fresh (p : Formula) (l banned : List A)
    (hn : ¬ ∃ a : A, ∀ y : A, y ∈ a ↔ truth p (y::l)) :
    ∃ x, test Cut (.outside p) l banned x := by
  classical
  by_contra h
  apply hn
  refine ⟨ZFSet.sep (fun x => truth p (x::l)) (cutSet ∪ listSet banned),?_⟩
  intro y
  rw [ZFSet.mem_sep,ZFSet.mem_union]
  constructor
  · exact fun hy => hy.2
  · intro hy
    refine ⟨?_,hy⟩
    by_cases hc : y ∈ Cut
    · exact Or.inl hc
    · right
      apply (mem_listSet y banned).mpr
      by_contra hb
      exact h ⟨y,hy,hc,hb⟩

end DESTRank
