import DEST.Strength
import Mathlib.Logic.Small.List

/-! Finite-query, set-coded hulls. Only the queries for a fixed finite
    fragment and additional reflection formulas are used. See
    WEAK_METATHEORY.md for the separate proof in ZFC without Power Set.
    Here ZFSet is the Lean realization of the construction, not an encoding
    of derivability in that weaker first-order theory. -/
set_option autoImplicit false
set_option maxHeartbeats 0

namespace DESTWeak
open DEST

/-- Each quantified subformula contributes its counterexample query. -/
def counters : DEST.Formula → List Query
  | .imp p q => counters p ++ counters q
  | .all p => .counter p :: counters p
  | _ => []

def localQueries (p : DEST.Formula) : List Query :=
  [.rep p, .diff p, .counter (.imp p .bot), .outside p] ++ counters p

def queries (ps : List DEST.Formula) : List Query :=
  [.diff (.mem 0 1), .counter (.imp (.mem 0 1) .bot), .outside (.eq 0 0)] ++
    ps.flatMap localQueries

theorem local_mem {ps : List DEST.Formula} {p : DEST.Formula}
    (hp : p ∈ ps) {q : Query} (hq : q ∈ localQueries p) : q ∈ queries ps := by
  unfold queries
  exact List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr ⟨p,hp,hq⟩))

/-- A single step is a set: an indexed range over a finite query list and
    lists of members of the current set. No ambient power set is taken. -/
noncomputable def stepCode (Q : List Query) (avoid d : A) : A :=
  letI : Small.{0} ↥(d : Set A) := ZFSet.small_coe d
  d ∪ ZFSet.range (fun t : {q : Query // q ∈ Q} × List (↥(d : Set A)) × List (↥(d : Set A)) =>
    pick (test (avoid : Set A) t.1.val (t.2.1.map Subtype.val) (t.2.2.map Subtype.val)))

noncomputable def stage (Q : List Query) (avoid seed : A) : ℕ → A
  | 0 => seed
  | n+1 => stepCode Q avoid (stage Q avoid seed n)

noncomputable def code (Q : List Query) (avoid seed : A) : A :=
  ZFSet.iUnion (stage Q avoid seed)

noncomputable abbrev dom (Q : List Query) (avoid seed : A) : Set A := (code Q avoid seed : Set A)

private theorem next_mono (Q : List Query) (avoid d : A) :
    (d : Set A) ⊆ (stepCode Q avoid d : Set A) := by
  intro a ha
  change a ∈ stepCode Q avoid d
  unfold stepCode
  exact ZFSet.mem_union.mpr (Or.inl ha)

private theorem next_countable (Q : List Query) (avoid d : A)
    (h : (d : Set A).Countable) : (stepCode Q avoid d : Set A).Countable := by
  letI : Countable ↥(d : Set A) := h
  have he : (stepCode Q avoid d : Set A) = (d : Set A) ∪
      Set.range (fun t : {q : Query // q ∈ Q} × List (↥(d : Set A)) × List (↥(d : Set A)) =>
        pick (test (avoid : Set A) t.1.val (t.2.1.map Subtype.val) (t.2.2.map Subtype.val))) := by
    ext a
    change a ∈ stepCode Q avoid d ↔ a ∈ d ∨ ∃ t : {q : Query // q ∈ Q} × List (↥(d : Set A)) × List (↥(d : Set A)),
      pick (test (avoid : Set A) t.1.val (t.2.1.map Subtype.val) (t.2.2.map Subtype.val)) = a
    simp only [stepCode,ZFSet.mem_union,ZFSet.mem_range]
  rw [he]
  exact h.union (Set.countable_range _)

private theorem stage_countable (Q : List Query) (avoid seed : A)
    (h : (seed : Set A).Countable) (n : ℕ) : (stage Q avoid seed n : Set A).Countable := by
  induction n with
  | zero => exact h
  | succ n ih => exact next_countable Q avoid _ ih

theorem code_countable (Q : List Query) (avoid seed : A)
    (h : (seed : Set A).Countable) : (dom Q avoid seed).Countable := by
  have he : dom Q avoid seed = ⋃ n, (stage Q avoid seed n : Set A) := by
    ext a
    change a ∈ code Q avoid seed ↔ a ∈ ⋃ n, (stage Q avoid seed n : Set A)
    rw [code, ZFSet.mem_iUnion, Set.mem_iUnion] <;> rfl
  rw [he]
  exact Set.countable_iUnion (stage_countable Q avoid seed h)

private theorem stage_mono (Q : List Query) (avoid seed : A) {n m : ℕ} (h : n ≤ m) :
    (stage Q avoid seed n : Set A) ⊆ (stage Q avoid seed m : Set A) := by
  induction m with
  | zero =>
    have h' : n = 0 := by omega
    subst n
    exact fun _ hx => hx
  | succ m ih =>
    by_cases h' : n ≤ m
    · exact fun _ hx => next_mono Q avoid _ (ih h' hx)
    · have h'' : n = m+1 := by omega
      subst n
      exact fun _ hx => hx

private theorem stage_dom (Q : List Query) (avoid seed : A) (n : ℕ) :
    (stage Q avoid seed n : Set A) ⊆ dom Q avoid seed := by
  intro a ha
  change a ∈ code Q avoid seed
  exact ZFSet.mem_iUnion.mpr ⟨n,ha⟩

theorem seed_dom (Q : List Query) (avoid seed : A) : (seed : Set A) ⊆ dom Q avoid seed :=
  stage_dom Q avoid seed 0

private theorem list_stage (Q : List Query) (avoid seed : A) (l : List A)
    (h : Supported (dom Q avoid seed) l) :
    ∃ n, Supported (stage Q avoid seed n : Set A) l := by
  induction l with
  | nil => exact ⟨0,by simp [Supported]⟩
  | cons a l ih =>
    have ha : a ∈ code Q avoid seed := h a (by simp)
    obtain ⟨n,hn⟩ := ZFSet.mem_iUnion.mp (show a ∈ ZFSet.iUnion (stage Q avoid seed) from ha)
    obtain ⟨m,hm⟩ := ih (fun x hx => h x (List.mem_cons.mpr (Or.inr hx)))
    refine ⟨max n m,supported_cons (stage_mono Q avoid seed (le_max_left n m) hn) ?_⟩
    intro x hx
    exact stage_mono Q avoid seed (le_max_right n m) (hm x hx)

/-- Closure for precisely the supplied queries, not for a truth predicate
    for all formulas over a proper class. -/
theorem witness (Q : List Query) (avoid seed : A) (q : Query) (hq : q ∈ Q)
    (l banned : List A) (hl : Supported (dom Q avoid seed) l)
    (hb : Supported (dom Q avoid seed) banned)
    (hex : ∃ x, test (avoid : Set A) q l banned x) :
    ∃ x ∈ dom Q avoid seed, test (avoid : Set A) q l banned x := by
  obtain ⟨n,hn⟩ := list_stage Q avoid seed l hl
  obtain ⟨m,hm⟩ := list_stage Q avoid seed banned hb
  let d := max n m
  have hn' : Supported (stage Q avoid seed d : Set A) l := fun x hx =>
    stage_mono Q avoid seed (le_max_left n m) (hn x hx)
  have hm' : Supported (stage Q avoid seed d : Set A) banned := fun x hx =>
    stage_mono Q avoid seed (le_max_right n m) (hm x hx)
  obtain ⟨l',hl'⟩ := lift_list l hn'
  obtain ⟨b',hb'⟩ := lift_list banned hm'
  refine ⟨pick (test (avoid : Set A) q l banned),?_,pick_spec hex⟩
  apply stage_dom Q avoid seed (d+1)
  change pick (test (avoid : Set A) q l banned) ∈ stepCode Q avoid (stage Q avoid seed d)
  simp only [stepCode,ZFSet.mem_union,ZFSet.mem_range]
  exact Or.inr ⟨(⟨q,hq⟩,l',b'),by simp [hl',hb']⟩

/-- Tarski–Vaught for a single fixed formula and its finite query list. -/
theorem reflect (Q : List Query) (avoid seed : A) (p : DEST.Formula)
    (hq : ∀ q ∈ counters p, q ∈ Q) (l : List A)
    (hl : Supported (dom Q avoid seed) l) :
    p.eval (dom Q avoid seed) l ↔ truth p l := by
  classical
  induction p generalizing l with
  | bot => rfl
  | eq i j => rfl
  | mem i j => rfl
  | imp p q ihp ihq =>
    change (p.eval (dom Q avoid seed) l → q.eval (dom Q avoid seed) l) ↔
      (truth p l → truth q l)
    rw [ihp (fun t ht => hq t (List.mem_append.mpr (Or.inl ht))) l hl,
      ihq (fun t ht => hq t (List.mem_append.mpr (Or.inr ht))) l hl]
  | all p ih =>
    change (∀ a ∈ dom Q avoid seed, p.eval (dom Q avoid seed) (a::l)) ↔
      (∀ a ∈ (Set.univ : Set A), truth p (a::l))
    have hc : ∀ q ∈ counters p, q ∈ Q := fun q h => hq q (List.mem_cons.mpr (Or.inr h))
    constructor
    · intro h a _
      by_contra hn
      obtain ⟨b,hb,hbad⟩ := witness Q avoid seed (.counter p)
        (hq _ (by simp [counters])) l [] hl (by simp [Supported]) ⟨a,hn⟩
      exact hbad ((ih hc (b::l) (supported_cons hb hl)).mp (h b hb))
    · intro h a ha
      exact (ih hc (a::l) (supported_cons ha hl)).mpr (h a (by simp))

/-- Separation on the actual set code plus a finite list, instead of
    the stronger assertion that arbitrary external countable classes are sets. -/
private noncomputable def listCode : List A → A
  | [] => ∅
  | a::l => insert a (listCode l)

private theorem mem_listCode (a : A) (l : List A) : a ∈ listCode l ↔ a ∈ l := by
  induction l with
  | nil => simp [listCode]
  | cons b l ih => simp [listCode,ZFSet.mem_insert_iff,ih]

theorem unrepresented_fresh (u : A) (p : DEST.Formula) (l banned : List A)
    (hn : ¬ ∃ a : A, ∀ y : A, y ∈ a ↔ truth p (y::l)) :
    ∃ x, test (u : Set A) (.outside p) l banned x := by
  classical
  by_contra h
  apply hn
  refine ⟨ZFSet.sep (fun x => truth p (x::l)) (u ∪ listCode banned),?_⟩
  intro y
  rw [ZFSet.mem_sep,ZFSet.mem_union]
  constructor
  · exact fun hy => hy.2
  · intro hy
    refine ⟨?_,hy⟩
    by_cases hu : y ∈ u
    · exact Or.inl hu
    · right
      apply (mem_listCode y banned).mpr
      by_contra hb
      exact h ⟨y,hy,hu,hb⟩

end DESTWeak
