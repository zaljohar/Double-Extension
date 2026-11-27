import DEST.SetExtensions
import DEST.SetMatching

set_option autoImplicit false
set_option maxHeartbeats 0

universe u

namespace DESTSet

open DESTReference

variable {X : Type u} {M : Model X} {qs : List DESTStrength.Unary} {s : Sentence}
variable (C : Regions M qs s)
local infix:50 " ∈ₛ " => M.mem

def Allowed (a b : X) : Prop := a ≠ b ∧ (Protected C b → a ∈ₛ b)

theorem def_allowed : BinaryDef M.toOperations (Allowed C) := by
  unfold Allowed BinaryDef
  exact Def.and (Def.eq (.var false) (.var true)).not
    (Def.imp (Def.app₁ (def_requested C.d C.u qs) (.var true))
      (Def.mem (.var false) (.var true)))

theorem fresh_single (a : X) (b : X) (hb : b ∈ₛ C.d) :
    ∃ x, LeftClass C x ∧ ¬ x ∈ₛ b ∧ RightClass C (single M x) ∧ Allowed C a (single M x) := by
  classical
  have hx : ∃ x, LeftClass C x ∧ ¬ x ∈ₛ b ∧ a ≠ single M x := by
    by_cases ha : ∃ x, x ∈ₛ C.d ∧ a = single M x
    · obtain ⟨x,hx,he⟩ := ha
      obtain ⟨y,hy,hyu,hyb⟩ := C.fresh (M.insert x b) (C.insert_d _ _ hx hb)
      have hn := fun h : y = x => hyb ((M.mem_insert _ _ _).mpr (Or.inl h))
      refine ⟨y,⟨hy,hyu⟩,fun h => hyb ((M.mem_insert _ _ _).mpr (Or.inr h)),?_⟩
      exact fun h => hn (single_injective (h.symm.trans he))
    · obtain ⟨y,hy,hyu,hyb⟩ := C.fresh b hb
      exact ⟨y,⟨hy,hyu⟩,hyb,fun he => ha ⟨y,hy,he⟩⟩
  obtain ⟨x,hx,hxb,he⟩ := hx
  exact ⟨x,hx,hxb,C.singleton_right hx,he,fun h => (C.singleton_not_protected hx h).elim⟩

theorem fresh_point {b : X} (hb : RightClass C b) (ban : X) (hban : ban ∈ₛ C.d) :
    ∃ a, LeftClass C a ∧ ¬ a ∈ₛ ban ∧ Allowed C a b := by
  classical
  by_cases hp : Protected C b
  · have hnot := C.protected_not_in hb.1 hp
    obtain ⟨q,hq,v,hv,he⟩ := hp
    have hargs := fun i => C.u_sub (hv i)
    obtain ⟨a,ha,ha',hau,han⟩ := C.outside q
      (request_mem (s := s) q hq (by simp)) ban hban v hargs (C.protected_proper q hq v hv hb.1 he)
    exact ⟨a,⟨ha,hau⟩,han,fun eq => hnot (eq ▸ ha),fun _ =>
      (he a).mpr ⟨ha,(C.ambient q hq v hargs a ha).mpr ha'⟩⟩
  · by_cases hd : b ∈ₛ C.d
    · obtain ⟨a,ha,hau,hb'⟩ := C.fresh (M.insert b ban) (C.insert_d _ _ hd hban)
      exact ⟨a,⟨ha,hau⟩,fun h => hb' ((M.mem_insert _ _ _).mpr (Or.inr h)),
        fun h => hb' ((M.mem_insert _ _ _).mpr (Or.inl h)),fun h => (hp h).elim⟩
    · obtain ⟨a,ha,hau,hab⟩ := C.fresh ban hban
      exact ⟨a,⟨ha,hau⟩,hab,fun h => hd (h ▸ ha),fun h => (hp h).elim⟩

structure Assignment where
  graph : X → X → Prop
  def_graph : BinaryDef M.toOperations graph
  input : ∀ a B, graph a B → a ∈ₛ C.d
  output_subset : ∀ a B, graph a B → ∀ y, y ∈ₛ B → y ∈ₛ C.d
  total : ∀ a, a ∈ₛ C.d → ∃ B, graph a B
  functional : ∀ a B B', graph a B → graph a B' → B = B'
  injective : ∀ a a' B, graph a B → graph a' B → a = a'
  fixed : ∀ a, graph a a ↔ a ∈ₛ C.u
  onto_right : ∀ B, RightClass C B → ∃ a, graph a B
  protected_match : ∀ a B, graph a B → Protected C B → ¬ a ∈ₛ C.u → a ∈ₛ B

theorem assignment (hr : CofinalReflection M) (hc : InternallyCountable M) :
    Nonempty (Assignment C) := by
  classical
  obtain ⟨l,t,hl,ht⟩ := C.left_and_right_sets hr
  obtain ⟨a,ha,hau,_⟩ := C.fresh M.zero C.zero_in
  obtain ⟨e,he⟩ := hc l ⟨a,(hl a).mpr ⟨ha,hau⟩⟩
  obtain ⟨f,hf⟩ := hc t ⟨single M a,(ht _).mpr (C.singleton_right ⟨ha,hau⟩)⟩
  let P : MatchingProblem M := {
    carrier := C.d
    left := l
    right := t
    allowed := Allowed C
    def_allowed := def_allowed C
    empty_in := C.zero_in
    insert_in := C.insert_d
    left_in := fun x hx => ((hl x).mp hx).1
    fresh_single := fun a _ b hb => by
      obtain ⟨x,hx,hb',ht',h⟩ := fresh_single C a b hb
      exact ⟨x,(hl x).mpr hx,hb',(ht _).mpr ht',h⟩
    fresh_point := fun b hb ban hban => by
      obtain ⟨x,hx,hxb,h⟩ := fresh_point C ((ht b).mp hb) ban hban
      exact ⟨x,(hl x).mpr hx,hxb,h⟩ }
  let F (a B : X) := (a ∈ₛ C.u ∧ B = a) ∨ Matched P e f a B
  have hF : BinaryDef M.toOperations F := by
    exact Def.or (Def.and (Def.mem (.var false) (.param C.u)) (Def.eq (.var true) (.var false)))
      (def_matched P e f)
  have hvalid {a B} (h : Matched P e f a B) :
      LeftClass C a ∧ RightClass C B ∧ Allowed C a B := by
    obtain ⟨ha,hb,h⟩ := matched_valid P e f h
    exact ⟨(hl a).mp ha,(ht B).mp hb,h⟩
  refine ⟨⟨F,hF,?_,?_,?_,?_,?_,?_,?_,?_⟩⟩
  · intro a B h
    rcases h with ⟨ha,_⟩ | h
    · exact C.u_sub ha
    · exact (hvalid h).1.1
  · intro a B h y hy
    rcases h with ⟨ha,rfl⟩ | h
    · exact C.trans_d _ _ hy (C.u_sub ha)
    · exact C.right_subset (hvalid h).2.1 _ hy
  · intro a ha
    by_cases hu : a ∈ₛ C.u
    · exact ⟨a,Or.inl ⟨hu,rfl⟩⟩
    · obtain ⟨b,hb⟩ := matched_left P e f he hf ((hl a).mpr ⟨ha,hu⟩)
      exact ⟨b,Or.inr hb⟩
  · intro a b c hb hc'
    rcases hb with ⟨hu,rfl⟩ | hm
    · rcases hc' with ⟨_,rfl⟩ | hc'
      · rfl
      · exact ((hvalid hc').1.2 hu).elim
    · rcases hc' with ⟨hu,rfl⟩ | hc'
      · exact ((hvalid hm).1.2 hu).elim
      · obtain ⟨g,hg,hb,hc'⟩ := matched_compare P e f he hf hm hc'
        exact hg.2.1 _ _ _ hb hc'
  · intro a c b ha hc'
    rcases ha with ⟨hu,rfl⟩ | hm
    · rcases hc' with ⟨_,heq⟩ | hc'
      · exact heq
      · exact ((hvalid hc').2.1.1 hu).elim
    · rcases hc' with ⟨hu,rfl⟩ | hc'
      · exact ((hvalid hm).2.1.1 hu).elim
      · obtain ⟨g,hg,ha,hc'⟩ := matched_compare P e f he hf hm hc'
        exact hg.2.2.1 _ _ _ ha hc'
  · intro a
    constructor
    · rintro (⟨hu,_⟩ | h)
      · exact hu
      · exact ((hvalid h).2.2.1 rfl).elim
    · intro h
      exact Or.inl ⟨h,rfl⟩
  · intro b hb
    obtain ⟨a,ha⟩ := matched_right P e f he hf ((ht b).mpr hb)
    exact ⟨a,Or.inr ha⟩
  · intro a b h hb hn
    rcases h with ⟨hu,_⟩ | h
    · exact (hn hu).elim
    · exact (hvalid h).2.2.2 hb

variable {C} (F : Assignment C)

def second (x a : X) : Prop := ∃ B, F.graph a B ∧ x ∈ₛ B

theorem def_second : BinaryDef M.toOperations (second F) := by
  unfold BinaryDef second
  apply Def.ex
  exact Def.and (Def.app₂ F.def_graph (.var (some true)) (.var none))
    (Def.mem (.var (some false)) (.var none))

theorem second_of_graph {a B : X} (h : F.graph a B) (x : X) : second F x a ↔ x ∈ₛ B := by
  constructor
  · rintro ⟨B',hB',hx⟩
    exact F.functional _ _ _ hB' h ▸ hx
  · intro hx
    exact ⟨B,h,hx⟩

end DESTSet
