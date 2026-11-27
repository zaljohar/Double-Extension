import DEST.SetFamilies
import DEST.Strength

set_option autoImplicit false
set_option maxHeartbeats 0

universe u

namespace DESTSet

open DESTReference

variable {X : Type u} (M : Model X)
local infix:50 " ∈ₛ " => M.mem

def disagreement {n : ℕ} (p : DESTReference.Formula (n+1)) : Query M where
  arity := n+1
  test := fun v a => ¬ (a ∈ₛ v 0 ↔ p.eval M.mem M.mem (push a (fun i => v i.succ)))
  definable := by
    apply Def.not
    apply Def.iff (Def.mem (.var none) (.var (some 0)))
    let f := fun i (v : Option (Fin (n+1)) → X) => push (v none) (fun j => v (some j.succ)) i
    apply eval_def M (Def.mem (.var false) (.var true)) p f
    intro i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp only [f,push_zero,push_succ]
    · exact TermDef.var none
    · exact TermDef.var (some j.succ)

def requests (qs : List DESTStrength.Unary) (s : Sentence) : List (Query M) :=
  outside M (top : DESTReference.Formula 1) :: (counters M s ++ qs.flatMap
    (fun q => [positive M q.2, representative M q.2, disagreement M q.2, outside M q.2] ++
      counters M q.2))

structure Regions (qs : List DESTStrength.Unary) (s : Sentence) where
  u : X
  d : X
  omega_in : M.omega ∈ₛ u
  ud : u ∈ₛ d
  trans_u : Transitive M u
  trans_d : Transitive M d
  insert_d : ∀ x y, x ∈ₛ d → y ∈ₛ d → M.insert x y ∈ₛ d
  closed_u : Closed M u (requests M qs s)
  closed_d : Closed M d (requests M qs s)

theorem regions (hM : CofinalReflection M) (qs : List DESTStrength.Unary) (s : Sentence) :
    Nonempty (Regions M qs s) := by
  obtain ⟨u,hu,htu,_,hcu⟩ := hM M.omega (requests M qs s)
  obtain ⟨d,hd,htd,hid,hcd⟩ := hM u (requests M qs s)
  exact ⟨⟨u,d,hu,hd,htu,htd,hid,hcu,hcd⟩⟩

variable {M} {qs : List DESTStrength.Unary} {s : Sentence} (C : Regions M qs s)

theorem Regions.u_sub {a : X} (ha : M.mem a C.u) : M.mem a C.d :=
  C.trans_d _ _ ha C.ud

theorem Regions.zero_in : M.mem M.zero C.d :=
  C.u_sub (C.trans_u _ _ M.zero_mem C.omega_in)

theorem request_mem (q : DESTStrength.Unary) (hq : q ∈ qs) {r : Query M}
    (hr : r ∈ [positive M q.2, representative M q.2, disagreement M q.2, outside M q.2] ++
      counters M q.2) : r ∈ requests M qs s :=
  List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr ⟨q,hq,hr⟩)))

theorem Regions.reflected (q : DESTStrength.Unary) (hq : q ∈ qs)
    (v : Fin (q.1+1) → Carrier M C.d) :
    q.2.eval (first M C.d) (first M C.d) v ↔ q.2.eval M.mem M.mem (fun i => (v i).val) :=
  reflect M C.closed_d q.2 (fun r hr => request_mem (s := s) q hq (List.mem_append.mpr (Or.inr hr))) v

theorem Regions.ambient (q : DESTStrength.Unary) (hq : q ∈ qs)
    (v : Fin q.1 → X) (hv : ∀ i, M.mem (v i) C.d) (x : X) (hx : M.mem x C.d) :
    Relativized (fun y => M.mem y C.d) M.mem M.mem q.2 (push x v) ↔ q.2.eval M.mem M.mem (push x v) := by
  let f : Fin (q.1+1) → Carrier M C.d := push ⟨x,hx⟩ (fun i => ⟨v i,hv i⟩)
  have h : (fun i => (f i).val) = push x v := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [f]
  rw [← h]
  exact (relativized_subtype _ _ _ q.2 f).trans (C.reflected q hq f)

theorem Regions.representative_in (q : DESTStrength.Unary) (hq : q ∈ qs)
    (v : Fin q.1 → X) (hv : ∀ i, M.mem (v i) C.u)
    (he : ∃ a, represents M q.2 v a) :
    ∃ a, M.mem a C.u ∧ represents M q.2 v a :=
  C.closed_u (representative M q.2) (request_mem (s := s) q hq (by simp)) v hv he

theorem Regions.outside (q : DESTStrength.Unary)
    (hq : outside M q.2 ∈ requests M qs s) (b : X) (hb : M.mem b C.d)
    (v : Fin q.1 → X) (hv : ∀ i, M.mem (v i) C.d)
    (he : ¬ ∃ a, represents M q.2 v a) :
    ∃ a, M.mem a C.d ∧ q.2.eval M.mem M.mem (push a v) ∧ ¬ M.mem a C.u ∧ ¬ M.mem a b := by
  have hargs : ∀ i, M.mem (outsideVal C.u b v i) C.d := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [outsideVal] using C.ud
    · refine Fin.cases ?_ (fun k => ?_) j
      · simpa only [outsideVal,push_succ,push_zero] using hb
      · simpa only [outsideVal,push_succ] using hv k
  obtain ⟨a,ha,ht⟩ := C.closed_d (DESTSet.outside M q.2) hq _ hargs
    (outside_exists M q.2 C.u b v he)
  exact ⟨a,ha,(outside_eval M q.2 C.u b a v).mp ht⟩

theorem Regions.fresh (b : X) (hb : M.mem b C.d) :
    ∃ a, M.mem a C.d ∧ ¬ M.mem a C.u ∧ ¬ M.mem a b := by
  let q : DESTStrength.Unary := ⟨0,top⟩
  have hn : ¬ ∃ a, represents M q.2 Fin.elim0 a := by
    rintro ⟨a,ha⟩
    exact mem_irrefl M a ((ha a).mpr (by simp [q,top,DESTReference.Formula.eval]))
  obtain ⟨a,ha,_,hu,hb'⟩ := C.outside q (by simp [q,requests]) b hb Fin.elim0
    (fun i => Fin.elim0 i) hn
  exact ⟨a,ha,hu,hb'⟩

def Requested (d a : X) (qs : List DESTStrength.Unary) (B : X) : Prop :=
  ∃ q ∈ qs, ∃ v : Fin q.1 → X, (∀ i, M.mem (v i) a) ∧ Extension M d q.2 v B

theorem def_requested (d a : X) (qs : List DESTStrength.Unary) :
    UnaryDef M.toOperations (Requested (M := M) d a qs) := by
  unfold Requested UnaryDef
  apply Def.ex_list
  intro q _
  apply Def.ex_values (P := fun (env : Unit → X) (v : Fin q.1 → X) =>
    (∀ i, M.mem (v i) a) ∧ Extension M d q.2 v (env ()))
  have hdef : Def M.toOperations (fun v : Unit ⊕ Fin q.1 → X => ∀ i, M.mem (v (Sum.inr i)) a) :=
    Def.all_fin (fun i => Def.mem (.var (Sum.inr i)) (.param a))
  exact Def.and hdef (defExtension M d q.2 (.var (Sum.inl ())) (fun i v => v (Sum.inr i))
    (fun i => TermDef.var (Sum.inr i)))

def LeftClass (a : X) : Prop := M.mem a C.d ∧ ¬ M.mem a C.u
abbrev Protected (B : X) : Prop := Requested (M := M) C.d C.u qs B
def RightClass (B : X) : Prop :=
  ¬ M.mem B C.u ∧ ((∃ a, LeftClass C a ∧ B = single M a) ∨
    Requested (M := M) C.d C.d qs B)

theorem def_left_class : UnaryDef M.toOperations (LeftClass C) := by
  unfold UnaryDef LeftClass
  set_logic

theorem def_right_class : UnaryDef M.toOperations (RightClass C) := by
  unfold UnaryDef RightClass
  apply Def.and (Def.mem (.var ()) (.param C.u)).not
  apply Def.or
  · apply Def.ex
    exact Def.and (Def.app₁ (def_left_class C) (.var none))
      (Def.eq (.var (some ())) ((TermDef.var none).insert (.param M.zero)))
  · exact def_requested C.d C.d qs

theorem Regions.from_ambient (q : DESTStrength.Unary) (hq : q ∈ qs) (v : Fin q.1 → X)
    (hv : ∀ i, M.mem (v i) C.d) {a : X} (ha : M.mem a C.d)
    (he : represents M q.2 v a) : Extension M C.d q.2 v a := by
  intro x
  constructor
  · intro hx
    have hd := C.trans_d _ _ hx ha
    exact ⟨hd,(C.ambient q hq v hv x hd).mpr ((he x).mp hx)⟩
  · rintro ⟨hx,hr⟩
    exact (he x).mpr ((C.ambient q hq v hv x hx).mp hr)

theorem Regions.protected_proper (q : DESTStrength.Unary) (hq : q ∈ qs) (v : Fin q.1 → X)
    (hv : ∀ i, M.mem (v i) C.u) {B : X} (hb : ¬ M.mem B C.u) (hB : Extension M C.d q.2 v B) :
    ¬ ∃ a, represents M q.2 v a := by
  intro he
  obtain ⟨a,ha,hr⟩ := C.representative_in q hq v hv he
  have eq : B = a :=
    extension_unique M hB (C.from_ambient q hq v (fun i => C.u_sub (hv i)) (C.u_sub ha) hr)
  exact hb (eq.symm ▸ ha)

theorem Regions.protected_not_in {B : X} (hb : ¬ M.mem B C.u)
    (hp : Protected C B) : ¬ M.mem B C.d := by
  classical
  rintro hd
  obtain ⟨q,hq,v,hv,hB⟩ := hp
  have hno := C.protected_proper q hq v hv hb hB
  apply hno
  refine ⟨B,?_⟩
  intro y
  by_contra hbad
  have hargs : ∀ i, M.mem (push B v i) C.d := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using hd
    · simpa using C.u_sub (hv j)
  obtain ⟨x,hx,hx'⟩ := C.closed_d (disagreement M q.2)
    (request_mem (s := s) q hq (by simp)) (push B v) hargs ⟨y,by simpa only [disagreement,push_succ,push_zero]⟩
  apply hx'
  simp only [push_zero,push_succ]
  rw [hB x]
  exact ⟨fun h => (C.ambient q hq v (fun i => C.u_sub (hv i)) x hx).mp h.2,
    fun h => ⟨hx,(C.ambient q hq v (fun i => C.u_sub (hv i)) x hx).mpr h⟩⟩

theorem Regions.singleton_not_protected {a : X} (ha : LeftClass C a) :
    ¬ Protected C (single M a) := by
  rintro ⟨q,hq,v,hv,hB⟩
  have hvars := fun i => C.u_sub (hv i)
  have htrue := ((hB a).mp ((mem_single M _ _).mpr rfl)).2
  have hpos := (C.ambient q hq v hvars a ha.1).mp htrue
  obtain ⟨x,hx,hP⟩ := C.closed_u (positive M q.2) (request_mem (s := s) q hq (by simp)) v hv ⟨a,hpos⟩
  have hd := C.u_sub hx
  have hB' := (hB x).mpr ⟨hd,(C.ambient q hq v hvars x hd).mpr hP⟩
  exact ha.2 ((mem_single M _ _).mp hB' ▸ hx)

theorem Regions.singleton_right {a : X} (ha : LeftClass C a) : RightClass C (single M a) := by
  refine ⟨?_,Or.inl ⟨a,ha,rfl⟩⟩
  intro h
  exact ha.2 (C.trans_u _ _ ((mem_single M _ _).mpr rfl) h)

theorem Regions.right_subset {B : X} (hB : RightClass C B) :
    ∀ x, M.mem x B → M.mem x C.d := by
  rcases hB.2 with ⟨a,ha,rfl⟩ | ⟨q,hq,v,hv,h⟩
  · intro x hx
    exact ((mem_single M _ _).mp hx).symm ▸ ha.1
  · exact extension_subset M h

theorem Regions.left_and_right_sets (hM : CofinalReflection M) :
    ∃ l t, (∀ a, M.mem a l ↔ LeftClass C a) ∧ (∀ B, M.mem B t ↔ RightClass C B) := by
  obtain ⟨l,hl⟩ := M.separation C.d _ (def_left_class C)
  let Q := qs.map (fun q => extensionQuery M C.d q.2)
  obtain ⟨e,hd,hte,hie,hce⟩ := hM C.d Q
  have hsub : ∀ x, M.mem x C.d → M.mem x e := fun x hx => hte _ _ hx hd
  obtain ⟨t,ht⟩ := M.separation e _ (def_right_class C)
  refine ⟨l,t,fun a => ⟨fun h => ((hl a).mp h).2,fun h => (hl a).mpr ⟨h.1,h⟩⟩,?_⟩
  intro B
  refine ⟨fun h => ((ht B).mp h).2,fun h => (ht B).mpr ⟨?_,h⟩⟩
  rcases h.2 with ⟨a,ha,rfl⟩ | ⟨q,hq,v,hv,hB⟩
  · exact hie _ _ (hsub _ ha.1) (hsub _ C.zero_in)
  · obtain ⟨b,hb,he⟩ := hce (extensionQuery M C.d q.2)
      (List.mem_map.mpr ⟨q,hq,rfl⟩) v (fun i => hsub _ (hv i)) (extension_exists _ _ _ _)
    exact (extension_unique M he hB) ▸ hb

end DESTSet
