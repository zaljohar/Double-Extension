import DEST.RankCut
import DEST.Original

set_option autoImplicit false
set_option maxHeartbeats 0
namespace DESTRank
open DEST

noncomputable def M : Set A := hull Cut DEST.seed
def U : Set A := Cut ∩ M
abbrev Carrier := ↥M

theorem M_countable : M.Countable := hull_countable DEST.seed_countable
noncomputable instance : Countable Carrier := M_countable

theorem U_sub_M : U ⊆ M := fun _ h => h.2

theorem seed_in_U : DEST.seed ⊆ U := fun x hx => ⟨seed_in_cut hx,seed_subset_hull Cut DEST.seed hx⟩

theorem vn_mem_U (n : ℕ) : vn n ∈ U := seed_in_U (Or.inl ⟨n,rfl⟩)
theorem omega_mem_U : omegaSet ∈ U := seed_in_U (Or.inr (by simp))

noncomputable def numeral (n : ℕ) : Carrier := ⟨vn n,U_sub_M (vn_mem_U n)⟩
noncomputable def omegaObj : Carrier := ⟨omegaSet,U_sub_M omega_mem_U⟩
instance : Nonempty Carrier := ⟨numeral 0⟩

def mem₁ (x a : Carrier) : Prop := x.val ∈ a.val

def E (a : Carrier) : Set Carrier := {x | mem₁ x a}

def extn (p : Formula) (l : List Carrier) : Set Carrier :=
  {x | truth p (x.val :: l.map Subtype.val)}

/-- The family of all first-language definable subsets of M, parameters allowed. -/
def Defs : Set (Set Carrier) := Set.range (fun t : Formula × List Carrier => extn t.1 t.2)

theorem defs_countable : Defs.Countable := Set.countable_range _

def Protected (S : Set Carrier) : Prop :=
  ∃ p : Formula, ∃ l : List Carrier,
    Supported U (l.map Subtype.val) ∧ extn p l = S

def Fixed (S : Set Carrier) : Prop := ∃ a : Carrier, a.val ∈ U ∧ E a = S

abbrev Outside := {a : Carrier // a.val ∉ U}
abbrev FreeExt := {S : Set Carrier // S ∈ Defs ∧ ¬ Fixed S}

instance : Countable Outside := inferInstance
noncomputable instance : Countable FreeExt := by
  letI : Countable ↥Defs := defs_countable
  exact Function.Injective.countable (f := fun s : FreeExt => (⟨s.val,s.property.1⟩ : ↥Defs))
    (by
      intro x y h
      apply Subtype.ext
      exact congrArg (fun s : ↥Defs => s.val) h)

@[simp] theorem extn_eq (a : Carrier) : extn (.eq 0 1) [a] = {a} := by
  ext x
  change (∃ z : A, some x.val = some z ∧ some a.val = some z) ↔ x = a
  simp only [Option.some.injEq]
  constructor
  · rintro ⟨z,hx,ha⟩
    exact Subtype.ext (hx.trans ha.symm)
  · intro h
    subst x
    exact ⟨a.val,rfl,rfl⟩

@[simp] theorem extn_mem (a : Carrier) : extn (.mem 0 1) [a] = E a := by
  ext x
  change (∃ z w : A, some x.val = some z ∧ some a.val = some w ∧ z ∈ w) ↔ x.val ∈ a.val
  simp

theorem E_def (a : Carrier) : E a ∈ Defs := ⟨(.mem 0 1,[a]), extn_mem a⟩

theorem singleton_def (a : Carrier) : ({a} : Set Carrier) ∈ Defs :=
  ⟨(.eq 0 1,[a]),extn_eq a⟩

theorem fixed_protected {S : Set Carrier} (h : Fixed S) : Protected S := by
  obtain ⟨a,ha,he⟩ := h
  refine ⟨.mem 0 1,[a],?_,(extn_mem a).trans he⟩
  simpa [Supported] using ha

/-- Trace equality on M reflects to equality on the ambient universe. -/
theorem trace_rep (a : Carrier) (p : Formula) (l : List Carrier)
    (h : E a = extn p l) : ∀ y : A, y ∈ a.val ↔ truth p (y::l.map Subtype.val) := by
  classical
  intro y
  by_contra hn
  obtain ⟨z,hz,hd⟩ := hull_witness (avoid := Cut) (seed := DEST.seed) (.diff p)
    (a.val :: l.map Subtype.val) []
    (supported_cons a.property (supported_map M l)) (by simp [Supported]) ⟨y,hn⟩
  have hz' : (⟨z,hz⟩ : Carrier) ∈ E a ↔ (⟨z,hz⟩ : Carrier) ∈ extn p l := by rw [h]
  exact hd hz'

theorem E_injective : Function.Injective E := by
  intro a b h
  apply Subtype.ext
  apply ZFSet.ext
  intro y
  have ht := trace_rep a (.mem 0 1) [b] (h.trans (extn_mem b).symm) y
  change (y ∈ a.val ↔ ∃ z w : A, some y = some z ∧ some b.val = some w ∧ z ∈ w) at ht
  simpa using ht

/-- A protected collection with an ambient representative has its representative
    in the uniform hull U. -/
theorem protected_rep (p : Formula) (l : List Carrier)
    (hl : Supported U (l.map Subtype.val))
    (h : ∃ a : A, ∀ y : A, y ∈ a ↔ truth p (y::l.map Subtype.val)) :
    ∃ a : Carrier, a.val ∈ U ∧ E a = extn p l := by
  obtain ⟨b,hb,hbr⟩ := cut_witness (.rep p) (l.map Subtype.val)
    (fun x hx => (hl x hx).1) h
  obtain ⟨a,ha,hr⟩ := hull_witness (avoid := Cut) (seed := DEST.seed) (.rep p)
    (l.map Subtype.val) [] (supported_map M l) (by simp [Supported]) h
  have e : a = b := by
    apply ZFSet.ext
    intro y
    exact (hr y).trans (hbr y).symm
  refine ⟨⟨a,ha⟩,⟨e.symm ▸ hb,ha⟩,?_⟩
  ext x
  exact hr x.val

theorem protected_trace_fixed {S : Set Carrier} (hp : Protected S)
    (a : Carrier) (he : E a = S) : a.val ∈ U := by
  obtain ⟨p,l,hl,hs⟩ := hp
  obtain ⟨b,hb,hrep⟩ := protected_rep p l hl ⟨a.val,trace_rep a p l (he.trans hs.symm)⟩
  have hab := E_injective ((he.trans hs.symm).trans hrep.symm)
  simpa [hab] using hb

/-- Infinite supply of points of a protected, unfixed extension outside U. -/
theorem protected_fresh (S : FreeExt) (hp : Protected S.val) (banned : List Outside) :
    ∃ a : Outside, a ∉ banned ∧ a.val ∈ S.val := by
  obtain ⟨p,l,hl,hs⟩ := hp
  have hn : ¬ ∃ a : A, ∀ y : A, y ∈ a ↔ truth p (y::l.map Subtype.val) := by
    intro h
    obtain ⟨a,ha,hr⟩ := protected_rep p l hl h
    exact S.property.2 ⟨a,ha,hr.trans hs⟩
  let b : List A := banned.map (fun x : Outside => x.val.val)
  have hb : Supported M b := by
    intro x hx
    obtain ⟨z,_,rfl⟩ := List.mem_map.mp hx
    exact z.val.property
  obtain ⟨a,ha,h⟩ := hull_witness (avoid := Cut) (seed := DEST.seed) (.outside p)
    (l.map Subtype.val) b (supported_map M l) hb
    (cut_unrepresented_fresh p (l.map Subtype.val) b hn)
  change truth p (a::l.map Subtype.val) ∧ a ∉ Cut ∧ a ∉ b at h
  refine ⟨⟨⟨a,ha⟩,fun hu => h.2.1 hu.1⟩,?_,?_⟩
  · intro hmem
    exact h.2.2 (List.mem_map.mpr ⟨_,hmem,rfl⟩)
  · rw [← hs]
    exact h.1

/-- Infinite supply outside U independently of the choice of extension. -/
theorem outside_fresh (banned : List Outside) : ∃ a : Outside, a ∉ banned := by
  have hn : ¬ ∃ a : A, ∀ y : A, y ∈ a ↔ truth (.eq 0 0) [y] := by
    rintro ⟨a,ha⟩
    exact ZFSet.mem_irrefl a ((ha a).mpr (by simp [truth, Formula.eval]))
  let b : List A := banned.map (fun x : Outside => x.val.val)
  have hb : Supported M b := by
    intro x hx
    obtain ⟨z,_,rfl⟩ := List.mem_map.mp hx
    exact z.val.property
  obtain ⟨a,ha,h⟩ := hull_witness (avoid := Cut) (seed := DEST.seed) (.outside (.eq 0 0))
    [] b (by simp [Supported]) hb (cut_unrepresented_fresh (.eq 0 0) [] b hn)
  change truth (.eq 0 0) [a] ∧ a ∉ Cut ∧ a ∉ b at h
  refine ⟨⟨⟨a,ha⟩,fun hu => h.2.1 hu.1⟩,?_⟩
  intro hm
  exact h.2.2 (List.mem_map.mpr ⟨_,hm,rfl⟩)

instance : Nonempty Outside := by
  obtain ⟨a,_⟩ := outside_fresh []
  exact ⟨a⟩

/-- A singleton of an outside point cannot be defined with U-parameters. -/
theorem singleton_not_protected (b : Outside) : ¬ Protected ({b.val} : Set Carrier) := by
  classical
  intro hp
  obtain ⟨p,l,hl,hs⟩ := hp
  obtain ⟨a,ha,hr⟩ := hull_witness (avoid := Cut) (seed := DEST.seed) (.rep (.eq 0 1))
    [b.val.val] [] (by simpa [Supported] using b.val.property) (by simp [Supported])
    ⟨{b.val.val},by
      intro y
      change y ∈ ({b.val.val} : A) ↔ ∃ z : A, some y = some z ∧ some b.val.val = some z
      rw [ZFSet.mem_singleton]
      simp only [Option.some.injEq]
      constructor
      · intro he; exact ⟨b.val.val,he,rfl⟩
      · rintro ⟨z,hz,hb⟩; exact hz.trans hb.symm⟩
  let a' : Carrier := ⟨a,ha⟩
  have he : E a' = ({b.val} : Set Carrier) := by
    ext y
    change y.val ∈ a ↔ y = b.val
    have hh := hr y.val
    change (y.val ∈ a ↔ ∃ z : A, some y.val = some z ∧ some b.val.val = some z) at hh
    constructor
    · intro hy
      obtain ⟨z,hz,hb⟩ := hh.mp hy
      exact Subtype.ext ((Option.some.inj hz).trans (Option.some.inj hb).symm)
    · intro hy
      have e : y.val = b.val.val := congrArg Subtype.val hy
      exact hh.mpr ⟨b.val.val,congrArg some e,rfl⟩
  have hu := protected_trace_fixed ⟨p,l,hl,hs⟩ a' he
  have hb : b.val.val ∈ a := by
    change b.val ∈ E a'
    rw [he]; simp
  exact b.property ⟨cut_transitive hu.1 hb,b.val.property⟩

noncomputable def freeSingleton (b : Outside) : FreeExt :=
  ⟨{b.val},singleton_def b.val,fun h => singleton_not_protected b (fixed_protected h)⟩

instance : Nonempty FreeExt := ⟨freeSingleton (Classical.choice inferInstance)⟩

def Allowed (a : Outside) (S : FreeExt) : Prop :=
  E a.val ≠ S.val ∧ (Protected S.val → a.val ∈ S.val)

theorem left_fresh (a : Outside) (l : List FreeExt) :
    ∃ S, S ∉ l ∧ Allowed a S := by
  let f : Outside → Set Carrier := fun b => {b.val}
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    have hm : x.val ∈ f y := by rw [← h]; simp [f]
    exact Set.mem_singleton_iff.mp hm
  obtain ⟨k,hk⟩ := pullback_list hf (E a.val :: l.map Subtype.val)
  obtain ⟨b,hb⟩ := outside_fresh k
  refine ⟨freeSingleton b,?_,?_,?_⟩
  · intro hm
    apply hb
    apply hk
    exact List.mem_cons.mpr (Or.inr (List.mem_map.mpr ⟨freeSingleton b,hm,rfl⟩))
  · intro he
    apply hb
    apply hk
    exact List.mem_cons.mpr (Or.inl he.symm)
  · intro hp
    exact (singleton_not_protected b hp).elim

theorem right_fresh (S : FreeExt) (l : List Outside) :
    ∃ a, a ∉ l ∧ Allowed a S := by
  classical
  by_cases hp : Protected S.val
  · obtain ⟨a,ha,hm⟩ := protected_fresh S hp l
    refine ⟨a,ha,?_,fun _ => hm⟩
    intro he
    exact a.property (protected_trace_fixed hp a.val he)
  · let f : Outside → Set Carrier := fun a => E a.val
    have hf : Function.Injective f := fun _ _ h => Subtype.ext (E_injective h)
    obtain ⟨k,hk⟩ := pullback_list hf [S.val]
    obtain ⟨a,ha⟩ := outside_fresh (l ++ k)
    refine ⟨a,fun h => ha (List.mem_append.mpr (Or.inl h)),?_,fun h => (hp h).elim⟩
    intro he
    exact ha (List.mem_append.mpr (Or.inr (hk a (by simpa using he))))

/-- The second-extension assignment; it is injective, onto the definable
    extensions, fixed precisely on U, and obeys the protected self-membership rule. -/
theorem extension_assignment : ∃ F : Carrier → Set Carrier,
    Function.Injective F ∧
    (∀ S : Set Carrier, S ∈ Defs → ∃ a, F a = S) ∧
    (∀ a, F a = E a ↔ a.val ∈ U) ∧
    (∀ a, Protected (F a) → a.val ∉ U → a ∈ F a) := by
  classical
  obtain ⟨e,he⟩ := countable_matching Allowed left_fresh right_fresh
  let F (a : Carrier) : Set Carrier := if h : a.val ∈ U then E a else (e ⟨a,h⟩).val
  have pos (a : Carrier) (h : a.val ∈ U) : F a = E a := by simp [F,h]
  have neg (a : Carrier) (h : a.val ∉ U) : F a = (e ⟨a,h⟩).val := by simp [F,h]
  refine ⟨F,?_,?_,?_,?_⟩
  · intro a b h
    by_cases ha : a.val ∈ U <;> by_cases hb : b.val ∈ U
    · exact E_injective ((pos a ha).symm.trans (h.trans (pos b hb)))
    · exact ((e ⟨b,hb⟩).property.2 ⟨a,ha,((pos a ha).symm.trans h).trans (neg b hb)⟩).elim
    · exact ((e ⟨a,ha⟩).property.2 ⟨b,hb,((pos b hb).symm.trans h.symm).trans (neg a ha)⟩).elim
    · have heq : e ⟨a,ha⟩ = e ⟨b,hb⟩ :=
        Subtype.ext ((neg a ha).symm.trans (h.trans (neg b hb)))
      exact congrArg Subtype.val (e.injective heq)
  · intro S hS
    by_cases h : Fixed S
    · obtain ⟨a,ha,heq⟩ := h
      exact ⟨a,(pos a ha).trans heq⟩
    · obtain ⟨a,ha⟩ := e.surjective ⟨S,hS,h⟩
      exact ⟨a.val,(neg a.val a.property).trans (congrArg Subtype.val ha)⟩
  · intro a
    constructor
    · intro h
      by_contra hn
      exact (he ⟨a,hn⟩).1 (h.symm.trans (neg a hn))
    · exact pos a
  · intro a hp hn
    have hh := neg a hn
    rw [hh] at hp ⊢
    exact (he ⟨a,hn⟩).2 hp

/-- Uniformity is defined solely by agreement of the two actual extensions. -/
def Uniform (r : Carrier → Carrier → Prop) (a : Carrier) : Prop :=
  ∀ y : Carrier, mem₁ y a ↔ r y a

/-- Corrected DEST schema, with capture avoided by de Bruijn semantics. -/
def IsDEST (r : Carrier → Carrier → Prop) : Prop :=
  (∀ a b : Carrier, (∀ y, mem₁ y a ↔ mem₁ y b) → a = b) ∧
  (∀ a b : Carrier, (∀ y, r y a ↔ r y b) → a = b) ∧
  (∀ (p : Formula) (l : List Carrier), ∃ a : Carrier,
    ∀ y : Carrier, r y a ↔ p.eval M (y.val :: l.map Subtype.val)) ∧
  (∀ (p : Formula) (l : List Carrier), (∀ b ∈ l, Uniform r b) →
    ∀ a : Carrier, (∀ y : Carrier, r y a ↔ p.eval M (y.val :: l.map Subtype.val)) →
      ¬ r a a → Uniform r a)

/-- Actual well-foundedness proves full set induction, even for predicates
    involving the second membership relation. -/
theorem first_wellFounded : WellFounded mem₁ := by
  exact InvImage.wf (fun x : Carrier => x.val) ZFSet.mem_wf

theorem full_set_induction (P : Carrier → Prop)
    (h : ∀ a : Carrier, (∀ y : Carrier, mem₁ y a → P y) → P a) : ∀ a, P a :=
  fun a => first_wellFounded.induction a h

/-- Standard natural numbers and their ordinary successor, on the actual domain. -/
theorem omega_exact (a : Carrier) : mem₁ a omegaObj ↔ ∃ n : ℕ, numeral n = a := by
  change a.val ∈ ZFSet.range vn ↔ _
  rw [ZFSet.mem_range]
  constructor
  · rintro ⟨n,hn⟩
    exact ⟨n,Subtype.ext hn⟩
  · rintro ⟨n,hn⟩
    exact ⟨n,congrArg Subtype.val hn⟩

theorem numeral_zero (a : Carrier) : ¬ mem₁ a (numeral 0) := ZFSet.notMem_empty a.val

theorem numeral_succ (a : Carrier) (n : ℕ) :
    mem₁ a (numeral (n+1)) ↔ a = numeral n ∨ mem₁ a (numeral n) := by
  change a.val ∈ insert (vn n) (vn n) ↔ _
  rw [ZFSet.mem_insert_iff]
  constructor
  · rintro (h|h)
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr h
  · rintro (h|h)
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr h

theorem natural_induction (P : Carrier → Prop) (h0 : P (numeral 0))
    (hs : ∀ n : ℕ, P (numeral n) → P (numeral (n+1))) :
    ∀ a, mem₁ a omegaObj → P a := by
  have hAll : ∀ n : ℕ, P (numeral n) := by
    intro n
    induction n with
    | zero => exact h0
    | succ n ih => exact hs n ih
  intro a ha
  obtain ⟨n,rfl⟩ := (omega_exact a).mp ha
  exact hAll n

/-- The ordinary first-language definition of an inductive set. -/
def IsInductive (a : Carrier) : Prop :=
  mem₁ (numeral 0) a ∧ ∀ n : Carrier, mem₁ n a →
    ∃ s : Carrier, mem₁ s a ∧ ∀ z : Carrier, mem₁ z s ↔ z = n ∨ mem₁ z n

theorem omega_inductive : IsInductive omegaObj := by
  refine ⟨(omega_exact _).mpr ⟨0,rfl⟩,?_⟩
  intro a ha
  obtain ⟨n,rfl⟩ := (omega_exact a).mp ha
  exact ⟨numeral (n+1),(omega_exact _).mpr ⟨n+1,rfl⟩,fun z => numeral_succ z n⟩

theorem omega_least_inductive (a : Carrier) (ha : IsInductive a) :
    ∀ z : Carrier, mem₁ z omegaObj → mem₁ z a := by
  apply natural_induction (fun z => mem₁ z a) ha.1
  intro n hn
  obtain ⟨s,hs,he⟩ := ha.2 (numeral n) hn
  have h : s = numeral (n+1) := by
    apply E_injective
    ext z
    exact (he z).trans (numeral_succ z n).symm
  exact h ▸ hs

/-- No hypotheses: a model of corrected DEST, with full first-membership
    well-foundedness and uniform standard natural numbers. -/
theorem exists_rank_model : ∃ r : Carrier → Carrier → Prop,
    IsDEST r ∧ WellFounded mem₁ ∧ Uniform r omegaObj ∧ (∀ n : ℕ, Uniform r (numeral n)) ∧
    (∀ a : Carrier, Uniform r a ↔ a.val ∈ U) := by
  classical
  obtain ⟨F,hF,honto,hfix,hself⟩ := extension_assignment
  let r (x a : Carrier) : Prop := x ∈ F a
  have hu (a : Carrier) : Uniform r a ↔ a.val ∈ U := by
    rw [← hfix a]
    constructor
    · intro h
      ext y
      exact (h y).symm
    · intro h y
      change y ∈ E a ↔ y ∈ F a
      rw [h]
  have realize (p : Formula) (l : List Carrier) (y : Carrier) :
      p.eval M (y.val::l.map Subtype.val) ↔ y ∈ extn p l :=
    hull_elementary Cut DEST.seed p _ (supported_cons y.property (supported_map M l))
  refine ⟨r,?_,first_wellFounded,(hu omegaObj).mpr omega_mem_U,(fun n => (hu (numeral n)).mpr (vn_mem_U n)),hu⟩
  refine ⟨?_,?_,?_,?_⟩
  · intro a b h
    apply E_injective
    ext y
    exact h y
  · intro a b h
    apply hF
    ext y
    exact h y
  · intro p l
    obtain ⟨a,ha⟩ := honto (extn p l) ⟨(p,l),rfl⟩
    refine ⟨a,fun y => ?_⟩
    change y ∈ F a ↔ _
    rw [ha]
    exact (realize p l y).symm
  · intro p l hl a ha hnot
    apply (hu a).mpr
    by_contra hnu
    have hEq : extn p l = F a := by
      ext y
      exact (realize p l y).symm.trans (ha y).symm
    have hp : Protected (F a) := by
      refine ⟨p,l,?_,hEq⟩
      intro y hy
      obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hy
      exact (hu b).mp (hl b hb)
    exact hnot (hself a hp hnu)


/-- First-extension subsethood in the countable hull implies actual
subsethood in the ambient set hierarchy, by the witness property. -/
theorem subset_reflect (a b : Carrier) (h : ∀ y : Carrier, mem₁ y a → mem₁ y b) : a.val ⊆ b.val := by
  classical
  intro y hy
  by_contra hn
  let p : Formula := .imp (.mem 0 1) (.mem 0 2)
  have hex : ∃ x, test Cut (.counter p) [a.val,b.val] [] x := by
    refine ⟨y,?_⟩
    have hh : ¬ (y ∈ a.val → y ∈ b.val) := fun h => hn (h hy)
    simpa [test,p,truth,Formula.eval] using hh
  obtain ⟨x,hx,hh⟩ := hull_witness (avoid := Cut) (seed := DEST.seed) (.counter p)
    [a.val,b.val] [] (by simp [Supported,a.property,b.property]) (by simp [Supported]) hex
  have hn' : ¬ (x ∈ a.val → x ∈ b.val) := by simpa [test,p,truth,Formula.eval] using hh
  exact hn' (h ⟨x,hx⟩)

/-- The full original theory + first-extension SU + first-membership TI,
with no hypotheses. The weak-metatheory ZF reduction is documented separately. -/
theorem exists_SU_TI_model : ∃ (X : Type 1) (m r : X → X → Prop),
    Nonempty X ∧ DESTOriginal.Original m r ∧ DESTOriginal.SU1 m r ∧ DESTOriginal.TI1 m r := by
  classical
  obtain ⟨r,⟨ext1,ext2,comp,unif⟩,hwf,hw,hn,hfix⟩ := exists_rank_model
  have hO : DESTOriginal.Original mem₁ r := by
    refine ⟨ext1,ext2,?_,?_,?_⟩
    · intro n p hp v
      obtain ⟨a,ha⟩ := comp (DESTSemantic.erase p) (DESTSemantic.params v)
      exact ⟨a,fun y => (ha y).trans (DESTSemantic.unary_translation M r p hp v y).symm⟩
    · intro n p hp v hv a ha hs
      have hr : ∀ y, r y a ↔ (DESTSemantic.erase p).eval M
          (y.val :: (DESTSemantic.params v).map Subtype.val) :=
        fun y => (ha y).trans (DESTSemantic.unary_translation M r p hp v y)
      exact unif (DESTSemantic.erase p) (DESTSemantic.params v)
        (DESTSemantic.params_all _ v hv) a hr (fun hh => hs ((ha a).mp hh))
    · intro z hz n p v hb hs a ha
      have ez : z = numeral 0 := ext1 _ _ (fun y => ⟨fun hy => (hz y hy).elim,
        fun hy => (numeral_zero y hy).elim⟩)
      subst z
      have hm : mem₁ a omegaObj := ha omegaObj omega_inductive
      apply natural_induction (fun y => p.eval mem₁ r (DESTReference.push y v)) hb _ a hm
      intro k hk
      have hN : DESTOriginal.Natural mem₁ (numeral 0) (numeral k) :=
        fun t ht => omega_least_inductive t ht _ ((omega_exact _).mpr ⟨k,rfl⟩)
      exact hs _ hN _ (fun y => numeral_succ y k) hk
  refine ⟨Carrier,mem₁,r,inferInstance,hO,?_,?_⟩
  · intro a b ha hb
    have hu := (hfix a).mp ha
    exact (hfix b).mpr ⟨cut_subset_closed hu.1 (subset_reflect b a hb),b.property⟩
  · intro n p v hs a
    exact hwf.induction a hs

end DESTRank
