import DEST.SetReflection

/-! Back-and-forth with an internal graph and internal enumerations. The
indices range over the model's omega, including its nonstandard numbers. -/
set_option autoImplicit false
set_option maxHeartbeats 0

universe u

namespace DESTSet

variable {X : Type u} (M : Model X)
local infix:50 " ∈ₛ " => M.mem

structure Enumeration (g a : X) : Prop where
  total : ∀ n, n ∈ₛ M.omega → ∃ x, entry M g n x
  maps : ∀ n x, n ∈ₛ M.omega → entry M g n x → x ∈ₛ a
  unique : ∀ n x y, n ∈ₛ M.omega → entry M g n x → entry M g n y → x = y
  onto : ∀ x, x ∈ₛ a → ∃ n, n ∈ₛ M.omega ∧ entry M g n x

def InternallyCountable : Prop :=
  ∀ a, (∃ x, x ∈ₛ a) → ∃ g, Enumeration M g a

structure MatchingProblem where
  carrier : X
  left : X
  right : X
  allowed : X → X → Prop
  def_allowed : BinaryDef M.toOperations allowed
  empty_in : M.zero ∈ₛ carrier
  insert_in : ∀ a b, a ∈ₛ carrier → b ∈ₛ carrier → M.insert a b ∈ₛ carrier
  left_in : ∀ a, a ∈ₛ left → a ∈ₛ carrier
  fresh_single : ∀ a, a ∈ₛ left → ∀ banned, banned ∈ₛ carrier →
    ∃ b, b ∈ₛ left ∧ ¬ b ∈ₛ banned ∧ single M b ∈ₛ right ∧ allowed a (single M b)
  fresh_point : ∀ b, b ∈ₛ right → ∀ banned, banned ∈ₛ carrier →
    ∃ a, a ∈ₛ left ∧ ¬ a ∈ₛ banned ∧ allowed a b

variable {M} (P : MatchingProblem M)

def Includes (A : Model X) (g h : X) : Prop := ∀ a b, entry A g a b → entry A h a b

theorem def_includes {ι : Type} {f g : (ι → X) → X}
    (hf : TermDef M.toOperations f) (hg : TermDef M.toOperations g) :
    Def M.toOperations (fun v => Includes M (f v) (g v)) := by
  unfold Includes
  apply Def.all
  apply Def.all
  exact Def.imp (defEntry M ((hf.relabel some).relabel some) (.var (some none)) (.var none))
    (defEntry M ((hg.relabel some).relabel some) (.var (some none)) (.var none))

def GoodMatch (g : X) : Prop :=
  (∀ a b, entry M g a b → M.mem a P.left ∧ M.mem b P.right ∧ P.allowed a b) ∧
  (∀ a b c, entry M g a b → entry M g a c → b = c) ∧
  (∀ a b c, entry M g a c → entry M g b c → a = b) ∧
  ∃ l t, M.mem l P.carrier ∧ M.mem t P.carrier ∧
    (∀ a, M.mem a l ↔ ∃ b, entry M g a b) ∧
    (∀ a, M.mem a t ↔ M.mem a P.left ∧ ∃ b, entry M g b (single M a))

theorem def_good_match : UnaryDef M.toOperations (GoodMatch P) := by
  unfold GoodMatch UnaryDef single
  set_logic
  apply Def.app₂ P.def_allowed
  set_logic

theorem good_empty : GoodMatch P M.zero := by
  refine ⟨?_, ?_, ?_, M.zero,M.zero,P.empty_in,P.empty_in, ?_, ?_⟩
  · intro a b h
    exact (M.empty _ h).elim
  · intro a b c h
    exact (M.empty _ h).elim
  · intro a b c h
    exact (M.empty _ h).elim
  · intro a
    exact ⟨fun h => (M.empty _ h).elim, fun ⟨_,h⟩ => (M.empty _ h).elim⟩
  · intro a
    exact ⟨fun h => (M.empty _ h).elim, fun ⟨_,_,h⟩ => (M.empty _ h).elim⟩

theorem single_injective : Function.Injective (single M) := by
  intro a b h
  exact (mem_single M a b).mp (h ▸ (mem_single M a a).mpr rfl)

theorem add_good {g a b : X} (hg : GoodMatch P g)
    (ha : M.mem a P.left) (hb : M.mem b P.right) (hab : P.allowed a b)
    (hleft : ¬ ∃ x, entry M g a x) (hright : ¬ ∃ x, entry M g x b) :
    GoodMatch P (M.insert (pair M.toOperations M.zero a b) g) := by
  classical
  obtain ⟨hbound,hfun,hinj,l,t,hl,ht,hL,hT⟩ := hg
  set g' := M.insert (pair M.toOperations M.zero a b) g
  have inserted (x y : X) : entry M g' x y ↔ (x = a ∧ y = b) ∨ entry M g x y :=
    entry_insert M
  have hdom (x : X) : M.mem x (M.insert a l) ↔ ∃ y, entry M g' x y := by
    rw [M.mem_insert, hL]
    constructor
    · rintro (rfl | ⟨y, hy⟩)
      · exact ⟨b,(inserted _ _).mpr (Or.inl ⟨rfl,rfl⟩)⟩
      · exact ⟨y,(inserted _ _).mpr (Or.inr hy)⟩
    · rintro ⟨y,hy⟩
      rcases (inserted _ _).mp hy with ⟨rfl,rfl⟩ | hy
      · exact Or.inl rfl
      · exact Or.inr ⟨y,hy⟩
  have hsingle (x : X) : (M.mem x P.left ∧ ∃ y, entry M g' y (single M x)) ↔
      (M.mem x P.left ∧ single M x = b) ∨ M.mem x t := by
    constructor
    · rintro ⟨hx,y,hy⟩
      rcases (inserted _ _).mp hy with ⟨_,e⟩ | hy
      · exact Or.inl ⟨hx,e⟩
      · exact Or.inr ((hT x).mpr ⟨hx,y,hy⟩)
    · rintro (⟨hx,e⟩ | ht)
      · exact ⟨hx,a,(inserted _ _).mpr (Or.inl ⟨rfl,e⟩)⟩
      · obtain ⟨hx,y,hy⟩ := (hT x).mp ht
        exact ⟨hx,y,(inserted _ _).mpr (Or.inr hy)⟩
  have htarget : ∃ t', M.mem t' P.carrier ∧
      ∀ x, M.mem x t' ↔ M.mem x P.left ∧ ∃ y, entry M g' y (single M x) := by
    by_cases he : ∃ c, M.mem c P.left ∧ single M c = b
    · obtain ⟨c,hc,he⟩ := he
      refine ⟨M.insert c t, P.insert_in c t (P.left_in c hc) ht, ?_⟩
      intro x
      rw [M.mem_insert, hsingle]
      constructor
      · rintro (rfl | hx)
        · exact Or.inl ⟨hc,he⟩
        · exact Or.inr hx
      · rintro (⟨_,hx⟩ | hx)
        · exact Or.inl (single_injective (M := M) (hx.trans he.symm))
        · exact Or.inr hx
    · refine ⟨t,ht,fun x => ?_⟩
      rw [hsingle]
      exact ⟨Or.inr,fun h => h.resolve_left (fun hx => he ⟨x,hx⟩)⟩
  obtain ⟨t',ht',hT'⟩ := htarget
  refine ⟨?_, ?_, ?_, M.insert a l,t',P.insert_in a l (P.left_in a ha) hl,ht',hdom,hT'⟩
  · intro x y h
    rcases (inserted _ _).mp h with ⟨rfl,rfl⟩ | h
    · exact ⟨ha,hb,hab⟩
    · exact hbound _ _ h
  · intro x y z hy hz
    rcases (inserted _ _).mp hy with hn₁ | ho₁
    · rcases (inserted _ _).mp hz with hn₂ | ho₂
      · exact hn₁.2.trans hn₂.2.symm
      · exact (hleft ⟨z,hn₁.1 ▸ ho₂⟩).elim
    · rcases (inserted _ _).mp hz with hn₂ | ho₂
      · exact (hleft ⟨y,hn₂.1 ▸ ho₁⟩).elim
      · exact hfun _ _ _ ho₁ ho₂
  · intro x y z hx hy
    rcases (inserted _ _).mp hx with hn₁ | ho₁
    · rcases (inserted _ _).mp hy with hn₂ | ho₂
      · exact hn₁.1.trans hn₂.1.symm
      · exact (hright ⟨y,hn₁.2 ▸ ho₂⟩).elim
    · rcases (inserted _ _).mp hy with hn₂ | ho₂
      · exact (hright ⟨x,hn₂.2 ▸ ho₁⟩).elim
      · exact hinj _ _ _ ho₁ ho₂

theorem cover_left {g a : X} (hg : GoodMatch P g) (ha : M.mem a P.left) :
    ∃ h, GoodMatch P h ∧ Includes M g h ∧ ∃ b, entry M h a b := by
  classical
  by_cases had : ∃ b, entry M g a b
  · exact ⟨g,hg,fun _ _ h => h,had⟩
  · obtain ⟨l,t,hl,ht,hL,hT⟩ := hg.2.2.2
    obtain ⟨b,hbl,hbt,hbr,hab⟩ := P.fresh_single a ha t ht
    have hnb : ¬ ∃ c, entry M g c (single M b) := fun h => hbt ((hT b).mpr ⟨hbl,h⟩)
    exact ⟨_,add_good P hg ha hbr hab had hnb,
      fun _ _ h => (entry_insert M).mpr (Or.inr h),
      single M b,(entry_insert M).mpr (Or.inl ⟨rfl,rfl⟩)⟩

theorem cover_right {g b : X} (hg : GoodMatch P g) (hb : M.mem b P.right) :
    ∃ h, GoodMatch P h ∧ Includes M g h ∧ ∃ a, entry M h a b := by
  classical
  by_cases hbc : ∃ a, entry M g a b
  · exact ⟨g,hg,fun _ _ h => h,hbc⟩
  · obtain ⟨l,t,hl,ht,hL,hT⟩ := hg.2.2.2
    obtain ⟨a,ha,hal,hab⟩ := P.fresh_point b hb l hl
    have hna : ¬ ∃ c, entry M g a c := fun h => hal ((hL a).mpr h)
    exact ⟨_,add_good P hg ha hb hab hna hbc,fun _ _ h => (entry_insert M).mpr (Or.inr h),
      a,(entry_insert M).mpr (Or.inl ⟨rfl,rfl⟩)⟩

variable (e f : X)

def Advances (n g h : X) : Prop :=
  GoodMatch P h ∧ Includes M g h ∧
    (∀ a, entry M e n a → ∃ b, entry M h a b) ∧
    (∀ b, entry M f n b → ∃ a, entry M h a b)

def MatchStep (n g h : X) : Prop :=
  Advances P e f n g h ∧ ∀ k, Advances P e f n g k → h = k ∨ M.lt h k

theorem def_advances {ι : Type} {i j k : (ι → X) → X}
    (hi : TermDef M.toOperations i) (hj : TermDef M.toOperations j) (hk : TermDef M.toOperations k) :
    Def M.toOperations (fun v => Advances P e f (i v) (j v) (k v)) := by
  unfold Advances
  apply Def.and (Def.app₁ (def_good_match P) hk)
  apply Def.and (def_includes hj hk)
  apply Def.and
  · apply Def.all
    apply Def.imp (defEntry M (.param e) (hi.relabel some) (.var none))
    apply Def.ex
    exact defEntry M ((hk.relabel some).relabel some) (.var (some none)) (.var none)
  · apply Def.all
    apply Def.imp (defEntry M (.param f) (hi.relabel some) (.var none))
    apply Def.ex
    exact defEntry M ((hk.relabel some).relabel some) (.var none) (.var (some none))

theorem def_match_step : TernaryDef M.toOperations (MatchStep P e f) := by
  unfold TernaryDef MatchStep
  apply Def.and (def_advances P e f (.var 0) (.var 1) (.var 2))
  apply Def.all
  exact Def.imp (def_advances P e f (.var (some 0)) (.var (some 1)) (.var none))
    (Def.or (Def.eq (.var (some 2)) (.var none)) (Def.lt (.var (some 2)) (.var none)))

theorem match_step_total (he : Enumeration M e P.left) (hf : Enumeration M f P.right)
    (n g : X) (hn : M.mem n M.omega) (hg : GoodMatch P g) :
    ∃ h, MatchStep P e f n g h ∧ GoodMatch P h := by
  have hx : ∃ h, Advances P e f n g h := by
    obtain ⟨a,ha⟩ := he.total n hn
    obtain ⟨b,hb⟩ := hf.total n hn
    obtain ⟨h,hh,hi,x,hx⟩ := cover_left P hg (he.maps _ _ hn ha)
    obtain ⟨k,hk,hj,y,hy⟩ := cover_right P hh (hf.maps _ _ hn hb)
    refine ⟨k,hk,fun c d h => hj c d (hi c d h), ?_, ?_⟩
    · intro a' ha'
      rw [he.unique n a' a hn ha' ha]
      exact ⟨x,hj _ _ hx⟩
    · intro b' hb'
      rw [hf.unique n b' b hn hb' hb]
      exact ⟨y,hy⟩
  obtain ⟨h,hh,hm⟩ := M.least_def _ (def_advances P e f (.param n) (.param g) (.var ())) hx
  exact ⟨h,⟨hh,hm⟩,hh.1⟩

theorem match_step_det (n g a b : X) (_ : M.mem n M.omega) (_ : GoodMatch P g)
    (ha : MatchStep P e f n g a) (hb : MatchStep P e f n g b) : a = b := by
  rcases ha.2 b hb.1 with h | h
  · exact h
  · rcases hb.2 a ha.1 with e | he
    · exact e.symm
    · exact (M.lt_asymm _ _ h he).elim

abbrev MatchingRun := Run M (GoodMatch P) (MatchStep P e f) M.zero

theorem match_run_mono (he : Enumeration M e P.left) (hf : Enumeration M f P.right) :
    ∀ k, M.mem k M.omega → ∀ h, MatchingRun P e f k h →
      ∀ n g, M.mem n (succ M k) → MatchingRun P e f n g → Includes M g h := by
  let C (k : X) := ∀ h, MatchingRun P e f k h →
    ∀ n g, M.mem n (succ M k) → MatchingRun P e f n g → Includes M g h
  have hr : BinaryDef M.toOperations (MatchingRun P e f) :=
    def_run M (def_good_match P) (def_match_step P e f)
  have hC : UnaryDef M.toOperations C := by
    unfold UnaryDef C
    apply Def.all
    apply Def.imp (Def.app₂ hr (.var (some ())) (.var none))
    apply Def.all
    apply Def.all
    let k := some (some (some ()))
    apply Def.imp (Def.mem (.var (some none)) ((TermDef.var k).insert (.var k)))
    apply Def.imp (Def.app₂ hr (.var (some none)) (.var none))
    exact def_includes (.var none) (.var (some (some none)))
  have hu {n a b : X} (ha : MatchingRun P e f n a) (hb : MatchingRun P e f n b) : a = b :=
    run_unique M (def_good_match P) (def_match_step P e f) (match_step_det P e f) ha hb
  apply nat_induction M C hC
  · intro h hh n g hn hg
    obtain rfl : n = M.zero := ((mem_succ M _ _).mp hn).resolve_right (M.empty _)
    rw [hu hg hh]
    exact fun _ _ ha => ha
  · intro k hk ih h hh n g hn hg
    rcases (mem_succ M _ _).mp hn with e | hn
    · subst n
      rw [hu hg hh]
      exact fun _ _ ha => ha
    · obtain ⟨a,ha⟩ := run_total M (def_good_match P) (def_match_step P e f)
        (good_empty P) (match_step_total P e f he hf) k hk
      obtain ⟨b,hb,hg'⟩ := match_step_total P e f he hf k a hk (run_good M ha)
      have e := hu (run_step M ha hb hg') hh
      exact fun x y ht => e ▸ hb.1.2.1 x y (ih a ha n g hn hg x y ht)

def Matched (a b : X) : Prop := ∃ n g, MatchingRun P e f n g ∧ entry M g a b

theorem def_matched : BinaryDef M.toOperations (Matched P e f) := by
  unfold BinaryDef Matched
  apply Def.ex
  apply Def.ex
  exact Def.and (Def.app₂ (def_run M (def_good_match P) (def_match_step P e f))
    (.var (some none)) (.var none))
    (defEntry M (.var none) (.var (some (some false))) (.var (some (some true))))

theorem matched_valid {a b : X} (h : Matched P e f a b) :
    M.mem a P.left ∧ M.mem b P.right ∧ P.allowed a b := by
  obtain ⟨n,g,hg,hm⟩ := h
  exact (run_good M hg).1 a b hm

theorem matched_compare (he : Enumeration M e P.left) (hf : Enumeration M f P.right)
    {a b c d : X} (h : Matched P e f a b) (h' : Matched P e f c d) :
    ∃ g, GoodMatch P g ∧ entry M g a b ∧ entry M g c d := by
  obtain ⟨n,g,hg,hm⟩ := h
  obtain ⟨k,h,hh,hm'⟩ := h'
  rcases nat_compare M n k hg.1 hh.1 with hnk | heq | hkn
  · exact ⟨h,run_good M hh,match_run_mono P e f he hf k hh.1 h hh n g
      ((mem_succ M _ _).mpr (Or.inr hnk)) hg _ _ hm,hm'⟩
  · exact ⟨h,run_good M hh,match_run_mono P e f he hf k hh.1 h hh n g
      ((mem_succ M _ _).mpr (Or.inl heq)) hg _ _ hm,hm'⟩
  · exact ⟨g,run_good M hg,hm,match_run_mono P e f he hf n hg.1 g hg k h
      ((mem_succ M _ _).mpr (Or.inr hkn)) hh _ _ hm'⟩

theorem matched_left (he : Enumeration M e P.left) (hf : Enumeration M f P.right)
    {a : X} (ha : M.mem a P.left) : ∃ b, Matched P e f a b := by
  obtain ⟨n,hn,he'⟩ := he.onto a ha
  obtain ⟨g,hg⟩ := run_total M (def_good_match P) (def_match_step P e f)
    (good_empty P) (match_step_total P e f he hf) n hn
  obtain ⟨k,hk,hgood⟩ := match_step_total P e f he hf n g hn (run_good M hg)
  obtain ⟨b,hb⟩ := hk.1.2.2.1 a he'
  exact ⟨b,succ M n,k,run_step M hg hk hgood,hb⟩

theorem matched_right (he : Enumeration M e P.left) (hf : Enumeration M f P.right)
    {b : X} (hb : M.mem b P.right) : ∃ a, Matched P e f a b := by
  obtain ⟨n,hn,hf'⟩ := hf.onto b hb
  obtain ⟨g,hg⟩ := run_total M (def_good_match P) (def_match_step P e f)
    (good_empty P) (match_step_total P e f he hf) n hn
  obtain ⟨k,hk,hgood⟩ := match_step_total P e f he hf n g hn (run_good M hg)
  obtain ⟨a,ha⟩ := hk.1.2.2.2 b hf'
  exact ⟨a,succ M n,k,run_step M hg hk hgood,ha⟩

end DESTSet
