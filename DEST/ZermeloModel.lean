import DEST.ZermeloSeparation

set_option autoImplicit false
set_option maxHeartbeats 0
universe u
namespace DESTOriginal
open DESTReference

/-- The requested single hereditarily uniform set carrying Zermelo set theory.
No ambient Foundation, Replacement, Infinity axiom or second-extension SU
is assumed. Every first-order Separation instance is verified semantically. -/
theorem exists_hereditarily_uniform_Z_model {X : Type u} (m r : X → X → Prop)
    (h : Original m r) (su : SU1 m r) :
    ∃ W, HereditarilyUniform m r W ∧ Transitive m W ∧ ZermeloModel m W := by
  obtain ⟨z,w,hz,hw,hu⟩ := exists_uniform_omega m r h
  let p : Formula 3 := inTowerF (Fin.succ 0) (Fin.succ (Fin.succ 0)) 0
  let v : Fin 2 → X := push z (push w Fin.elim0)
  have hv : ∀ i, Uniform m r (v i) := by
    intro i; refine Fin.cases ?_ (fun j => ?_) i
    · simpa [v] using hu.2 z hw.1.1
    · refine Fin.cases ?_ (fun k => Fin.elim0 k) j
      simpa [v] using hu.1
  have he (a : X) : p.eval m r (push a v) ↔ InTower m z w a := by
    simp only [p,v,inTowerF_correct,push_zero,push_succ]
  obtain ⟨W,hW,hmem⟩ := collect m r h p (inTowerF_first _ _ _) v hv _ he
    (tower_uniform m r h su z w hz hw hu)
  have hWU : AllUniform m r W := ⟨hW,fun a ha => tower_uniform m r h su z w hz hw hu a ((hmem a).mp ha)⟩
  have htr : Transitive m W := fun y x hxy hy => (hmem x).mpr
    (tower_trans m r h su z w hz hw hu y x ((hmem y).mp hy) hxy)
  have hsub : ∀ a b, m a W → Sub m b a → m b W := fun a b ha hb =>
    (hmem b).mpr (tower_subset m r h su z w hz hw hu a b ((hmem a).mp ha) hb)
  have stage_in (k a : X) (ha : Stage m z w k a) : m a W := by
    obtain ⟨s,b,_,hb,hp⟩ := stage_advance m r h su z w hz hw hu k a ha
    exact (hmem a).mpr ⟨s,b,hb,(hp a).mpr (fun _ hx => hx)⟩
  obtain ⟨w',hw'⟩ := stage_total m r h su z w hz hw hu z hw.1.1
  have ew := stage_zero m r h su z w hz hw hu w' hw'
  subst w'
  have hwW := stage_in z w hw'
  have hzW := htr w z hw.1.1 hwW
  refine ⟨W,⟨hW,W,htr,fun _ hx => hx,hWU.2⟩,htr,?_⟩
  constructor
  · intro a b ha hb hh
    apply h.ext1
    intro y
    exact ⟨fun hy => (hh y (htr a y hy ha)).mp hy,
      fun hy => (hh y (htr b y hy hb)).mpr hy⟩
  · exact ⟨z,hzW,hz⟩
  · intro a b ha hb
    obtain ⟨c,hc,hcp⟩ := uniform_unordered_pair m r h a b (hWU.2 a ha) (hWU.2 b hb)
    obtain ⟨k,d,hd,had,hbd⟩ := common_stage m r h su z w hz hw hu a b ((hmem a).mp ha) ((hmem b).mp hb)
    have hcd : Sub m c d := by
      intro y hy
      rcases (hcp y).mp hy with e | e
      · exact e.symm ▸ had
      · exact e.symm ▸ hbd
    exact ⟨c,hsub d c (stage_in k d hd) hcd,hcp⟩
  · intro a ha
    obtain ⟨b,hb,hun⟩ := uniform_union m r h a (hWU.2 a ha) (fun y x hx hy =>
      hWU.2 y (htr x y hy (htr a x hx ha)))
    obtain ⟨k,c,⟨g,hg,hv'⟩,hac⟩ := (hmem a).mp ha
    have good := all_stages_good m r h su z w hz hw hu k (hg k c hv').1 c ⟨g,hg,hv'⟩
    have hbc : Sub m b c := by
      intro y hy
      obtain ⟨x,hxa,hyx⟩ := (hun y).mp hy
      exact good.2.1 x y hyx (good.2.1 a x hxa hac)
    exact ⟨b,hsub c b (stage_in k c ⟨g,hg,hv'⟩) hbc,hun⟩
  · intro a ha
    obtain ⟨b,hb,hpow⟩ := uniform_power m r h su a (hWU.2 a ha)
    obtain ⟨k,c,⟨g,hg,hv'⟩,hac⟩ := (hmem a).mp ha
    have good := all_stages_good m r h su z w hz hw hu k (hg k c hv').1 c ⟨g,hg,hv'⟩
    obtain ⟨s,d,_,hd,hp⟩ := stage_advance m r h su z w hz hw hu k c ⟨g,hg,hv'⟩
    have hbd : Sub m b d := by
      intro y hy
      apply (hp y).mpr
      intro x hx
      exact good.2.1 a x ((hpow y).mp hy x hx) hac
    exact ⟨b,hsub d b (stage_in s d hd) hbd,fun y _ => hpow y⟩
  · exact ⟨z,w,hzW,hwW,hz,hw.1⟩
  · intro a ha hex
    obtain ⟨k,c,⟨g,hg,hv'⟩,hac⟩ := (hmem a).mp ha
    have good := all_stages_good m r h su z w hz hw hu k (hg k c hv').1 c ⟨g,hg,hv'⟩
    exact good.2.2 a ⟨fun y hy => good.2.1 a y hy hac,hex⟩
  · intro n p hp vs a
    exact separation_in_domain m r h W hWU htr hsub p hp vs a

end DESTOriginal
