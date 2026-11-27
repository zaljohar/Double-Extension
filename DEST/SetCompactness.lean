import DEST.SetFragment
import Mathlib.ModelTheory.Satisfiability

set_option autoImplicit false
set_option maxHeartbeats 0

universe u

namespace DESTSet

open FirstOrder DESTReference

inductive Relation : ℕ → Type
  | mem₁ : Relation 2
  | mem₂ : Relation 2

def language : Language where
  Functions := fun _ => Empty
  Relations := Relation

@[instance_reducible] def structureOn {X : Type u} (m r : X → X → Prop) : language.Structure X where
  funMap f := f.elim
  RelMap
    | .mem₁, a => m (a 0) (a 1)
    | .mem₂, a => r (a 0) (a 1)

def membership₁ (X : Type u) [language.Structure X] (x a : X) : Prop :=
  Language.Structure.RelMap (L := language) Relation.mem₁ ![x,a]

def membership₂ (X : Type u) [language.Structure X] (x a : X) : Prop :=
  Language.Structure.RelMap (L := language) Relation.mem₂ ![x,a]

private def term {k : ℕ} (v : Fin k) : language.Term (Empty ⊕ Fin k) := .var (.inr v)

private theorem realizePair {X : Type u} [language.Structure X] {k : ℕ} (a : Fin k → X)
    (i j : Fin k) :
    (fun l => (![term i,term j] l).realize (Sum.elim Empty.elim a)) = ![a i,a j] := by
  funext l
  refine Fin.cases ?_ (fun t => ?_) l
  · rfl
  · refine Fin.cases ?_ (fun t' => t'.elim0) t
    rfl

/-- DEST inserts the new variable at the front. Mathlib appends it. -/
def embedBounded : {n : ℕ} → DESTReference.Formula n → {k : ℕ} →
    (Fin n → Fin k) → language.BoundedFormula Empty k
  | _, .bot, _, _ => .falsum
  | _, .eq i j, _, f => .equal (term (f i)) (term (f j))
  | _, .mem1 i j, _, f => Language.Relations.boundedFormula₂ (L := language)
      Relation.mem₁ (term (f i)) (term (f j))
  | _, .mem2 i j, _, f => Language.Relations.boundedFormula₂ (L := language)
      Relation.mem₂ (term (f i)) (term (f j))
  | _, .imp p q, _, f => .imp (embedBounded p f) (embedBounded q f)
  | _, .all p, k, f => .all (embedBounded p (push (Fin.last k) fun i => (f i).castSucc))

def embed (s : DESTReference.Sentence) : language.Sentence := embedBounded s Fin.elim0

theorem embedBounded_correct {X : Type u} [language.Structure X] {n k : ℕ}
    (p : DESTReference.Formula n) (f : Fin n → Fin k) (a : Fin k → X) :
    (embedBounded p f).Realize Empty.elim a ↔
      p.eval (membership₁ X) (membership₂ X) (a ∘ f) := by
  induction p generalizing k with
  | bot => rfl
  | eq i j => rfl
  | mem1 i j =>
    change Language.Structure.RelMap (L := language) Relation.mem₁
      (fun l => (![term (f i),term (f j)] l).realize (Sum.elim Empty.elim a)) ↔ membership₁ X _ _
    rw [realizePair]
    rfl
  | mem2 i j =>
    change Language.Structure.RelMap (L := language) Relation.mem₂
      (fun l => (![term (f i),term (f j)] l).realize (Sum.elim Empty.elim a)) ↔ membership₂ X _ _
    rw [realizePair]
    rfl
  | imp p q hp hq => simp only [embedBounded, Language.BoundedFormula.realize_imp, DESTReference.Formula.eval,
      hp, hq]
  | all p ih =>
    simp only [embedBounded, Language.BoundedFormula.realize_all, DESTReference.Formula.eval]
    apply forall_congr'
    intro x
    rw [ih]
    have he : (Fin.snoc a x ∘ push (Fin.last k) fun i => (f i).castSucc) = push x (a ∘ f) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [Function.comp_def]
      · simp [Function.comp_def]
    rw [he]

theorem embed_correct (X : Type u) [language.Structure X] (s : DESTReference.Sentence) :
    (embed s).Realize X ↔ s.eval (membership₁ X) (membership₂ X) Fin.elim0 := by
  have h := embedBounded_correct s (Fin.elim0 : Fin 0 → Fin 0) (Fin.elim0 : Fin 0 → X)
  have hl : (default : Empty → X) = Empty.elim := by funext i; exact i.elim
  have hr : ((Fin.elim0 : Fin 0 → X) ∘ (Fin.elim0 : Fin 0 → Fin 0)) = Fin.elim0 := by
    funext i
    exact Fin.elim0 i
  change (embedBounded s Fin.elim0).Realize (default : Empty → X) default ↔ _
  have hd : (default : Fin 0 → X) = Fin.elim0 := by funext i; exact Fin.elim0 i
  rw [hl,hd,← hr]
  exact h

def fragmentTheory (qs : List DESTStrength.Unary) (s : DESTReference.Sentence) : language.Theory :=
  embed '' {p | DESTStrength.Fragment qs p ∨ p = s}

/-- A single first-language sentence true in the weak model can be retained
along with every axiom of DEST + TI₁. -/
theorem reference_model_from_set_model {X : Type u} {M : Model X}
    (hr : CofinalReflection M) (hc : InternallyCountable M)
    (s : DESTReference.Sentence) (hs : s.firstOnly) (ht : s.eval M.mem M.mem Fin.elim0) :
    ∃ (Y : Type) (m r : Y → Y → Prop), Nonempty Y ∧ Satisfies m r ∧ s.eval m r Fin.elim0 := by
  have hdir : Directed (· ⊆ ·) (fun qs => fragmentTheory qs s) := by
    intro qs ts
    refine ⟨qs ++ ts, ?_, ?_⟩
    · rintro _ ⟨p,hp,rfl⟩
      exact ⟨p,hp.imp_left (DESTStrength.fragment_mono (fun q hq => List.mem_append_left _ hq)),rfl⟩
    · rintro _ ⟨p,hp,rfl⟩
      exact ⟨p,hp.imp_left (DESTStrength.fragment_mono (fun q hq => List.mem_append_right _ hq)),rfl⟩
  have hsat := (Language.Theory.isSatisfiable_directed_union_iff hdir).mpr (fun qs => by
    obtain ⟨d,g,hne,hfrag,href⟩ := finite_fragment_inside hr hc qs s hs
    let r (a b : Carrier M d) := entry M g a.val b.val
    let : language.Structure (Carrier M d) := structureOn (first M d) r
    have : (Carrier M d) ⊨ fragmentTheory qs s := by
      constructor
      rintro _ ⟨p,hp,rfl⟩
      apply (embed_correct _ p).mpr
      change p.eval (first M d) r Fin.elim0
      rcases hp with hp | rfl
      · exact hfrag _ hp
      · exact href.mpr ht
    exact Language.Theory.Model.isSatisfiable (Carrier M d))
  let Y := hsat.some
  have holds (p : DESTReference.Sentence) (qs : List DESTStrength.Unary)
      (hp : DESTStrength.Fragment qs p ∨ p = s) :
      p.eval (membership₁ Y) (membership₂ Y) Fin.elim0 := by
    apply (embed_correct Y p).mp
    apply Language.Theory.realize_sentence_of_mem (⋃ qs, fragmentTheory qs s)
    exact Set.mem_iUnion.mpr ⟨qs,p,hp,rfl⟩
  refine ⟨Y,membership₁ Y,membership₂ Y,inferInstance,?_,holds s [] (Or.inr rfl)⟩
  intro p hp
  obtain ⟨qs,hqs⟩ := DESTStrength.axiom_in_fragment hp
  exact holds p qs (Or.inl hqs)

end DESTSet
