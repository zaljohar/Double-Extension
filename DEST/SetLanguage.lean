import DEST.ReferenceTheory

/-! Formulas with parameters for the definitional expansion by adjunction.
Quantifiers range over the carrier of the set-theory model. -/
set_option autoImplicit false
set_option maxHeartbeats 0

universe u

namespace DESTSet

structure Operations (X : Type u) where
  mem : X → X → Prop
  lt : X → X → Prop
  insert : X → X → X

variable {X : Type u}

/-- There is one function symbol, adjoining an element to a set. -/
inductive Term (X : Type u) (ι : Type) where
  | var (i : ι)
  | param (a : X)
  | insert (a b : Term X ι)

def Term.eval (o : Operations X) {ι : Type} (v : ι → X) : Term X ι → X
  | .var i => v i
  | .param a => a
  | .insert a b => o.insert (a.eval o v) (b.eval o v)

def Term.subst {ι κ : Type} (f : ι → Term X κ) : Term X ι → Term X κ
  | .var i => f i
  | .param a => .param a
  | .insert a b => .insert (a.subst f) (b.subst f)

@[simp] theorem Term.eval_subst {ι κ : Type} (o : Operations X) (v : κ → X)
    (f : ι → Term X κ) (t : Term X ι) :
    (t.subst f).eval o v = t.eval o (fun i => (f i).eval o v) := by
  induction t with
  | var i => rfl
  | param a => rfl
  | insert a b ha hb => simp only [subst, eval, ha, hb]

def liftTerm {ι κ : Type} (f : ι → Term X κ) : Option ι → Term X (Option κ)
  | none => .var none
  | some i => (f i).subst fun k => .var (some k)

inductive Formula (X : Type u) : Type → Type (max u 1) where
  | bot {ι : Type} : Formula X ι
  | eq {ι : Type} (a b : Term X ι) : Formula X ι
  | mem {ι : Type} (a b : Term X ι) : Formula X ι
  | lt {ι : Type} (a b : Term X ι) : Formula X ι
  | imp {ι : Type} (p q : Formula X ι) : Formula X ι
  | all {ι : Type} (p : Formula X (Option ι)) : Formula X ι

def Formula.eval (o : Operations X) : {ι : Type} → Formula X ι → (ι → X) → Prop
  | _, .bot, _ => False
  | _, .eq a b, v => a.eval o v = b.eval o v
  | _, .mem a b, v => o.mem (a.eval o v) (b.eval o v)
  | _, .lt a b, v => o.lt (a.eval o v) (b.eval o v)
  | _, .imp p q, v => p.eval o v → q.eval o v
  | _, .all p, v => ∀ a, p.eval o (fun i => i.elim a v)

def Formula.subst : {ι κ : Type} → (ι → Term X κ) → Formula X ι → Formula X κ
  | _, _, _, .bot => .bot
  | _, _, f, .eq a b => .eq (a.subst f) (b.subst f)
  | _, _, f, .mem a b => .mem (a.subst f) (b.subst f)
  | _, _, f, .lt a b => .lt (a.subst f) (b.subst f)
  | _, _, f, .imp p q => .imp (p.subst f) (q.subst f)
  | _, _, f, .all p => .all (p.subst (liftTerm f))

theorem Formula.eval_subst {ι κ : Type} (o : Operations X) (v : κ → X)
    (f : ι → Term X κ) (p : Formula X ι) :
    (p.subst f).eval o v ↔ p.eval o (fun i => (f i).eval o v) := by
  induction p generalizing κ with
  | bot => rfl
  | eq a b => simp only [subst, eval, Term.eval_subst]
  | mem a b => simp only [subst, eval, Term.eval_subst]
  | lt a b => simp only [subst, eval, Term.eval_subst]
  | imp p q hp hq => simp only [subst, eval, hp, hq]
  | all p ih =>
    simp only [subst, eval, ih]
    have he (a : X) : (fun i => (liftTerm f i).eval o (fun j => j.elim a v)) =
        (fun i => i.elim a (fun j => (f j).eval o v)) := by
      funext i
      cases i <;> simp [liftTerm, Term.eval]
    simp only [he]

def TermDef (o : Operations X) {ι : Type} (f : (ι → X) → X) : Prop :=
  ∃ t : Term X ι, ∀ v, t.eval o v = f v

def Def (o : Operations X) {ι : Type} (P : (ι → X) → Prop) : Prop :=
  ∃ p : Formula X ι, ∀ v, p.eval o v ↔ P v

namespace TermDef

variable {o : Operations X} {ι : Type}

theorem var (i : ι) : TermDef o (fun v => v i) := ⟨.var i, fun _ => rfl⟩

theorem param (a : X) : TermDef o (fun _ : ι → X => a) := ⟨.param a, fun _ => rfl⟩

theorem insert {f g : (ι → X) → X} (hf : TermDef o f) (hg : TermDef o g) :
    TermDef o (fun v => o.insert (f v) (g v)) := by
  obtain ⟨s,hs⟩ := hf
  obtain ⟨t,ht⟩ := hg
  exact ⟨.insert s t, fun v => by simp only [Term.eval, hs, ht]⟩

end TermDef

namespace Def

variable {o : Operations X} {ι κ : Type}
variable {P Q : (ι → X) → Prop}

theorem congr (hP : Def o P) (h : ∀ v, P v ↔ Q v) : Def o Q := by
  obtain ⟨p,hp⟩ := hP
  exact ⟨p, fun v => (hp v).trans (h v)⟩

theorem bot : Def o (fun _ : ι → X => False) := ⟨.bot, fun _ => Iff.rfl⟩

theorem eq {f g : (ι → X) → X} (hf : TermDef o f) (hg : TermDef o g) :
    Def o (fun v => f v = g v) := by
  obtain ⟨s,hs⟩ := hf
  obtain ⟨t,ht⟩ := hg
  exact ⟨.eq s t, fun v => by simp only [Formula.eval, hs, ht]⟩

theorem mem {f g : (ι → X) → X} (hf : TermDef o f) (hg : TermDef o g) :
    Def o (fun v => o.mem (f v) (g v)) := by
  obtain ⟨s,hs⟩ := hf
  obtain ⟨t,ht⟩ := hg
  exact ⟨.mem s t, fun v => by simp only [Formula.eval, hs, ht]⟩

theorem lt {f g : (ι → X) → X} (hf : TermDef o f) (hg : TermDef o g) :
    Def o (fun v => o.lt (f v) (g v)) := by
  obtain ⟨s,hs⟩ := hf
  obtain ⟨t,ht⟩ := hg
  exact ⟨.lt s t, fun v => by simp only [Formula.eval, hs, ht]⟩

theorem imp (hP : Def o P) (hQ : Def o Q) : Def o (fun v => P v → Q v) := by
  obtain ⟨p,hp⟩ := hP
  obtain ⟨q,hq⟩ := hQ
  exact ⟨.imp p q, fun v => by simp only [Formula.eval, hp, hq]⟩

theorem not (hP : Def o P) : Def o (fun v => ¬ P v) := hP.imp bot

theorem and (hP : Def o P) (hQ : Def o Q) : Def o (fun v => P v ∧ Q v) :=
  (hP.imp hQ.not).not.congr (fun _ => by classical tauto)

theorem or (hP : Def o P) (hQ : Def o Q) : Def o (fun v => P v ∨ Q v) :=
  (hP.not.imp hQ).congr (fun _ => by classical tauto)

theorem iff (hP : Def o P) (hQ : Def o Q) : Def o (fun v => P v ↔ Q v) :=
  ((hP.imp hQ).and (hQ.imp hP)).congr (fun _ => by tauto)

theorem top : Def o (fun _ : ι → X => True) := bot.not.congr (fun _ => by simp)

theorem all {R : (ι → X) → X → Prop}
    (h : Def o (fun v : Option ι → X => R (fun i => v (some i)) (v none))) :
    Def o (fun v => ∀ x, R v x) := by
  obtain ⟨p,hp⟩ := h
  exact ⟨.all p, fun v => by simp only [Formula.eval, hp, Option.elim_some, Option.elim_none]⟩

theorem ex {R : (ι → X) → X → Prop}
    (h : Def o (fun v : Option ι → X => R (fun i => v (some i)) (v none))) :
    Def o (fun v => ∃ x, R v x) := by
  have ha : Def o (fun v => ∀ x, ¬ R v x) := all (R := fun v x => ¬ R v x) h.not
  exact ha.not.congr (fun _ => by classical push Not; rfl)

theorem comp (hP : Def o P) (f : ι → (κ → X) → X) (hf : ∀ i, TermDef o (f i)) :
    Def o (fun v => P (fun i => f i v)) := by
  classical
  obtain ⟨p,hp⟩ := hP
  choose t ht using hf
  refine ⟨p.subst t, fun v => (p.eval_subst o v t).trans ?_⟩
  simpa only [ht] using hp (fun i => (t i).eval o v)

theorem relabel (hP : Def o P) (f : ι → κ) : Def o (fun v => P (fun i => v (f i))) :=
  hP.comp _ (fun i => TermDef.var (f i))

end Def

abbrev UnaryDef (o : Operations X) (P : X → Prop) :=
  Def o (fun v : Unit → X => P (v ()))

abbrev BinaryDef (o : Operations X) (P : X → X → Prop) :=
  Def o (fun v : Bool → X => P (v false) (v true))

abbrev TernaryDef (o : Operations X) (P : X → X → X → Prop) :=
  Def o (fun v : Fin 3 → X => P (v 0) (v 1) (v 2))

namespace Def

variable {o : Operations X} {ι : Type}

theorem app₁ {P : X → Prop} (h : UnaryDef o P) {f : (ι → X) → X} (hf : TermDef o f) :
    Def o (fun v => P (f v)) := h.comp (fun _ => f) (fun _ => hf)

theorem app₂ {P : X → X → Prop} (h : BinaryDef o P) {f g : (ι → X) → X}
    (hf : TermDef o f) (hg : TermDef o g) : Def o (fun v => P (f v) (g v)) :=
  h.comp (fun i => if i then g else f) (by intro i; cases i; exact hf; exact hg)

theorem app₃ {P : X → X → X → Prop} (h : TernaryDef o P) {f g k : (ι → X) → X}
    (hf : TermDef o f) (hg : TermDef o g) (hk : TermDef o k) :
    Def o (fun v => P (f v) (g v) (k v)) :=
  h.comp (Fin.cases f (Fin.cases g (fun _ => k))) (by
    intro i
    refine Fin.cases hf (fun j => Fin.cases hg (fun _ => hk) j) i)

end Def

end DESTSet
