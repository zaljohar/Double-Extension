import Mathlib.Tactic.Tauto
import Mathlib.Data.Fin.Basic

/-! Independent reference language. This module does not import the DEST
construction, its syntax, or its specification. Index 0 is the newest variable.
Only equality, two binary relations, falsity, implication and universal
quantification are primitive. The other classical connectives are abbreviations.
-/
set_option autoImplicit false
set_option maxHeartbeats 0

universe u

namespace DESTReference

inductive Formula : ℕ → Type where
  | bot {n : ℕ} : Formula n
  | eq {n : ℕ} : Fin n → Fin n → Formula n
  | mem1 {n : ℕ} : Fin n → Fin n → Formula n
  | mem2 {n : ℕ} : Fin n → Fin n → Formula n
  | imp {n : ℕ} : Formula n → Formula n → Formula n
  | all {n : ℕ} : Formula (n+1) → Formula n

abbrev Sentence := Formula 0

def Formula.firstOnly : {n : ℕ} → Formula n → Prop
  | _, .bot => True
  | _, .eq _ _ => True
  | _, .mem1 _ _ => True
  | _, .mem2 _ _ => False
  | _, .imp p q => p.firstOnly ∧ q.firstOnly
  | _, .all p => p.firstOnly

def push {X : Type u} {n : ℕ} (x : X) (v : Fin n → X) : Fin (n+1) → X := Fin.cases x v

@[simp] theorem push_zero {X : Type u} {n : ℕ} (x : X) (v : Fin n → X) :
    push x v 0 = x := by simp [push]
@[simp] theorem push_succ {X : Type u} {n : ℕ} (x : X) (v : Fin n → X) (i : Fin n) :
    push x v i.succ = v i := by simp [push]

theorem push_eta {X : Type u} {n : ℕ} (v : Fin (n+1) → X) :
    push (v 0) (fun i => v i.succ) = v := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

def Formula.eval {X : Type u} (m1 m2 : X → X → Prop) :
    {n : ℕ} → Formula n → (Fin n → X) → Prop
  | _, .bot, _ => False
  | _, .eq i j, v => v i = v j
  | _, .mem1 i j, v => m1 (v i) (v j)
  | _, .mem2 i j, v => m2 (v i) (v j)
  | _, .imp p q, v => p.eval m1 m2 v → q.eval m1 m2 v
  | _, .all p, v => ∀ x : X, p.eval m1 m2 (push x v)

def liftRen {n k : ℕ} (f : Fin n → Fin k) : Fin (n+1) → Fin (k+1) :=
  Fin.cases 0 (fun i => (f i).succ)

@[simp] theorem liftRen_zero {n k : ℕ} (f : Fin n → Fin k) : liftRen f 0 = 0 := by simp [liftRen]
@[simp] theorem liftRen_succ {n k : ℕ} (f : Fin n → Fin k) (i : Fin n) :
    liftRen f i.succ = (f i).succ := by simp [liftRen]

/-- Renaming free variables, lifted below every binder. This is capture avoiding. -/
def Formula.rename : {n k : ℕ} → (Fin n → Fin k) → Formula n → Formula k
  | _, _, _, .bot => .bot
  | _, _, f, .eq i j => .eq (f i) (f j)
  | _, _, f, .mem1 i j => .mem1 (f i) (f j)
  | _, _, f, .mem2 i j => .mem2 (f i) (f j)
  | _, _, f, .imp p q => .imp (p.rename f) (q.rename f)
  | _, _, f, .all p => .all (p.rename (liftRen f))

@[simp] theorem eval_rename {X : Type u} (m1 m2 : X → X → Prop)
    {n k : ℕ} (p : Formula n) (f : Fin n → Fin k) (v : Fin k → X) :
    (p.rename f).eval m1 m2 v ↔ p.eval m1 m2 (fun i => v (f i)) := by
  induction p generalizing k with
  | bot => rfl
  | eq i j => rfl
  | mem1 i j => rfl
  | mem2 i j => rfl
  | imp p q ihp ihq => simp only [Formula.rename, Formula.eval, ihp, ihq]
  | all p ih =>
    simp only [Formula.rename, Formula.eval]
    have h (x : X) : (fun i => push x v (liftRen f i)) =
        push x (fun i => v (f i)) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp
    simp only [ih, h]

def atVar {n k : ℕ} (p : Formula (n+1)) (i : Fin k) (f : Fin n → Fin k) : Formula k :=
  p.rename (Fin.cases i f)

@[simp] theorem eval_atVar {X : Type u} (m1 m2 : X → X → Prop) {n k : ℕ}
    (p : Formula (n+1)) (i : Fin k) (f : Fin n → Fin k) (v : Fin k → X) :
    (atVar p i f).eval m1 m2 v ↔ p.eval m1 m2 (push (v i) (fun j => v (f j))) := by
  rw [atVar, eval_rename]
  have h : (fun j => v (Fin.cases i f j)) = push (v i) (fun j => v (f j)) := by
    funext j
    refine Fin.cases ?_ (fun t => ?_) j <;> simp
  rw [h]

def neg {n : ℕ} (p : Formula n) : Formula n := .imp p .bot
def conj {n : ℕ} (p q : Formula n) : Formula n := neg (.imp p (neg q))
def disj {n : ℕ} (p q : Formula n) : Formula n := .imp (neg p) q
def iffF {n : ℕ} (p q : Formula n) : Formula n := conj (.imp p q) (.imp q p)
def ex {n : ℕ} (p : Formula (n+1)) : Formula n := neg (.all (neg p))
def top {n : ℕ} : Formula n := .imp .bot .bot

section Connectives
variable {X : Type u} (m1 m2 : X → X → Prop) {n : ℕ} (v : Fin n → X)
@[simp] theorem eval_neg (p : Formula n) : (neg p).eval m1 m2 v ↔ ¬ p.eval m1 m2 v := Iff.rfl
@[simp] theorem eval_conj (p q : Formula n) : (conj p q).eval m1 m2 v ↔ p.eval m1 m2 v ∧ q.eval m1 m2 v := by
  classical
  simp only [conj, eval_neg, Formula.eval]
  tauto
@[simp] theorem eval_disj (p q : Formula n) : (disj p q).eval m1 m2 v ↔ p.eval m1 m2 v ∨ q.eval m1 m2 v := by
  classical
  simp only [disj, Formula.eval, eval_neg]
  tauto
@[simp] theorem eval_iffF (p q : Formula n) : (iffF p q).eval m1 m2 v ↔ (p.eval m1 m2 v ↔ q.eval m1 m2 v) := by
  simp only [iffF, eval_conj, Formula.eval]
  tauto
@[simp] theorem eval_ex (p : Formula (n+1)) : (ex p).eval m1 m2 v ↔ ∃ x : X, p.eval m1 m2 (push x v) := by
  classical
  simp only [ex, eval_neg, Formula.eval]
  push_neg <;> rfl
@[simp] theorem eval_top : (top : Formula n).eval m1 m2 v := by simp [top, Formula.eval]
end Connectives

/-- Universal closure of all free variables, in head-first order. -/
def close : {n : ℕ} → Formula n → Sentence
  | 0, p => p
  | _+1, p => close (.all p)

@[simp] theorem eval_close {X : Type u} (m1 m2 : X → X → Prop)
    {n : ℕ} (p : Formula n) :
    (close p).eval m1 m2 Fin.elim0 ↔ ∀ v : Fin n → X, p.eval m1 m2 v := by
  induction n with
  | zero =>
    change p.eval m1 m2 Fin.elim0 ↔ _
    constructor
    · intro h v
      have he : v = Fin.elim0 := by funext i; exact Fin.elim0 i
      rwa [he]
    · intro h; exact h _
  | succ n ih =>
    rw [close, ih]
    change (∀ (v : Fin n → X) (x : X), p.eval m1 m2 (push x v)) ↔ _
    constructor
    · intro h v
      simpa only [push_eta] using h (fun i => v i.succ) (v 0)
    · intro h v x; exact h _

-- Reference sentence constructors (not definitions from the construction).
def uniformF {n : ℕ} (a : Fin n) : Formula n := .all (iffF (.mem1 0 a.succ) (.mem2 0 a.succ))
def allUniform : (n : ℕ) → Formula n
  | 0 => top
  | n+1 => conj (uniformF 0) ((allUniform n).rename Fin.succ)

def extensionality (second : Bool) : Sentence :=
  let atom : Fin 3 → Fin 3 → Formula 3 := if second then .mem2 else .mem1
  .all (.all (.imp (.all (iffF (atom 0 (Fin.succ 0)) (atom 0 (Fin.succ (Fin.succ 0))))) (.eq 0 (Fin.succ 0))))

/-- Within y,x,parameters: the original y stays at 0, and the parameters
    move past the newly bound x. -/
def extensionF {n : ℕ} (p : Formula (n+1)) : Formula (n+1) :=
  .all (iffF (.mem2 0 (Fin.succ 0)) (atVar p 0 (fun i => i.succ.succ)))

def comprehension {n : ℕ} (p : Formula (n+1)) : Sentence := close (ex (extensionF p))

/-- The literal corrected test ¬φ(x,parameters), not an assumed equivalent.
    The same formula p is evaluated with x as its distinguished variable. -/
def uniformity {n : ℕ} (p : Formula (n+1)) : Sentence :=
  close (.imp (allUniform n) (.all (.imp (extensionF p) (.imp (neg p) (uniformF 0)))))

def zeroF {n : ℕ} (z : Fin n) : Formula n := .all (neg (.mem1 0 z.succ))
def succF {n : ℕ} (a b : Fin n) : Formula n :=
  .all (iffF (.mem1 0 b.succ) (disj (.eq 0 a.succ) (.mem1 0 a.succ)))
def inductiveF {n : ℕ} (z a : Fin n) : Formula n :=
  conj (.mem1 z a) (.all (.imp (.mem1 0 a.succ)
    (ex (conj (.mem1 0 a.succ.succ) (succF (Fin.succ 0) 0)))))
def omegaF {n : ℕ} (z w : Fin n) : Formula n :=
  conj (inductiveF z w) (.all (.imp (inductiveF z.succ 0)
    (.all (.imp (.mem1 0 w.succ.succ) (.mem1 0 (Fin.succ 0))))))
def infinity : Sentence := ex (ex (conj (zeroF 0) (omegaF 0 (Fin.succ 0))))

/-- z,w are the two newest variables; the schema is conditional on their
    being the first-membership empty set and least inductive set. -/
def natBody {n : ℕ} (p : Formula (n+1)) : Formula (n+2) :=
  .imp (conj (zeroF 0) (omegaF 0 (Fin.succ 0)))
    (.imp (atVar p 0 (fun i => i.succ.succ))
      (.imp (.all (.imp (.mem1 0 (Fin.succ (Fin.succ 0)))
          (.all (.imp (succF (Fin.succ 0) 0)
            (.imp (atVar p (Fin.succ 0) (fun i => i.succ.succ.succ.succ))
              (atVar p 0 (fun i => i.succ.succ.succ.succ)))))))
        (.all (.imp (.mem1 0 (Fin.succ (Fin.succ 0)))
          (atVar p 0 (fun i => i.succ.succ.succ))))))

def naturalInduction {n : ℕ} (p : Formula (n+1)) : Sentence := close (Formula.all (Formula.all (natBody p)))
def setInduction {n : ℕ} (p : Formula (n+1)) : Sentence :=
  close (.imp (.all (.imp (.all (.imp (.mem1 0 (Fin.succ 0))
    (atVar p 0 (fun i => i.succ.succ)))) p)) (.all p))

/-- Explicit closed sentences of the corrected reference theory. Infinity is
    included as a witness for the intended interpretation of naturals; full
    first-membership set induction is a strengthening of ordinal induction. -/
inductive Axiom : Sentence → Prop where
  | ext1 : Axiom (extensionality false)
  | ext2 : Axiom (extensionality true)
  | comp {n : ℕ} (p : Formula (n+1)) : p.firstOnly → Axiom (comprehension p)
  | unif {n : ℕ} (p : Formula (n+1)) : p.firstOnly → Axiom (uniformity p)
  | inf : Axiom infinity
  | natInd {n : ℕ} (p : Formula (n+1)) : Axiom (naturalInduction p)
  | setInd {n : ℕ} (p : Formula (n+1)) : Axiom (setInduction p)

def Satisfies {X : Type u} (m1 m2 : X → X → Prop) : Prop :=
  ∀ s : Sentence, Axiom s → s.eval m1 m2 Fin.elim0

end DESTReference
