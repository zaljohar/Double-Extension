import DEST.SetMatching
import DEST.OriginalClosedSpecification
import DEST.StandardArithmeticSpecification

/-! Model-theoretic formulation of the exact relative strength. The two
published reductions are explicit propositions used as hypotheses. -/

set_option autoImplicit false

namespace DESTExact

open DESTArithmetic DESTReference

structure Arithmetic (N R : Type) where
  zero : N
  succ : N → N
  add : N → N → N
  mul : N → N → N
  mem : N → R → Prop

namespace Arithmetic

variable {N R : Type} (M : Arithmetic N R)

def term : {n : ℕ} → NumTerm n → (Fin n → N) → N
  | _, .var i, v => v i
  | _, .zero, _ => M.zero
  | _, .succ t, v => M.succ (term t v)
  | _, .add t s, v => M.add (term t v) (term s v)
  | _, .mul t s, v => M.mul (term t v) (term s v)

def truth : {n k : ℕ} → StandardFormula n k → (Fin n → N) → (Fin k → R) → Prop
  | _, _, .bot, _, _ => False
  | _, _, .numEq t s, v, _ => M.term t v = M.term s v
  | _, _, .realEq i j, _, e => e i = e j
  | _, _, .mem t i, v, e => M.mem (M.term t v) (e i)
  | _, _, .imp p q, v, e => truth p v e → truth q v e
  | _, _, .allNum p, v, e => ∀ a, truth p (push a v) e
  | _, _, .allReal p, v, e => ∀ a, truth p v (push a e)

/-- Peano equations, set extensionality, and induction with all parameters. -/
structure Basic : Prop where
  succ_ne_zero : ∀ a, M.succ a ≠ M.zero
  succ_injective : Function.Injective M.succ
  add_zero : ∀ a, M.add a M.zero = a
  add_succ : ∀ a b, M.add a (M.succ b) = M.succ (M.add a b)
  mul_zero : ∀ a, M.mul a M.zero = M.zero
  mul_succ : ∀ a b, M.mul a (M.succ b) = M.add (M.mul a b) a
  extensionality : ∀ a b, (∀ i, M.mem i a ↔ M.mem i b) → a = b
  induction_schema : ∀ {n k : ℕ} (p : StandardFormula (n+1) k) (v : Fin n → N) (e : Fin k → R),
    M.truth p (push M.zero v) e →
    (∀ a, M.truth p (push a v) e → M.truth p (push (M.succ a) v) e) →
    ∀ a, M.truth p (push a v) e

/-- Full impredicative comprehension allowing arbitrary real parameters. -/
def Full : Prop := M.Basic ∧ ∀ {n k : ℕ} (p : StandardFormula (n+1) k)
    (v : Fin n → N) (e : Fin k → R), ∃ A, ∀ a, M.mem a A ↔ M.truth p (push a v) e

/-- Comprehension with number parameters and with arbitrary bound real quantifiers. -/
def ParameterFree : Prop := M.Basic ∧ ∀ {n : ℕ} (p : StandardFormula (n+1) 0) (v : Fin n → N),
    ∃ A, ∀ a, M.mem a A ↔ M.truth p (push a v) Fin.elim0

end Arithmetic

def Z2Satisfiable : Prop := ∃ (N R : Type) (M : Arithmetic N R), M.Full

def ParameterFreeSatisfiable : Prop := ∃ (N R : Type) (M : Arithmetic N R), M.ParameterFree

def OriginalSatisfiable : Prop :=
  ∃ (X : Type) (m r : X → X → Prop), Nonempty X ∧ DESTOriginalClosed.Satisfies m r

def InductiveSatisfiable : Prop := ∃ (X : Type) (m r : X → X → Prop),
  Nonempty X ∧ DESTOriginalClosed.Satisfies m r ∧ DESTOriginal.TI1 m r

/-- The model-existence consequence of Friedman's restriction theorem. -/
def FriedmanRestriction : Prop := ParameterFreeSatisfiable → Z2Satisfiable

/-- The model-existence consequence of the tree interpretation and its
countable constructible cut, with finite reflection there. -/
def ConstructibleInterpretation : Prop := Z2Satisfiable →
  ∃ (X : Type) (M : DESTSet.Model X), DESTSet.CofinalReflection M ∧ DESTSet.InternallyCountable M

end DESTExact
