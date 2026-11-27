import DEST.TwoSortedSpecification

set_option autoImplicit false
universe u
namespace DESTArithmetic
open DESTReference DESTStrength

abbrev Number {X : Type u} (m : X → X → Prop) (w : X) := {a : X // m a w}
abbrev RealObject {X : Type u} (m : X → X → Prop) (w : X) := {a : X // IsReal m w a}

/-- Actual operations on the number sort; not operations on external Nat. -/
structure NumberOperations {X : Type u} (m : X → X → Prop) (z w : X) where
  zero : Number m w
  succ : Number m w → Number m w
  add : Number m w → Number m w → Number m w
  mul : Number m w → Number m w → Number m w
  zero_ok : zero.val = z
  succ_ok : ∀ a, SuccRel m a.val (succ a).val
  add_ok : ∀ a b, AddRel m z w a.val b.val (add a b).val
  mul_ok : ∀ a b, MulRel m z w a.val b.val (mul a b).val

inductive NumTerm : ℕ → Type where
  | var {n : ℕ} : Fin n → NumTerm n
  | zero {n : ℕ} : NumTerm n
  | succ {n : ℕ} : NumTerm n → NumTerm n
  | add {n : ℕ} : NumTerm n → NumTerm n → NumTerm n
  | mul {n : ℕ} : NumTerm n → NumTerm n → NumTerm n

def NumTerm.eval {X : Type u} {m : X → X → Prop} {z w : X}
    (o : NumberOperations m z w) : {n : ℕ} → NumTerm n → (Fin n → Number m w) → Number m w
  | _, .var a, v => v a
  | _, .zero, _ => o.zero
  | _, .succ a, v => o.succ (a.eval o v)
  | _, .add a b, v => o.add (a.eval o v) (b.eval o v)
  | _, .mul a b, v => o.mul (a.eval o v) (b.eval o v)

def arNeg {n : ℕ} (p : ArithFormula n) : ArithFormula n := .imp p .bot
def arAnd {n : ℕ} (p q : ArithFormula n) : ArithFormula n := arNeg (.imp p (arNeg q))
def arExNum {n : ℕ} (p : ArithFormula (n+1)) : ArithFormula n := arNeg (.allNum (arNeg p))

/-- A term denotes the object at position b, with numerical existential
witnesses for all intermediate subterms. -/
def NumTerm.graph : {n : ℕ} → NumTerm n → {d : ℕ} → (Fin n → Fin d) → Fin d → ArithFormula d
  | _, .var a, _, f, b => .eq b (f a)
  | _, .zero, _, _, b => .zero b
  | _, .succ t, _, f, b => arExNum (arAnd (t.graph (fun i => (f i).succ) 0) (.succ 0 b.succ))
  | _, .add t s, _, f, b => arExNum (arExNum (arAnd
      (t.graph (fun i => (f i).succ.succ) (Fin.succ 0))
      (arAnd (s.graph (fun i => (f i).succ.succ) 0) (.add (Fin.succ 0) 0 b.succ.succ))))
  | _, .mul t s, _, f, b => arExNum (arExNum (arAnd
      (t.graph (fun i => (f i).succ.succ) (Fin.succ 0))
      (arAnd (s.graph (fun i => (f i).succ.succ) 0) (.mul (Fin.succ 0) 0 b.succ.succ))))

/-- Standard genuinely two-sorted first-order syntax for second-order
arithmetic (Henkin semantics). Number terms use only numeric variables;
real variables have their own independently scoped context. -/
inductive StandardFormula : ℕ → ℕ → Type where
  | bot {n k : ℕ} : StandardFormula n k
  | numEq {n k : ℕ} : NumTerm n → NumTerm n → StandardFormula n k
  | realEq {n k : ℕ} : Fin k → Fin k → StandardFormula n k
  | mem {n k : ℕ} : NumTerm n → Fin k → StandardFormula n k
  | imp {n k : ℕ} : StandardFormula n k → StandardFormula n k → StandardFormula n k
  | allNum {n k : ℕ} : StandardFormula (n+1) k → StandardFormula n k
  | allReal {n k : ℕ} : StandardFormula n (k+1) → StandardFormula n k

def StandardFormula.eval {X : Type u} {m : X → X → Prop} {z w : X}
    (o : NumberOperations m z w) : {n k : ℕ} → StandardFormula n k →
      (Fin n → Number m w) → (Fin k → RealObject m w) → Prop
  | _, _, .bot, _, _ => False
  | _, _, .numEq t s, v, _ => t.eval o v = s.eval o v
  | _, _, .realEq a b, _, v => v a = v b
  | _, _, .mem t a, v, e => m (t.eval o v).val (e a).val
  | _, _, .imp p q, v, e => p.eval o v e → q.eval o v e
  | _, _, .allNum p, v, e => ∀ a : Number m w, p.eval o (push a v) e
  | _, _, .allReal p, v, e => ∀ a : RealObject m w, p.eval o v (push a e)

def StandardFormula.relationalize : {n k : ℕ} → StandardFormula n k → {d : ℕ} →
      (Fin n → Fin d) → (Fin k → Fin d) → ArithFormula d
  | _, _, .bot, _, _, _ => .bot
  | _, _, .numEq t s, _, f, _ => arExNum (arExNum (arAnd
      (t.graph (fun i => (f i).succ.succ) (Fin.succ 0))
      (arAnd (s.graph (fun i => (f i).succ.succ) 0) (.eq (Fin.succ 0) 0))))
  | _, _, .realEq a b, _, _, e => .eq (e a) (e b)
  | _, _, .mem t a, _, f, e => arExNum (arAnd (t.graph (fun i => (f i).succ) 0) (.mem 0 (e a).succ))
  | _, _, .imp p q, _, f, e => .imp (p.relationalize f e) (q.relationalize f e)
  | _, _, .allNum p, _, f, e => .allNum (p.relationalize (liftRen f) (fun i => (e i).succ))
  | _, _, .allReal p, _, f, e => .allReal (p.relationalize (fun i => (f i).succ) (liftRen e))

/-- The usual functional-language axioms of PA and full parameter-free
second-order comprehension, with induction for all formulas and parameters. -/
structure StandardArithmeticModel {X : Type u} {m : X → X → Prop} {z w : X}
    (o : NumberOperations m z w) : Prop where
  succ_ne_zero : ∀ a, o.succ a ≠ o.zero
  succ_injective : Function.Injective o.succ
  add_zero : ∀ a, o.add a o.zero = a
  add_succ : ∀ a b, o.add a (o.succ b) = o.succ (o.add a b)
  mul_zero : ∀ a, o.mul a o.zero = o.zero
  mul_succ : ∀ a b, o.mul a (o.succ b) = o.add (o.mul a b) a
  real_ext : ∀ a b : RealObject m w, (∀ k : Number m w, m k.val a.val ↔ m k.val b.val) → a = b
  comprehension : ∀ {n : ℕ} (p : StandardFormula (n+1) 0) (v : Fin n → Number m w),
    ∃ A : RealObject m w, ∀ k : Number m w, m k.val A.val ↔ p.eval o (push k v) Fin.elim0
  induction_schema : ∀ {n k : ℕ} (p : StandardFormula (n+1) k)
    (v : Fin n → Number m w) (e : Fin k → RealObject m w),
    p.eval o (push o.zero v) e →
    (∀ a, p.eval o (push a v) e → p.eval o (push (o.succ a) v) e) →
    ∀ a, p.eval o (push a v) e

end DESTArithmetic
