import DEST.ArithmeticSpecification

set_option autoImplicit false
universe u
namespace DESTArithmetic
open DESTReference DESTStrength

/-- Internal Kuratowski pair. No external pair coding or standardness assumption. -/
def PairCode {X : Type u} (m : X → X → Prop) (p a b : X) : Prop :=
  ∃ s t, (∀ y, m y s ↔ y = a) ∧ (∀ y, m y t ↔ y = a ∨ y = b) ∧
    (∀ y, m y p ↔ y = s ∨ y = t)

def GraphValue {X : Type u} (m : X → X → Prop) (g k v : X) : Prop :=
  ∃ p, m p g ∧ PairCode m p k v

def Index {X : Type u} (m : X → X → Prop) (k n : X) : Prop := k = n ∨ m k n

/-- The finite graph has precisely the indicated index domain, numerical
values, a unique value at each index, the specified base and transition. -/
structure RecGraph {X : Type u} (m : X → X → Prop) (H : X → X → Prop)
    (z w i n g : X) : Prop where
  range : ∀ k v, GraphValue m g k v → Index m k n ∧ m v w
  total : ∀ k, Index m k n → ∃ v, GraphValue m g k v
  functional : ∀ k b c, GraphValue m g k b → GraphValue m g k c → b = c
  base : GraphValue m g z i
  next : ∀ k l b c, GraphValue m g k b → GraphValue m g l c → SuccRel m k l → H b c

def RecOutput {X : Type u} (m : X → X → Prop) (H : X → X → Prop)
    (z w i n v : X) : Prop := ∃ g, RecGraph m H z w i n g ∧ GraphValue m g n v

/-- z,w,a are fixed context objects, b,c the old/new values. -/
abbrev StepSyntax := {n : ℕ} → Fin n → Fin n → Fin n → Fin n → Fin n → Formula n

def StepCorrect {X : Type u} (m r : X → X → Prop) (step : StepSyntax)
    (H : X → X → X → X → X → Prop) : Prop :=
  ∀ {n : ℕ} (v : Fin n → X) (z w a b c : Fin n),
    (step z w a b c).eval m r v ↔ H (v z) (v w) (v a) (v b) (v c)
def pairF {n : ℕ} (p a b : Fin n) : Formula n :=
  (ex (ex (conj (Formula.all (iffF (Formula.mem1 0 (Fin.succ (Fin.succ 0))) (Formula.eq 0 a.succ.succ.succ))) (conj (Formula.all (iffF (Formula.mem1 0 (Fin.succ 0)) (disj (Formula.eq 0 a.succ.succ.succ) (Formula.eq 0 b.succ.succ.succ)))) (Formula.all (iffF (Formula.mem1 0 p.succ.succ.succ) (disj (Formula.eq 0 (Fin.succ (Fin.succ 0))) (Formula.eq 0 (Fin.succ 0)))))))))
def valueF {n : ℕ} (g k v : Fin n) : Formula n :=
  (ex (conj (Formula.mem1 0 g.succ) (pairF 0 k.succ v.succ)))
def indexF {n : ℕ} (k t : Fin n) : Formula n :=
  (disj (Formula.eq k t) (Formula.mem1 k t))
def graphF {n : ℕ} (step : StepSyntax) (z w a i t g : Fin n) : Formula n :=
  (conj (Formula.all (Formula.all (Formula.imp (valueF g.succ.succ (Fin.succ 0) 0) (conj (indexF (Fin.succ 0) t.succ.succ) (Formula.mem1 0 w.succ.succ))))) (conj (Formula.all (Formula.imp (indexF 0 t.succ) (ex (valueF g.succ.succ (Fin.succ 0) 0)))) (conj (Formula.all (Formula.all (Formula.all (Formula.imp (valueF g.succ.succ.succ (Fin.succ (Fin.succ 0)) (Fin.succ 0)) (Formula.imp (valueF g.succ.succ.succ (Fin.succ (Fin.succ 0)) 0) (Formula.eq (Fin.succ 0) 0)))))) (conj (valueF g z i) (Formula.all (Formula.all (Formula.all (Formula.all (Formula.imp (valueF g.succ.succ.succ.succ (Fin.succ (Fin.succ (Fin.succ 0))) (Fin.succ 0)) (Formula.imp (valueF g.succ.succ.succ.succ (Fin.succ (Fin.succ 0)) 0) (Formula.imp (succF (Fin.succ (Fin.succ (Fin.succ 0))) (Fin.succ (Fin.succ 0))) (step z.succ.succ.succ.succ w.succ.succ.succ.succ a.succ.succ.succ.succ (Fin.succ 0) 0))))))))))))
def graphExistsF {n : ℕ} (step : StepSyntax) (z w a i t : Fin n) : Formula n :=
  (ex (conj (uniformF 0) (conj (Formula.all (Formula.imp (Formula.mem1 0 (Fin.succ 0)) (uniformF 0))) (graphF step z.succ w.succ a.succ i.succ t.succ 0))))
def agreeF {n : ℕ} (g h k : Fin n) : Formula n :=
  (Formula.all (Formula.all (Formula.imp (valueF g.succ.succ k.succ.succ (Fin.succ 0)) (Formula.imp (valueF h.succ.succ k.succ.succ 0) (Formula.eq (Fin.succ 0) 0)))))
def outputF {n : ℕ} (step : StepSyntax) (z w a i t v : Fin n) : Formula n :=
  (ex (conj (graphF step z.succ w.succ a.succ i.succ t.succ 0) (valueF 0 t.succ v.succ)))

def AddRel {X : Type u} (m : X → X → Prop) (z w a n v : X) : Prop :=
  RecOutput m (SuccRel m) z w a n v

def MulRel {X : Type u} (m : X → X → Prop) (z w a n v : X) : Prop :=
  RecOutput m (fun b c => AddRel m z w b a c) z w z n v

def succStep : StepSyntax := fun {_} _ _ _ b c => succF b c

def addF {n : ℕ} (z w a b c : Fin n) : Formula n := outputF succStep z w a a b c

def mulStep : StepSyntax := fun {_} z w a b c => addF z w b a c

def mulF {n : ℕ} (z w a b c : Fin n) : Formula n := outputF mulStep z w a z b c

/-- Arithmetic operations in arbitrary internal natural-number structures. -/
structure ArithmeticLaws {X : Type u} (m : X → X → Prop) (z w : X) : Prop where
  add_total : ∀ a b, m a w → m b w → ∃ c, m c w ∧ AddRel m z w a b c
  add_unique : ∀ a b c d, m b w → AddRel m z w a b c → AddRel m z w a b d → c = d
  add_range : ∀ a b c, AddRel m z w a b c → m c w
  add_zero : ∀ a, m a w → AddRel m z w a z a
  add_succ : ∀ a b c b' c', m b w → m b' w → AddRel m z w a b c →
    SuccRel m b b' → SuccRel m c c' → m c' w → AddRel m z w a b' c'
  mul_total : ∀ a b, m a w → m b w → ∃ c, m c w ∧ MulRel m z w a b c
  mul_unique : ∀ a b c d, m a w → m b w → MulRel m z w a b c → MulRel m z w a b d → c = d
  mul_range : ∀ a b c, MulRel m z w a b c → m c w
  mul_zero : ∀ a, m a w → MulRel m z w a z z
  mul_succ : ∀ a b c b' c', m a w → m b w → m b' w → MulRel m z w a b c →
    SuccRel m b b' → AddRel m z w c a c' → m c' w → MulRel m z w a b' c'

end DESTArithmetic
