import DEST.RecursionSpecification

set_option autoImplicit false
universe u
namespace DESTArithmetic
open DESTReference DESTStrength

/-- Relational arithmetic syntax, independent of the set-theoretic translation.
The single variable context is the disjoint list of number and real variables;
quantifier constructors retain the sort. Every well-sorted relational
arithmetic formula is included (the grammar also permits unsorted atoms).
Terms involving 0, successor, addition and multiplication can be flattened
into relational atoms by introducing number-bound witnesses. -/
inductive ArithFormula : ℕ → Type where
  | bot {n : ℕ} : ArithFormula n
  | eq {n : ℕ} : Fin n → Fin n → ArithFormula n
  | mem {n : ℕ} : Fin n → Fin n → ArithFormula n
  | zero {n : ℕ} : Fin n → ArithFormula n
  | succ {n : ℕ} : Fin n → Fin n → ArithFormula n
  | add {n : ℕ} : Fin n → Fin n → Fin n → ArithFormula n
  | mul {n : ℕ} : Fin n → Fin n → Fin n → ArithFormula n
  | imp {n : ℕ} : ArithFormula n → ArithFormula n → ArithFormula n
  | allNum {n : ℕ} : ArithFormula (n+1) → ArithFormula n
  | allReal {n : ℕ} : ArithFormula (n+1) → ArithFormula n

def ArithFormula.eval {X : Type u} (m : X → X → Prop) (z w : X) :
    {n : ℕ} → ArithFormula n → (Fin n → X) → Prop
  | _, .bot, _ => False
  | _, .eq a b, v => v a = v b
  | _, .mem a b, v => m (v a) (v b)
  | _, .zero a, v => v a = z
  | _, .succ a b, v => SuccRel m (v a) (v b)
  | _, .add a b c, v => AddRel m z w (v a) (v b) (v c)
  | _, .mul a b c, v => MulRel m z w (v a) (v b) (v c)
  | _, .imp p q, v => p.eval m z w v → q.eval m z w v
  | _, .allNum p, v => ∀ a, m a w → p.eval m z w (push a v)
  | _, .allReal p, v => ∀ a, IsReal m w a → p.eval m z w (push a v)

/-- z,w are the indices of the empty object and omega in the target
context. f embeds the arithmetic variables in that same context. -/
def ArithFormula.translate : {n : ℕ} → ArithFormula n → {d : ℕ} →
    Fin d → Fin d → (Fin n → Fin d) → Formula d
  | _, .bot, _, _, _, _ => .bot
  | _, .eq a b, _, _, _, f => .eq (f a) (f b)
  | _, .mem a b, _, _, _, f => .mem1 (f a) (f b)
  | _, .zero a, _, z, _, f => .eq (f a) z
  | _, .succ a b, _, _, _, f => succF (f a) (f b)
  | _, .add a b c, _, z, w, f => addF z w (f a) (f b) (f c)
  | _, .mul a b c, _, z, w, f => mulF z w (f a) (f b) (f c)
  | _, .imp p q, _, z, w, f => .imp (p.translate z w f) (q.translate z w f)
  | _, .allNum p, _, z, w, f =>
    .all (.imp (.mem1 0 w.succ) (p.translate z.succ w.succ (liftRen f)))
  | _, .allReal p, _, z, w, f =>
    .all (.imp (subsetF 0 w.succ) (p.translate z.succ w.succ (liftRen f)))

/-- Semantic parameter-free relational second-order arithmetic. All free
parameters in comprehension are numbers, while induction permits arbitrary
parameters. Set quantifiers range over all first-membership subsets. This
specification states closure under the complete relational grammar above;
it is not a claim about the internal arithmetization of proof systems. -/
structure ParamFreeArithmetic {X : Type u} (m : X → X → Prop) (z w : X) : Prop where
  successor : SuccessorLaws m z w
  arithmetic : ArithmeticLaws m z w
  real_ext : ∀ a b, IsReal m w a → IsReal m w b →
    (∀ k, m k w → (m k a ↔ m k b)) → a = b
  comprehension : ∀ {n : ℕ} (p : ArithFormula (n+1)) (v : Fin n → X),
    (∀ j, m (v j) w) → ∃ A, IsReal m w A ∧
      ∀ k, m k w → (m k A ↔ p.eval m z w (push k v))
  induction_schema : ∀ {n : ℕ} (p : ArithFormula (n+1)) (v : Fin n → X),
    p.eval m z w (push z v) →
    (∀ a, m a w → ∀ b, SuccRel m a b → p.eval m z w (push a v) →
      p.eval m z w (push b v)) → ∀ a, m a w → p.eval m z w (push a v)

end DESTArithmetic
