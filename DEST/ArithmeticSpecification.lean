import DEST.StrengthSpecification

set_option autoImplicit false

universe u
namespace DESTArithmetic
open DESTReference DESTStrength

/-- All first-membership subsets, not only uniform ones. -/
def IsReal {X : Type u} (m : X → X → Prop) (w a : X) : Prop :=
  ∀ y, m y a → m y w

/-- A relational language with arbitrary first-language definable atoms.
The distinguished omega parameter is the newest variable of each atom.
Quantifiers have explicit number or real guards. This is a formula
translation interface, not an assertion that arithmetic operations exist. -/
inductive Guarded : ℕ → Type where
  | atom {n : ℕ} (p : Formula (n+1)) : p.firstOnly → Guarded n
  | bot {n : ℕ} : Guarded n
  | imp {n : ℕ} : Guarded n → Guarded n → Guarded n
  | allNum {n : ℕ} : Guarded (n+1) → Guarded n
  | allReal {n : ℕ} : Guarded (n+1) → Guarded n

def Guarded.eval {X : Type u} (m : X → X → Prop) (w : X) :
    {n : ℕ} → Guarded n → (Fin n → X) → Prop
  | _, .atom p _, v => p.eval m m (push w v)
  | _, .bot, _ => False
  | _, .imp p q, v => p.eval m w v → q.eval m w v
  | _, .allNum p, v => ∀ a, m a w → p.eval m w (push a v)
  | _, .allReal p, v => ∀ a, IsReal m w a → p.eval m w (push a v)

def swapHead {n : ℕ} : Fin (n+2) → Fin (n+2) :=
  Fin.cases (Fin.succ 0) (Fin.cases 0 (fun i => i.succ.succ))

def subsetF {n : ℕ} (a b : Fin n) : Formula n :=
  .all (.imp (.mem1 0 a.succ) (.mem1 0 b.succ))

/-- Translate into the actual first-order reference language. When a new
variable is bound it is inserted before omega, so the head swap restores
omega to the distinguished position in the recursive translation. -/
def Guarded.translate : {n : ℕ} → Guarded n → Formula (n+1)
  | _, .atom p _ => p
  | _, .bot => .bot
  | _, .imp p q => .imp p.translate q.translate
  | _, .allNum p => .all (.imp (.mem1 0 (Fin.succ 0)) (p.translate.rename swapHead))
  | _, .allReal p => .all (.imp (subsetF 0 (Fin.succ 0)) (p.translate.rename swapHead))

def SuccRel {X : Type u} (m : X → X → Prop) (a b : X) : Prop :=
  ∀ y, m y b ↔ y = a ∨ m y a

def TransitiveObject {X : Type u} (m : X → X → Prop) (a : X) : Prop :=
  ∀ y x, m x y → m y a → m x a

/-- Basic Peano successor properties, proved without assuming an externally
standard numeral frame. Addition and multiplication are not included here. -/
structure SuccessorLaws {X : Type u} (m : X → X → Prop) (z w : X) : Prop where
  zero_mem : m z w
  total : ∀ a, m a w → ∃ b, m b w ∧ SuccRel m a b
  functional : ∀ a b c, SuccRel m a b → SuccRel m a c → b = c
  not_zero : ∀ a b, SuccRel m a b → b ≠ z
  injective : ∀ a b c, m a w → m b w → SuccRel m a c → SuccRel m b c → a = b
  predecessor : ∀ a, m a w → a = z ∨ ∃ b, m b w ∧ SuccRel m b a
  transitive : ∀ a, m a w → TransitiveObject m a
  irreflexive : ∀ a, m a w → ¬ m a a
  members : ∀ a, m a w → ∀ y, m y a → m y w

end DESTArithmetic
