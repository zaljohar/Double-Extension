import DEST.OriginalSpecification
import DEST.ReferenceLogic

/-! Closed-sentence formulation of original DEST, with no Infinity axiom.
The relational induction scheme uses membership in every inductive set,
including when no inductive set is initially given. -/
set_option autoImplicit false
namespace DESTOriginalClosed
open DESTReference

def naturalF {n : ℕ} (z a : Fin n) : Formula n :=
  .all (.imp (inductiveF z.succ 0) (.mem1 a.succ 0))

-- The free context is z followed by the n parameters of p.
def natBody {n : ℕ} (p : Formula (n+1)) : Formula (n+1) :=
  .imp (zeroF 0)
    (.imp (atVar p 0 (fun i => i.succ))
      (.imp (.all (.imp (naturalF (Fin.succ 0) 0)
        (.all (.imp (succF (Fin.succ 0) 0)
          (.imp (atVar p (Fin.succ 0) (fun i => i.succ.succ.succ))
            (atVar p 0 (fun i => i.succ.succ.succ)))))))
        (.all (.imp (naturalF (Fin.succ 0) 0)
          (atVar p 0 (fun i => i.succ.succ))))))

def naturalInduction {n : ℕ} (p : Formula (n+1)) : Sentence :=
  close (Formula.all (natBody p))

inductive Axiom : Sentence → Prop where
  | ext1 : Axiom (extensionality false)
  | ext2 : Axiom (extensionality true)
  | comp {n : ℕ} (p : Formula (n+1)) : p.firstOnly → Axiom (comprehension p)
  | unif {n : ℕ} (p : Formula (n+1)) : p.firstOnly → Axiom (DESTReference.uniformity p)
  | natInd {n : ℕ} (p : Formula (n+1)) : Axiom (naturalInduction p)

universe u

def Satisfies {X : Type u} (m r : X → X → Prop) : Prop :=
  ∀ s, Axiom s → s.eval m r Fin.elim0

def Consistent : Prop := ¬ Derives Axiom (.bot : Sentence)

end DESTOriginalClosed
