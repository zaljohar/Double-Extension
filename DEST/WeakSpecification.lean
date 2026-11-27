import DEST.StrengthSpecification
import DEST.Specification

/-! Independent ambient numeral specification for the finite-fragment
    reflection endpoint. No implementation module is imported. -/
set_option autoImplicit false

namespace DESTWeak

noncomputable def ambientNumeral : ℕ → DEST.A
  | 0 => ∅
  | n+1 => insert (ambientNumeral n) (ambientNumeral n)

noncomputable def ambientOmega : DEST.A := ZFSet.range ambientNumeral

/-- Independent first-language erasure for the closed-sentence endpoint. -/
def eraseFirst : {n : ℕ} → DESTReference.Formula n → DEST.Formula
  | _, .bot => .bot
  | _, .eq i j => .eq i.val j.val
  | _, .mem1 i j => .mem i.val j.val
  | _, .mem2 _ _ => .bot
  | _, .imp p q => .imp (eraseFirst p) (eraseFirst q)
  | _, .all p => .all (eraseFirst p)

end DESTWeak
