import DEST.Specification
import DEST.ReferenceTheory

set_option autoImplicit false
set_option maxHeartbeats 0

universe u

namespace DESTSemantic
open DESTReference

/-- The translation drops the second atom only in the impossible case where
    a supposedly first-language formula actually contains that atom. -/
def erase : {n : ℕ} → Formula n → DEST.Formula
  | _, .bot => .bot
  | _, .eq i j => .eq i.val j.val
  | _, .mem1 i j => .mem i.val j.val
  | _, .mem2 _ _ => .bot
  | _, .imp p q => .imp (erase p) (erase q)
  | _, .all p => .all (erase p)

/-- A list of all parameter values in order, without any assumption of
    distinctness, uniformity, or a bound on the length. -/
def params {X : Type u} : {n : ℕ} → (Fin n → X) → List X
  | 0, _ => []
  | _+1, v => v 0 :: params (fun i => v i.succ)

theorem params_lookup (D : Set DEST.A) {n : ℕ} (v : Fin n → D) (i : Fin n) :
    ((params v).map Subtype.val)[i.val]? = some (v i).val := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [params]
    · simpa [params] using ih (fun k => v k.succ) j

theorem params_all {X : Type u} {n : ℕ} (P : X → Prop) (v : Fin n → X)
    (h : ∀ i, P (v i)) : ∀ a ∈ params v, P a := by
  induction n with
  | zero => simp [params]
  | succ n ih =>
    intro a ha
    change a ∈ v 0 :: params (fun i => v i.succ) at ha
    rcases List.mem_cons.mp ha with he | ht
    · rw [he]; exact h 0
    · exact ih (fun i => v i.succ) (fun i => h i.succ) a ht

/-- S1/S3: semantic preservation on *every* well-scoped first-language
    formula, in any domain, not just formulas used in the construction. -/
theorem first_language_translation (D : Set DEST.A) (r : D → D → Prop)
    {n : ℕ} (p : Formula n) (hp : p.firstOnly) (v : Fin n → D) (l : List DEST.A)
    (hl : ∀ i : Fin n, l[i.val]? = some (v i).val) :
    p.eval (DESTVerification.first D) r v ↔ (erase p).eval D l := by
  induction p generalizing l with
  | bot => rfl
  | eq i j =>
    simp only [erase, Formula.eval, DEST.Formula.eval, hl, Option.some.injEq]
    constructor
    · intro h; exact ⟨(v i).val, rfl, congrArg Subtype.val h.symm⟩
    · rintro ⟨a, hi, hj⟩; exact Subtype.ext (hi.trans hj.symm)
  | mem1 i j =>
    simp [erase, Formula.eval, DEST.Formula.eval, hl, DESTVerification.first]
  | mem2 i j => exact False.elim hp
  | imp p q ihp ihq =>
    change p.firstOnly ∧ q.firstOnly at hp
    simp only [erase, Formula.eval, DEST.Formula.eval, ihp hp.1 v l hl, ihq hp.2 v l hl]
  | all p ih =>
    change p.firstOnly at hp
    change (∀ a : D, p.eval (DESTVerification.first D) r (push a v)) ↔
      (∀ a ∈ D, (erase p).eval D (a :: l))
    have h (a : D) : ∀ i, (a.val :: l)[i.val]? = some (push a v i).val := by
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · simpa using hl j
    constructor
    · intro hAll a ha
      exact (ih hp (push ⟨a, ha⟩ v) (a :: l) (h ⟨a, ha⟩)).mp (hAll ⟨a, ha⟩)
    · intro hAll a
      exact (ih hp (push a v) (a.val :: l) (h a)).mpr (hAll a.val a.property)

theorem unary_translation (D : Set DEST.A) (r : D → D → Prop) {n : ℕ}
    (p : Formula (n+1)) (hp : p.firstOnly) (v : Fin n → D) (y : D) :
    p.eval (DESTVerification.first D) r (push y v) ↔
      (erase p).eval D (y.val :: (params v).map Subtype.val) := by
  apply first_language_translation D r p hp
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simpa using params_lookup D v j

section Semantics
variable {X : Type u} (m1 m2 : X → X → Prop)

@[simp] theorem uniformF_correct {n : ℕ} (i : Fin n) (v : Fin n → X) :
    (uniformF i).eval m1 m2 v ↔ ∀ y, m1 y (v i) ↔ m2 y (v i) := by
  simp [uniformF, Formula.eval]

@[simp] theorem allUniform_correct {n : ℕ} (v : Fin n → X) :
    (allUniform n).eval m1 m2 v ↔ ∀ i : Fin n, ∀ y, m1 y (v i) ↔ m2 y (v i) := by
  induction n with
  | zero =>
    constructor
    · intro _ i; exact Fin.elim0 i
    · intro _; simp [allUniform]
  | succ n ih =>
    simp only [allUniform, eval_conj, uniformF_correct, eval_rename, ih]
    constructor
    · intro h i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact h.1
      · exact h.2 j
    · intro h; exact ⟨h 0, fun i => h i.succ⟩

@[simp] theorem extension_correct {n : ℕ} (p : Formula (n+1)) (x : X) (v : Fin n → X) :
    (extensionF p).eval m1 m2 (push x v) ↔
      ∀ y : X, m2 y x ↔ p.eval m1 m2 (push y v) := by
  simp [extensionF, Formula.eval]

/-- S2: the literal capture-avoiding self test equals non-self-membership
    under the comprehension condition. This is a theorem, not a convention. -/
theorem self_test_correct {n : ℕ} (p : Formula (n+1)) (x : X) (v : Fin n → X)
    (h : ∀ y : X, m2 y x ↔ p.eval m1 m2 (push y v)) :
    (¬ p.eval m1 m2 (push x v)) ↔ ¬ m2 x x := not_congr (h x).symm

@[simp] theorem zero_correct {n : ℕ} (i : Fin n) (v : Fin n → X) :
    (zeroF i).eval m1 m2 v ↔ ∀ a, ¬ m1 a (v i) := by
  simp [zeroF, Formula.eval]
@[simp] theorem succ_correct {n : ℕ} (i j : Fin n) (v : Fin n → X) :
    (succF i j).eval m1 m2 v ↔ ∀ a, m1 a (v j) ↔ a = v i ∨ m1 a (v i) := by
  simp [succF, Formula.eval]
@[simp] theorem inductive_correct {n : ℕ} (i j : Fin n) (v : Fin n → X) :
    (inductiveF i j).eval m1 m2 v ↔ m1 (v i) (v j) ∧
      ∀ a, m1 a (v j) → ∃ b, m1 b (v j) ∧ (∀ c, m1 c b ↔ c = a ∨ m1 c a) := by
  simp [inductiveF, Formula.eval]
@[simp] theorem omega_correct {n : ℕ} (i j : Fin n) (v : Fin n → X) :
    (omegaF i j).eval m1 m2 v ↔
      (m1 (v i) (v j) ∧ ∀ a, m1 a (v j) → ∃ b, m1 b (v j) ∧
        (∀ c, m1 c b ↔ c = a ∨ m1 c a)) ∧
      (∀ t, (m1 (v i) t ∧ ∀ a, m1 a t → ∃ b, m1 b t ∧
        (∀ c, m1 c b ↔ c = a ∨ m1 c a)) → ∀ a, m1 a (v j) → m1 a t) := by
  simp [omegaF, Formula.eval]
/-- Explicit correspondence of the closed comprehension sentence with its
    intended universally closed scheme. -/
theorem comprehension_correct {n : ℕ} (p : Formula (n+1)) :
    (comprehension p).eval m1 m2 Fin.elim0 ↔
      ∀ v : Fin n → X, ∃ a : X, ∀ y : X, m2 y a ↔ p.eval m1 m2 (push y v) := by
  simp only [comprehension, eval_close, eval_ex, extension_correct]

theorem uniformity_correct {n : ℕ} (p : Formula (n+1)) :
    (uniformity p).eval m1 m2 Fin.elim0 ↔
      ∀ v : Fin n → X, (∀ i : Fin n, ∀ y, m1 y (v i) ↔ m2 y (v i)) →
      ∀ a : X, (∀ y, m2 y a ↔ p.eval m1 m2 (push y v)) →
      ¬ p.eval m1 m2 (push a v) → ∀ y, m1 y a ↔ m2 y a := by
  simp only [uniformity, eval_close, Formula.eval, allUniform_correct,
    extension_correct, eval_neg, uniformF_correct, push_zero]

theorem first_extensionality_correct :
    (extensionality false).eval m1 m2 Fin.elim0 ↔
      ∀ a b : X, (∀ y, m1 y a ↔ m1 y b) → a = b := by
  simp [extensionality, Formula.eval] <;> (constructor <;> intro h a b he <;> exact h b a he)

theorem second_extensionality_correct :
    (extensionality true).eval m1 m2 Fin.elim0 ↔
      ∀ a b : X, (∀ y, m2 y a ↔ m2 y b) → a = b := by
  simp [extensionality, Formula.eval] <;> (constructor <;> intro h a b he <;> exact h b a he)

theorem setInduction_correct {n : ℕ} (p : Formula (n+1)) :
    (setInduction p).eval m1 m2 Fin.elim0 ↔
      ∀ v : Fin n → X, (∀ a : X, (∀ y : X, m1 y a → p.eval m1 m2 (push y v)) →
        p.eval m1 m2 (push a v)) → ∀ a : X, p.eval m1 m2 (push a v) := by
  simp only [setInduction, eval_close, Formula.eval, eval_atVar, push_zero, push_succ]

end Semantics

/-- S2/S4/S5: every closed sentence of the independently defined reference
    theory holds in the SAME model specified by the existing proof. -/
theorem model_satisfies_reference (D : Set DEST.A) (r : D → D → Prop)
    (num : ℕ → D) (w : D) (h : DESTVerification.ModelSpec D r num w) :
    Satisfies (DESTVerification.first D) r := by
  classical
  let m := DESTVerification.first D
  rcases h with ⟨⟨ext1, ext2, comp, unif⟩, wf, hw, hn, inj, hz, hs, hex, hind, hleast, hnat, hset⟩
  intro s ax
  cases ax with
  | ext1 =>
    exact (first_extensionality_correct m r).mpr ext1
  | ext2 =>
    exact (second_extensionality_correct m r).mpr ext2
  | comp p hp =>
    apply (comprehension_correct m r p).mpr
    intro v
    obtain ⟨a, ha⟩ := comp (erase p) (params v)
    exact ⟨a, fun y => (ha y).trans (unary_translation D r p hp v y).symm⟩
  | unif p hp =>
    apply (uniformity_correct m r p).mpr
    intro v hv a ha hna
    have hr : ∀ y, r y a ↔ (erase p).eval D (y.val :: (params v).map Subtype.val) :=
      fun y => (ha y).trans (unary_translation D r p hp v y)
    have hu : ∀ b ∈ params v, DESTVerification.uniform D r b := params_all _ v hv
    exact unif (erase p) (params v) hu a hr ((self_test_correct m r p a v ha).mp hna)
  | inf =>
    simp only [infinity, eval_ex, eval_conj, zero_correct, omega_correct, push_zero, push_succ]
    exact ⟨w, num 0, hz, hind, hleast⟩
  | natInd p =>
    simp only [naturalInduction, eval_close, Formula.eval, natBody, eval_conj,
      zero_correct, omega_correct, succ_correct, eval_atVar, push_zero, push_succ]
    intro v w' z hzw hb hstep a ha
    obtain ⟨hz', hw'⟩ := hzw
    have ez : z = num 0 := ext1 _ _ (fun y => ⟨fun hy => (hz' y hy).elim, fun hy => (hz y hy).elim⟩)
    subst z
    have ew : w' = w := ext1 _ _ (fun y => ⟨hw'.2 w hind y, hleast w' hw'.1 y⟩)
    subst w'
    apply hnat (fun y => p.eval m r (push y v)) hb _ a ha
    intro k hk
    exact hstep (num k) ((hex _).mpr ⟨k, rfl⟩) (num (k+1)) (fun y => hs y k) hk
  | setInd p =>
    apply (setInduction_correct m r p).mpr
    intro v h
    exact hset (fun a => p.eval m r (push a v)) h

end DESTSemantic
