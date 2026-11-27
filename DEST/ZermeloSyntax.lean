import DEST.Original

set_option autoImplicit false
set_option maxHeartbeats 0
universe u
namespace DESTOriginal
open DESTReference

theorem succF_first {n : ℕ} (a b : Fin n) : (succF a b).firstOnly := by
  simp [succF,iffF,conj,disj,neg,Formula.firstOnly]

def subF {n : ℕ} (a b : Fin n) : Formula n :=
  (Formula.all (Formula.imp (Formula.mem1 0 (Fin.succ a)) (Formula.mem1 0 (Fin.succ b))))

@[simp] theorem subF_correct {X : Type u} (m r : X → X → Prop) {n : ℕ}
    (v : Fin n → X) (a b : Fin n) :
    (subF a b).eval m r v ↔ Sub m (v a) (v b) := by
  simp only [subF,Sub,eval_conj,eval_disj,eval_neg,eval_iffF,eval_ex,Formula.eval,
    push_zero,push_succ,DESTSemantic.push_push_one]

theorem subF_first {n : ℕ} (a b : Fin n) : (subF a b).firstOnly := by
  simp [subF,Formula.firstOnly,neg,conj,disj,iffF,ex]

def transF {n : ℕ} (a : Fin n) : Formula n :=
  (Formula.all (Formula.all (Formula.imp (Formula.mem1 0 (Fin.succ 0)) (Formula.imp (Formula.mem1 (Fin.succ 0) (Fin.succ (Fin.succ a))) (Formula.mem1 0 (Fin.succ (Fin.succ a)))))))

@[simp] theorem transF_correct {X : Type u} (m r : X → X → Prop) {n : ℕ}
    (v : Fin n → X) (a : Fin n) :
    (transF a).eval m r v ↔ Transitive m (v a) := by
  simp only [transF,Transitive,eval_conj,eval_disj,eval_neg,eval_iffF,eval_ex,Formula.eval,
    push_zero,push_succ,DESTSemantic.push_push_one]

theorem transF_first {n : ℕ} (a : Fin n) : (transF a).firstOnly := by
  simp [transF,Formula.firstOnly,neg,conj,disj,iffF,ex]

def powerF {n : ℕ} (a b : Fin n) : Formula n :=
  (Formula.all (iffF (Formula.mem1 0 (Fin.succ b)) (subF 0 (Fin.succ a))))

@[simp] theorem powerF_correct {X : Type u} (m r : X → X → Prop) {n : ℕ}
    (v : Fin n → X) (a b : Fin n) :
    (powerF a b).eval m r v ↔ Power m (v a) (v b) := by
  simp only [powerF,Power,eval_conj,eval_disj,eval_neg,eval_iffF,eval_ex,Formula.eval,
    push_zero,push_succ,DESTSemantic.push_push_one,subF_correct]

theorem powerF_first {n : ℕ} (a b : Fin n) : (powerF a b).firstOnly := by
  simp [powerF,Formula.firstOnly,neg,conj,disj,iffF,ex,subF_first]

def WFSet {X : Type u} (m : X → X → Prop) (a : X) : Prop :=
  (∀ b, ((Sub m b a ∧ (∃ x, m x b)) → (∃ x, (m x b ∧ (∀ y, (m y b → ¬ (m y x)))))))

def wfF {n : ℕ} (a : Fin n) : Formula n :=
  (Formula.all (Formula.imp (conj (subF 0 (Fin.succ a)) (ex (Formula.mem1 0 (Fin.succ 0)))) (ex (conj (Formula.mem1 0 (Fin.succ 0)) (Formula.all (Formula.imp (Formula.mem1 0 (Fin.succ (Fin.succ 0))) (neg (Formula.mem1 0 (Fin.succ 0)))))))))

@[simp] theorem wfF_correct {X : Type u} (m r : X → X → Prop) {n : ℕ}
    (v : Fin n → X) (a : Fin n) :
    (wfF a).eval m r v ↔ WFSet m (v a) := by
  simp only [wfF,WFSet,eval_conj,eval_disj,eval_neg,eval_iffF,eval_ex,Formula.eval,
    push_zero,push_succ,DESTSemantic.push_push_one,subF_correct]

theorem wfF_first {n : ℕ} (a : Fin n) : (wfF a).firstOnly := by
  simp [wfF,Formula.firstOnly,neg,conj,disj,iffF,ex,subF_first]

def GoodStage {X : Type u} (m r : X → X → Prop) (a : X) : Prop :=
  (AllUniform m r a ∧ (Transitive m a ∧ WFSet m a))

def goodF {n : ℕ} (a : Fin n) : Formula n :=
  (conj (allUniformF a) (conj (transF a) (wfF a)))

@[simp] theorem goodF_correct {X : Type u} (m r : X → X → Prop) {n : ℕ}
    (v : Fin n → X) (a : Fin n) :
    (goodF a).eval m r v ↔ GoodStage m r (v a) := by
  simp only [goodF,GoodStage,eval_conj,eval_disj,eval_neg,eval_iffF,eval_ex,Formula.eval,
    push_zero,push_succ,DESTSemantic.push_push_one,allUniformF_correct,transF_correct,wfF_correct]

def PairCode {X : Type u} (m : X → X → Prop) (p a b : X) : Prop :=
  (∃ s, (∃ t, ((∀ y, (m y s ↔ y = a)) ∧ ((∀ y, (m y t ↔ (y = a ∨ y = b))) ∧ (∀ y, (m y p ↔ (y = s ∨ y = t)))))))

def pairF {n : ℕ} (p a b : Fin n) : Formula n :=
  (ex (ex (conj (Formula.all (iffF (Formula.mem1 0 (Fin.succ (Fin.succ 0))) (Formula.eq 0 (Fin.succ (Fin.succ (Fin.succ a)))))) (conj (Formula.all (iffF (Formula.mem1 0 (Fin.succ 0)) (disj (Formula.eq 0 (Fin.succ (Fin.succ (Fin.succ a)))) (Formula.eq 0 (Fin.succ (Fin.succ (Fin.succ b))))))) (Formula.all (iffF (Formula.mem1 0 (Fin.succ (Fin.succ (Fin.succ p)))) (disj (Formula.eq 0 (Fin.succ (Fin.succ 0))) (Formula.eq 0 (Fin.succ 0)))))))))

@[simp] theorem pairF_correct {X : Type u} (m r : X → X → Prop) {n : ℕ}
    (v : Fin n → X) (p a b : Fin n) :
    (pairF p a b).eval m r v ↔ PairCode m (v p) (v a) (v b) := by
  simp only [pairF,PairCode,eval_conj,eval_disj,eval_neg,eval_iffF,eval_ex,Formula.eval,
    push_zero,push_succ,DESTSemantic.push_push_one]

theorem pairF_first {n : ℕ} (p a b : Fin n) : (pairF p a b).firstOnly := by
  simp [pairF,Formula.firstOnly,neg,conj,disj,iffF,ex]

def Value {X : Type u} (m : X → X → Prop) (g k a : X) : Prop :=
  (∃ p, (m p g ∧ PairCode m p k a))

def valueF {n : ℕ} (g k a : Fin n) : Formula n :=
  (ex (conj (Formula.mem1 0 (Fin.succ g)) (pairF 0 (Fin.succ k) (Fin.succ a))))

@[simp] theorem valueF_correct {X : Type u} (m r : X → X → Prop) {n : ℕ}
    (v : Fin n → X) (g k a : Fin n) :
    (valueF g k a).eval m r v ↔ Value m (v g) (v k) (v a) := by
  simp only [valueF,Value,eval_conj,eval_disj,eval_neg,eval_iffF,eval_ex,Formula.eval,
    push_zero,push_succ,DESTSemantic.push_push_one,pairF_correct]

theorem valueF_first {n : ℕ} (g k a : Fin n) : (valueF g k a).firstOnly := by
  simp [valueF,Formula.firstOnly,neg,conj,disj,iffF,ex,pairF_first]

def TowerGraph {X : Type u} (m : X → X → Prop) (z w g : X) : Prop :=
  (∀ k, (∀ a, (Value m g k a → (m k w ∧ ((k = z → a = w) ∧ (¬ (k = z) → (∃ j, (∃ b, (Succ m j k ∧ (Value m g j b ∧ Power m b a))))))))))

def graphF {n : ℕ} (z w g : Fin n) : Formula n :=
  (Formula.all (Formula.all (Formula.imp (valueF (Fin.succ (Fin.succ g)) (Fin.succ 0) 0) (conj (Formula.mem1 (Fin.succ 0) (Fin.succ (Fin.succ w))) (conj (Formula.imp (Formula.eq (Fin.succ 0) (Fin.succ (Fin.succ z))) (Formula.eq 0 (Fin.succ (Fin.succ w)))) (Formula.imp (neg (Formula.eq (Fin.succ 0) (Fin.succ (Fin.succ z)))) (ex (ex (conj (succF (Fin.succ 0) (Fin.succ (Fin.succ (Fin.succ 0)))) (conj (valueF (Fin.succ (Fin.succ (Fin.succ (Fin.succ g)))) (Fin.succ 0) 0) (powerF 0 (Fin.succ (Fin.succ 0)))))))))))))

@[simp] theorem graphF_correct {X : Type u} (m r : X → X → Prop) {n : ℕ}
    (v : Fin n → X) (z w g : Fin n) :
    (graphF z w g).eval m r v ↔ TowerGraph m (v z) (v w) (v g) := by
  simp only [graphF,TowerGraph,eval_conj,eval_disj,eval_neg,eval_iffF,eval_ex,Formula.eval,
    push_zero,push_succ,DESTSemantic.push_push_one,powerF_correct,DESTSemantic.succ_correct,valueF_correct]

theorem graphF_first {n : ℕ} (z w g : Fin n) : (graphF z w g).firstOnly := by
  simp [graphF,Formula.firstOnly,neg,conj,disj,iffF,ex,powerF_first,succF_first,valueF_first]

def Stage {X : Type u} (m : X → X → Prop) (z w k a : X) : Prop :=
  (∃ g, (TowerGraph m z w g ∧ Value m g k a))

def stageF {n : ℕ} (z w k a : Fin n) : Formula n :=
  (ex (conj (graphF (Fin.succ z) (Fin.succ w) 0) (valueF 0 (Fin.succ k) (Fin.succ a))))

@[simp] theorem stageF_correct {X : Type u} (m r : X → X → Prop) {n : ℕ}
    (v : Fin n → X) (z w k a : Fin n) :
    (stageF z w k a).eval m r v ↔ Stage m (v z) (v w) (v k) (v a) := by
  simp only [stageF,Stage,eval_conj,eval_disj,eval_neg,eval_iffF,eval_ex,Formula.eval,
    push_zero,push_succ,DESTSemantic.push_push_one,graphF_correct,valueF_correct]

theorem stageF_first {n : ℕ} (z w k a : Fin n) : (stageF z w k a).firstOnly := by
  simp [stageF,Formula.firstOnly,neg,conj,disj,iffF,ex,graphF_first,valueF_first]

def StageExists {X : Type u} (m r : X → X → Prop) (z w k : X) : Prop :=
  (∃ g, (∃ a, (AllUniform m r g ∧ (Uniform m r a ∧ (TowerGraph m z w g ∧ Value m g k a)))))

def stageExistsF {n : ℕ} (z w k : Fin n) : Formula n :=
  (ex (ex (conj (allUniformF (Fin.succ 0)) (conj (uniformF 0) (conj (graphF (Fin.succ (Fin.succ z)) (Fin.succ (Fin.succ w)) (Fin.succ 0)) (valueF (Fin.succ 0) (Fin.succ (Fin.succ k)) 0))))))

@[simp] theorem stageExistsF_correct {X : Type u} (m r : X → X → Prop) {n : ℕ}
    (v : Fin n → X) (z w k : Fin n) :
    (stageExistsF z w k).eval m r v ↔ StageExists m r (v z) (v w) (v k) := by
  simp only [stageExistsF,StageExists,eval_conj,eval_disj,eval_neg,eval_iffF,eval_ex,Formula.eval,
    push_zero,push_succ,DESTSemantic.push_push_one,allUniformF_correct,graphF_correct,DESTSemantic.uniformF_correct,valueF_correct]

def StageGood {X : Type u} (m r : X → X → Prop) (z w k : X) : Prop :=
  (∀ a, (Stage m z w k a → GoodStage m r a))

def stageGoodF {n : ℕ} (z w k : Fin n) : Formula n :=
  (Formula.all (Formula.imp (stageF (Fin.succ z) (Fin.succ w) (Fin.succ k) 0) (goodF 0)))

@[simp] theorem stageGoodF_correct {X : Type u} (m r : X → X → Prop) {n : ℕ}
    (v : Fin n → X) (z w k : Fin n) :
    (stageGoodF z w k).eval m r v ↔ StageGood m r (v z) (v w) (v k) := by
  simp only [stageGoodF,StageGood,eval_conj,eval_disj,eval_neg,eval_iffF,eval_ex,Formula.eval,
    push_zero,push_succ,DESTSemantic.push_push_one,goodF_correct,stageF_correct]

def StageUnique {X : Type u} (m : X → X → Prop) (z w k : X) : Prop :=
  (∀ a, (∀ b, (Stage m z w k a → (Stage m z w k b → a = b))))

def stageUniqueF {n : ℕ} (z w k : Fin n) : Formula n :=
  (Formula.all (Formula.all (Formula.imp (stageF (Fin.succ (Fin.succ z)) (Fin.succ (Fin.succ w)) (Fin.succ (Fin.succ k)) (Fin.succ 0)) (Formula.imp (stageF (Fin.succ (Fin.succ z)) (Fin.succ (Fin.succ w)) (Fin.succ (Fin.succ k)) 0) (Formula.eq (Fin.succ 0) 0)))))

@[simp] theorem stageUniqueF_correct {X : Type u} (m r : X → X → Prop) {n : ℕ}
    (v : Fin n → X) (z w k : Fin n) :
    (stageUniqueF z w k).eval m r v ↔ StageUnique m (v z) (v w) (v k) := by
  simp only [stageUniqueF,StageUnique,eval_conj,eval_disj,eval_neg,eval_iffF,eval_ex,Formula.eval,
    push_zero,push_succ,DESTSemantic.push_push_one,stageF_correct]

theorem stageUniqueF_first {n : ℕ} (z w k : Fin n) : (stageUniqueF z w k).firstOnly := by
  simp [stageUniqueF,Formula.firstOnly,neg,conj,disj,iffF,ex,stageF_first]

def StageNest {X : Type u} (m : X → X → Prop) (z w k : X) : Prop :=
  (∀ j, (∀ a, (∀ b, (m j k → (Stage m z w j a → (Stage m z w k b → Sub m a b))))))

def stageNestF {n : ℕ} (z w k : Fin n) : Formula n :=
  (Formula.all (Formula.all (Formula.all (Formula.imp (Formula.mem1 (Fin.succ (Fin.succ 0)) (Fin.succ (Fin.succ (Fin.succ k)))) (Formula.imp (stageF (Fin.succ (Fin.succ (Fin.succ z))) (Fin.succ (Fin.succ (Fin.succ w))) (Fin.succ (Fin.succ 0)) (Fin.succ 0)) (Formula.imp (stageF (Fin.succ (Fin.succ (Fin.succ z))) (Fin.succ (Fin.succ (Fin.succ w))) (Fin.succ (Fin.succ (Fin.succ k))) 0) (subF (Fin.succ 0) 0)))))))

@[simp] theorem stageNestF_correct {X : Type u} (m r : X → X → Prop) {n : ℕ}
    (v : Fin n → X) (z w k : Fin n) :
    (stageNestF z w k).eval m r v ↔ StageNest m (v z) (v w) (v k) := by
  simp only [stageNestF,StageNest,eval_conj,eval_disj,eval_neg,eval_iffF,eval_ex,Formula.eval,
    push_zero,push_succ,DESTSemantic.push_push_one,stageF_correct,subF_correct]

theorem stageNestF_first {n : ℕ} (z w k : Fin n) : (stageNestF z w k).firstOnly := by
  simp [stageNestF,Formula.firstOnly,neg,conj,disj,iffF,ex,stageF_first,subF_first]

def InTower {X : Type u} (m : X → X → Prop) (z w x : X) : Prop :=
  (∃ k, (∃ a, (Stage m z w k a ∧ m x a)))

def inTowerF {n : ℕ} (z w x : Fin n) : Formula n :=
  (ex (ex (conj (stageF (Fin.succ (Fin.succ z)) (Fin.succ (Fin.succ w)) (Fin.succ 0) 0) (Formula.mem1 (Fin.succ (Fin.succ x)) 0))))

@[simp] theorem inTowerF_correct {X : Type u} (m r : X → X → Prop) {n : ℕ}
    (v : Fin n → X) (z w x : Fin n) :
    (inTowerF z w x).eval m r v ↔ InTower m (v z) (v w) (v x) := by
  simp only [inTowerF,InTower,eval_conj,eval_disj,eval_neg,eval_iffF,eval_ex,Formula.eval,
    push_zero,push_succ,DESTSemantic.push_push_one,stageF_correct]

theorem inTowerF_first {n : ℕ} (z w x : Fin n) : (inTowerF z w x).firstOnly := by
  simp [inTowerF,Formula.firstOnly,neg,conj,disj,iffF,ex,stageF_first]

def NumCore {X : Type u} (m : X → X → Prop) (a w : X) : Prop :=
  (Transitive m a ∧ (¬ (m a a) ∧ Sub m a w))

def numCoreF {n : ℕ} (a w : Fin n) : Formula n :=
  (conj (transF a) (conj (neg (Formula.mem1 a a)) (subF a w)))

@[simp] theorem numCoreF_correct {X : Type u} (m r : X → X → Prop) {n : ℕ}
    (v : Fin n → X) (a w : Fin n) :
    (numCoreF a w).eval m r v ↔ NumCore m (v a) (v w) := by
  simp only [numCoreF,NumCore,eval_conj,eval_disj,eval_neg,eval_iffF,eval_ex,Formula.eval,
    push_zero,push_succ,DESTSemantic.push_push_one,subF_correct,transF_correct]

theorem numCoreF_first {n : ℕ} (a w : Fin n) : (numCoreF a w).firstOnly := by
  simp [numCoreF,Formula.firstOnly,neg,conj,disj,iffF,ex,subF_first,transF_first]

def Pred {X : Type u} (m : X → X → Prop) (z w a : X) : Prop :=
  (a = z ∨ (∃ b, (m b w ∧ Succ m b a)))

def predF {n : ℕ} (z w a : Fin n) : Formula n :=
  (disj (Formula.eq a z) (ex (conj (Formula.mem1 0 (Fin.succ w)) (succF 0 (Fin.succ a)))))

@[simp] theorem predF_correct {X : Type u} (m r : X → X → Prop) {n : ℕ}
    (v : Fin n → X) (z w a : Fin n) :
    (predF z w a).eval m r v ↔ Pred m (v z) (v w) (v a) := by
  simp only [predF,Pred,eval_conj,eval_disj,eval_neg,eval_iffF,eval_ex,Formula.eval,
    push_zero,push_succ,DESTSemantic.push_push_one,DESTSemantic.succ_correct]

theorem predF_first {n : ℕ} (z w a : Fin n) : (predF z w a).firstOnly := by
  simp [predF,Formula.firstOnly,neg,conj,disj,iffF,ex,succF_first]

def Earlier {X : Type u} (m : X → X → Prop) (n s k : X) : Prop :=
  (m n k → (s = k ∨ m s k))

def earlierF {n : ℕ} (n s k : Fin n) : Formula n :=
  (Formula.imp (Formula.mem1 n k) (disj (Formula.eq s k) (Formula.mem1 s k)))

@[simp] theorem earlierF_correct {X : Type u} (m r : X → X → Prop) {n : ℕ}
    (v : Fin n → X) (n s k : Fin n) :
    (earlierF n s k).eval m r v ↔ Earlier m (v n) (v s) (v k) := by
  simp only [earlierF,Earlier,eval_conj,eval_disj,eval_neg,eval_iffF,eval_ex,Formula.eval,
    push_zero,push_succ,DESTSemantic.push_push_one]

theorem earlierF_first {n : ℕ} (n s k : Fin n) : (earlierF n s k).firstOnly := by
  simp [earlierF,Formula.firstOnly,neg,conj,disj,iffF,ex]

def Compare {X : Type u} (m : X → X → Prop) (a b : X) : Prop :=
  (a = b ∨ (m a b ∨ m b a))

def compareF {n : ℕ} (a b : Fin n) : Formula n :=
  (disj (Formula.eq a b) (disj (Formula.mem1 a b) (Formula.mem1 b a)))

@[simp] theorem compareF_correct {X : Type u} (m r : X → X → Prop) {n : ℕ}
    (v : Fin n → X) (a b : Fin n) :
    (compareF a b).eval m r v ↔ Compare m (v a) (v b) := by
  simp only [compareF,Compare,eval_conj,eval_disj,eval_neg,eval_iffF,eval_ex,Formula.eval,
    push_zero,push_succ,DESTSemantic.push_push_one]

theorem compareF_first {n : ℕ} (a b : Fin n) : (compareF a b).firstOnly := by
  simp [compareF,Formula.firstOnly,neg,conj,disj,iffF,ex]

def Avoid {X : Type u} (m : X → X → Prop) (a b : X) : Prop :=
  (¬ (m a b) ∧ (∀ y, (m y a → ¬ (m y b))))

def avoidF {n : ℕ} (a b : Fin n) : Formula n :=
  (conj (neg (Formula.mem1 a b)) (Formula.all (Formula.imp (Formula.mem1 0 (Fin.succ a)) (neg (Formula.mem1 0 (Fin.succ b))))))

@[simp] theorem avoidF_correct {X : Type u} (m r : X → X → Prop) {n : ℕ}
    (v : Fin n → X) (a b : Fin n) :
    (avoidF a b).eval m r v ↔ Avoid m (v a) (v b) := by
  simp only [avoidF,Avoid,eval_conj,eval_disj,eval_neg,eval_iffF,eval_ex,Formula.eval,
    push_zero,push_succ,DESTSemantic.push_push_one]

theorem avoidF_first {n : ℕ} (a b : Fin n) : (avoidF a b).firstOnly := by
  simp [avoidF,Formula.firstOnly,neg,conj,disj,iffF,ex]

end DESTOriginal
