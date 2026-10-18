import formalization.RelativeAlgorithmBridge

/-! Sparse block compilation of actual relative matrix restrictions. -/
namespace MatrixDimensionAudit.BlockRelativeAlgorithmBridge
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.Arithmetic
open OAI.MatrixMultiplication.Arithmetic.RecursiveBlock
open RelativeAlgorithmBridge
open scoped BigOperators
noncomputable section
attribute [local instance] GlobalFamilySampleBridge.productFiniteX GlobalFamilySampleBridge.productFiniteY
attribute [local instance] GlobalFamilySampleBridge.matrixFiniteX GlobalFamilySampleBridge.matrixFiniteY
attribute [local instance] CatalystReuseBridge.diagonalFiniteX CatalystReuseBridge.diagonalFiniteY
attribute [local instance] CatalystReuseBridge.diagonalDecX CatalystReuseBridge.diagonalDecY

def split (a t : Nat) : Fin (a*t) ≃ (Fin a × Fin t) := finProdFinEquiv.symm

/-- Fix the fine row, contraction, and column indices of every target block. -/
def slice {m B t : Nat} (inputs : Fin m × MatrixInput (B*t) (B*t) (B*t) → ℚ)
    (i j k : Fin t) : Fin m × MatrixInput B B B → ℚ
  | (g,.inl xy) => inputs (g,.inl (join xy.1 i,join xy.2 j))
  | (g,.inr xy) => inputs (g,.inr (join xy.1 j,join xy.2 k))

def blockLeft {q A m B t : Nat} (p : MatrixTensorMaps q A m B)
    (inputs : Fin m × MatrixInput (B*t) (B*t) (B*t) → ℚ) (s : Fin q) (u v : Fin (A*t)) : ℚ :=
  ∑ x : Fin m × (Fin B × Fin B), p.first x (s,((split A t u).1,(split A t v).1)) *
    inputs (x.1,.inl (join x.2.1 (split A t u).2,join x.2.2 (split A t v).2))

def blockRight {q A m B t : Nat} (p : MatrixTensorMaps q A m B)
    (inputs : Fin m × MatrixInput (B*t) (B*t) (B*t) → ℚ) (s : Fin q) (u v : Fin (A*t)) : ℚ :=
  ∑ y : Fin m × (Fin B × Fin B), p.second y (s,((split A t u).1,(split A t v).1)) *
    inputs (y.1,.inr (join y.2.1 (split A t u).2,join y.2.2 (split A t v).2))

/-- Each full source multiplication is the sum of its scalar block slices. -/
theorem source_product_slices {q A m B t : Nat} (p : MatrixTensorMaps q A m B)
    (inputs : Fin m × MatrixInput (B*t) (B*t) (B*t) → ℚ)
    (s : Fin q) (u v : Fin A) (i k : Fin t) :
    (∑ j : Fin (A*t), blockLeft p inputs s (join u i) j * blockRight p inputs s j (join v k)) =
      ∑ w : Fin t, ∑ j : Fin A,
        encodedLeft p (slice inputs i w k) s u j * encodedRight p (slice inputs i w k) s j v := by
  have h := (finProdFinEquiv : (Fin A × Fin t) ≃ Fin (A*t)).sum_comp
    (fun j => blockLeft p inputs s (join u i) j * blockRight p inputs s j (join v k))
  rw [← h, Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  apply Finset.sum_congr rfl
  intro j _
  simp only [blockLeft, blockRight, encodedLeft, encodedRight, slice, split, join, Equiv.symm_apply_apply]

/-- The original scalar restriction is applied independently at every fine
contraction index, preserving all target products. -/
theorem block_coefficient_correct {q A m B t : Nat} (p : MatrixTensorMaps q A m B)
    (inputs : Fin m × MatrixInput (B*t) (B*t) (B*t) → ℚ)
    (g : Fin m) (u v : Fin B) (i k : Fin t) :
    (∑ z : Fin q × (Fin A × Fin A), p.third (g,(v,u)) (z.1,(z.2.2,z.2.1)) *
      ∑ j : Fin (A*t), blockLeft p inputs z.1 (join z.2.1 i) j *
        blockRight p inputs z.1 j (join z.2.2 k)) =
      ∑ j : Fin (B*t), inputs (g,.inl (join u i,j)) * inputs (g,.inr (j,join v k)) := by
  simp_rw [source_product_slices, Finset.mul_sum]
  rw [Finset.sum_comm]
  have ht : (∑ j : Fin (B*t), inputs (g,.inl (join u i,j)) * inputs (g,.inr (j,join v k))) =
      ∑ w : Fin t, ∑ j : Fin B,
        inputs (g,.inl (join u i,join j w)) * inputs (g,.inr (join j w,join v k)) := by
    have h := (finProdFinEquiv : (Fin B × Fin t) ≃ Fin (B*t)).sum_comp
      (fun j => inputs (g,.inl (join u i,j)) * inputs (g,.inr (j,join v k)))
    rw [← h, Fintype.sum_prod_type, Finset.sum_comm]
    rfl
  rw [ht]
  apply Finset.sum_congr rfl
  intro w _
  simpa only [Finset.mul_sum, slice] using coefficient_batch_correct p (slice inputs i w k) g u v

/-- Each source entry sums only the base m*B² entries at its own fine coordinate. -/
def inputExpressions {q A m B : Nat} (p : MatrixTensorMaps q A m B) (t : Nat) :
    (Fin q × MatrixInput (A*t) (A*t) (A*t)) →
      Expression ℚ (Fin m × MatrixInput (B*t) (B*t) (B*t))
  | (s,.inl uv) => LinearExpression.linear
      (fun x : Fin m × (Fin B × Fin B) => p.first x (s,((split A t uv.1).1,(split A t uv.2).1)))
      (fun x => (x.1,.inl (join x.2.1 (split A t uv.1).2,join x.2.2 (split A t uv.2).2)))
  | (s,.inr uv) => LinearExpression.linear
      (fun y : Fin m × (Fin B × Fin B) => p.second y (s,((split A t uv.1).1,(split A t uv.2).1)))
      (fun y => (y.1,.inr (join y.2.1 (split A t uv.1).2,join y.2.2 (split A t uv.2).2)))

def inputProgram {q A m B : Nat} (p : MatrixTensorMaps q A m B) (t : Nat) :=
  Family.expressions (inputExpressions p t)

/-- Decode each fine output entry using only q*A² base coefficients. -/
def outputExpressions {q A m B : Nat} (p : MatrixTensorMaps q A m B) (t : Nat)
    (o : Fin m × (Fin (B*t) × Fin (B*t))) :
    Expression ℚ (Fin q × (Fin (A*t) × Fin (A*t))) :=
  LinearExpression.linear (fun z : Fin q × (Fin A × Fin A) =>
    p.third (o.1,((split B t o.2.2).1,(split B t o.2.1).1)) (z.1,(z.2.2,z.2.1)))
    (fun z => (z.1,(join z.2.1 (split B t o.2.1).2,join z.2.2 (split B t o.2.2).2)))

def outputProgram {q A m B : Nat} (p : MatrixTensorMaps q A m B) (t : Nat) :=
  Family.expressions (outputExpressions p t)

/-- Exactly q complete source algorithms are called between the sparse linear stages. -/
def batchProgram {q A m B : Nat} (p : MatrixTensorMaps q A m B) (t : Nat)
    (alg : MatrixAlgorithm ℚ (A*t) (A*t) (A*t)) :
    Family ℚ (Fin m × MatrixInput (B*t) (B*t) (B*t)) (Fin m × (Fin (B*t) × Fin (B*t))) :=
  (inputProgram p t).compose ((Family.copies q (Family.ofMatrix alg)).compose (outputProgram p t))

theorem inputProgram_left {q A m B t : Nat} (p : MatrixTensorMaps q A m B)
    (inputs : Fin m × MatrixInput (B*t) (B*t) (B*t) → ℚ) (s : Fin q) (u v : Fin (A*t)) :
    (inputProgram p t).eval inputs (s,.inl (u,v)) = blockLeft p inputs s u v := by
  simp only [inputProgram, Family.eval_expressions, inputExpressions, LinearExpression.eval_linear, blockLeft]

theorem inputProgram_right {q A m B t : Nat} (p : MatrixTensorMaps q A m B)
    (inputs : Fin m × MatrixInput (B*t) (B*t) (B*t) → ℚ) (s : Fin q) (u v : Fin (A*t)) :
    (inputProgram p t).eval inputs (s,.inr (u,v)) = blockRight p inputs s u v := by
  simp only [inputProgram, Family.eval_expressions, inputExpressions, LinearExpression.eval_linear, blockRight]

theorem batchProgram_correct {q A m B t : Nat} (p : MatrixTensorMaps q A m B)
    (alg : MatrixAlgorithm ℚ (A*t) (A*t) (A*t)) (halg : alg.Correct)
    (inputs : Fin m × MatrixInput (B*t) (B*t) (B*t) → ℚ) (g : Fin m) (u v : Fin (B*t)) :
    (batchProgram p t alg).eval inputs (g,(u,v)) =
      ∑ j, inputs (g,.inl (u,j)) * inputs (g,.inr (j,v)) := by
  have hu := (split B t).symm_apply_apply u
  have hv := (split B t).symm_apply_apply v
  change join (split B t u).1 (split B t u).2 = u at hu
  change join (split B t v).1 (split B t v).2 = v at hv
  simp only [batchProgram, Family.eval_compose, outputProgram, Family.eval_expressions,
    outputExpressions, LinearExpression.eval_linear, Family.eval_copies, Family.eval_ofMatrix alg halg]
  simp only [inputProgram_left, inputProgram_right]
  have h := block_coefficient_correct p inputs g (split B t u).1 (split B t v).1
    (split B t u).2 (split B t v).2
  rw [hu,hv] at h
  exact h

theorem inputProgram_cost {q A m B : Nat} (p : MatrixTensorMaps q A m B) (t : Nat) :
    (inputProgram p t).cost = 4*q*m*A^2*B^2*t^2 := by
  simp only [inputProgram, Family.cost_expressions, Fintype.sum_prod_type, Fintype.sum_sum_type,
    inputExpressions, LinearExpression.cost_linear, Fintype.card_prod, Fintype.card_fin]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
  ring

theorem outputProgram_cost {q A m B : Nat} (p : MatrixTensorMaps q A m B) (t : Nat) :
    (outputProgram p t).cost = 2*q*m*A^2*B^2*t^2 := by
  simp only [outputProgram, Family.cost_expressions, outputExpressions, LinearExpression.cost_linear,
    Fintype.card_prod, Fintype.card_fin]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
  ring

/-- The overhead is quadratic in the block width; every full source call is retained. -/
theorem batchProgram_cost {q A m B t : Nat} (p : MatrixTensorMaps q A m B)
    (alg : MatrixAlgorithm ℚ (A*t) (A*t) (A*t)) :
    (batchProgram p t alg).cost = q*alg.cost + 6*q*m*A^2*B^2*t^2 := by
  rw [batchProgram, Family.cost_compose, Family.cost_compose, Family.cost_copies,
    Family.cost_ofMatrix, inputProgram_cost, outputProgram_cost]
  ring

/-- Apply the sparse compiler to the closed supplied-family restriction. -/
def suppliedProgram (family : AllRowProfile.Family n K) (k j t : Nat)
    (alg : MatrixAlgorithm ℚ (SuppliedGlobalRestrictionBridge.inputWidth family k j*t)
      (SuppliedGlobalRestrictionBridge.inputWidth family k j*t)
      (SuppliedGlobalRestrictionBridge.inputWidth family k j*t)) :=
  batchProgram (SuppliedGlobalRestrictionBridge.suppliedMaps family k j) t alg

theorem suppliedProgram_correct (family : AllRowProfile.Family n K) (k j t : Nat)
    (alg : MatrixAlgorithm ℚ (SuppliedGlobalRestrictionBridge.inputWidth family k j*t)
      (SuppliedGlobalRestrictionBridge.inputWidth family k j*t)
      (SuppliedGlobalRestrictionBridge.inputWidth family k j*t)) (halg : alg.Correct)
    (inputs : Fin (SuppliedGlobalRestrictionBridge.outputCopies family k j) × MatrixInput
      (SuppliedGlobalRestrictionBridge.outputWidth family k j*t)
      (SuppliedGlobalRestrictionBridge.outputWidth family k j*t)
      (SuppliedGlobalRestrictionBridge.outputWidth family k j*t) → ℚ)
    (g : Fin (SuppliedGlobalRestrictionBridge.outputCopies family k j))
    (u v : Fin (SuppliedGlobalRestrictionBridge.outputWidth family k j*t)) :
    (suppliedProgram family k j t alg).eval inputs (g,(u,v)) =
      ∑ w, inputs (g,.inl (u,w)) * inputs (g,.inr (w,v)) :=
  batchProgram_correct _ alg halg inputs g u v

theorem suppliedProgram_cost (family : AllRowProfile.Family n K) (k j t : Nat)
    (alg : MatrixAlgorithm ℚ (SuppliedGlobalRestrictionBridge.inputWidth family k j*t)
      (SuppliedGlobalRestrictionBridge.inputWidth family k j*t)
      (SuppliedGlobalRestrictionBridge.inputWidth family k j*t)) :
    (suppliedProgram family k j t alg).cost =
      SuppliedGlobalRestrictionBridge.inputCopies family k j * alg.cost +
        6 * SuppliedGlobalRestrictionBridge.inputCopies family k j *
          SuppliedGlobalRestrictionBridge.outputCopies family k j *
          (SuppliedGlobalRestrictionBridge.inputWidth family k j)^2 *
          (SuppliedGlobalRestrictionBridge.outputWidth family k j)^2 * t^2 :=
  batchProgram_cost _ alg

end
end MatrixDimensionAudit.BlockRelativeAlgorithmBridge
