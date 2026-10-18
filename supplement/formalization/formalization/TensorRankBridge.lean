import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensorFlattening
import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensorSymmetrization
import formalization.FreeAuxiliaryBridge

namespace MatrixDimensionAudit.TensorRankBridge
open OAI.MatrixMultiplication.Foundation
open GeneralFlow GeneralRowSector AllRowProfile GeneralRowCatalyst JointDimensionCertificate

noncomputable section
variable (F : Type) [Field F]

/-- A concrete tensor together with an identity minor of its output flattening. -/
structure FullTensor where
  X : Type
  Y : Type
  Z : Type
  finiteZ : Fintype Z
  equalZ : DecidableEq Z
  tensor : Tensor F X Y Z
  left : Z → X
  right : Z → Y
  identity : ∀ i j, tensor (left i) (right i) j = if i = j then 1 else 0

attribute [instance] FullTensor.finiteZ FullTensor.equalZ

namespace FullTensor
variable {F}
def unit : FullTensor F where
  X := Unit
  Y := Unit
  Z := Unit
  finiteZ := inferInstance
  equalZ := inferInstance
  tensor := fun _ _ _ => 1
  left := id
  right := id
  identity := by intro i j; cases i; cases j; simp

def product (A B : FullTensor F) : FullTensor F where
  X := A.X × B.X
  Y := A.Y × B.Y
  Z := A.Z × B.Z
  finiteZ := inferInstance
  equalZ := inferInstance
  tensor := Tensor.product A.tensor B.tensor
  left := fun z => (A.left z.1, B.left z.2)
  right := fun z => (A.right z.1, B.right z.2)
  identity := by
    intro i j
    simp only [Tensor.product, A.identity, B.identity]
    by_cases h₁ : i.1 = j.1 <;> by_cases h₂ : i.2 = j.2 <;>
      simp [h₁, h₂, Prod.ext_iff]

def power (A : FullTensor F) : Nat → FullTensor F
  | 0 => unit
  | n + 1 => product A (power A n)

def dimension (A : FullTensor F) : Nat := Fintype.card A.Z

@[simp] theorem dimension_unit : (unit (F := F)).dimension = 1 := by
  change Fintype.card Unit = 1
  exact Fintype.card_unit

@[simp] theorem dimension_product (A B : FullTensor F) :
    (product A B).dimension = A.dimension * B.dimension := by
  change Fintype.card (A.Z × B.Z) = Fintype.card A.Z * Fintype.card B.Z
  exact Fintype.card_prod A.Z B.Z

@[simp] theorem dimension_power (A : FullTensor F) (n : Nat) :
    (power A n).dimension = A.dimension ^ n := by
  induction n with
  | zero => simp [power]
  | succ n ih => simp [power, ih, pow_succ, Nat.mul_comm]

/-- Output flattening, with coefficient pairs as rows. -/
def flattening (A : FullTensor F) : Matrix (A.X × A.Y) A.Z F :=
  fun xy z => A.tensor xy.1 xy.2 z

theorem flattening_rank (A : FullTensor F) : A.flattening.rank = A.dimension := by
  apply Nat.le_antisymm (Matrix.rank_le_card_width A.flattening)
  have minor : A.flattening.submatrix (fun i => (A.left i, A.right i)) id =
      (1 : Matrix A.Z A.Z F) := by
    funext i j
    exact A.identity i j
  have lower := Matrix.rank_submatrix_le A.flattening
    (fun i => (A.left i, A.right i)) id
  rw [minor, Matrix.rank_one] at lower
  exact lower

theorem rank_floor (A : FullTensor F) {rank : Nat}
    (h : Tensor.RankAtMost A.tensor rank) : A.dimension ≤ rank :=
  h.card_le_of_identity A.left A.right id A.identity
end FullTensor

/-- The ordinary polynomial multiplication tensor, with no cyclic wraparound. -/
def convolution (r b : Nat) : Tensor F (Fin r) (Fin b) (Fin (r + b - 1)) :=
  fun i j k => if i.val + j.val = k.val then 1 else 0

private def outputLeft (r b : Nat) (hr : 0 < r) (t : Fin (r + b - 1)) : Fin r :=
  ⟨min t.val (r - 1), by have := Nat.min_le_right t.val (r - 1); omega⟩

private def outputRight (r b : Nat) (hr : 0 < r) (hb : 0 < b) (t : Fin (r + b - 1)) : Fin b :=
  ⟨t.val - (r - 1), by have := t.isLt; omega⟩

private theorem output_sum (r b : Nat) (hr : 0 < r) (hb : 0 < b) (t : Fin (r + b - 1)) :
    (outputLeft r b hr t).val + (outputRight r b hr hb t).val = t.val := by
  simp only [outputLeft, outputRight]
  omega

def convolutionOutput (r b : Nat) (hr : 0 < r) (hb : 0 < b) : FullTensor F where
  X := Fin r
  Y := Fin b
  Z := Fin (r + b - 1)
  finiteZ := inferInstance
  equalZ := inferInstance
  tensor := convolution F r b
  left := outputLeft r b hr
  right := outputRight r b hr hb
  identity := by
    intro i j
    simp only [convolution, output_sum r b hr hb]
    simp [Fin.ext_iff]

def convolutionFirst (r b : Nat) (hb : 0 < b) : FullTensor F where
  X := Fin b
  Y := Fin (r + b - 1)
  Z := Fin r
  finiteZ := inferInstance
  equalZ := inferInstance
  tensor := Tensor.cyclic (convolution F r b)
  left := fun _ => ⟨0, hb⟩
  right := fun i => ⟨i.val, by have := i.isLt; omega⟩
  identity := by
    intro i j
    simp [Tensor.cyclic, convolution, Fin.ext_iff, eq_comm]

def convolutionSecond (r b : Nat) (hr : 0 < r) : FullTensor F where
  X := Fin (r + b - 1)
  Y := Fin r
  Z := Fin b
  finiteZ := inferInstance
  equalZ := inferInstance
  tensor := Tensor.cyclic (Tensor.cyclic (convolution F r b))
  left := fun j => ⟨j.val, by have := j.isLt; omega⟩
  right := fun _ => ⟨0, hr⟩
  identity := by
    intro i j
    simp [Tensor.cyclic, convolution, Fin.ext_iff, eq_comm]

/-- Exactly C(r,b) ⊗ C(r,b)^cyc ⊗ C(r,b)^(cyc²). -/
def cyclicConvolution (r b : Nat) (hr : 0 < r) (hb : 0 < b) : FullTensor F :=
  ((convolutionOutput F r b hr hb).product (convolutionFirst F r b hb)).product
    (convolutionSecond F r b hr)

@[simp] theorem cyclicConvolution_dimension (r b : Nat) (hr : 0 < r) (hb : 0 < b) :
    (cyclicConvolution F r b hr hb).dimension = r * b * (r + b - 1) := by
  change Fintype.card ((Fin (r + b - 1) × Fin r) × Fin b) = _
  rw [Fintype.card_prod, Fintype.card_prod]
  simp only [Fintype.card_fin]
  ac_rfl


/-- The same cyclic triple, rotated to expose its first leg. -/
def cyclicConvolutionFirst (r b : Nat) (hr : 0 < r) (hb : 0 < b) : FullTensor F :=
  ((convolutionFirst F r b hb).product (convolutionSecond F r b hr)).product
    (convolutionOutput F r b hr hb)

/-- The same cyclic triple, rotated to expose its second leg. -/
def cyclicConvolutionSecond (r b : Nat) (hr : 0 < r) (hb : 0 < b) : FullTensor F :=
  ((convolutionSecond F r b hr).product (convolutionOutput F r b hr hb)).product
    (convolutionFirst F r b hb)

@[simp] theorem cyclicConvolutionFirst_tensor (r b : Nat) (hr : 0 < r) (hb : 0 < b) :
    (cyclicConvolutionFirst F r b hr hb).tensor =
      Tensor.cyclic (cyclicConvolution F r b hr hb).tensor := rfl

@[simp] theorem cyclicConvolutionSecond_tensor (r b : Nat) (hr : 0 < r) (hb : 0 < b) :
    (cyclicConvolutionSecond F r b hr hb).tensor =
      Tensor.cyclic (Tensor.cyclic (cyclicConvolution F r b hr hb).tensor) := rfl

/-- All three actual flattenings have their complete leg dimension. -/
theorem cyclicConvolution_full_flattenings (r b : Nat) (hr : 0 < r) (hb : 0 < b) :
    (cyclicConvolution F r b hr hb).flattening.rank = r * b * (r + b - 1) ∧
    (cyclicConvolutionFirst F r b hr hb).flattening.rank = r * b * (r + b - 1) ∧
    (cyclicConvolutionSecond F r b hr hb).flattening.rank = r * b * (r + b - 1) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [FullTensor.flattening_rank, cyclicConvolution_dimension]
  · rw [FullTensor.flattening_rank]
    change Fintype.card ((Fin r × Fin b) × Fin (r + b - 1)) = _
    rw [Fintype.card_prod, Fintype.card_prod]
    simp only [Fintype.card_fin]
  · rw [FullTensor.flattening_rank]
    change Fintype.card ((Fin b × Fin (r + b - 1)) × Fin r) = _
    rw [Fintype.card_prod, Fintype.card_prod]
    simp only [Fintype.card_fin]
    ac_rfl

/-- Transposing the two input legs reverses the orientation parity.
The output coordinate has the same value after the dimension reindexing. -/
theorem convolution_transpose (r b : Nat) (i : Fin r) (j : Fin b)
    (t : Fin (b + r - 1)) :
    convolution F b r j i t =
      convolution F r b i j (Fin.cast (by omega : b + r - 1 = r + b - 1) t) := by
  simp [convolution, Nat.add_comm]

/-- False is the three even orientations. True is the three odd orientations,
represented as the cyclic triple of the input-transposed convolution C(b,r). -/
def signedCyclicConvolution (negative : Bool) (r b : Nat)
    (hr : 0 < r) (hb : 0 < b) : FullTensor F :=
  if negative then cyclicConvolution F b r hb hr else cyclicConvolution F r b hr hb

@[simp] theorem signedCyclicConvolution_dimension (negative : Bool) (r b : Nat)
    (hr : 0 < r) (hb : 0 < b) :
    (signedCyclicConvolution F negative r b hr hb).dimension = r * b * (r + b - 1) := by
  cases negative <;> simp [signedCyclicConvolution, Nat.add_comm, Nat.mul_comm]

/-- The consumed factor at an interior state x. -/
def splitFactor (negative : Bool) (r : Nat) (hr : 2 ≤ r) (x : Nat) : FullTensor F :=
  signedCyclicConvolution F negative r (r - 1 + x) (by omega) (by omega)

@[simp] theorem splitFactor_dimension (negative : Bool) (r : Nat) (hr : 2 ≤ r) (x : Nat) :
    (splitFactor F negative r hr x).dimension = splitLeg r x := by
  rw [splitFactor, signedCyclicConvolution_dimension]
  unfold splitLeg
  congr 1
  omega

def resetFactor (negative : Bool) (r : Nat) (hr : 2 ≤ r) : FullTensor F :=
  signedCyclicConvolution F negative r (4 * r - 1) (by omega) (by omega)

@[simp] theorem resetFactor_dimension (negative : Bool) (r : Nat) (hr : 2 ≤ r) :
    (resetFactor F negative r hr).dimension = resetLeg r := by
  rw [resetFactor, signedCyclicConvolution_dimension]
  unfold resetLeg
  congr 1
  omega

def sourceFactor (r : Nat) (hr : 2 ≤ r) : FullTensor F :=
  cyclicConvolution F r r (by omega) (by omega)

@[simp] theorem sourceFactor_dimension (r : Nat) (hr : 2 ≤ r) :
    (sourceFactor F r hr).dimension = sourceLeg r := by
  simp [sourceFactor, sourceLeg, two_mul]

def splitFactors (negative : Bool) (r : Nat) (hr : 2 ≤ r) : List Nat → FullTensor F
  | [] => FullTensor.unit
  | x :: xs => (splitFactor F negative r hr x).product (splitFactors negative r hr xs)

@[simp] theorem splitFactors_dimension (negative : Bool) (r : Nat) (hr : 2 ≤ r) (xs : List Nat) :
    (splitFactors F negative r hr xs).dimension = (xs.map (splitLeg r)).prod := by
  induction xs with
  | nil => simp [splitFactors]
  | cons x xs ih => simp [splitFactors, ih]

/-- The top row removes precisely the K external source copies. -/
def topConsumed (row : Row r 1 K) (hr : 2 ≤ r) : FullTensor F :=
  (splitFactors F false r hr (removeInjected K (parents row.actions))).product
    ((resetFactor F false r hr).power row.Z)

@[simp] theorem topConsumed_dimension (row : Row r 1 K) (hr : 2 ≤ r) :
    (topConsumed F row hr).dimension = topCharge row := by
  simp [topConsumed, topCharge]

def lowerConsumed (negative : Bool) (row : Row r 2 K) (hr : 2 ≤ r) : FullTensor F :=
  (splitFactors F negative r hr (parents row.actions)).product ((resetFactor F negative r hr).power row.Z)

@[simp] theorem lowerConsumed_dimension (negative : Bool) (row : Row r 2 K) (hr : 2 ≤ r) :
    (lowerConsumed F negative row hr).dimension = lowerCharge row := by
  simp [lowerConsumed, lowerCharge]

/-- depth is the number of rows below the positive top row. -/
def lowerRowsConsumed (depth : Nat) : {n : Nat} → LowerRows K n → FullTensor F
  | _, .nil => FullTensor.unit
  | _, .cons row tail =>
    (lowerConsumed F (decide (depth % 2 = 1)) row (by omega)).product
      (lowerRowsConsumed (depth + 1) tail)

@[simp] theorem lowerRowsConsumed_dimension (depth : Nat) (rows : LowerRows K n) :
    (lowerRowsConsumed F depth rows).dimension = lowerRowsCharge rows := by
  induction rows generalizing depth with
  | nil => simp [lowerRowsConsumed, lowerRowsCharge]
  | cons row tail ih => simp [lowerRowsConsumed, lowerRowsCharge, ih]

def familyConsumed (family : Family n K) : FullTensor F :=
  (topConsumed F family.top (by omega)).product (lowerRowsConsumed F 1 family.lower)

@[simp] theorem familyConsumed_dimension (family : Family n K) :
    (familyConsumed F family).dimension = familyCharge family := by
  simp [familyConsumed, familyCharge]

/-- The actual joint source and consumed-catalyst tensor, before any decomposition. -/
def jointSource (family : Family n K) (k j : Nat) : FullTensor F :=
  ((sourceFactor F (n + 2) (by omega)).power (K * k * j)).product
    ((familyConsumed F family).power k)

@[simp] theorem jointSource_dimension (family : Family n K) (k j : Nat) :
    (jointSource F family k j).dimension =
      sourceLeg (n + 2) ^ (K * k * j) * familyCharge family ^ k := by
  simp [jointSource]

/-- A genuine tensor decomposition pays the full source-and-catalyst leg product. -/
theorem jointSource_rank_floor (family : Family n K) (k j rank : Nat)
    (decomposition : Tensor.RankAtMost (jointSource F family k j).tensor rank) :
    sourceLeg (n + 2) ^ (K * k * j) * familyCharge family ^ k ≤ rank := by
  simpa using (jointSource F family k j).rank_floor decomposition

/-- The prior pooled dimension endpoint now takes an actual tensor decomposition
instead of the numerical source-flattening rank-floor hypothesis. -/
theorem actual_tensor_pooled_dimension_bound (family : Family n K)
    (rank exactification copies k j : Nat) (hK : 0 < K) (hk : 0 < k) (hj : 0 < j)
    (exactification_pos : 0 < exactification)
    (copies_paid : family.count ^ 3 ≤ copies)
    (decomposition : Tensor.RankAtMost (jointSource F family k j).tensor rank)
    (raw : (rank * exactification ^ j * copies ^ (k * j)) *
      (family.dimension ^ (k * j)) ^ 3 <
      family.count ^ (3 * k * j) * ((2 ^ K * family.count) ^ (k * j)) ^ 3) :
    2 ^ 24 ≤ family.dimension ^ (k * j) := by
  exact actual_pooled_dimension_bound family rank exactification copies k j hK hk hj
    exactification_pos copies_paid (jointSource_rank_floor F family k j rank decomposition) raw

/-- The same actual tensor bound with independent auxiliary dimensions. -/
theorem actual_tensor_free_auxiliary_dimension_bound (family : Family n K)
    (auxiliary rank exactification copies k j : Nat)
    (hK : 0 < K) (hk : 0 < k) (hj : 0 < j)
    (exactification_pos : 0 < exactification)
    (copies_paid : auxiliary ^ 3 ≤ copies)
    (decomposition : Tensor.RankAtMost (jointSource F family k j).tensor rank)
    (raw : (rank * exactification ^ j * copies ^ (k * j)) *
      (family.dimension ^ (k * j)) ^ 3 <
      family.count ^ (3 * k * j) * ((2 ^ K * auxiliary) ^ (k * j)) ^ 3) :
    2 ^ 24 ≤ family.dimension ^ (k * j) := by
  exact FreeAuxiliaryBridge.actual_free_auxiliary_dimension_bound family auxiliary rank
    exactification copies k j hK hk hj exactification_pos copies_paid
    (jointSource_rank_floor F family k j rank decomposition) raw

/-- Concrete separator resources and an actual source-tensor decomposition give
an all-index threshold without a numerical rank-floor hypothesis. -/
theorem actual_tensor_polynomial_auxiliary_dimension_bound (family : Family n K)
    (separators : List FreeAuxiliaryBridge.Separator) (rank k j : Nat)
    (hK : 0 < K) (hk : 0 < k) (hj : 0 < j)
    (count_eq : FreeAuxiliaryBridge.blockCount separators = family.count)
    (decomposition : Tensor.RankAtMost (jointSource F family k j).tensor rank)
    (raw : (rank * FreeAuxiliaryBridge.polynomialExactification separators k ^ j *
      FreeAuxiliaryBridge.cyclicCopies separators ^ (k * j)) *
      (family.dimension ^ (k * j)) ^ 3 <
      FreeAuxiliaryBridge.blockCount separators ^ (3 * k * j) *
        ((2 ^ K * FreeAuxiliaryBridge.auxiliaryCount separators) ^ (k * j)) ^ 3) :
    2 ^ 24 ≤ family.dimension ^ (k * j) := by
  exact FreeAuxiliaryBridge.polynomial_auxiliary_dimension_bound family separators rank k j
    hK hk hj count_eq (jointSource_rank_floor F family k j rank decomposition) raw

end
end MatrixDimensionAudit.TensorRankBridge

#print axioms MatrixDimensionAudit.TensorRankBridge.FullTensor.flattening_rank
#print axioms MatrixDimensionAudit.TensorRankBridge.cyclicConvolution_full_flattenings
#print axioms MatrixDimensionAudit.TensorRankBridge.jointSource_rank_floor
#print axioms MatrixDimensionAudit.TensorRankBridge.actual_tensor_pooled_dimension_bound
#print axioms MatrixDimensionAudit.TensorRankBridge.actual_tensor_free_auxiliary_dimension_bound
#print axioms MatrixDimensionAudit.TensorRankBridge.actual_tensor_polynomial_auxiliary_dimension_bound

#print axioms MatrixDimensionAudit.TensorRankBridge.convolution_transpose
#print axioms MatrixDimensionAudit.TensorRankBridge.signedCyclicConvolution_dimension
