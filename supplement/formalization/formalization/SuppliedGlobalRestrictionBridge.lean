import formalization.GlobalExactRestrictionBridge
import formalization.FamilyRankSupplyBridge
import formalization.RealExponentBridge

/-!
The complete actual relative matrix restriction with its rank supply already
instantiated, and the numerical dimension obstruction for its exact parameters.
No rank-certificate, separator-count, or copy-payment premise is required.
-/

namespace MatrixDimensionAudit.SuppliedGlobalRestrictionBridge

open OAI.MatrixMultiplication.Foundation
open TensorRankBridge TensorResourcePoolingBridge CatalystReuseBridge AllRowProfile
open GlobalFamilySampleBridge GlobalExactRestrictionBridge FlowActionTensorBridge
open scoped BigOperators

noncomputable section

attribute [local instance] GlobalFamilySampleBridge.productFiniteX GlobalFamilySampleBridge.productFiniteY
  GlobalFamilySampleBridge.matrixFiniteX GlobalFamilySampleBridge.matrixFiniteY
  CatalystReuseBridge.diagonalFiniteX CatalystReuseBridge.diagonalFiniteY
  CatalystReuseBridge.diagonalDecX CatalystReuseBridge.diagonalDecY

/-- The actual joint-source evaluation supply, with one powered common catalyst. -/
def sourceRank (family : Family n K) (k j : ℕ) : ℕ :=
  (((2 * (n + 2) - 1) ^ 3) ^ (K * k * j)) * FamilyRankSupplyBridge.familyCost family ^ k

def exactification (family : Family n K) (k : ℕ) : ℕ := k * familyDegree family + 1

def inputWidth (family : Family n K) (k j : ℕ) : ℕ := family.dimension ^ (k * j)

def outputWidth (family : Family n K) (k j : ℕ) : ℕ := (2 ^ K * family.count) ^ (k * j)

def outputCopies (family : Family n K) (k j : ℕ) : ℕ := family.count ^ (3 * k * j)

/-- Every source copy, exactification node, and powered local copy is charged. -/
def inputCopies (family : Family n K) (k j : ℕ) : ℕ :=
  sourceRank family k j * exactification family k ^ j * familyCopies family ^ (k * j)

/-- Three actual relative restriction matrices, with the source certificate
supplied by its explicit decomposition rather than by a caller premise. -/
def suppliedMaps (family : Family n K) (k j : ℕ) :
    Maps ((diagonalFull (inputCopies family k j)).product (matrixFull (inputWidth family k j)))
      ((diagonalFull (outputCopies family k j)).product (matrixFull (outputWidth family k j))) :=
  familyRelative family k j (sourceRank family k j) (FamilyRankSupplyBridge.jointSource_rank family k j)

/-- Complete coefficient identity with the four actual relative parameters. -/
theorem supplied_identity (family : Family n K) (k j : ℕ) :
    Tensor.restrict (suppliedMaps family k j).first (suppliedMaps family k j).second
      (suppliedMaps family k j).third
      (Tensor.directSum (fun _ : Fin (inputCopies family k j) =>
        (matrixFull (inputWidth family k j)).tensor)) =
      Tensor.directSum (fun _ : Fin (outputCopies family k j) =>
        (matrixFull (outputWidth family k j)).tensor) :=
  family_relative_identity family k j (sourceRank family k j)
    (FamilyRankSupplyBridge.jointSource_rank family k j)

/-- Closed resource formula: the common catalyst is charged to power k,
while the external source power and every separator/reuse cost remain explicit. -/
theorem input_copies_formula (family : Family n K) (k j : ℕ) :
    inputCopies family k j =
      FamilyRankSupplyBridge.familyCost family ^ k *
        (k * familyDegree family + 1) ^ j * familyCopies family ^ (k * j) *
          (2 * (n + 2) - 1) ^ (3 * K * k * j) := by
  unfold inputCopies sourceRank exactification
  rw [← pow_mul, show 3 * (K * k * j) = 3 * K * k * j by ring]
  ac_rfl

private theorem separator_product_pos (ss : List FreeAuxiliaryBridge.Separator) :
    0 < FreeAuxiliaryBridge.blockCount ss := by
  induction ss with
  | nil => exact Nat.zero_lt_one
  | cons s ss ih => exact Nat.mul_pos s.blocks_pos ih

/-- All actual sector factors are positive, including zero-width actions and resets. -/
theorem count_pos (family : Family n K) : 0 < family.count := by
  rw [← family_separator_count family]
  exact separator_product_pos _

/-- The source matrix width is positive from the proved actual family baseline. -/
theorem dimension_pos (family : Family n K) : 0 < family.dimension := by
  have h := GeneralRowDimension.family_branch_baseline family
  exact lt_of_lt_of_le (Nat.pow_pos (Nat.mul_pos (by decide) (Nat.pow_pos (by decide)))) h

private theorem separator_product_paid (ss : List FreeAuxiliaryBridge.Separator) :
    FreeAuxiliaryBridge.blockCount ss ≤
      (ss.map (fun s => s.blocks + s.blocks - 1)).prod := by
  induction ss with
  | nil => exact Nat.le_refl _
  | cons s ss ih =>
      have hp := s.blocks_pos
      have hl : s.blocks ≤ s.blocks + s.blocks - 1 := by omega
      exact Nat.mul_le_mul hl ih

/-- Derive the actual cubic copy payment from the actual separator list and
its proved block-count identity. It is not an endpoint assumption. -/
theorem copies_paid (family : Family n K) : family.count ^ 3 ≤ familyCopies family := by
  rw [family_copies_formula, ← family_separator_count family]
  exact Nat.pow_le_pow_left (separator_product_paid _) 3

theorem copies_pos (family : Family n K) : 0 < familyCopies family :=
  lt_of_lt_of_le (Nat.pow_pos (count_pos family)) (copies_paid family)

/-- Positivity of the supplied joint rank follows from the actual flattening floor. -/
theorem source_rank_pos (family : Family n K) (k j : ℕ) : 0 < sourceRank family k j := by
  have hc : 0 < GeneralRowCatalyst.familyCharge family := by
    simpa only [familyConsumed_dimension] using catalyst_dimension_pos family
  have hs : 0 < GeneralRowCatalyst.sourceLeg (n + 2) := by
    unfold GeneralRowCatalyst.sourceLeg
    have : 0 < 2 * (n + 2) - 1 := by omega
    positivity
  exact lt_of_lt_of_le (Nat.mul_pos (Nat.pow_pos hs) (Nat.pow_pos hc))
    (FamilyRankSupplyBridge.jointSource_cost_floor family k j)

theorem input_width_pos (family : Family n K) (k j : ℕ) : 0 < inputWidth family k j :=
  Nat.pow_pos (dimension_pos family)

theorem output_width_pos (family : Family n K) (k j : ℕ) : 0 < outputWidth family k j :=
  Nat.pow_pos (Nat.mul_pos (Nat.pow_pos (by decide)) (count_pos family))

theorem output_copies_pos (family : Family n K) (k j : ℕ) : 0 < outputCopies family k j :=
  Nat.pow_pos (count_pos family)

theorem input_copies_pos (family : Family n K) (k j : ℕ) : 0 < inputCopies family k j := by
  unfold inputCopies
  exact Nat.mul_pos (Nat.mul_pos (source_rank_pos family k j)
    (Nat.pow_pos (by unfold exactification; omega))) (Nat.pow_pos (copies_pos family))

/-- The supplied actual relative parameters meet the existing dimension
obstruction whenever their strict cubic comparison holds. -/
theorem dimension_bound_of_cubic (family : Family n K) (k j : ℕ)
    (hK : 0 < K) (hk : 0 < k) (hj : 0 < j)
    (raw : inputCopies family k j * inputWidth family k j ^ 3 <
      outputCopies family k j * outputWidth family k j ^ 3) :
    2 ^ 24 ≤ inputWidth family k j := by
  exact actual_tensor_pooled_dimension_bound ℚ family (sourceRank family k j)
    (exactification family k) (familyCopies family) k j hK hk hj
    (by unfold exactification; omega) (copies_paid family)
    (FamilyRankSupplyBridge.jointSource_rank family k j) raw

/-- Exact relative logarithmic parameter expression for the actual matrix copies. -/
def relativeExponent (family : Family n K) (k j : ℕ) : ℝ :=
  (Real.log (inputCopies family k j : ℝ) - Real.log (outputCopies family k j : ℝ)) /
    (Real.log (outputWidth family k j : ℝ) - Real.log (inputWidth family k j : ℝ))

/-- A positive gain and the actual relative expression below three imply the
same A>=2^24 threshold, without supplied rank/count/copy hypotheses. -/
theorem dimension_bound_of_exponent (family : Family n K) (k j : ℕ)
    (hK : 0 < K) (hk : 0 < k) (hj : 0 < j)
    (gain : inputWidth family k j < outputWidth family k j)
    (exponent : relativeExponent family k j < 3) :
    2 ^ 24 ≤ inputWidth family k j := by
  have hraw := (RealExponentBridge.nat_relative_exponent_lt_three_iff
    (inputWidth family k j) (outputWidth family k j)
    (inputCopies family k j) (outputCopies family k j)
    (input_width_pos family k j) (output_width_pos family k j)
    (input_copies_pos family k j) (output_copies_pos family k j) gain).mp exponent
  exact dimension_bound_of_cubic family k j hK hk hj hraw

#print axioms suppliedMaps
#print axioms supplied_identity
#print axioms input_copies_formula
#print axioms copies_paid
#print axioms source_rank_pos
#print axioms dimension_bound_of_cubic
#print axioms dimension_bound_of_exponent

end
end MatrixDimensionAudit.SuppliedGlobalRestrictionBridge
