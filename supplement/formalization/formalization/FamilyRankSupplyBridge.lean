import formalization.ConvolutionRankSupplyBridge

/-! Actual evaluation-rank supply for the population-expanded family catalyst and joint source. -/
namespace MatrixDimensionAudit.FamilyRankSupplyBridge
open OAI.MatrixMultiplication.Foundation
open TensorRankBridge GeneralRowCatalyst AllRowProfile GeneralFlow
open scoped BigOperators
noncomputable section

/-- Evaluation cost of the actual list of consumed split factors. -/
def splitCost (r : ℕ) (xs : List ℕ) : ℕ :=
  (xs.map (fun x => (2 * r - 2 + x) ^ 3)).prod

def topCost (row : Row r 1 K) : ℕ :=
  splitCost r (removeInjected K (parents row.actions)) * ((5 * r - 2) ^ 3) ^ row.Z

def lowerCost (row : Row r 2 K) : ℕ :=
  splitCost r (parents row.actions) * ((5 * r - 2) ^ 3) ^ row.Z

def lowerRowsCost : {n : ℕ} → LowerRows K n → ℕ
  | _, .nil => 1
  | _, .cons row tail => lowerCost row * lowerRowsCost tail

def familyCost (family : Family n K) : ℕ := topCost family.top * lowerRowsCost family.lower

/-- The scalar FullTensor has its one-term decomposition. -/
theorem unit_rank : Tensor.RankAtMost (FullTensor.unit (F := ℚ)).tensor 1 := by
  refine ⟨fun _ _ => 1, fun _ _ => 1, fun _ _ => 1, ?_⟩
  funext x y z
  simp [FullTensor.unit, Tensor.rankOne]

/-- Actual signed split-factor rank supply at the state-dependent interpolation length. -/
theorem splitFactor_rank (negative : Bool) (r : ℕ) (hr : 2 ≤ r) (x : ℕ) :
    Tensor.RankAtMost (splitFactor ℚ negative r hr x).tensor ((2 * r - 2 + x) ^ 3) := by
  have hs := ConvolutionRankSupplyBridge.signed_full_rank negative r (r - 1 + x)
    (by omega) (by omega)
  have hw : r + (r - 1 + x) - 1 = 2 * r - 2 + x := by omega
  simpa only [splitFactor, hw] using hs

/-- Every factor in the actual consumed split list is supplied, with its multiplicity. -/
theorem splitFactors_rank (negative : Bool) (r : ℕ) (hr : 2 ≤ r) (xs : List ℕ) :
    Tensor.RankAtMost (splitFactors ℚ negative r hr xs).tensor (splitCost r xs) := by
  induction xs with
  | nil => exact unit_rank
  | cons x xs ih =>
      exact (splitFactor_rank negative r hr x).product ih

/-- The actual signed reset source power, including the empty power. -/
theorem resetPower_rank (negative : Bool) (r : ℕ) (hr : 2 ≤ r) (z : ℕ) :
    Tensor.RankAtMost ((resetFactor ℚ negative r hr).power z).tensor (((5 * r - 2) ^ 3) ^ z) := by
  have hs := ConvolutionRankSupplyBridge.signed_full_power_rank negative r (4 * r - 1) z
    (by omega) (by omega)
  have hw : r + (4 * r - 1) - 1 = 5 * r - 2 := by omega
  simpa only [resetFactor, hw] using hs

/-- Top catalyst supply removes exactly the externally injected copies already removed in its definition. -/
theorem topConsumed_rank (row : Row r 1 K) (hr : 2 ≤ r) :
    Tensor.RankAtMost (topConsumed ℚ row hr).tensor (topCost row) :=
  (splitFactors_rank false r hr _).product (resetPower_rank false r hr row.Z)

/-- Lower-row supply retains every parent and the actual row orientation. -/
theorem lowerConsumed_rank (negative : Bool) (row : Row r 2 K) (hr : 2 ≤ r) :
    Tensor.RankAtMost (lowerConsumed ℚ negative row hr).tensor (lowerCost row) :=
  (splitFactors_rank negative r hr _).product (resetPower_rank negative r hr row.Z)

/-- All alternating lower-row signs are handled on their named tensors. -/
theorem lowerRowsConsumed_rank (depth : ℕ) (rows : LowerRows K n) :
    Tensor.RankAtMost (lowerRowsConsumed ℚ depth rows).tensor (lowerRowsCost rows) := by
  induction rows generalizing depth with
  | nil => exact unit_rank
  | @cons n row tail ih =>
      exact (lowerConsumed_rank (decide (depth % 2 = 1)) row (by omega)).product (ih (depth + 1))

/-- A supplied rank certificate for the entire actual family catalyst, with no rank premise. -/
theorem familyConsumed_rank (family : Family n K) :
    Tensor.RankAtMost (familyConsumed ℚ family).tensor (familyCost family) :=
  (topConsumed_rank family.top (by omega)).product (lowerRowsConsumed_rank 1 family.lower)

/-- The complete population-expanded joint source has an actual evaluation decomposition. -/
theorem jointSource_rank (family : Family n K) (k j : ℕ) :
    Tensor.RankAtMost (jointSource ℚ family k j).tensor
      ((((2 * (n + 2) - 1) ^ 3) ^ (K * k * j)) * familyCost family ^ k) := by
  have hs := ConvolutionRankSupplyBridge.signed_full_power_rank false (n + 2) (n + 2)
    (K * k * j) (by omega) (by omega)
  have hw : n + 2 + (n + 2) - 1 = 2 * (n + 2) - 1 := by omega
  change Tensor.RankAtMost ((sourceFactor ℚ (n + 2) (by omega)).power (K * k * j)).tensor _ at hs
  have hc := (PowerCoordinateBridge.power_rankAtMost_iff ℚ (familyConsumed ℚ family) k _).mpr
    ((familyConsumed_rank family).power k)
  have hp := hs.product hc
  change Tensor.RankAtMost (jointSource ℚ family k j).tensor _ at hp
  simpa only [hw] using hp

/-- The existing flattening floor is paid by this concrete global evaluation certificate. -/
theorem jointSource_cost_floor (family : Family n K) (k j : ℕ) :
    sourceLeg (n + 2) ^ (K * k * j) * familyCharge family ^ k ≤
      (((2 * (n + 2) - 1) ^ 3) ^ (K * k * j)) * familyCost family ^ k :=
  jointSource_rank_floor ℚ family k j _ (jointSource_rank family k j)

end
end MatrixDimensionAudit.FamilyRankSupplyBridge
