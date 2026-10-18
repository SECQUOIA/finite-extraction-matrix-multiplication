import Mathlib.Analysis.SpecialFunctions.Log.Basic
import formalization.TensorRankBridge

/-!
Exact conversion between the relative logarithmic exponent and the strict
pooled integer comparison. The tensor decomposition and separator resource
conditions remain explicit hypotheses in the endpoint theorem.
-/

namespace MatrixDimensionAudit.RealExponentBridge

/-- Clearing a positive logarithmic gain denominator gives precisely the
cubic pooled comparison. All logarithm arguments are strictly positive. -/
theorem real_relative_exponent_lt_three_iff (A B r m : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hr : 0 < r) (hm : 0 < m) (hAB : A < B) :
    (Real.log r - Real.log m) / (Real.log B - Real.log A) < 3 ↔
      r * A ^ 3 < m * B ^ 3 := by
  have denominator_pos : 0 < Real.log B - Real.log A :=
    sub_pos.mpr (Real.log_lt_log hA hAB)
  have left_pos : 0 < r * A ^ 3 := mul_pos hr (pow_pos hA _)
  have right_pos : 0 < m * B ^ 3 := mul_pos hm (pow_pos hB _)
  calc
    (Real.log r - Real.log m) / (Real.log B - Real.log A) < 3 ↔
        Real.log (r * A ^ 3) < Real.log (m * B ^ 3) := by
      rw [div_lt_iff₀ denominator_pos,
        Real.log_mul (ne_of_gt hr) (ne_of_gt (pow_pos hA 3)),
        Real.log_mul (ne_of_gt hm) (ne_of_gt (pow_pos hB 3)),
        Real.log_pow, Real.log_pow]
      norm_num
      constructor <;> intro h <;> linarith
    _ ↔ r * A ^ 3 < m * B ^ 3 := Real.log_lt_log_iff left_pos right_pos

/-- The exact integer form, with natural numbers cast to reals only inside
the logarithms. There is no rounding or numerical logarithm evaluation. -/
theorem nat_relative_exponent_lt_three_iff (A B r m : Nat)
    (hA : 0 < A) (hB : 0 < B) (hr : 0 < r) (hm : 0 < m) (hAB : A < B) :
    (Real.log (r : ℝ) - Real.log (m : ℝ)) /
        (Real.log (B : ℝ) - Real.log (A : ℝ)) < 3 ↔
      r * A ^ 3 < m * B ^ 3 := by
  have converted := real_relative_exponent_lt_three_iff (A : ℝ) (B : ℝ) (r : ℝ) (m : ℝ)
    (by exact_mod_cast hA) (by exact_mod_cast hB)
    (by exact_mod_cast hr) (by exact_mod_cast hm) (by exact_mod_cast hAB)
  exact_mod_cast converted

open OAI.MatrixMultiplication.Foundation
open AllRowProfile

/-- The actual free-auxiliary tensor endpoint, now triggered by the relative
exponent being below three rather than by a supplied integer comparison.
Positive gain and logarithm arguments are explicit domain conditions. -/
theorem actual_tensor_free_auxiliary_dimension_bound_of_exponent
    (F : Type) [Field F] (family : Family n K)
    (auxiliary rank exactification copies k j : Nat)
    (hK : 0 < K) (hk : 0 < k) (hj : 0 < j)
    (auxiliary_pos : 0 < auxiliary) (rank_pos : 0 < rank)
    (count_pos : 0 < family.count) (dimension_pos : 0 < family.dimension)
    (exactification_pos : 0 < exactification)
    (copies_paid : auxiliary ^ 3 ≤ copies)
    (decomposition : Tensor.RankAtMost (TensorRankBridge.jointSource F family k j).tensor rank)
    (gain : family.dimension ^ (k * j) < (2 ^ K * auxiliary) ^ (k * j))
    (exponent :
      (Real.log ((rank * exactification ^ j * copies ^ (k * j) : Nat) : ℝ) -
        Real.log ((family.count ^ (3 * k * j) : Nat) : ℝ)) /
      (Real.log (((2 ^ K * auxiliary) ^ (k * j) : Nat) : ℝ) -
        Real.log ((family.dimension ^ (k * j) : Nat) : ℝ)) < 3) :
    2 ^ 24 ≤ family.dimension ^ (k * j) := by
  have copies_pos : 0 < copies :=
    lt_of_lt_of_le (Nat.pow_pos auxiliary_pos) copies_paid
  have raw := (nat_relative_exponent_lt_three_iff
    (family.dimension ^ (k * j)) ((2 ^ K * auxiliary) ^ (k * j))
    (rank * exactification ^ j * copies ^ (k * j)) (family.count ^ (3 * k * j))
    (Nat.pow_pos dimension_pos)
    (Nat.pow_pos (Nat.mul_pos (by positivity) auxiliary_pos))
    (Nat.mul_pos (Nat.mul_pos rank_pos (Nat.pow_pos exactification_pos))
      (Nat.pow_pos copies_pos))
    (Nat.pow_pos count_pos) gain).mp exponent
  exact TensorRankBridge.actual_tensor_free_auxiliary_dimension_bound F family
    auxiliary rank exactification copies k j hK hk hj exactification_pos copies_paid
    decomposition raw

end MatrixDimensionAudit.RealExponentBridge

#print axioms MatrixDimensionAudit.RealExponentBridge.real_relative_exponent_lt_three_iff
#print axioms MatrixDimensionAudit.RealExponentBridge.nat_relative_exponent_lt_three_iff
#print axioms MatrixDimensionAudit.RealExponentBridge.actual_tensor_free_auxiliary_dimension_bound_of_exponent
