import formalization.SeparatorInterpolationBridge
import formalization.PowerCoordinateBridge

/-!
Explicit rational rank supply for the actual convolution, signed cyclic
FullTensor sources, and complete matrix tensors. No rank-supply premise occurs.
-/

namespace MatrixDimensionAudit.ConvolutionRankSupplyBridge

open OAI.MatrixMultiplication.Foundation
open Separator TensorRankBridge TriplingRestrictionBridge PowerCoordinateBridge Polynomial
open scoped BigOperators

noncomputable section

/-- The actual Lagrange evaluation/interpolation coefficient identity. -/
theorem convolution_coefficient (r b : ℕ) (i : Fin r) (j : Fin b)
    (k : Fin (r + b - 1)) :
    (∑ s : Fin (r + b - 1), rationalNode s.val ^ i.val * rationalNode s.val ^ j.val *
      (Lagrange.basis (Finset.range (r + b - 1)) rationalNode s.val).coeff k.val) =
      convolution ℚ r b i j k := by
  have hd : i.val + j.val < (Finset.range (r + b - 1)).card := by
    simp only [Finset.card_range]
    have := i.isLt; have := j.isLt; omega
  have hi := sourceCoefficient_eq_taylor (Finset.range (r + b - 1)) rationalNode
    rationalNode_injective.injOn (0 : ℚ) i.val j.val k.val hd
  have hs : (∑ s : Fin (r + b - 1), rationalNode s.val ^ i.val * rationalNode s.val ^ j.val *
      (Lagrange.basis (Finset.range (r + b - 1)) rationalNode s.val).coeff k.val) =
      sourceCoefficient (Finset.range (r + b - 1)) rationalNode 0 i.val j.val k.val := by
    unfold sourceCoefficient
    simp only [sub_zero, taylor_zero]
    exact Fin.sum_univ_eq_sum_range (fun s => rationalNode s ^ i.val * rationalNode s ^ j.val *
      (Lagrange.basis (Finset.range (r + b - 1)) rationalNode s).coeff k.val) _
  rw [hs, hi]
  simp [← pow_add, coeff_X_pow, convolution, eq_comm]

/-- An explicit ell-term decomposition of actual convolution, with ell=r+b-1. -/
theorem convolution_rank (r b : ℕ) :
    Tensor.RankAtMost (convolution ℚ r b) (r + b - 1) := by
  let a : Fin (r + b - 1) → Fin r → ℚ := fun s i => rationalNode s.val ^ i.val
  let bb : Fin (r + b - 1) → Fin b → ℚ := fun s j => rationalNode s.val ^ j.val
  let c : Fin (r + b - 1) → Fin (r + b - 1) → ℚ := fun s k =>
    (Lagrange.basis (Finset.range (r + b - 1)) rationalNode s.val).coeff k.val
  have ht : convolution ℚ r b = fun i j k =>
      ∑ s : Fin (r + b - 1), Tensor.rankOne (a s) (bb s) (c s) i j k := by
    funext i j k
    exact (convolution_coefficient r b i j k).symm
  rw [ht]
  simpa only [Fintype.card_fin] using Tensor.rankAtMost_sum_rankOne a bb c

/-- The actual cyclic triple uses three explicit product decompositions. -/
theorem cyclic_triple_rank (r b : ℕ) :
    Tensor.RankAtMost (cyclicTriple ℚ (convolution ℚ r b)) ((r + b - 1) ^ 3) := by
  have h := convolution_rank r b
  simpa only [cyclicTriple, pow_succ, pow_zero, mul_one, one_mul] using
    (h.product h.cyclic).product h.cyclic.cyclic

/-- Rank supply for the exact FullTensor cyclic source used in the ledger. -/
theorem cyclic_full_rank (r b : ℕ) (hr : 0 < r) (hb : 0 < b) :
    Tensor.RankAtMost (cyclicConvolution ℚ r b hr hb).tensor ((r + b - 1) ^ 3) :=
  cyclic_triple_rank r b

/-- Both orientation parities have the same supplied rank, using the actual
input-transposed convolution realization of the odd sign. -/
theorem signed_full_rank (negative : Bool) (r b : ℕ) (hr : 0 < r) (hb : 0 < b) :
    Tensor.RankAtMost (signedCyclicConvolution ℚ negative r b hr hb).tensor
      ((r + b - 1) ^ 3) := by
  cases negative
  · exact cyclic_full_rank r b hr hb
  · change Tensor.RankAtMost (cyclicConvolution ℚ b r hb hr).tensor ((r + b - 1) ^ 3)
    simpa only [Nat.add_comm] using cyclic_full_rank b r hb hr

/-- External function-indexed tensor powers, including N=0. -/
theorem signed_tensor_power_rank (negative : Bool) (r b N : ℕ)
    (hr : 0 < r) (hb : 0 < b) :
    Tensor.RankAtMost
      (Tensor.power (signedCyclicConvolution ℚ negative r b hr hb).tensor N)
      (((r + b - 1) ^ 3) ^ N) :=
  (signed_full_rank negative r b hr hb).power N

/-- Nested-pair FullTensor powers use the proved coordinate transport. -/
theorem signed_full_power_rank (negative : Bool) (r b N : ℕ)
    (hr : 0 < r) (hb : 0 < b) :
    Tensor.RankAtMost ((signedCyclicConvolution ℚ negative r b hr hb).power N).tensor
      (((r + b - 1) ^ 3) ^ N) :=
  (power_rankAtMost_iff ℚ _ N _).mpr (signed_tensor_power_rank negative r b N hr hb)

/-- The complete matrix tensor, decomposed by the three matrix indices. -/
theorem matrix_rank (h : ℕ) :
    Tensor.RankAtMost (Tensor.matrixCoefficients (K := ℚ) (Fin h) (Fin h) (Fin h)) (h ^ 3) := by
  let a : (Fin h × Fin h × Fin h) → (Fin h × Fin h) → ℚ :=
    fun s x => if x.1 = s.1 ∧ x.2 = s.2.1 then 1 else 0
  let b : (Fin h × Fin h × Fin h) → (Fin h × Fin h) → ℚ :=
    fun s y => if y.1 = s.2.1 ∧ y.2 = s.2.2 then 1 else 0
  let c : (Fin h × Fin h × Fin h) → (Fin h × Fin h) → ℚ :=
    fun s z => if z.1 = s.2.2 ∧ z.2 = s.1 then 1 else 0
  have ht : Tensor.matrixCoefficients (K := ℚ) (Fin h) (Fin h) (Fin h) =
      fun x y z => ∑ s : Fin h × Fin h × Fin h,
        Tensor.rankOne (a s) (b s) (c s) x y z := by
    funext x y z
    by_cases hxy : x.2 = y.1 <;> by_cases hyz : y.2 = z.1 <;>
      by_cases hzx : z.2 = x.1 <;>
      simp_all [Tensor.matrixCoefficients, Tensor.rankOne, a, b, c,
        Fintype.sum_prod_type, ite_and, mul_ite, Finset.sum_ite_irrel, eq_comm]
  rw [ht]
  simpa [pow_succ, Nat.mul_assoc] using Tensor.rankAtMost_sum_rankOne a b c

/-- The actual cyclic-convolution and full-matrix source product, with its
complete rational rank supply. Both factors use external tensor powers. -/
theorem source_product_power_rank (r b h N : ℕ) :
    Tensor.RankAtMost
      (Tensor.product (Tensor.power (cyclicTriple ℚ (convolution ℚ r b)) N)
        (Tensor.power (Tensor.matrixCoefficients (K := ℚ) (Fin h) (Fin h) (Fin h)) N))
      (((r + b - 1) ^ 3 * h ^ 3) ^ N) := by
  simpa only [mul_pow] using ((cyclic_triple_rank r b).power N).product ((matrix_rank h).power N)

/-- The same source supply for either actual orientation sign. -/
theorem signed_source_product_power_rank (negative : Bool) (r b h N : ℕ)
    (hr : 0 < r) (hb : 0 < b) :
    Tensor.RankAtMost
      (Tensor.product (Tensor.power (signedCyclicConvolution ℚ negative r b hr hb).tensor N)
        (Tensor.power (Tensor.matrixCoefficients (K := ℚ) (Fin h) (Fin h) (Fin h)) N))
      (((r + b - 1) ^ 3 * h ^ 3) ^ N) := by
  simpa only [mul_pow] using
    (signed_tensor_power_rank negative r b N hr hb).product ((matrix_rank h).power N)

/-- The first factor may instead use the ledger's nested-pair power coordinates. -/
theorem full_source_product_power_rank (negative : Bool) (r b h N : ℕ)
    (hr : 0 < r) (hb : 0 < b) :
    Tensor.RankAtMost
      (Tensor.product ((signedCyclicConvolution ℚ negative r b hr hb).power N).tensor
        (Tensor.power (Tensor.matrixCoefficients (K := ℚ) (Fin h) (Fin h) (Fin h)) N))
      (((r + b - 1) ^ 3 * h ^ 3) ^ N) := by
  simpa only [mul_pow] using
    (signed_full_power_rank negative r b N hr hb).product ((matrix_rank h).power N)

#print axioms convolution_coefficient
#print axioms convolution_rank
#print axioms signed_full_rank
#print axioms signed_full_power_rank
#print axioms matrix_rank
#print axioms source_product_power_rank
#print axioms full_source_product_power_rank

end
end MatrixDimensionAudit.ConvolutionRankSupplyBridge
