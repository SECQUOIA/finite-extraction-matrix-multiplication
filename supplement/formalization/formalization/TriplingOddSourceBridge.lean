import formalization.TriplingLocalSourceBridge

namespace MatrixDimensionAudit.TriplingOddSourceBridge
open OAI.MatrixMultiplication.Foundation
open TensorRankBridge TriplingRestrictionBridge TriplingLocalRecipeBridge TriplingLocalSourceBridge
open DependentSeparator SeparatorTensor
open scoped BigOperators

noncomputable section

/-- Exchange the last two factor coordinates inside a tensor-product leg. -/
def swapTail (X Y Z : Type) : ((X × Y) × Z) ≃ ((X × Z) × Y) where
  toFun := fun x => ((x.1.1, x.2), x.1.2)
  invFun := fun x => ((x.1.1, x.2), x.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

def backwardOutput (r b : Nat) : Fin (b + r - 1) ≃ Fin (r + b - 1) :=
  finCongr (by omega)

/-- A negative first leg becomes the positive second leg. -/
def oddX (r b : Nat) (hr : 0 < r) (hb : 0 < b) :
    (cyclicConvolution ℚ b r hb hr).X ≃ (cyclicConvolution ℚ r b hr hb).Y :=
  (swapTail _ _ _).trans
    (Equiv.prodCongr (Equiv.prodCongr (Equiv.refl _) (backwardOutput r b)) (Equiv.refl _))

def oddY (r b : Nat) (hr : 0 < r) (hb : 0 < b) :
    (cyclicConvolution ℚ b r hb hr).Y ≃ (cyclicConvolution ℚ r b hr hb).X :=
  (swapTail _ _ _).trans (Equiv.prodCongr (Equiv.refl _) (backwardOutput r b))

def oddZ (r b : Nat) (hr : 0 < r) (hb : 0 < b) :
    (cyclicConvolution ℚ b r hb hr).Z ≃ (cyclicConvolution ℚ r b hr hb).Z :=
  (swapTail _ _ _).trans
    (Equiv.prodCongr (Equiv.prodCongr (backwardOutput r b) (Equiv.refl _)) (Equiv.refl _))

/-- Input symmetry of C, followed by factor permutations, exchanges two whole
legs of S. It is not a leg-preserving identification of the two orientations. -/
theorem odd_tensor_identity (r b : Nat) (hr : 0 < r) (hb : 0 < b) :
    (cyclicConvolution ℚ b r hb hr).tensor =
      Tensor.pullback (oddX r b hr hb) (oddY r b hr hb) (oddZ r b hr hb)
        (transposeInputs ℚ (cyclicConvolution ℚ r b hr hb).tensor) := by
  funext x y z
  change ((if x.1.1.val + y.1.1.val = z.1.1.val then (1 : ℚ) else 0) *
    (if z.1.2.val + x.1.2.val = y.1.2.val then 1 else 0)) *
    (if y.2.val + z.2.val = x.2.val then 1 else 0) =
    ((if y.1.1.val + x.1.1.val = z.1.1.val then 1 else 0) *
      (if z.2.val + y.2.val = x.2.val then 1 else 0)) *
      (if x.1.2.val + z.1.2.val = y.1.2.val then 1 else 0)
  have ha : (if y.1.1.val + x.1.1.val = z.1.1.val then (1 : ℚ) else 0) =
      (if x.1.1.val + y.1.1.val = z.1.1.val then 1 else 0) :=
    congrArg (fun t => if t = z.1.1.val then (1 : ℚ) else 0) (Nat.add_comm _ _)
  have hb' : (if z.2.val + y.2.val = x.2.val then (1 : ℚ) else 0) =
      (if y.2.val + z.2.val = x.2.val then 1 else 0) :=
    congrArg (fun t => if t = x.2.val then (1 : ℚ) else 0) (Nat.add_comm _ _)
  have hc : (if x.1.2.val + z.1.2.val = y.1.2.val then (1 : ℚ) else 0) =
      (if z.1.2.val + x.1.2.val = y.1.2.val then 1 else 0) :=
    congrArg (fun t => if t = y.1.2.val then (1 : ℚ) else 0) (Nat.add_comm _ _)
  rw [ha, hb', hc]
  exact mul_right_comm _ _ _

/-- Transposition transports an actual rank decomposition by exchanging its
first two coefficient families. -/
theorem rank_transpose {X Y Z : Type} {T : Tensor ℚ X Y Z} {R : Nat}
    (h : Tensor.RankAtMost T R) : Tensor.RankAtMost (transposeInputs ℚ T) R := by
  obtain ⟨a, b, c, h⟩ := h
  refine ⟨b, a, c, ?_⟩
  funext y x z
  change T x y z = _
  rw [h]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun t => t * c i z) (mul_comm (a i x) (b i y))

theorem positive_of_negative (r b N R : Nat) (hr : 0 < r) (hb : 0 < b)
    (h : Tensor.RankAtMost ((cyclicConvolution ℚ b r hb hr).power N).tensor R) :
    Tensor.RankAtMost ((cyclicConvolution ℚ r b hr hb).power N).tensor R := by
  have hn := (PowerCoordinateBridge.power_rankAtMost_iff ℚ _ N R).mp h
  have he : Tensor.power (transposeInputs ℚ (cyclicConvolution ℚ r b hr hb).tensor) N =
      Tensor.pullback (fun x i => (oddX r b hr hb).symm (x i))
        (fun y i => (oddY r b hr hb).symm (y i))
        (fun z i => (oddZ r b hr hb).symm (z i))
        (Tensor.power (cyclicConvolution ℚ b r hb hr).tensor N) := by
    funext x y z
    change (∏ i : Fin N, _) = ∏ i : Fin N, _
    apply Finset.prod_congr rfl
    intro i _
    have ht := congrFun (congrFun (congrFun (odd_tensor_identity r b hr hb)
      ((oddX r b hr hb).symm (x i))) ((oddY r b hr hb).symm (y i)))
      ((oddZ r b hr hb).symm (z i))
    simpa only [Tensor.pullback, Equiv.apply_symm_apply] using ht.symm
  have ht : Tensor.RankAtMost
      (Tensor.power (transposeInputs ℚ (cyclicConvolution ℚ r b hr hb).tensor) N) R := by
    rw [he]
    exact hn.pullback _ _ _
  apply (PowerCoordinateBridge.power_rankAtMost_iff ℚ _ N R).mpr
  exact rank_transpose ht

theorem positive_reset_rank_of_negative (r N R : Nat) (hr : 2 ≤ r)
    (h : Tensor.RankAtMost ((resetFactor ℚ true r hr).power N).tensor R) :
    Tensor.RankAtMost ((resetFactor ℚ false r hr).power N).tensor R := by
  exact positive_of_negative r (4 * r - 1) N R (by omega) (by omega) h

/-- The full local recipe accepts an actual odd reset-source decomposition
and retains the same complete M^(3k) output, auxiliary factor, and joint charge. -/
theorem actual_local_recipe_odd_split (r N m aux k R : Nat) (hr : 2 ≤ r)
    (source_rank : Tensor.RankAtMost ((resetFactor ℚ true r hr).power N).tensor R) :
    Tensor.RankAtMost (Tensor.directSum
      (fun _ : Fin k → Index N m => Tensor.product
        ((child r N (by omega)).power k).tensor (Tensor.power (auxiliary aux) k)))
      ((3 * k * localDegree N m aux + 1) *
        ell (Tripling.blockCount N m) aux ^ (3 * k) * R ^ k) :=
  actual_local_recipe_reset_split r N m aux k R hr
    (positive_reset_rank_of_negative r N R hr source_rank)

/-- Both reset parities feed the same actual local output tensor. -/
theorem actual_local_recipe_signed_split (negative : Bool) (r N m aux k R : Nat) (hr : 2 ≤ r)
    (source_rank : Tensor.RankAtMost ((resetFactor ℚ negative r hr).power N).tensor R) :
    Tensor.RankAtMost (Tensor.directSum
      (fun _ : Fin k → Index N m => Tensor.product
        ((child r N (by omega)).power k).tensor (Tensor.power (auxiliary aux) k)))
      ((3 * k * localDegree N m aux + 1) *
        ell (Tripling.blockCount N m) aux ^ (3 * k) * R ^ k) := by
  cases negative with
  | false => exact actual_local_recipe_reset_split r N m aux k R hr source_rank
  | true => exact actual_local_recipe_odd_split r N m aux k R hr source_rank

end
end MatrixDimensionAudit.TriplingOddSourceBridge

#print axioms MatrixDimensionAudit.TriplingOddSourceBridge.odd_tensor_identity
#print axioms MatrixDimensionAudit.TriplingOddSourceBridge.rank_transpose
#print axioms MatrixDimensionAudit.TriplingOddSourceBridge.positive_of_negative
#print axioms MatrixDimensionAudit.TriplingOddSourceBridge.positive_reset_rank_of_negative
#print axioms MatrixDimensionAudit.TriplingOddSourceBridge.actual_local_recipe_odd_split
#print axioms MatrixDimensionAudit.TriplingOddSourceBridge.actual_local_recipe_signed_split
