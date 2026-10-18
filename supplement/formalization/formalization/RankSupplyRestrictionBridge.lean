import formalization.ConvolutionRankSupplyBridge
import formalization.TensorResourcePoolingBridge

/-!
A rank decomposition supplies actual restriction matrices from copies of an
arbitrary spectator tensor. The spectator remains the source resource; no
rank decomposition or scalar rank charge is required for it.
-/

namespace MatrixDimensionAudit.RankSupplyRestrictionBridge

open OAI.MatrixMultiplication.Foundation
open TensorRankBridge TensorResourcePoolingBridge
open scoped BigOperators

noncomputable section

variable {K X Y Z U V W : Type*} [CommSemiring K]

/-- A coefficient matrix acts linearly on its finite source coordinate space. -/
def coefficientLinear {I J : Type*} [Fintype I] (A : J → I → K) :
    (I → K) →ₗ[K] (J → K) where
  toFun v j := ∑ i, A j i * v i
  map_add' v w := by funext j; simp [mul_add, Finset.sum_add_distrib]
  map_smul' c v := by funext j; simp [Finset.mul_sum, mul_left_comm]

/-- One decomposition factor controls the copy label and preserves the entire
spectator coordinate through a Kronecker delta. -/
def supplyMatrix {I : Type*} [DecidableEq U] (a : I → X → K) :
    (X × U) → (I × U) → K :=
  fun xu iu => if iu.2 = xu.2 then a iu.1 xu.1 else 0

/-- Complete coefficient identity for the three decomposition-based matrices. -/
theorem restrict_decomposition
    [Fintype U] [Fintype V] [Fintype W]
    [DecidableEq U] [DecidableEq V] [DecidableEq W]
    (R : ℕ) (a : Fin R → X → K) (b : Fin R → Y → K) (c : Fin R → Z → K)
    (T : Tensor K U V W) :
    Tensor.restrict (supplyMatrix a) (supplyMatrix b) (supplyMatrix c)
      (Tensor.directSum (fun _ : Fin R => T)) =
      Tensor.product (fun x y z => ∑ i, Tensor.rankOne (a i) (b i) (c i) x y z) T := by
  funext xu yv zw
  simp [Tensor.restrict, Tensor.directSum, Tensor.product, Tensor.rankOne, supplyMatrix,
    Fintype.sum_prod_type, ite_and, ite_mul, mul_ite, Finset.sum_mul, Finset.sum_ite_irrel]

/-- A genuine rank-R decomposition gives three actual restriction matrices
from R copies of T to S tensor T. T is retained as an arbitrary resource. -/
theorem relative_restriction
    [Fintype U] [Fintype V] [Fintype W]
    [DecidableEq U] [DecidableEq V] [DecidableEq W]
    (S : Tensor K X Y Z) (T : Tensor K U V W) (R : ℕ)
    (hS : Tensor.RankAtMost S R) :
    ∃ (A : (X × U) → (Fin R × U) → K)
      (B : (Y × V) → (Fin R × V) → K)
      (C : (Z × W) → (Fin R × W) → K),
      Tensor.restrict A B C (Tensor.directSum (fun _ : Fin R => T)) = Tensor.product S T := by
  rcases hS with ⟨a, b, c, hS⟩
  refine ⟨supplyMatrix a, supplyMatrix b, supplyMatrix c, ?_⟩
  rw [restrict_decomposition, ← hS]

/-- Any further restriction can be composed with the supplied three matrices. -/
theorem compose_relative_restriction {X' Y' Z' : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W]
    [DecidableEq U] [DecidableEq V] [DecidableEq W]
    (S : Tensor K X Y Z) (T : Tensor K U V W) (R : ℕ)
    (hS : Tensor.RankAtMost S R)
    (D : X' → (X × U) → K) (E : Y' → (Y × V) → K) (F : Z' → (Z × W) → K) :
    ∃ (A : X' → (Fin R × U) → K) (B : Y' → (Fin R × V) → K)
      (C : Z' → (Fin R × W) → K),
      Tensor.restrict A B C (Tensor.directSum (fun _ : Fin R => T)) =
        Tensor.restrict D E F (Tensor.product S T) := by
  obtain ⟨A, B, C, h⟩ := relative_restriction S T R hS
  refine ⟨Tensor.composeRestrictionMatrix D A, Tensor.composeRestrictionMatrix E B,
    Tensor.composeRestrictionMatrix F C, ?_⟩
  rw [← Tensor.restrict_restrict, h]

/-- An algorithm for the R-copy spectator resource transports without charging
any separate decomposition of the spectator tensor. -/
theorem relative_rank_transport
    [Fintype U] [Fintype V] [Fintype W]
    [DecidableEq U] [DecidableEq V] [DecidableEq W]
    (S : Tensor K X Y Z) (T : Tensor K U V W) (R B : ℕ)
    (hS : Tensor.RankAtMost S R)
    (hT : Tensor.RankAtMost (Tensor.directSum (fun _ : Fin R => T)) B) :
    Tensor.RankAtMost (Tensor.product S T) B := by
  obtain ⟨A, B, C, h⟩ := relative_restriction S T R hS
  rw [← h]
  exact hT.restrict A B C

/-- FullTensor product coordinates agree with the generic relative restriction.
Only the spectator's source coordinate spaces must be finite. -/
theorem full_tensor_restriction (S T : FullTensor ℚ)
    [Fintype T.X] [Fintype T.Y] (R : ℕ) (hS : Tensor.RankAtMost S.tensor R) :
    ∃ (A : (S.product T).X → (Fin R × T.X) → ℚ)
      (B : (S.product T).Y → (Fin R × T.Y) → ℚ)
      (C : (S.product T).Z → (Fin R × T.Z) → ℚ),
      Tensor.restrict A B C (Tensor.directSum (fun _ : Fin R => T.tensor)) =
        (S.product T).tensor := by
  classical
  exact relative_restriction S.tensor T.tensor R hS

local instance matrixFiniteX (D : ℕ) : Fintype (matrixFull D).X := by
  change Fintype (Fin D × Fin D)
  infer_instance

local instance matrixFiniteY (D : ℕ) : Fintype (matrixFull D).Y := by
  change Fintype (Fin D × Fin D)
  infer_instance

/-- The matrix tensor remains the input resource: exactly R copies of T_D
supply S tensor T_D. No D^3 rank charge appears. -/
theorem full_matrix_restriction (S : FullTensor ℚ) (D R : ℕ)
    (hS : Tensor.RankAtMost S.tensor R) :
    ∃ (A : (S.product (matrixFull D)).X → (Fin R × (matrixFull D).X) → ℚ)
      (B : (S.product (matrixFull D)).Y → (Fin R × (matrixFull D).Y) → ℚ)
      (C : (S.product (matrixFull D)).Z → (Fin R × (matrixFull D).Z) → ℚ),
      Tensor.restrict A B C
        (Tensor.directSum (fun _ : Fin R => (matrixFull D).tensor)) =
          (S.product (matrixFull D)).tensor := by
  exact full_tensor_restriction S (matrixFull D) R hS

/-- The spectator-preserving matrix restriction also transports a batch
algorithm at its own cost B, rather than R times a naive matrix rank. -/
theorem full_matrix_rank_transport (S : FullTensor ℚ) (D R B : ℕ)
    (hS : Tensor.RankAtMost S.tensor R)
    (hT : Tensor.RankAtMost
      (Tensor.directSum (fun _ : Fin R => (matrixFull D).tensor)) B) :
    Tensor.RankAtMost (S.product (matrixFull D)).tensor B := by
  obtain ⟨A, B, C, h⟩ := full_matrix_restriction S D R hS
  rw [← h]
  exact hT.restrict A B C

/-- The explicit Lagrange convolution supply directly yields a relative
restriction with an arbitrary retained spectator, without a rank premise. -/
theorem convolution_resource_restriction
    [Fintype U] [Fintype V] [Fintype W]
    [DecidableEq U] [DecidableEq V] [DecidableEq W]
    (r b : ℕ) (T : Tensor ℚ U V W) :
    ∃ (A : (Fin r × U) → (Fin (r + b - 1) × U) → ℚ)
      (B : (Fin b × V) → (Fin (r + b - 1) × V) → ℚ)
      (C : (Fin (r + b - 1) × W) → (Fin (r + b - 1) × W) → ℚ),
      Tensor.restrict A B C (Tensor.directSum (fun _ : Fin (r + b - 1) => T)) =
        Tensor.product (convolution ℚ r b) T :=
  relative_restriction _ T _ (ConvolutionRankSupplyBridge.convolution_rank r b)

#print axioms restrict_decomposition
#print axioms relative_restriction
#print axioms compose_relative_restriction
#print axioms relative_rank_transport
#print axioms full_tensor_restriction
#print axioms full_matrix_restriction
#print axioms full_matrix_rank_transport
#print axioms convolution_resource_restriction

end
end MatrixDimensionAudit.RankSupplyRestrictionBridge
