import formalization.TriplingContextBridge
import formalization.DeterminantCyclicRecipeBridge

namespace MatrixDimensionAudit.TensorResourcePoolingBridge
open OAI.MatrixMultiplication.Foundation
open TensorRankBridge TriplingRestrictionBridge TriplingOddSourceBridge
open scoped BigOperators

noncomputable section

/-- The cubic matrix tensor, including width zero. -/
def matrix (a : Nat) := Tensor.matrixCoefficients (K := ℚ) (Fin a) (Fin a) (Fin a)

/-- The cubic tensor has an explicit identity minor without a positivity premise. -/
def matrixFull (a : Nat) : FullTensor ℚ where
  X := Fin a × Fin a
  Y := Fin a × Fin a
  Z := Fin a × Fin a
  finiteZ := inferInstance
  equalZ := inferInstance
  tensor := matrix a
  left := fun z => (z.2, z.1)
  right := fun z => (z.1, z.1)
  identity := by
    intro i j
    simp only [matrix, Tensor.matrixCoefficients, true_and]
    have he : (i.1 = j.1 ∧ j.2 = i.2) ↔ i = j := by
      simp only [Prod.ext_iff]
      aesop
    simp only [he]

/-- Simultaneously exchange the two middle coordinates of a pair of pairs. -/
def shufflePairs (A B C D : Type) : ((A × B) × (C × D)) ≃ ((A × C) × (B × D)) where
  toFun := fun x => ((x.1.1, x.2.1), (x.1.2, x.2.2))
  invFun := fun x => ((x.1.1, x.2.1), (x.1.2, x.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

def matrixProductCoordinates (a b : Nat) :
    ((Fin a × Fin a) × (Fin b × Fin b)) ≃ (Fin (a * b) × Fin (a * b)) :=
  (shufflePairs _ _ _ _).trans (Equiv.prodCongr finProdFinEquiv finProdFinEquiv)

/-- Matrix-entry coordinates identify T_a tensor T_b with T_(a*b). -/
theorem matrix_product (a b : Nat) :
    Tensor.product (matrix a) (matrix b) =
      Tensor.pullback (matrixProductCoordinates a b) (matrixProductCoordinates a b)
        (matrixProductCoordinates a b) (matrix (a * b)) := by
  funext x y z
  simp only [Tensor.product, matrix, Tensor.matrixCoefficients, Tensor.pullback,
    matrixProductCoordinates, Equiv.trans_apply, Equiv.prodCongr_apply, shufflePairs,
    Equiv.coe_fn_mk]
  split_ifs <;> simp_all

/-- Separate a dependent family of pairs into its two coordinate families. -/
def splitPairs {I : Type} (A B : I → Type) : (∀ i, A i × B i) ≃ ((∀ i, A i) × (∀ i, B i)) where
  toFun := fun x => ((fun i => (x i).1), (fun i => (x i).2))
  invFun := fun x i => (x.1 i, x.2 i)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Equality of matrix-entry indices is preserved by an actual equivalence. -/
theorem matrix_reindex {A B : Type} [DecidableEq A] [DecidableEq B] (e : A ≃ B) :
    Tensor.matrixCoefficients (K := ℚ) A A A =
      Tensor.pullback (Equiv.prodCongr e e) (Equiv.prodCongr e e) (Equiv.prodCongr e e)
        (Tensor.matrixCoefficients B B B) := by
  funext x y z
  simp only [Tensor.matrixCoefficients, Tensor.pullback, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, Equiv.apply_eq_iff_eq]

/-- Products of cubic matrix coefficients are cubic matrix coefficients on the
actual dependent function coordinate type. -/
theorem matrix_family_coefficients {I : Type} [Fintype I] [DecidableEq I] (a : I → Nat)
    (x y z : ∀ i, Fin (a i) × Fin (a i)) :
    (∏ i, matrix (a i) (x i) (y i) (z i)) =
      Tensor.matrixCoefficients (K := ℚ) (∀ i, Fin (a i)) (∀ i, Fin (a i)) (∀ i, Fin (a i))
        (splitPairs _ _ x) (splitPairs _ _ y) (splitPairs _ _ z) := by
  classical
  simp only [matrix, Tensor.matrixCoefficients, splitPairs, Equiv.coe_fn_mk]
  simp only [Fintype.prod_ite_zero, Finset.prod_const_one, funext_iff, forall_and]

def familyIndex {I : Type} [Fintype I] (a : I → Nat) :
    (∀ i, Fin (a i)) ≃ Fin (∏ i, a i) :=
  by
  classical
  exact (Fintype.equivFin _).trans (finCongr (by simp only [Fintype.card_pi, Fintype.card_fin]))

def matrixFamilyCoordinates {I : Type} [Fintype I] (a : I → Nat) :
    (∀ i, Fin (a i) × Fin (a i)) ≃ (Fin (∏ i, a i) × Fin (∏ i, a i)) :=
  (splitPairs _ _).trans (Equiv.prodCongr (familyIndex a) (familyIndex a))

theorem matrix_family {I : Type} [Fintype I] [DecidableEq I] (a : I → Nat)
    (x y z : ∀ i, Fin (a i) × Fin (a i)) :
    (∏ i, matrix (a i) (x i) (y i) (z i)) =
      matrix (∏ i, a i) (matrixFamilyCoordinates a x) (matrixFamilyCoordinates a y)
        (matrixFamilyCoordinates a z) := by
  rw [matrix_family_coefficients]
  exact congrFun (congrFun (congrFun (matrix_reindex (familyIndex a)) (splitPairs _ _ x))
    (splitPairs _ _ y)) (splitPairs _ _ z)

/-- An explicit base-a index for each word, including the empty word and a=0. -/
def wordIndex (a : Nat) : (k : Nat) → (Fin k → Fin a) ≃ Fin (a ^ k)
  | 0 => {
      toFun := fun _ => 0
      invFun := fun _ i => Fin.elim0 i
      left_inv := by intro x; funext i; exact Fin.elim0 i
      right_inv := by intro x; apply Fin.ext; exact (Fin.val_eq_zero x).symm }
  | k + 1 =>
      ((PowerCoordinateBridge.consCoordinates (Equiv.refl (Fin k → Fin a))).symm.trans
        (Equiv.prodCongr (Equiv.refl (Fin a)) (wordIndex a k))).trans
        (finProdFinEquiv.trans (finCongr (by rw [pow_succ'])))

def matrixPowerCoordinates (a k : Nat) :
    (Fin k → Fin a × Fin a) ≃ (Fin (a ^ k) × Fin (a ^ k)) :=
  (splitPairs _ _).trans (Equiv.prodCongr (wordIndex a k) (wordIndex a k))

theorem matrix_power (a k : Nat) :
    Tensor.power (matrix a) k = Tensor.pullback (matrixPowerCoordinates a k)
      (matrixPowerCoordinates a k) (matrixPowerCoordinates a k) (matrix (a ^ k)) := by
  funext x y z
  change (∏ i, matrix a (x i) (y i) (z i)) = _
  rw [matrix_family_coefficients (fun _ : Fin k => a)]
  exact congrFun (congrFun (congrFun (matrix_reindex (wordIndex a k)) (splitPairs _ _ x))
    (splitPairs _ _ y)) (splitPairs _ _ z)

def matrixNestedX (a k : Nat) :=
  (PowerCoordinateBridge.xCoordinates ℚ (matrixFull a) k).trans (matrixPowerCoordinates a k)
def matrixNestedY (a k : Nat) :=
  (PowerCoordinateBridge.yCoordinates ℚ (matrixFull a) k).trans (matrixPowerCoordinates a k)
def matrixNestedZ (a k : Nat) :=
  (PowerCoordinateBridge.zCoordinates ℚ (matrixFull a) k).trans (matrixPowerCoordinates a k)

theorem matrix_nested_power (a k : Nat) :
    ((matrixFull a).power k).tensor = Tensor.pullback (matrixNestedX a k)
      (matrixNestedY a k) (matrixNestedZ a k) (matrix (a ^ k)) := by
  funext x y z
  rw [PowerCoordinateBridge.power_tensor_identity]
  exact congrFun (congrFun (congrFun (matrix_power a k)
    (PowerCoordinateBridge.xCoordinates ℚ (matrixFull a) k x))
    (PowerCoordinateBridge.yCoordinates ℚ (matrixFull a) k y))
    (PowerCoordinateBridge.zCoordinates ℚ (matrixFull a) k z)

/-- Entry transposition on all three legs restores the cubic matrix tensor. -/
theorem matrix_transpose (a : Nat) :
    transposeInputs ℚ (matrix a) =
      Tensor.pullback (Equiv.prodComm _ _) (Equiv.prodComm _ _) (Equiv.prodComm _ _) (matrix a) := by
  funext x y z
  change (if y.2 = x.1 ∧ x.2 = z.1 ∧ z.2 = y.1 then (1 : ℚ) else 0) =
    if x.1 = y.2 ∧ y.1 = z.2 ∧ z.1 = x.2 then 1 else 0
  congr 1
  aesop

def matrixTransposePowerCoordinates (a k : Nat) :=
  (matrixPowerCoordinates a k).trans (Equiv.prodComm _ _)

theorem matrix_transpose_power (a k : Nat) :
    transposeInputs ℚ (Tensor.power (matrix a) k) =
      Tensor.pullback (matrixTransposePowerCoordinates a k) (matrixTransposePowerCoordinates a k)
        (matrixTransposePowerCoordinates a k) (matrix (a ^ k)) := by
  funext x y z
  have hp := congrFun (congrFun (congrFun (matrix_power a k) y) x) z
  have ht := congrFun (congrFun (congrFun (matrix_transpose (a ^ k))
    (matrixPowerCoordinates a k x)) (matrixPowerCoordinates a k y)) (matrixPowerCoordinates a k z)
  exact hp.trans ht

/-- Coordinate changes carry actual rank certificates in both directions. -/
theorem coordinate_rank_iff {X Y Z X' Y' Z' : Type}
    (T : Tensor ℚ X Y Z) (U : Tensor ℚ X' Y' Z')
    (ex : X ≃ X') (ey : Y ≃ Y') (ez : Z ≃ Z')
    (he : T = Tensor.pullback ex ey ez U) (R : Nat) :
    Tensor.RankAtMost T R ↔ Tensor.RankAtMost U R := by
  constructor
  · intro h
    have hi : U = Tensor.pullback ex.symm ey.symm ez.symm T := by
      rw [he]
      funext x y z
      simp only [Tensor.pullback, Equiv.apply_symm_apply]
    rw [hi]
    exact h.pullback _ _ _
  · intro h
    rw [he]
    exact h.pullback _ _ _

/-- Pool an auxiliary power inside a local block and an unchanged spectator. -/
def poolAuxiliary {X U : Type} (a k : Nat) :
    ((X × (Fin k → Fin a × Fin a)) × U) ≃ ((X × (Fin (a ^ k) × Fin (a ^ k))) × U) :=
  Equiv.prodCongr (Equiv.prodCongr (Equiv.refl X) (matrixPowerCoordinates a k)) (Equiv.refl U)

def poolOddAuxiliary {X U : Type} (a k : Nat) :
    ((X × (Fin k → Fin a × Fin a)) × U) ≃ ((X × (Fin (a ^ k) × Fin (a ^ k))) × U) :=
  Equiv.prodCongr (Equiv.prodCongr (Equiv.refl X) (matrixTransposePowerCoordinates a k)) (Equiv.refl U)

theorem odd_output_pool {X Y Z U V W : Type} (T : Tensor ℚ X Y Z) (S : Tensor ℚ U V W)
    (a k : Nat) :
    Tensor.product (transposeInputs ℚ (Tensor.product T (Tensor.power (matrix a) k))) S =
      Tensor.pullback (poolOddAuxiliary a k) (poolOddAuxiliary a k) (poolOddAuxiliary a k)
        (Tensor.product (Tensor.product (transposeInputs ℚ T) (matrix (a ^ k))) S) := by
  rw [TriplingContextBridge.transpose_product, matrix_transpose_power]
  rfl

theorem odd_output_pool_rank {X Y Z U V W : Type} (T : Tensor ℚ X Y Z) (S : Tensor ℚ U V W)
    (a k R : Nat)
    (h : Tensor.RankAtMost
      (Tensor.product (transposeInputs ℚ (Tensor.product T (Tensor.power (matrix a) k))) S) R) :
    Tensor.RankAtMost (Tensor.product (Tensor.product (transposeInputs ℚ T) (matrix (a ^ k))) S) R :=
  (coordinate_rank_iff _ _ _ _ _ (odd_output_pool T S a k) R).mp h

theorem positive_output_pool {X Y Z U V W : Type} (T : Tensor ℚ X Y Z) (S : Tensor ℚ U V W)
    (a k : Nat) :
    Tensor.product (Tensor.product T (Tensor.power (matrix a) k)) S =
      Tensor.pullback (poolAuxiliary a k) (poolAuxiliary a k) (poolAuxiliary a k)
        (Tensor.product (Tensor.product T (matrix (a ^ k))) S) := by
  rw [matrix_power]
  rfl

theorem positive_output_pool_rank {X Y Z U V W : Type} (T : Tensor ℚ X Y Z) (S : Tensor ℚ U V W)
    (a k R : Nat)
    (h : Tensor.RankAtMost (Tensor.product (Tensor.product T (Tensor.power (matrix a) k)) S) R) :
    Tensor.RankAtMost (Tensor.product (Tensor.product T (matrix (a ^ k))) S) R :=
  (coordinate_rank_iff _ _ _ _ _ (positive_output_pool T S a k) R).mp h

/-- These maps change the named signed resource after a whole-leg transpose.
They do not identify the two untransposed signs by maps on fixed legs. -/
def signedTransposeX (negative : Bool) (r b : Nat) (hr : 0 < r) (hb : 0 < b) :
    (signedCyclicConvolution ℚ negative r b hr hb).Y ≃
      (signedCyclicConvolution ℚ (!negative) r b hr hb).X :=
  match negative with
  | false => (oddX r b hr hb).symm
  | true => oddY r b hr hb

def signedTransposeY (negative : Bool) (r b : Nat) (hr : 0 < r) (hb : 0 < b) :
    (signedCyclicConvolution ℚ negative r b hr hb).X ≃
      (signedCyclicConvolution ℚ (!negative) r b hr hb).Y :=
  match negative with
  | false => (oddY r b hr hb).symm
  | true => oddX r b hr hb

def signedTransposeZ (negative : Bool) (r b : Nat) (hr : 0 < r) (hb : 0 < b) :
    (signedCyclicConvolution ℚ negative r b hr hb).Z ≃
      (signedCyclicConvolution ℚ (!negative) r b hr hb).Z :=
  match negative with
  | false => (oddZ r b hr hb).symm
  | true => oddZ r b hr hb

theorem signed_transpose (negative : Bool) (r b : Nat) (hr : 0 < r) (hb : 0 < b) :
    transposeInputs ℚ (signedCyclicConvolution ℚ negative r b hr hb).tensor =
      Tensor.pullback (signedTransposeX negative r b hr hb) (signedTransposeY negative r b hr hb)
        (signedTransposeZ negative r b hr hb) (signedCyclicConvolution ℚ (!negative) r b hr hb).tensor := by
  cases negative with
  | false =>
      change transposeInputs ℚ (cyclicConvolution ℚ r b hr hb).tensor =
        Tensor.pullback (oddX r b hr hb).symm (oddY r b hr hb).symm (oddZ r b hr hb).symm
          (cyclicConvolution ℚ b r hb hr).tensor
      funext x y z
      have ht := congrFun (congrFun (congrFun (odd_tensor_identity r b hr hb)
        ((oddX r b hr hb).symm x)) ((oddY r b hr hb).symm y)) ((oddZ r b hr hb).symm z)
      change (cyclicConvolution ℚ b r hb hr).tensor _ _ _ =
        transposeInputs ℚ (cyclicConvolution ℚ r b hr hb).tensor
          ((oddX r b hr hb) ((oddX r b hr hb).symm x))
          ((oddY r b hr hb) ((oddY r b hr hb).symm y))
          ((oddZ r b hr hb) ((oddZ r b hr hb).symm z)) at ht
      rw [(oddX r b hr hb).apply_symm_apply, (oddY r b hr hb).apply_symm_apply,
        (oddZ r b hr hb).apply_symm_apply] at ht
      exact ht.symm
  | true =>
      funext x y z
      exact congrFun (congrFun (congrFun (odd_tensor_identity r b hr hb) y) x) z

def splitTransposeX (negative : Bool) (r : Nat) (hr : 2 ≤ r) (x : Nat) :=
  signedTransposeX negative r (r - 1 + x) (by omega) (by omega)
def splitTransposeY (negative : Bool) (r : Nat) (hr : 2 ≤ r) (x : Nat) :=
  signedTransposeY negative r (r - 1 + x) (by omega) (by omega)
def splitTransposeZ (negative : Bool) (r : Nat) (hr : 2 ≤ r) (x : Nat) :=
  signedTransposeZ negative r (r - 1 + x) (by omega) (by omega)

theorem splitFactor_transpose (negative : Bool) (r : Nat) (hr : 2 ≤ r) (x : Nat) :
    transposeInputs ℚ (splitFactor ℚ negative r hr x).tensor =
      Tensor.pullback (splitTransposeX negative r hr x) (splitTransposeY negative r hr x)
        (splitTransposeZ negative r hr x) (splitFactor ℚ (!negative) r hr x).tensor :=
  signed_transpose negative r (r - 1 + x) (by omega) (by omega)

def resetTransposeX (negative : Bool) (r : Nat) (hr : 2 ≤ r) :=
  signedTransposeX negative r (4 * r - 1) (by omega) (by omega)
def resetTransposeY (negative : Bool) (r : Nat) (hr : 2 ≤ r) :=
  signedTransposeY negative r (4 * r - 1) (by omega) (by omega)
def resetTransposeZ (negative : Bool) (r : Nat) (hr : 2 ≤ r) :=
  signedTransposeZ negative r (4 * r - 1) (by omega) (by omega)

theorem resetFactor_transpose (negative : Bool) (r : Nat) (hr : 2 ≤ r) :
    transposeInputs ℚ (resetFactor ℚ negative r hr).tensor =
      Tensor.pullback (resetTransposeX negative r hr) (resetTransposeY negative r hr)
        (resetTransposeZ negative r hr) (resetFactor ℚ (!negative) r hr).tensor :=
  signed_transpose negative r (4 * r - 1) (by omega) (by omega)

/-- A finite family of named full tensors, with actual dependent coordinates. -/
def resourceFamily {I : Type} [Fintype I] (A : I → FullTensor ℚ) : FullTensor ℚ := by
  classical
  exact {
    X := ∀ i, (A i).X
    Y := ∀ i, (A i).Y
    Z := ∀ i, (A i).Z
    finiteZ := inferInstance
    equalZ := inferInstance
    tensor := fun x y z => ∏ i, (A i).tensor (x i) (y i) (z i)
    left := fun z i => (A i).left (z i)
    right := fun z i => (A i).right (z i)
    identity := by
      intro x y
      simp only [FullTensor.identity, Fintype.prod_ite_zero, Finset.prod_const_one, ← funext_iff] }

def zipThree {I : Type} (X Y Z : I → Type) :
    (((∀ i, X i) × (∀ i, Y i)) × (∀ i, Z i)) ≃ (∀ i, (X i × Y i) × Z i) where
  toFun := fun x i => ((x.1.1 i, x.1.2 i), x.2 i)
  invFun := fun x => ((fun i => (x i).1.1, fun i => (x i).1.2), fun i => (x i).2)
  left_inv _ := rfl
  right_inv _ := rfl

open DeterminantSplitRecipeBridge in
def splitChildResources (negative : Bool) (r c h : Nat) (hr : 0 < r) (hc : h + 1 ≤ c)
    (counts : Fin (h + 1) → Nat) : FullTensor ℚ :=
  resourceFamily (fun p : GroupedPosition counts => signedCyclicConvolution ℚ negative r
    (c + h - 2 * p.1.val) hr (by have := p.1.isLt; omega))

open DeterminantSplitRecipeBridge DeterminantCyclicRecipeBridge in
def childPositiveX (r c h : Nat) (hr : 0 < r) (hc : h + 1 ≤ c) (counts : Fin (h + 1) → Nat) :
    ChildX r c h counts ≃ (splitChildResources false r c h hr hc counts).X :=
  zipThree _ _ _
open DeterminantSplitRecipeBridge DeterminantCyclicRecipeBridge in
def childPositiveY (r c h : Nat) (hr : 0 < r) (hc : h + 1 ≤ c) (counts : Fin (h + 1) → Nat) :
    ChildY r c h counts ≃ (splitChildResources false r c h hr hc counts).Y :=
  zipThree _ _ _
open DeterminantSplitRecipeBridge DeterminantCyclicRecipeBridge in
def childPositiveZ (r c h : Nat) (hr : 0 < r) (hc : h + 1 ≤ c) (counts : Fin (h + 1) → Nat) :
    ChildZ r c h counts ≃ (splitChildResources false r c h hr hc counts).Z :=
  zipThree _ _ _

open DeterminantSplitRecipeBridge DeterminantCyclicRecipeBridge in
theorem cyclic_child_resources (r c h : Nat) (hr : 0 < r) (hc : h + 1 ≤ c)
    (counts : Fin (h + 1) → Nat) :
    cyclicChild r c h counts = Tensor.pullback (childPositiveX r c h hr hc counts)
      (childPositiveY r c h hr hc counts) (childPositiveZ r c h hr hc counts)
      (splitChildResources false r c h hr hc counts).tensor := by
  funext x y z
  rw [cyclicChild_symmetrized_depth_product r c h hr hc counts]
  change (∏ j, ∏ i : Fin (counts j), _) = ∏ p : (j : Fin (h + 1)) × Fin (counts j), _
  rw [Fintype.prod_sigma]
  rfl

open DeterminantSplitRecipeBridge DeterminantCyclicRecipeBridge in
def childNegativeX (r c h : Nat) (hr : 0 < r) (hc : h + 1 ≤ c) (counts : Fin (h + 1) → Nat) :
    ChildY r c h counts ≃ (splitChildResources true r c h hr hc counts).X :=
  (childPositiveY r c h hr hc counts).trans
    (Equiv.piCongrRight (fun p : GroupedPosition counts =>
      signedTransposeX false r (c + h - 2 * p.1.val) hr (by have := p.1.isLt; omega)))
open DeterminantSplitRecipeBridge DeterminantCyclicRecipeBridge in
def childNegativeY (r c h : Nat) (hr : 0 < r) (hc : h + 1 ≤ c) (counts : Fin (h + 1) → Nat) :
    ChildX r c h counts ≃ (splitChildResources true r c h hr hc counts).Y :=
  (childPositiveX r c h hr hc counts).trans
    (Equiv.piCongrRight (fun p : GroupedPosition counts =>
      signedTransposeY false r (c + h - 2 * p.1.val) hr (by have := p.1.isLt; omega)))
open DeterminantSplitRecipeBridge DeterminantCyclicRecipeBridge in
def childNegativeZ (r c h : Nat) (hr : 0 < r) (hc : h + 1 ≤ c) (counts : Fin (h + 1) → Nat) :
    ChildZ r c h counts ≃ (splitChildResources true r c h hr hc counts).Z :=
  (childPositiveZ r c h hr hc counts).trans
    (Equiv.piCongrRight (fun p : GroupedPosition counts =>
      signedTransposeZ false r (c + h - 2 * p.1.val) hr (by have := p.1.isLt; omega)))

open DeterminantSplitRecipeBridge DeterminantCyclicRecipeBridge in
theorem transposed_cyclic_child_resources (r c h : Nat) (hr : 0 < r) (hc : h + 1 ≤ c)
    (counts : Fin (h + 1) → Nat) :
    transposeInputs ℚ (cyclicChild r c h counts) =
      Tensor.pullback (childNegativeX r c h hr hc counts) (childNegativeY r c h hr hc counts)
        (childNegativeZ r c h hr hc counts) (splitChildResources true r c h hr hc counts).tensor := by
  funext x y z
  have hp := congrFun (congrFun (congrFun (cyclic_child_resources r c h hr hc counts) y) x) z
  change transposeInputs ℚ (cyclicChild r c h counts) x y z = _ at hp
  rw [hp]
  change (∏ p : GroupedPosition counts,
      transposeInputs ℚ (signedCyclicConvolution ℚ false r (c + h - 2 * p.1.val) hr
        (by have := p.1.isLt; omega)).tensor
        (childPositiveY r c h hr hc counts x p) (childPositiveX r c h hr hc counts y p)
        (childPositiveZ r c h hr hc counts z p)) = _
  apply Finset.prod_congr rfl
  intro p _
  exact congrFun (congrFun (congrFun
    (signed_transpose false r (c + h - 2 * p.1.val) hr (by have := p.1.isLt; omega))
    (childPositiveY r c h hr hc counts x p)) (childPositiveX r c h hr hc counts y p))
    (childPositiveZ r c h hr hc counts z p)

theorem matrix_resource_family {I : Type} [Fintype I] [DecidableEq I] (a : I → Nat) :
    (resourceFamily (fun i => matrixFull (a i))).tensor =
      Tensor.pullback (matrixFamilyCoordinates a) (matrixFamilyCoordinates a)
        (matrixFamilyCoordinates a) (matrix (∏ i, a i)) := by
  funext x y z
  exact matrix_family a x y z

/-- State one is the existing external source tensor, for either square sign. -/
theorem splitFactor_one (negative : Bool) (r : Nat) (hr : 2 ≤ r) :
    splitFactor ℚ negative r hr 1 = sourceFactor ℚ r hr := by
  have hw : r - 1 + 1 = r := by omega
  unfold splitFactor signedCyclicConvolution sourceFactor
  simp only [hw]
  cases negative <;> rfl

/-- State 3r is exactly the existing signed reset tensor. -/
theorem splitFactor_reset (negative : Bool) (r : Nat) (hr : 2 ≤ r) :
    splitFactor ℚ negative r hr (3 * r) = resetFactor ℚ negative r hr := by
  have hw : r - 1 + 3 * r = 4 * r - 1 := by omega
  unfold splitFactor resetFactor
  simp only [hw]

/-- At ledger state x, the child width is exactly the named split resource at
state x+h-2j. The range hypothesis prevents truncated subtraction. -/
theorem split_child_named_factor (negative : Bool) (r x h : Nat) (hr : 2 ≤ r)
    (hhx : h ≤ x) (j : Fin (h + 1)) :
    signedCyclicConvolution ℚ negative r (r - 1 + x + h - 2 * j.val) (by omega)
      (by have := j.isLt; omega) = splitFactor ℚ negative r hr (x + h - 2 * j.val) := by
  have hw : r - 1 + x + h - 2 * j.val = r - 1 + (x + h - 2 * j.val) := by
    have := j.isLt
    omega
  unfold splitFactor
  simp only [hw]

end
end MatrixDimensionAudit.TensorResourcePoolingBridge

#print axioms MatrixDimensionAudit.TensorResourcePoolingBridge.matrix
#print axioms MatrixDimensionAudit.TensorResourcePoolingBridge.matrixFull
#print axioms MatrixDimensionAudit.TensorResourcePoolingBridge.shufflePairs
#print axioms MatrixDimensionAudit.TensorResourcePoolingBridge.matrixProductCoordinates
#print axioms MatrixDimensionAudit.TensorResourcePoolingBridge.matrix_product
#print axioms MatrixDimensionAudit.TensorResourcePoolingBridge.splitPairs
#print axioms MatrixDimensionAudit.TensorResourcePoolingBridge.matrix_reindex
#print axioms MatrixDimensionAudit.TensorResourcePoolingBridge.matrix_family_coefficients
#print axioms MatrixDimensionAudit.TensorResourcePoolingBridge.familyIndex
#print axioms MatrixDimensionAudit.TensorResourcePoolingBridge.matrixFamilyCoordinates
#print axioms MatrixDimensionAudit.TensorResourcePoolingBridge.matrix_family
#print axioms MatrixDimensionAudit.TensorResourcePoolingBridge.wordIndex
#print axioms MatrixDimensionAudit.TensorResourcePoolingBridge.matrixPowerCoordinates
#print axioms MatrixDimensionAudit.TensorResourcePoolingBridge.matrix_power
#print axioms MatrixDimensionAudit.TensorResourcePoolingBridge.matrixNestedX
#print axioms MatrixDimensionAudit.TensorResourcePoolingBridge.matrixNestedY
#print axioms MatrixDimensionAudit.TensorResourcePoolingBridge.matrixNestedZ
#print axioms MatrixDimensionAudit.TensorResourcePoolingBridge.matrix_nested_power
#print axioms MatrixDimensionAudit.TensorResourcePoolingBridge.matrix_transpose
#print axioms MatrixDimensionAudit.TensorResourcePoolingBridge.matrixTransposePowerCoordinates
#print axioms MatrixDimensionAudit.TensorResourcePoolingBridge.matrix_transpose_power
#print axioms MatrixDimensionAudit.TensorResourcePoolingBridge.coordinate_rank_iff
#print axioms MatrixDimensionAudit.TensorResourcePoolingBridge.poolAuxiliary
#print axioms MatrixDimensionAudit.TensorResourcePoolingBridge.poolOddAuxiliary
#print axioms MatrixDimensionAudit.TensorResourcePoolingBridge.odd_output_pool
#print axioms MatrixDimensionAudit.TensorResourcePoolingBridge.odd_output_pool_rank
#print axioms MatrixDimensionAudit.TensorResourcePoolingBridge.positive_output_pool
#print axioms MatrixDimensionAudit.TensorResourcePoolingBridge.positive_output_pool_rank
#print axioms MatrixDimensionAudit.TensorResourcePoolingBridge.signedTransposeX
#print axioms MatrixDimensionAudit.TensorResourcePoolingBridge.signedTransposeY
#print axioms MatrixDimensionAudit.TensorResourcePoolingBridge.signedTransposeZ
#print axioms MatrixDimensionAudit.TensorResourcePoolingBridge.signed_transpose
#print axioms MatrixDimensionAudit.TensorResourcePoolingBridge.splitTransposeX
#print axioms MatrixDimensionAudit.TensorResourcePoolingBridge.splitTransposeY
#print axioms MatrixDimensionAudit.TensorResourcePoolingBridge.splitTransposeZ
#print axioms MatrixDimensionAudit.TensorResourcePoolingBridge.splitFactor_transpose
#print axioms MatrixDimensionAudit.TensorResourcePoolingBridge.resetTransposeX
#print axioms MatrixDimensionAudit.TensorResourcePoolingBridge.resetTransposeY
#print axioms MatrixDimensionAudit.TensorResourcePoolingBridge.resetTransposeZ
#print axioms MatrixDimensionAudit.TensorResourcePoolingBridge.resetFactor_transpose
#print axioms MatrixDimensionAudit.TensorResourcePoolingBridge.resourceFamily
#print axioms MatrixDimensionAudit.TensorResourcePoolingBridge.zipThree
#print axioms MatrixDimensionAudit.TensorResourcePoolingBridge.splitChildResources
#print axioms MatrixDimensionAudit.TensorResourcePoolingBridge.childPositiveX
#print axioms MatrixDimensionAudit.TensorResourcePoolingBridge.childPositiveY
#print axioms MatrixDimensionAudit.TensorResourcePoolingBridge.childPositiveZ
#print axioms MatrixDimensionAudit.TensorResourcePoolingBridge.cyclic_child_resources
#print axioms MatrixDimensionAudit.TensorResourcePoolingBridge.childNegativeX
#print axioms MatrixDimensionAudit.TensorResourcePoolingBridge.childNegativeY
#print axioms MatrixDimensionAudit.TensorResourcePoolingBridge.childNegativeZ
#print axioms MatrixDimensionAudit.TensorResourcePoolingBridge.transposed_cyclic_child_resources
#print axioms MatrixDimensionAudit.TensorResourcePoolingBridge.matrix_resource_family
#print axioms MatrixDimensionAudit.TensorResourcePoolingBridge.splitFactor_one
#print axioms MatrixDimensionAudit.TensorResourcePoolingBridge.splitFactor_reset
#print axioms MatrixDimensionAudit.TensorResourcePoolingBridge.split_child_named_factor
