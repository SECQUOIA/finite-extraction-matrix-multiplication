import formalization.TriplingOrientationBridge

namespace MatrixDimensionAudit.TriplingSectorAlignmentBridge
open OAI.MatrixMultiplication.Foundation
open TensorRankBridge TriplingRestrictionBridge PowerCoordinateBridge TriplingOrientationBridge
open scoped BigOperators

noncomputable section

/-- Match the reference word's middle positions bijectively with the source
word's middle positions. -/
def middleEquiv {n m : Nat} (w v : Word n m) :
    {i : Fin n // v.val i = .middle} ≃ {i : Fin n // w.val i = .middle} :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_subtype, Fintype.card_subtype]
    change middleCount v.val = middleCount w.val
    exact v.property.trans w.property.symm)

/-- Extend the middle-position matching to a permutation of all positions. -/
def positionPermutation {n m : Nat} (w v : Word n m) : Equiv.Perm (Fin n) :=
  (middleEquiv w v).extendSubtype

theorem position_middle_iff {n m : Nat} (w v : Word n m) (i : Fin n) :
    w.val (positionPermutation w v i) = .middle ↔ v.val i = .middle := by
  by_cases hi : v.val i = .middle
  · have h := (middleEquiv w v).extendSubtype_mem i hi
    exact ⟨fun _ => hi, fun _ => h⟩
  · have h := (middleEquiv w v).extendSubtype_not_mem i hi
    exact ⟨fun hw => False.elim (h hw), fun hv => False.elim (hi hv)⟩

theorem yWidth_position (r b : Nat) {n m : Nat} (w v : Word n m) (i : Fin n) :
    yWidth r b (w.val (positionPermutation w v i)) = yWidth r b (v.val i) := by
  have h := position_middle_iff w v i
  cases hw : w.val (positionPermutation w v i) <;> cases hv : v.val i <;>
    simp_all [yWidth]

theorem zWidth_position (r b : Nat) {n m : Nat} (w v : Word n m) (i : Fin n) :
    zWidth r b (w.val (positionPermutation w v i)) = zWidth r b (v.val i) := by
  have h := position_middle_iff w v i
  cases hw : w.val (positionPermutation w v i) <;> cases hv : v.val i <;>
    simp_all [zWidth]

def alignX (r : Nat) {n m : Nat} (w v : Word n m) : (Fin n → Fin r) ≃ (Fin n → Fin r) :=
  Equiv.piCongrLeft' (fun _ => Fin r) (positionPermutation w v).symm

def alignY (r b : Nat) {n m : Nat} (w v : Word n m) : sectorY r b n m w ≃ sectorY r b n m v :=
  (Equiv.piCongrLeft' (fun i => Fin (yWidth r b (w.val i))) (positionPermutation w v).symm).trans
    (Equiv.piCongrRight (fun i => finCongr (yWidth_position r b w v i)))

def alignZ (r b : Nat) {n m : Nat} (w v : Word n m) : sectorZ r b n m w ≃ sectorZ r b n m v :=
  (Equiv.piCongrLeft' (fun i => Fin (zWidth r b (w.val i))) (positionPermutation w v).symm).trans
    (Equiv.piCongrRight (fun i => finCongr (zWidth_position r b w v i)))

variable (F : Type) [Field F]

private theorem orientedBlock_cast (r b : Nat) (s t : Label)
    (h : s = .middle ↔ t = .middle)
    (hy : yWidth r b s = yWidth r b t) (hz : zWidth r b s = zWidth r b t)
    (x : Fin r) (y : Fin (yWidth r b s)) (z : Fin (zWidth r b s)) :
    orientedBlock F r b s x y z =
      orientedBlock F r b t x (Fin.cast hy y) (Fin.cast hz z) := by
  cases s <;> cases t <;> simp_all [orientedBlock, yWidth, zWidth] <;> rfl

/-- Any two retained words with the same middle count give coordinate-isomorphic
normalized sectors. Only the middle flag matters, since both outer blocks agree. -/
theorem sector_alignment (r b n m : Nat) (w v : Word n m) :
    normalizedSector F r b n m w =
      Tensor.pullback (alignX r w v) (alignY r b w v) (alignZ r b w v)
        (normalizedSector F r b n m v) := by
  funext x y z
  change (∏ i, orientedBlock F r b (w.val i) (x i) (y i) (z i)) = _
  calc
    _ = ∏ i, orientedBlock F r b (w.val (positionPermutation w v i))
        (x (positionPermutation w v i)) (y (positionPermutation w v i))
        (z (positionPermutation w v i)) := (Equiv.prod_comp (positionPermutation w v) _).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      exact orientedBlock_cast F r b _ _ (position_middle_iff w v i)
        (yWidth_position r b w v i) (zWidth_position r b w v i) _ _ _

/-- The three sector choices are independent. -/
def mixedSector (r b n m : Nat) (u v w : Word n m) :=
  Tensor.product (Tensor.product (normalizedSector F r b n m u)
    (Tensor.cyclic (normalizedSector F r b n m v)))
    (Tensor.cyclic (Tensor.cyclic (normalizedSector F r b n m w)))

def mixedX (r b n m : Nat) (u v w : Word n m) :=
  Equiv.prodCongr (Equiv.prodCongr (Equiv.refl (Fin n → Fin r)) (alignY r b v u)) (alignZ r b w u)

def mixedY (r b n m : Nat) (u v w : Word n m) :=
  Equiv.prodCongr (Equiv.prodCongr (Equiv.refl (sectorY r b n m u)) (alignZ r b v u)) (alignX r w u)

def mixedZ (r b n m : Nat) (u v w : Word n m) :=
  Equiv.prodCongr (Equiv.prodCongr (Equiv.refl (sectorZ r b n m u)) (alignX r v u)) (alignY r b w u)

theorem mixed_to_reference (r b n m : Nat) (u v w : Word n m) :
    mixedSector F r b n m u v w =
      Tensor.pullback (mixedX r b n m u v w) (mixedY r b n m u v w)
        (mixedZ r b n m u v w) (cyclicTriple F (normalizedSector F r b n m u)) := by
  rw [mixedSector, sector_alignment F r b n m v u, sector_alignment F r b n m w u]
  rfl

/-- All independent triples yield the signed product with m negative factors;
the first word serves only as a reference for matching positions. -/
theorem mixed_signed_product (r b n m : Nat) (hr : 0 < r) (hb : 0 < b) (u v w : Word n m) :
    mixedSector F r b n m u v w = Tensor.pullback
      ((mixedX r b n m u v w).trans (sectorX F r b n m hr hb u))
      ((mixedY r b n m u v w).trans (sectorYEquiv F r b n m hr hb u))
      ((mixedZ r b n m u v w).trans (sectorZEquiv F r b n m hr hb u))
      (signedProduct F r b n m hr hb u) := by
  rw [mixed_to_reference F r b n m u v w, sector_orientation F r b n m hr hb u]
  rfl

/-- At b=r, every independently chosen triple has the same actual S(r,r)^n
tensor, using the rank bridge's nested-pair power coordinates. -/
theorem mixed_square_fullPower (r n m : Nat) (hr : 0 < r) (u v w : Word n m) :
    mixedSector F r r n m u v w = Tensor.pullback
      ((mixedX r r n m u v w).trans (commonFullX F r n m hr u))
      ((mixedY r r n m u v w).trans (commonFullY F r n m hr u))
      ((mixedZ r r n m u v w).trans (commonFullZ F r n m hr u))
      ((cyclicConvolution F r r hr hr).power n).tensor := by
  rw [mixed_to_reference F r r n m u v w, square_sector_fullPower F r n m hr u]
  rfl

/-- The independent choices are indexed by the full cube of the actual word set. -/
theorem all_sector_triples_card (n m : Nat) :
    Fintype.card ((Word n m × Word n m) × Word n m) =
      (n.choose m * 2 ^ (n - m)) ^ 3 := by
  simp only [Fintype.card_prod]
  change (TriplingSectorCountBridge.count n m * TriplingSectorCountBridge.count n m) *
    TriplingSectorCountBridge.count n m = _
  rw [TriplingSectorCountBridge.count_eq_choose]
  ring

namespace Separated
open DependentSeparator

/-- Three independently selected sectors of the actual separator target. -/
def mixedSelected (r b N m aux : Nat) (h₁ h₂ h₃ : Fin (Tripling.blockCount N m))
    (j₁ j₂ j₃ : Fin aux) :=
  Tensor.product (Tensor.product
    (TriplingOrientationBridge.Separated.selectedSector r b N m aux h₁ j₁)
    (Tensor.cyclic (TriplingOrientationBridge.Separated.selectedSector r b N m aux h₂ j₂)))
    (Tensor.cyclic (Tensor.cyclic
      (TriplingOrientationBridge.Separated.selectedSector r b N m aux h₃ j₃)))

theorem mixedSelected_eq_normalized (r b N m aux : Nat)
    (h₁ h₂ h₃ : Fin (Tripling.blockCount N m)) (j₁ j₂ j₃ : Fin aux) :
    mixedSelected r b N m aux h₁ h₂ h₃ j₁ j₂ j₃ =
      mixedSector ℚ r b N m (Tripling.blockWord N m h₁)
        (Tripling.blockWord N m h₂) (Tripling.blockWord N m h₃) := by
  unfold mixedSelected
  rw [TriplingOrientationBridge.Separated.selectedSector_eq_normalized,
    TriplingOrientationBridge.Separated.selectedSector_eq_normalized,
    TriplingOrientationBridge.Separated.selectedSector_eq_normalized]
  rfl

/-- No equality constraint is imposed on h₁,h₂,h₃: every independent triple
has the common square tensor power after the independent first-leg separation. -/
theorem mixedSelected_square_fullPower (r N m aux : Nat) (hr : 0 < r)
    (h₁ h₂ h₃ : Fin (Tripling.blockCount N m)) (j₁ j₂ j₃ : Fin aux) :
    mixedSelected r r N m aux h₁ h₂ h₃ j₁ j₂ j₃ = Tensor.pullback
      ((mixedX r r N m (Tripling.blockWord N m h₁) (Tripling.blockWord N m h₂)
        (Tripling.blockWord N m h₃)).trans (commonFullX ℚ r N m hr (Tripling.blockWord N m h₁)))
      ((mixedY r r N m (Tripling.blockWord N m h₁) (Tripling.blockWord N m h₂)
        (Tripling.blockWord N m h₃)).trans (commonFullY ℚ r N m hr (Tripling.blockWord N m h₁)))
      ((mixedZ r r N m (Tripling.blockWord N m h₁) (Tripling.blockWord N m h₂)
        (Tripling.blockWord N m h₃)).trans (commonFullZ ℚ r N m hr (Tripling.blockWord N m h₁)))
      ((cyclicConvolution ℚ r r hr hr).power N).tensor := by
  rw [mixedSelected_eq_normalized]
  exact mixed_square_fullPower ℚ r N m hr _ _ _

end Separated

end
end MatrixDimensionAudit.TriplingSectorAlignmentBridge

#print axioms MatrixDimensionAudit.TriplingSectorAlignmentBridge.position_middle_iff
#print axioms MatrixDimensionAudit.TriplingSectorAlignmentBridge.sector_alignment
#print axioms MatrixDimensionAudit.TriplingSectorAlignmentBridge.mixed_to_reference
#print axioms MatrixDimensionAudit.TriplingSectorAlignmentBridge.mixed_signed_product
#print axioms MatrixDimensionAudit.TriplingSectorAlignmentBridge.mixed_square_fullPower
#print axioms MatrixDimensionAudit.TriplingSectorAlignmentBridge.all_sector_triples_card
#print axioms MatrixDimensionAudit.TriplingSectorAlignmentBridge.Separated.mixedSelected_eq_normalized
#print axioms MatrixDimensionAudit.TriplingSectorAlignmentBridge.Separated.mixedSelected_square_fullPower
