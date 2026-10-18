import formalization.TriplingSectorCountBridge
import formalization.DependentSeparatorBridge

namespace MatrixDimensionAudit.TriplingOrientationBridge
open OAI.MatrixMultiplication.Foundation
open TensorRankBridge TriplingRestrictionBridge PowerCoordinateBridge
open scoped BigOperators

noncomputable section
variable (F : Type) [Field F]

def negative : Label → Bool
  | .middle => true
  | .left | .right => false

def factor (r b : Nat) (hr : 0 < r) (hb : 0 < b) (s : Label) : FullTensor F :=
  signedCyclicConvolution F (negative s) r b hr hb

theorem negative_count (n m : Nat) (w : Word n m) :
    (Finset.univ.filter (fun i => negative (w.val i) = true)).card = m := by
  have h : Finset.univ.filter (fun i => negative (w.val i) = true) = middlePositions w.val := by
    ext i
    simp only [middlePositions, Finset.mem_filter, Finset.mem_univ, true_and]
    cases w.val i <;> simp [negative]
  rw [h]
  exact w.property

theorem positive_count (n m : Nat) (w : Word n m) :
    (Finset.univ.filter (fun i => negative (w.val i) = false)).card = n - m := by
  have h : Finset.univ.filter (fun i => negative (w.val i) = false) =
      (Finset.univ.filter (fun i => negative (w.val i) = true))ᶜ := by
    ext i
    simp only [Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and]
    cases w.val i <;> simp [negative]
  rw [h, Finset.card_compl, negative_count]
  simp

/-- Rotate the three factor coordinates inside a tensor-product leg. -/
def rotateCoordinates (X Y Z : Type) : ((X × Y) × Z) ≃ ((Z × X) × Y) where
  toFun := fun x => ((x.2, x.1.1), x.1.2)
  invFun := fun x => ((x.1.2, x.2), x.1.1)
  left_inv _ := rfl
  right_inv _ := rfl

def outputSwap (r b : Nat) : Fin (r + b - 1) ≃ Fin (b + r - 1) :=
  finCongr (by omega)

def factorX (r b : Nat) (hr : 0 < r) (hb : 0 < b) : (s : Label) →
    ((Fin r × Fin (yWidth r b s)) × Fin (zWidth r b s)) ≃ (factor F r b hr hb s).X
  | .left | .right => Equiv.refl _
  | .middle => (rotateCoordinates _ _ _).trans
      (Equiv.prodCongr (Equiv.refl _) (outputSwap r b))

def factorY (r b : Nat) (hr : 0 < r) (hb : 0 < b) : (s : Label) →
    ((Fin (yWidth r b s) × Fin (zWidth r b s)) × Fin r) ≃ (factor F r b hr hb s).Y
  | .left | .right => Equiv.refl _
  | .middle => (rotateCoordinates _ _ _).trans
      (Equiv.prodCongr (Equiv.prodCongr (Equiv.refl _) (outputSwap r b)) (Equiv.refl _))

def factorZ (r b : Nat) (hr : 0 < r) (hb : 0 < b) : (s : Label) →
    ((Fin (zWidth r b s) × Fin r) × Fin (yWidth r b s)) ≃ (factor F r b hr hb s).Z
  | .left | .right => Equiv.refl _
  | .middle => (rotateCoordinates _ _ _).trans
      (Equiv.prodCongr (Equiv.prodCongr (outputSwap r b) (Equiv.refl _)) (Equiv.refl _))

/-- Outer blocks give S+; the exchanged middle block gives S- after explicit
factor-coordinate permutations and the convolution input-transpose identity. -/
theorem factor_orientation (r b : Nat) (hr : 0 < r) (hb : 0 < b) (s : Label) :
    cyclicTriple F (orientedBlock F r b s) =
      Tensor.pullback (factorX F r b hr hb s) (factorY F r b hr hb s)
        (factorZ F r b hr hb s) (factor F r b hr hb s).tensor := by
  funext x y z
  cases s with
  | left => rfl
  | right => rfl
  | middle =>
      change ((if x.1.1.val + z.1.1.val = y.1.1.val then (1 : F) else 0) *
        (if z.1.2.val + y.1.2.val = x.1.2.val then 1 else 0)) *
        (if y.2.val + x.2.val = z.2.val then 1 else 0) =
        ((if x.2.val + y.2.val = z.2.val then 1 else 0) *
          (if z.1.1.val + x.1.1.val = y.1.1.val then 1 else 0)) *
          (if y.1.2.val + z.1.2.val = x.1.2.val then 1 else 0)
      have ha : (if z.1.1.val + x.1.1.val = y.1.1.val then (1 : F) else 0) =
          (if x.1.1.val + z.1.1.val = y.1.1.val then 1 else 0) :=
        congrArg (fun t => if t = y.1.1.val then (1 : F) else 0) (Nat.add_comm _ _)
      have hb' : (if y.1.2.val + z.1.2.val = x.1.2.val then (1 : F) else 0) =
          (if z.1.2.val + y.1.2.val = x.1.2.val then 1 else 0) :=
        congrArg (fun t => if t = x.1.2.val then (1 : F) else 0) (Nat.add_comm _ _)
      have hc : (if x.2.val + y.2.val = z.2.val then (1 : F) else 0) =
          (if y.2.val + x.2.val = z.2.val then 1 else 0) :=
        congrArg (fun t => if t = z.2.val then (1 : F) else 0) (Nat.add_comm _ _)
      rw [ha, hb', hc]
      exact (mul_comm _ _).trans (mul_assoc _ _ _).symm

/-- Zip three function coordinates into a function of triples. The coordinate
types may depend on the position. -/
def zipCoordinates {n : Nat} (X Y Z : Fin n → Type) :
    (((∀ i, X i) × (∀ i, Y i)) × (∀ i, Z i)) ≃ (∀ i, (X i × Y i) × Z i) where
  toFun := fun x i => ((x.1.1 i, x.1.2 i), x.2 i)
  invFun := fun x => ((fun i => (x i).1.1, fun i => (x i).1.2), fun i => (x i).2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- This tensor is a standalone sector, after its first leg has been separated. -/
def normalizedSector (r b n m : Nat) (w : Word n m) :
    Tensor F (Fin n → Fin r) (sectorY r b n m w) (sectorZ r b n m w) :=
  fun x y z => ∏ i, orientedBlock F r b (w.val i) (x i) (y i) (z i)

def signedProduct (r b n m : Nat) (hr : 0 < r) (hb : 0 < b) (w : Word n m) :
    Tensor F ((i : Fin n) → (factor F r b hr hb (w.val i)).X)
      ((i : Fin n) → (factor F r b hr hb (w.val i)).Y)
      ((i : Fin n) → (factor F r b hr hb (w.val i)).Z) :=
  fun x y z => ∏ i, (factor F r b hr hb (w.val i)).tensor (x i) (y i) (z i)

def sectorX (r b n m : Nat) (hr : 0 < r) (hb : 0 < b) (w : Word n m) :=
  (zipCoordinates (fun _ : Fin n => Fin r) (fun i => Fin (yWidth r b (w.val i)))
    (fun i => Fin (zWidth r b (w.val i)))).trans
    (Equiv.piCongrRight (fun i => factorX F r b hr hb (w.val i)))

def sectorYEquiv (r b n m : Nat) (hr : 0 < r) (hb : 0 < b) (w : Word n m) :=
  (zipCoordinates (fun i : Fin n => Fin (yWidth r b (w.val i)))
    (fun i => Fin (zWidth r b (w.val i))) (fun _ => Fin r)).trans
    (Equiv.piCongrRight (fun i => factorY F r b hr hb (w.val i)))

def sectorZEquiv (r b n m : Nat) (hr : 0 < r) (hb : 0 < b) (w : Word n m) :=
  (zipCoordinates (fun i : Fin n => Fin (zWidth r b (w.val i)))
    (fun _ => Fin r) (fun i => Fin (yWidth r b (w.val i)))).trans
    (Equiv.piCongrRight (fun i => factorZ F r b hr hb (w.val i)))

/-- The cyclic triple of a selected sector is a product of the signed cyclic
convolution tensors, with negative sign exactly at its middle positions. -/
theorem sector_orientation (r b n m : Nat) (hr : 0 < r) (hb : 0 < b) (w : Word n m) :
    cyclicTriple F (normalizedSector F r b n m w) =
      Tensor.pullback (sectorX F r b n m hr hb w) (sectorYEquiv F r b n m hr hb w)
        (sectorZEquiv F r b n m hr hb w) (signedProduct F r b n m hr hb w) := by
  funext x y z
  change (∏ i, orientedBlock F r b (w.val i) (x.1.1 i) (y.1.1 i) (z.1.1 i)) *
    (∏ i, orientedBlock F r b (w.val i) (z.1.2 i) (x.1.2 i) (y.1.2 i)) *
    (∏ i, orientedBlock F r b (w.val i) (y.2 i) (z.2 i) (x.2 i)) = _
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  exact congrFun (congrFun (congrFun (factor_orientation F r b hr hb (w.val i))
    ((x.1.1 i, x.1.2 i), x.2 i)) ((y.1.1 i, y.1.2 i), y.2 i))
    ((z.1.1 i, z.1.2 i), z.2 i)

/-- At equal input widths the signed rank-bridge realizations have identical
coordinate types. The nontrivial middle-block permutations are in factorX/Y/Z. -/
def squareX (r : Nat) (hr : 0 < r) (s : Label) :
    (factor F r r hr hr s).X ≃ (cyclicConvolution F r r hr hr).X := by
  cases s <;> exact Equiv.refl _

def squareY (r : Nat) (hr : 0 < r) (s : Label) :
    (factor F r r hr hr s).Y ≃ (cyclicConvolution F r r hr hr).Y := by
  cases s <;> exact Equiv.refl _

def squareZ (r : Nat) (hr : 0 < r) (s : Label) :
    (factor F r r hr hr s).Z ≃ (cyclicConvolution F r r hr hr).Z := by
  cases s <;> exact Equiv.refl _

theorem square_factor_tensor (r : Nat) (hr : 0 < r) (s : Label)
    (x : (factor F r r hr hr s).X) (y : (factor F r r hr hr s).Y)
    (z : (factor F r r hr hr s).Z) :
    (factor F r r hr hr s).tensor x y z =
      (cyclicConvolution F r r hr hr).tensor
        (squareX F r hr s x) (squareY F r hr s y) (squareZ F r hr s z) := by
  cases s <;> rfl

/-- In particular the actual cyclic triple of the exchanged middle block is
coordinate-isomorphic to S(r,r), using the local factor permutation above. -/
theorem square_block_orientation (r : Nat) (hr : 0 < r) (s : Label) :
    cyclicTriple F (orientedBlock F r r s) =
      Tensor.pullback ((factorX F r r hr hr s).trans (squareX F r hr s))
        ((factorY F r r hr hr s).trans (squareY F r hr s))
        ((factorZ F r r hr hr s).trans (squareZ F r hr s))
        (cyclicConvolution F r r hr hr).tensor := by
  rw [factor_orientation F r r hr hr s]
  funext x y z
  exact square_factor_tensor F r hr s _ _ _

def commonX (r n m : Nat) (hr : 0 < r) (w : Word n m) :=
  (sectorX F r r n m hr hr w).trans
    (Equiv.piCongrRight (fun i => squareX F r hr (w.val i)))

def commonY (r n m : Nat) (hr : 0 < r) (w : Word n m) :=
  (sectorYEquiv F r r n m hr hr w).trans
    (Equiv.piCongrRight (fun i => squareY F r hr (w.val i)))

def commonZ (r n m : Nat) (hr : 0 < r) (w : Word n m) :=
  (sectorZEquiv F r r n m hr hr w).trans
    (Equiv.piCongrRight (fun i => squareZ F r hr (w.val i)))

/-- Every selected square sector has the same cyclic triple S(r,r)^tensor_n,
under explicit bijections of its three coefficient-coordinate sets. -/
theorem square_sector_orientation (r n m : Nat) (hr : 0 < r) (w : Word n m) :
    cyclicTriple F (normalizedSector F r r n m w) =
      Tensor.pullback (commonX F r n m hr w) (commonY F r n m hr w)
        (commonZ F r n m hr w) (Tensor.power (cyclicConvolution F r r hr hr).tensor n) := by
  rw [sector_orientation F r r n m hr hr w]
  funext x y z
  change (∏ i, (factor F r r hr hr (w.val i)).tensor
    (sectorX F r r n m hr hr w x i) (sectorYEquiv F r r n m hr hr w y i)
    (sectorZEquiv F r r n m hr hr w z i)) =
      ∏ i, (cyclicConvolution F r r hr hr).tensor
        (squareX F r hr (w.val i) (sectorX F r r n m hr hr w x i))
        (squareY F r hr (w.val i) (sectorYEquiv F r r n m hr hr w y i))
        (squareZ F r hr (w.val i) (sectorZEquiv F r r n m hr hr w z i))
  exact Finset.prod_congr rfl (fun i _ => square_factor_tensor F r hr (w.val i) _ _ _)

def commonFullX (r n m : Nat) (hr : 0 < r) (w : Word n m) :=
  (commonX F r n m hr w).trans (xCoordinates F (cyclicConvolution F r r hr hr) n).symm

def commonFullY (r n m : Nat) (hr : 0 < r) (w : Word n m) :=
  (commonY F r n m hr w).trans (yCoordinates F (cyclicConvolution F r r hr hr) n).symm

def commonFullZ (r n m : Nat) (hr : 0 < r) (w : Word n m) :=
  (commonZ F r n m hr w).trans (zCoordinates F (cyclicConvolution F r r hr hr) n).symm

theorem square_sector_fullPower (r n m : Nat) (hr : 0 < r) (w : Word n m) :
    cyclicTriple F (normalizedSector F r r n m w) =
      Tensor.pullback (commonFullX F r n m hr w) (commonFullY F r n m hr w)
        (commonFullZ F r n m hr w) ((cyclicConvolution F r r hr hr).power n).tensor := by
  rw [square_sector_orientation F r n m hr w]
  exact (pullback_from_fullPower F (cyclicConvolution F r r hr hr) n
    (commonX F r n m hr w) (commonY F r n m hr w) (commonZ F r n m hr w)).symm

namespace Separated
open DependentSeparator

/-- Normalize a selected sector of the actual dependent separator target, and
select one matching auxiliary coordinate. Its first leg already carries h. -/
def selectedSector (r b N m aux : Nat) (h : Fin (Tripling.blockCount N m)) (j : Fin aux) :
    Tensor ℚ (Fin N → Fin r) (Tripling.blockY r b N m h) (Tripling.blockZ r b N m h) :=
  Tensor.pullback
    (fun x => (h, fun i => normalizeFirst r ((Tripling.blockWord N m h).val i) (x i)))
    (fun y => (j, ⟨h, y⟩)) (fun z => (j, ⟨h, z⟩))
    (dependentTarget (n := aux) (Tripling.blocks r b N m))

theorem selectedSector_eq_normalized (r b N m aux : Nat)
    (h : Fin (Tripling.blockCount N m)) (j : Fin aux) :
    selectedSector r b N m aux h j =
      normalizedSector ℚ r b N m (Tripling.blockWord N m h) := by
  funext x y z
  simp only [selectedSector, Tensor.pullback, dependentTarget_same, ↓reduceIte]
  change (∏ i, block ℚ r b ((Tripling.blockWord N m h).val i)
    (normalizeFirst r ((Tripling.blockWord N m h).val i) (x i)) (y i) (z i)) = _
  exact Finset.prod_congr rfl (fun i _ => block_normalized ℚ r b _ _ _ _)

/-- Only after the dependent separator has supplied an independent first-leg
sector label do we apply the word-dependent reversal and the cyclic maps. -/
theorem selected_square_fullPower (r N m aux : Nat) (hr : 0 < r)
    (h : Fin (Tripling.blockCount N m)) (j : Fin aux) :
    cyclicTriple ℚ (selectedSector r r N m aux h j) =
      Tensor.pullback (commonFullX ℚ r N m hr (Tripling.blockWord N m h))
        (commonFullY ℚ r N m hr (Tripling.blockWord N m h))
        (commonFullZ ℚ r N m hr (Tripling.blockWord N m h))
        ((cyclicConvolution ℚ r r hr hr).power N).tensor := by
  rw [selectedSector_eq_normalized]
  exact square_sector_fullPower ℚ r N m hr (Tripling.blockWord N m h)

end Separated

end
end MatrixDimensionAudit.TriplingOrientationBridge

#print axioms MatrixDimensionAudit.TriplingOrientationBridge.factor_orientation
#print axioms MatrixDimensionAudit.TriplingOrientationBridge.negative_count
#print axioms MatrixDimensionAudit.TriplingOrientationBridge.positive_count
#print axioms MatrixDimensionAudit.TriplingOrientationBridge.sector_orientation
#print axioms MatrixDimensionAudit.TriplingOrientationBridge.square_factor_tensor
#print axioms MatrixDimensionAudit.TriplingOrientationBridge.square_block_orientation
#print axioms MatrixDimensionAudit.TriplingOrientationBridge.square_sector_orientation
#print axioms MatrixDimensionAudit.TriplingOrientationBridge.square_sector_fullPower
#print axioms MatrixDimensionAudit.TriplingOrientationBridge.Separated.selectedSector_eq_normalized
#print axioms MatrixDimensionAudit.TriplingOrientationBridge.Separated.selected_square_fullPower
