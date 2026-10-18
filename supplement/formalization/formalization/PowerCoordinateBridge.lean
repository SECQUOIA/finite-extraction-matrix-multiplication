import formalization.TriplingRestrictionBridge

namespace MatrixDimensionAudit.PowerCoordinateBridge
open OAI.MatrixMultiplication.Foundation
open TensorRankBridge
open TriplingRestrictionBridge
open scoped BigOperators

noncomputable section
variable (F : Type) [Field F]

/-- A coordinate equivalence induces the usual linear permutation of coefficient vectors. -/
def coordinateLinearEquiv {X Y : Type} (e : X ≃ Y) : (X → F) ≃ₗ[F] (Y → F) :=
  LinearEquiv.funCongrLeft F F e.symm

@[simp] theorem coordinateLinearEquiv_apply {X Y : Type} (e : X ≃ Y)
    (f : X → F) (y : Y) : coordinateLinearEquiv F e f y = f (e.symm y) := rfl

/-- The scalar tensor's sole coordinate corresponds to the empty word. -/
def emptyCoordinates (X : Type) : Unit ≃ (Fin 0 → X) where
  toFun := fun _ i => Fin.elim0 i
  invFun := fun _ => ()
  left_inv := by intro x; cases x; rfl
  right_inv := by intro x; funext i; exact Fin.elim0 i

/-- Prepend the head of a nested pair to the word representing its tail. -/
def consCoordinates {X Y : Type} {n : Nat} (e : Y ≃ (Fin n → X)) :
    (X × Y) ≃ (Fin (n + 1) → X) where
  toFun := fun x => Fin.cons x.1 (e x.2)
  invFun := fun x => (x 0, e.symm (Fin.tail x))
  left_inv := by intro x; simp
  right_inv := by intro x; simp

def xCoordinates (A : FullTensor F) : (n : Nat) → (A.power n).X ≃ (Fin n → A.X)
  | 0 => emptyCoordinates A.X
  | n + 1 => consCoordinates (xCoordinates A n)

def yCoordinates (A : FullTensor F) : (n : Nat) → (A.power n).Y ≃ (Fin n → A.Y)
  | 0 => emptyCoordinates A.Y
  | n + 1 => consCoordinates (yCoordinates A n)

def zCoordinates (A : FullTensor F) : (n : Nat) → (A.power n).Z ≃ (Fin n → A.Z)
  | 0 => emptyCoordinates A.Z
  | n + 1 => consCoordinates (zCoordinates A n)

/-- The two power conventions have exactly the same coefficients under these
three explicit coordinate equivalences, including the zero-th power. -/
theorem power_tensor_identity (A : FullTensor F) (n : Nat)
    (x : (A.power n).X) (y : (A.power n).Y) (z : (A.power n).Z) :
    (A.power n).tensor x y z =
      Tensor.power A.tensor n (xCoordinates F A n x) (yCoordinates F A n y)
        (zCoordinates F A n z) := by
  induction n with
  | zero => simp [FullTensor.power, FullTensor.unit, Tensor.power]
  | succ n ih =>
      change A.tensor x.1 y.1 z.1 * (A.power n).tensor x.2 y.2 z.2 =
        ∏ i : Fin (n + 1), A.tensor
          (Fin.cons (α := fun _ => A.X) x.1 (xCoordinates F A n x.2) i)
          (Fin.cons (α := fun _ => A.Y) y.1 (yCoordinates F A n y.2) i)
          (Fin.cons (α := fun _ => A.Z) z.1 (zCoordinates F A n z.2) i)
      rw [Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [ih]
      rfl

theorem fullPower_eq_pullback (A : FullTensor F) (n : Nat) :
    (A.power n).tensor = Tensor.pullback
      (xCoordinates F A n) (yCoordinates F A n) (zCoordinates F A n)
      (Tensor.power A.tensor n) := by
  funext x y z
  exact power_tensor_identity F A n x y z

theorem tensorPower_eq_pullback (A : FullTensor F) (n : Nat) :
    Tensor.power A.tensor n = Tensor.pullback
      (xCoordinates F A n).symm (yCoordinates F A n).symm (zCoordinates F A n).symm
      (A.power n).tensor := by
  funext x y z
  simp only [Tensor.pullback, power_tensor_identity, Equiv.apply_symm_apply]

/-- Any restriction of the function-indexed power can be performed directly on
the nested-pair power by composing its coordinate maps with the inverses above. -/
theorem pullback_from_fullPower (A : FullTensor F) (n : Nat) {X Y Z : Type}
    (fx : X → (Fin n → A.X)) (fy : Y → (Fin n → A.Y))
    (fz : Z → (Fin n → A.Z)) :
    Tensor.pullback ((xCoordinates F A n).symm ∘ fx)
      ((yCoordinates F A n).symm ∘ fy) ((zCoordinates F A n).symm ∘ fz)
      (A.power n).tensor = Tensor.pullback fx fy fz (Tensor.power A.tensor n) := by
  funext x y z
  simp only [Tensor.pullback, Function.comp_apply, power_tensor_identity, Equiv.apply_symm_apply]

/-- Actual rank decompositions transport in both directions through the reindexing. -/
theorem power_rankAtMost_iff (A : FullTensor F) (n rank : Nat) :
    Tensor.RankAtMost (A.power n).tensor rank ↔
      Tensor.RankAtMost (Tensor.power A.tensor n) rank := by
  constructor
  · intro h
    rw [tensorPower_eq_pullback F A n]
    exact h.pullback _ _ _
  · intro h
    rw [fullPower_eq_pullback F A n]
    exact h.pullback _ _ _

/-- The earlier actual-tensor rank floor therefore applies to the external power
without a caller-provided numerical floor. -/
theorem tensorPower_rank_floor (A : FullTensor F) (n rank : Nat)
    (decomposition : Tensor.RankAtMost (Tensor.power A.tensor n) rank) :
    A.dimension ^ n ≤ rank := by
  have h := (A.power n).rank_floor ((power_rankAtMost_iff F A n rank).mpr decomposition)
  simpa only [FullTensor.dimension_power] using h

/-- The generalized tripling source, now an actual FullTensor from the rank bridge. -/
def triplingFull (r b : Nat) (hr : 0 < r) (hb : 0 < b) : FullTensor F :=
  convolutionOutput F r (sourceWidth r b) hr (by unfold sourceWidth; omega)

/-- The fixed-middle restriction applied directly to the nested-pair source.
The first-leg map is a fixed coordinate equivalence independent of the sector. -/
def triplingFromFull (r b n m : Nat) (hr : 0 < r) (hb : 0 < b) :
    Tensor F (Fin n → Fin r) (keptY r b n m) (keptZ r b n m) :=
  Tensor.pullback (xCoordinates F (triplingFull F r b hr hb) n).symm
    (fun y => (yCoordinates F (triplingFull F r b hr hb) n).symm y.val)
    (fun z => (zCoordinates F (triplingFull F r b hr hb) n).symm z.val)
    ((triplingFull F r b hr hb).power n).tensor

theorem triplingFromFull_eq_restricted (r b n m : Nat) (hr : 0 < r) (hb : 0 < b) :
    triplingFromFull F r b n m hr hb = restricted F r b n m := by
  exact pullback_from_fullPower F (triplingFull F r b hr hb) n id Subtype.val Subtype.val

theorem triplingFromFull_sector_identity (r b n m : Nat) (hr : 0 < r) (hb : 0 < b)
    (w : Word n m) (x : Fin n → Fin r) (y : sectorY r b n m w)
    (z : sectorZ r b n m w) :
    triplingFromFull F r b n m hr hb x (sectorEmbeddingY r b n m hr hb w y)
      (sectorEmbeddingZ r b n m hr hb w z) =
      ∏ i, block F r b (w.val i) (x i) (y i) (z i) := by
  rw [triplingFromFull_eq_restricted F r b n m hr hb]
  exact sector_tensor_identity F r b n m hr hb w x y z

theorem triplingFromFull_normalized_sector (r b n m : Nat) (hr : 0 < r) (hb : 0 < b)
    (w : Word n m) (x : Fin n → Fin r) (y : sectorY r b n m w)
    (z : sectorZ r b n m w) :
    triplingFromFull F r b n m hr hb (fun i => normalizeFirst r (w.val i) (x i))
      (sectorEmbeddingY r b n m hr hb w y) (sectorEmbeddingZ r b n m hr hb w z) =
      ∏ i, orientedBlock F r b (w.val i) (x i) (y i) (z i) := by
  rw [triplingFromFull_eq_restricted F r b n m hr hb]
  exact sector_normalized_tensor_identity F r b n m hr hb w x y z

theorem triplingFromFull_cross_sector_zero (r b n m : Nat) (hr : 0 < r) (hb : 0 < b)
    (w v : Word n m) (h : w ≠ v) (x : Fin n → Fin r)
    (y : sectorY r b n m w) (z : sectorZ r b n m v) :
    triplingFromFull F r b n m hr hb x (sectorEmbeddingY r b n m hr hb w y)
      (sectorEmbeddingZ r b n m hr hb v z) = 0 := by
  rw [triplingFromFull_eq_restricted F r b n m hr hb]
  exact cross_sector_zero F r b n m hr hb w v h x y z

end
end MatrixDimensionAudit.PowerCoordinateBridge

#print axioms MatrixDimensionAudit.PowerCoordinateBridge.power_tensor_identity
#print axioms MatrixDimensionAudit.PowerCoordinateBridge.fullPower_eq_pullback
#print axioms MatrixDimensionAudit.PowerCoordinateBridge.tensorPower_eq_pullback
#print axioms MatrixDimensionAudit.PowerCoordinateBridge.pullback_from_fullPower
#print axioms MatrixDimensionAudit.PowerCoordinateBridge.power_rankAtMost_iff
#print axioms MatrixDimensionAudit.PowerCoordinateBridge.tensorPower_rank_floor
#print axioms MatrixDimensionAudit.PowerCoordinateBridge.triplingFromFull_eq_restricted
#print axioms MatrixDimensionAudit.PowerCoordinateBridge.triplingFromFull_sector_identity
#print axioms MatrixDimensionAudit.PowerCoordinateBridge.triplingFromFull_normalized_sector
#print axioms MatrixDimensionAudit.PowerCoordinateBridge.triplingFromFull_cross_sector_zero
