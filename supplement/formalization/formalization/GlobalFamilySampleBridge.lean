import formalization.OriginalLocalSampleBridge
import formalization.LedgerRelationPackingBridge

namespace MatrixDimensionAudit.GlobalFamilySampleBridge
open OAI.MatrixMultiplication.Foundation
open TensorRankBridge TensorResourcePoolingBridge SignedCatalystLedgerBridge
open LedgerRelationPackingBridge FlowActionTensorBridge GeneralRowSector AllRowProfile
open OriginalLocalSampleBridge FamilyPolynomialAssemblyBridge SeparatorTensor
open scoped BigOperators

noncomputable section

local instance productFiniteX (A B : FullTensor ℚ) [Fintype A.X] [Fintype B.X] :
    Fintype (A.product B).X := by change Fintype (A.X × B.X); infer_instance
local instance productFiniteY (A B : FullTensor ℚ) [Fintype A.Y] [Fintype B.Y] :
    Fintype (A.product B).Y := by change Fintype (A.Y × B.Y); infer_instance
local instance powerFiniteX (A : FullTensor ℚ) [Fintype A.X] (k : Nat) : Fintype (A.power k).X :=
  Fintype.ofEquiv (Fin k → A.X) (PowerCoordinateBridge.xCoordinates ℚ A k).symm
local instance powerFiniteY (A : FullTensor ℚ) [Fintype A.Y] (k : Nat) : Fintype (A.power k).Y :=
  Fintype.ofEquiv (Fin k → A.Y) (PowerCoordinateBridge.yCoordinates ℚ A k).symm
local instance resourceFiniteX {I : Type} [Fintype I] (A : I → FullTensor ℚ)
    [∀ i, Fintype (A i).X] : Fintype (resourceFamily A).X := by
  classical
  change Fintype (∀ i, (A i).X)
  infer_instance
local instance resourceFiniteY {I : Type} [Fintype I] (A : I → FullTensor ℚ)
    [∀ i, Fintype (A i).Y] : Fintype (resourceFamily A).Y := by
  classical
  change Fintype (∀ i, (A i).Y)
  infer_instance

def familyX {I : Type} [Fintype I] (A : I → FullTensor ℚ) : (∀ i, (A i).X) ≃ (resourceFamily A).X :=
  Equiv.refl _
def familyY {I : Type} [Fintype I] (A : I → FullTensor ℚ) : (∀ i, (A i).Y) ≃ (resourceFamily A).Y :=
  Equiv.refl _
def familyZ {I : Type} [Fintype I] (A : I → FullTensor ℚ) : (∀ i, (A i).Z) ≃ (resourceFamily A).Z :=
  Equiv.refl _

theorem family_iso_coeff {I : Type} [Fintype I] (A : I → FullTensor ℚ) (B : FullTensor ℚ)
    (p : Iso (resourceFamily A) B) (x : ∀ i, (A i).X) (y : ∀ i, (A i).Y) (z : ∀ i, (A i).Z) :
    tensorFamily (fun i => (A i).tensor) x y z =
      B.tensor (((familyX A).trans p.x) x) (((familyY A).trans p.y) y) (((familyZ A).trans p.z) z) :=
  p.coeff _ _ _

local instance cyclicFiniteX (r b : Nat) (hr : 0 < r) (hb : 0 < b) :
    Fintype (cyclicConvolution ℚ r b hr hb).X :=
  show Fintype ((Fin r × Fin b) × Fin (r + b - 1)) from inferInstance
local instance cyclicFiniteY (r b : Nat) (hr : 0 < r) (hb : 0 < b) :
    Fintype (cyclicConvolution ℚ r b hr hb).Y :=
  show Fintype ((Fin b × Fin (r + b - 1)) × Fin r) from inferInstance
local instance signedFiniteX (negative : Bool) (r b : Nat) (hr : 0 < r) (hb : 0 < b) :
    Fintype (signedCyclicConvolution ℚ negative r b hr hb).X := by
  cases negative <;> dsimp [signedCyclicConvolution] <;> infer_instance
local instance signedFiniteY (negative : Bool) (r b : Nat) (hr : 0 < r) (hb : 0 < b) :
    Fintype (signedCyclicConvolution ℚ negative r b hr hb).Y := by
  cases negative <;> dsimp [signedCyclicConvolution] <;> infer_instance
local instance matrixFiniteX (a : Nat) : Fintype (matrixFull a).X :=
  show Fintype (Fin a × Fin a) from inferInstance
local instance matrixFiniteY (a : Nat) : Fintype (matrixFull a).Y :=
  show Fintype (Fin a × Fin a) from inferInstance

/-- A normalized relation retains its original source matrices and a polynomial
whose constant is the full independent-copy output tensor. -/
structure NormalizedSample (A B : FullTensor ℚ) [Fintype A.X] [Fintype A.Y]
    (M copies degree : Nat) where
  polynomial : Tensor (Polynomial ℚ) (Fin (M ^ 3) × B.X) (Fin (M ^ 3) × B.Y) (Fin (M ^ 3) × B.Z)
  maps : SampleMaps copies A.tensor polynomial
  constant : evaluate polynomial 0 = Tensor.directSum (fun _ : Fin (M ^ 3) => B.tensor)
  bound : ∀ x y z, (polynomial x y z).natDegree ≤ degree

/-- Change the original source coordinates while retaining the actual matrices. -/
def reindexSourceMaps {X Y Z X' Y' Z' U V W : Type}
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype U] [Fintype V] [Fintype W]
    {L : Nat} {T : Tensor ℚ X Y Z} {P : Tensor (Polynomial ℚ) X' Y' Z'}
    (maps : SampleMaps L T P) (S : Tensor ℚ U V W)
    (ex : X ≃ U) (ey : Y ≃ V) (ez : Z ≃ W)
    (he : T = Tensor.pullback ex ey ez S) : SampleMaps L S P := by
  classical
  let cx := Equiv.prodCongr (Equiv.refl (Fin L)) ex
  let cy := Equiv.prodCongr (Equiv.refl (Fin L)) ey
  let cz := Equiv.prodCongr (Equiv.refl (Fin L)) ez
  have hc : Tensor.directSum (fun _ : Fin L => T) =
      Tensor.pullback cx cy cz (Tensor.directSum (fun _ : Fin L => S)) := by
    rw [he, ← Tensor.directSum_pullback]
    rfl
  exact {
    first := fun _ ε x u => maps.first () ε x (u.1, ex.symm u.2)
    second := fun _ ε y v => maps.second () ε y (v.1, ey.symm v.2)
    third := fun _ ε z w => maps.third () ε z (w.1, ez.symm w.2)
    identity := fun ε hε _ => by
      have hp := maps.identity ε hε ()
      rw [hc, FamilyPolynomialAssemblyBridge.restriction_reindex] at hp
      exact hp }

theorem directSum_reindex {I J X Y Z U V W : Type} [DecidableEq I] [DecidableEq J]
    (T : Tensor ℚ X Y Z) (S : Tensor ℚ U V W) (ec : I ≃ J)
    (ex : X ≃ U) (ey : Y ≃ V) (ez : Z ≃ W) (he : T = Tensor.pullback ex ey ez S) :
    Tensor.directSum (fun _ : I => T) =
      Tensor.pullback (Equiv.prodCongr ec ex) (Equiv.prodCongr ec ey) (Equiv.prodCongr ec ez)
        (Tensor.directSum (fun _ : J => S)) := by
  funext x y z
  change (if x.1 = y.1 ∧ x.1 = z.1 then T x.2 y.2 z.2 else 0) =
    if ec x.1 = ec y.1 ∧ ec x.1 = ec z.1 then S (ex x.2) (ey y.2) (ez z.2) else 0
  rw [he]
  simp only [Tensor.pullback, ec.injective.eq_iff]

/-- Normalize the full summand tensor and all copy labels before interpolation. -/
def normalizeOutput {X Y Z J : Type} [DecidableEq J]
    (A B : FullTensor ℚ) [Fintype A.X] [Fintype A.Y]
    (M L d : Nat) (P : Tensor (Polynomial ℚ) (J × X) (J × Y) (J × Z))
    (maps : SampleMaps L A.tensor P) (T : Tensor ℚ X Y Z)
    (hc : evaluate P 0 = Tensor.directSum (fun _ : J => T))
    (hd : ∀ x y z, (P x y z).natDegree ≤ d)
    (ec : J ≃ Fin (M ^ 3)) (ex : X ≃ B.X) (ey : Y ≃ B.Y) (ez : Z ≃ B.Z)
    (he : T = Tensor.pullback ex ey ez B.tensor) : NormalizedSample A B M L d := by
  let cx := Equiv.prodCongr ec ex
  let cy := Equiv.prodCongr ec ey
  let cz := Equiv.prodCongr ec ez
  exact {
    polynomial := Tensor.pullback cx.symm cy.symm cz.symm P
    maps := maps.pullback (fun _ => cx.symm) (fun _ => cy.symm) (fun _ => cz.symm)
    bound := fun x y z => hd (cx.symm x) (cy.symm y) (cz.symm z)
    constant := by
      have hs := directSum_reindex T B.tensor ec ex ey ez he
      funext x y z
      change evaluate P 0 (cx.symm x) (cy.symm y) (cz.symm z) = _
      rw [hc, hs]
      change Tensor.directSum (fun _ : Fin (M ^ 3) => B.tensor) (cx (cx.symm x)) (cy (cy.symm y)) (cz (cz.symm z)) = _
      rw [cx.apply_symm_apply, cy.apply_symm_apply, cz.apply_symm_apply] }

def signedInputTensor (negative : Bool) (r c h N : Nat) (hr : 0 < r) (hc : 0 < c) :=
  Tensor.product (Tensor.power (signedCyclicConvolution ℚ negative r c hr hc).tensor N)
    (Tensor.power (matrix (h + 1)) N)
def signedInputFull (negative : Bool) (r c h N : Nat) (hr : 0 < r) (hc : 0 < c) :=
  ((signedCyclicConvolution ℚ negative r c hr hc).power N).product (matrixFull ((h + 1) ^ N))
def splitInputX (negative : Bool) (r c h N : Nat) (hr : 0 < r) (hc : 0 < c) :=
  Equiv.prodCongr (PowerCoordinateBridge.xCoordinates ℚ (signedCyclicConvolution ℚ negative r c hr hc) N).symm
    (matrixPowerCoordinates (h + 1) N)
def splitInputY (negative : Bool) (r c h N : Nat) (hr : 0 < r) (hc : 0 < c) :=
  Equiv.prodCongr (PowerCoordinateBridge.yCoordinates ℚ (signedCyclicConvolution ℚ negative r c hr hc) N).symm
    (matrixPowerCoordinates (h + 1) N)
def splitInputZ (negative : Bool) (r c h N : Nat) (hr : 0 < r) (hc : 0 < c) :=
  Equiv.prodCongr (PowerCoordinateBridge.zCoordinates ℚ (signedCyclicConvolution ℚ negative r c hr hc) N).symm
    (matrixPowerCoordinates (h + 1) N)

theorem split_input_identity (negative : Bool) (r c h N : Nat) (hr : 0 < r) (hc : 0 < c) :
    signedInputTensor negative r c h N hr hc =
      Tensor.pullback (splitInputX negative r c h N hr hc) (splitInputY negative r c h N hr hc)
        (splitInputZ negative r c h N hr hc) (signedInputFull negative r c h N hr hc).tensor := by
  unfold signedInputTensor
  rw [PowerCoordinateBridge.tensorPower_eq_pullback ℚ (signedCyclicConvolution ℚ negative r c hr hc) N,
    matrix_power]
  rfl

def unitMatrixCoordinates : Unit ≃ (Fin 1 × Fin 1) where
  toFun := fun _ => (0, 0)
  invFun := fun _ => ()
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
def matrixUnitIso : Iso (FullTensor.unit (F := ℚ)) (matrixFull 1) where
  x := unitMatrixCoordinates
  y := unitMatrixCoordinates
  z := unitMatrixCoordinates
  coeff := fun _ _ _ => rfl

def addMatrixOneIso (A : FullTensor ℚ) : Iso A (A.product (matrixFull 1)) :=
  (Iso.unitRight A).symm.trans ((Iso.refl A).product matrixUnitIso)

def resetFrameIso (negative : Bool) (r Z : Nat) (hr : 2 ≤ r) :
    Iso ((signedCyclicConvolution ℚ negative r (TriplingRestrictionBridge.sourceWidth r r)
      (by omega) (by unfold TriplingRestrictionBridge.sourceWidth; omega)).power Z)
      (((resetFactor ℚ negative r hr).power Z).product (matrixFull 1)) :=
  (Iso.power (Iso.ofEq (tripling_reset_named negative r hr)) Z).trans (addMatrixOneIso _)

def resetInputX (negative : Bool) (r Z : Nat) (hr : 2 ≤ r) :=
  (PowerCoordinateBridge.xCoordinates ℚ (signedCyclicConvolution ℚ negative r
    (TriplingRestrictionBridge.sourceWidth r r) (by omega)
    (by unfold TriplingRestrictionBridge.sourceWidth; omega)) Z).symm.trans (resetFrameIso negative r Z hr).x
def resetInputY (negative : Bool) (r Z : Nat) (hr : 2 ≤ r) :=
  (PowerCoordinateBridge.yCoordinates ℚ (signedCyclicConvolution ℚ negative r
    (TriplingRestrictionBridge.sourceWidth r r) (by omega)
    (by unfold TriplingRestrictionBridge.sourceWidth; omega)) Z).symm.trans (resetFrameIso negative r Z hr).y
def resetInputZ (negative : Bool) (r Z : Nat) (hr : 2 ≤ r) :=
  (PowerCoordinateBridge.zCoordinates ℚ (signedCyclicConvolution ℚ negative r
    (TriplingRestrictionBridge.sourceWidth r r) (by omega)
    (by unfold TriplingRestrictionBridge.sourceWidth; omega)) Z).symm.trans (resetFrameIso negative r Z hr).z

theorem reset_input_identity (negative : Bool) (r Z : Nat) (hr : 2 ≤ r) :
    Tensor.power (signedCyclicConvolution ℚ negative r (TriplingRestrictionBridge.sourceWidth r r)
      (by omega) (by unfold TriplingRestrictionBridge.sourceWidth; omega)).tensor Z =
      Tensor.pullback (resetInputX negative r Z hr) (resetInputY negative r Z hr) (resetInputZ negative r Z hr)
        (((resetFactor ℚ negative r hr).power Z).product (matrixFull 1)).tensor := by
  funext x y z
  have ht := congrFun (congrFun (congrFun
    (PowerCoordinateBridge.tensorPower_eq_pullback ℚ (signedCyclicConvolution ℚ negative r
      (TriplingRestrictionBridge.sourceWidth r r) (by omega)
      (by unfold TriplingRestrictionBridge.sourceWidth; omega)) Z) x) y) z
  exact ht.trans ((resetFrameIso negative r Z hr).coeff _ _ _)

local instance splitFiniteX (negative : Bool) (r : Nat) (hr : 2 ≤ r) (x : Nat) :
    Fintype (splitFactor ℚ negative r hr x).X := by unfold splitFactor; infer_instance
local instance splitFiniteY (negative : Bool) (r : Nat) (hr : 2 ≤ r) (x : Nat) :
    Fintype (splitFactor ℚ negative r hr x).Y := by unfold splitFactor; infer_instance
local instance resetFiniteX (negative : Bool) (r : Nat) (hr : 2 ≤ r) :
    Fintype (resetFactor ℚ negative r hr).X := by unfold resetFactor; infer_instance
local instance resetFiniteY (negative : Bool) (r : Nat) (hr : 2 ≤ r) :
    Fintype (resetFactor ℚ negative r hr).Y := by unfold resetFactor; infer_instance
local instance sourceFiniteX (r : Nat) (hr : 2 ≤ r) :
    Fintype (sourceFactor ℚ r hr).X := by unfold sourceFactor; infer_instance
local instance sourceFiniteY (r : Nat) (hr : 2 ≤ r) :
    Fintype (sourceFactor ℚ r hr).Y := by unfold sourceFactor; infer_instance
local instance childFiniteX (negative : Bool) (r c h : Nat) (hr : 0 < r) (hc : h + 1 ≤ c)
    (counts : Fin (h + 1) → Nat) : Fintype (splitChildResources negative r c h hr hc counts).X := by
  unfold splitChildResources
  infer_instance
local instance childFiniteY (negative : Bool) (r c h : Nat) (hr : 0 < r) (hc : h + 1 ≤ c)
    (counts : Fin (h + 1) → Nat) : Fintype (splitChildResources negative r c h hr hc counts).Y := by
  unfold splitChildResources
  infer_instance
local instance relationInputFiniteX (q : Relation) : Fintype q.inputResource.X := by
  cases q <;> dsimp [Relation.inputResource] <;> infer_instance
local instance relationInputFiniteY (q : Relation) : Fintype q.inputResource.Y := by
  cases q <;> dsimp [Relation.inputResource] <;> infer_instance
local instance relationOutputFiniteX (q : Relation) : Fintype q.outputResource.X := by
  cases q <;> dsimp [Relation.outputResource] <;> infer_instance
local instance relationOutputFiniteY (q : Relation) : Fintype q.outputResource.Y := by
  cases q <;> dsimp [Relation.outputResource] <;> infer_instance

def inputFrame (q : Relation) := q.inputResource.product (matrixFull q.inputMatrixWidth)
def outputFrame (q : Relation) := q.outputResource.product (matrixFull q.blocks)
def relationCopies (q : Relation) := (q.blocks + q.blocks - 1) ^ 3
def relationDegree (q : Relation) := 3 * (q.blocks - 1)
local instance inputFrameFiniteX (q : Relation) : Fintype (inputFrame q).X := by unfold inputFrame; infer_instance
local instance inputFrameFiniteY (q : Relation) : Fintype (inputFrame q).Y := by unfold inputFrame; infer_instance
local instance outputFrameFiniteX (q : Relation) : Fintype (outputFrame q).X := by unfold outputFrame; infer_instance
local instance outputFrameFiniteY (q : Relation) : Fintype (outputFrame q).Y := by unfold outputFrame; infer_instance

set_option maxHeartbeats 1000000 in
def splitSample (negative : Bool) (r : Nat) (hr : 2 ≤ r) (a : Action r) :
    NormalizedSample (inputFrame (.split negative r hr a)) (outputFrame (.split negative r hr a))
      a.count (relationCopies (.split negative r hr a)) (relationDegree (.split negative r hr a)) := by
  classical
  let c := actionColumn a
  let hc := action_column_legal a hr
  let counts := actionCounts a
  let M := a.count
  let J := DeterminantCyclicRecipeBridge.Index a.h a.width counts
  have hm : DeterminantSplitRecipeBridge.wordCount a.h a.width counts = M := (action_sector_count a).symm
  let ec : J ≃ Fin (M ^ 3) := (cubicCopies _).trans (finCongr (congrArg (fun n : Nat => n ^ 3) hm))
  have hd : ∀ x y z, (splitOutputPolynomial r c a.h a.width M counts x y z).natDegree ≤ 3 * (M - 1) := by
    simpa only [M, Nat.min_self] using action_polynomial_degree a M
  cases negative with
  | false =>
    let q := Relation.split false r hr a
    let sx := splitInputX false r c a.h a.width (by omega) (by omega)
    let sy := splitInputY false r c a.h a.width (by omega) (by omega)
    let sz := splitInputZ false r c a.h a.width (by omega) (by omega)
    have hs : splitSource r c a.h a.width = Tensor.pullback sx sy sz (inputFrame q).tensor :=
      split_input_identity false r c a.h a.width (by omega) (by omega)
    let raw := reindexSourceMaps (positiveActionMaps a hr M) (inputFrame q).tensor sx sy sz hs
    have hcpl : ell (DeterminantSplitRecipeBridge.wordCount a.h a.width counts) M ^ 3 = relationCopies q :=
      action_copy_count a M
    rw [hcpl] at raw
    let ex := Equiv.prodCongr (childPositiveX r c a.h (by omega) hc counts) (Equiv.refl (Fin M × Fin M))
    let ey := Equiv.prodCongr (childPositiveY r c a.h (by omega) hc counts) (Equiv.refl (Fin M × Fin M))
    let ez := Equiv.prodCongr (childPositiveZ r c a.h (by omega) hc counts) (Equiv.refl (Fin M × Fin M))
    have hb : Tensor.product (DeterminantCyclicRecipeBridge.cyclicChild r c a.h counts) (matrix M) =
        Tensor.pullback ex ey ez (outputFrame q).tensor := by
      rw [cyclic_child_resources r c a.h (by omega) hc counts]
      rfl
    exact normalizeOutput (inputFrame q) (outputFrame q) M (relationCopies q) (relationDegree q)
      (splitOutputPolynomial r c a.h a.width M counts) raw _
      (split_output_constant r c a.h a.width M counts) hd ec ex ey ez hb
  | true =>
    let q := Relation.split true r hr a
    let sx := splitInputX true r c a.h a.width (by omega) (by omega)
    let sy := splitInputY true r c a.h a.width (by omega) (by omega)
    let sz := splitInputZ true r c a.h a.width (by omega) (by omega)
    have hs : splitSource c r a.h a.width = Tensor.pullback sx sy sz (inputFrame q).tensor :=
      split_input_identity true r c a.h a.width (by omega) (by omega)
    let raw := reindexSourceMaps (negativeActionMaps a hr M) (inputFrame q).tensor sx sy sz hs
    have hcpl : ell (DeterminantSplitRecipeBridge.wordCount a.h a.width counts) M ^ 3 = relationCopies q :=
      action_copy_count a M
    rw [hcpl] at raw
    let ex := Equiv.prodCongr (childNegativeX r c a.h (by omega) hc counts) (Equiv.prodComm (Fin M) (Fin M))
    let ey := Equiv.prodCongr (childNegativeY r c a.h (by omega) hc counts) (Equiv.prodComm (Fin M) (Fin M))
    let ez := Equiv.prodCongr (childNegativeZ r c a.h (by omega) hc counts) (Equiv.prodComm (Fin M) (Fin M))
    have hb : Tensor.product (TriplingRestrictionBridge.transposeInputs ℚ
        (DeterminantCyclicRecipeBridge.cyclicChild r c a.h counts))
        (TriplingRestrictionBridge.transposeInputs ℚ (matrix M)) =
        Tensor.pullback ex ey ez (outputFrame q).tensor := by
      rw [transposed_cyclic_child_resources r c a.h (by omega) hc counts, matrix_transpose M]
      rfl
    have hconst : evaluate (fun y x z => splitOutputPolynomial r c a.h a.width M counts x y z) 0 =
        Tensor.directSum (fun _ : J => Tensor.product (TriplingRestrictionBridge.transposeInputs ℚ
          (DeterminantCyclicRecipeBridge.cyclicChild r c a.h counts))
          (TriplingRestrictionBridge.transposeInputs ℚ (matrix M))) := by
      simpa only [DeterminantCyclicRecipeBridge.output, DeterminantCyclicRecipeBridge.outputBlock,
        TriplingContextBridge.transpose_directSum, TriplingContextBridge.transpose_product,
        DeterminantCyclicRecipeBridge.matrixAux, matrix]
        using negative_split_output_constant r c a.h a.width M counts
    exact normalizeOutput (inputFrame q) (outputFrame q) M (relationCopies q) (relationDegree q)
      (fun y x z => splitOutputPolynomial r c a.h a.width M counts x y z) raw _ hconst
      (fun y x z => hd x y z) ec ex ey ez hb

def squareBaseX (r : Nat) (hr : 2 ≤ r) : (sourceFactor ℚ r hr).Y ≃ (sourceFactor ℚ r hr).X :=
  signedTransposeX false r r (by omega) (by omega)
def squareBaseY (r : Nat) (hr : 2 ≤ r) : (sourceFactor ℚ r hr).X ≃ (sourceFactor ℚ r hr).Y :=
  signedTransposeY false r r (by omega) (by omega)
def squareBaseZ (r : Nat) (hr : 2 ≤ r) : (sourceFactor ℚ r hr).Z ≃ (sourceFactor ℚ r hr).Z :=
  signedTransposeZ false r r (by omega) (by omega)
theorem square_base_identity (r : Nat) (hr : 2 ≤ r) :
    TriplingRestrictionBridge.transposeInputs ℚ (sourceFactor ℚ r hr).tensor =
      Tensor.pullback (squareBaseX r hr) (squareBaseY r hr) (squareBaseZ r hr) (sourceFactor ℚ r hr).tensor :=
  signed_transpose false r r (by omega) (by omega)

def squarePowerX (r Z : Nat) (hr : 2 ≤ r) :=
  ((PowerCoordinateBridge.yCoordinates ℚ (sourceFactor ℚ r hr) Z).trans
    (Equiv.piCongrRight (fun _ : Fin Z => squareBaseX r hr))).trans
    (PowerCoordinateBridge.xCoordinates ℚ (sourceFactor ℚ r hr) Z).symm
def squarePowerY (r Z : Nat) (hr : 2 ≤ r) :=
  ((PowerCoordinateBridge.xCoordinates ℚ (sourceFactor ℚ r hr) Z).trans
    (Equiv.piCongrRight (fun _ : Fin Z => squareBaseY r hr))).trans
    (PowerCoordinateBridge.yCoordinates ℚ (sourceFactor ℚ r hr) Z).symm
def squarePowerZ (r Z : Nat) (hr : 2 ≤ r) :=
  ((PowerCoordinateBridge.zCoordinates ℚ (sourceFactor ℚ r hr) Z).trans
    (Equiv.piCongrRight (fun _ : Fin Z => squareBaseZ r hr))).trans
    (PowerCoordinateBridge.zCoordinates ℚ (sourceFactor ℚ r hr) Z).symm

theorem square_power_identity (r Z : Nat) (hr : 2 ≤ r) :
    TriplingRestrictionBridge.transposeInputs ℚ ((sourceFactor ℚ r hr).power Z).tensor =
      Tensor.pullback (squarePowerX r Z hr) (squarePowerY r Z hr) (squarePowerZ r Z hr)
        ((sourceFactor ℚ r hr).power Z).tensor := by
  let A := sourceFactor ℚ r hr
  funext x y z
  change (A.power Z).tensor y x z = (A.power Z).tensor (squarePowerX r Z hr x)
    (squarePowerY r Z hr y) (squarePowerZ r Z hr z)
  rw [PowerCoordinateBridge.power_tensor_identity, PowerCoordinateBridge.power_tensor_identity]
  change (∏ i, A.tensor
    (PowerCoordinateBridge.xCoordinates ℚ A Z y i) (PowerCoordinateBridge.yCoordinates ℚ A Z x i)
    (PowerCoordinateBridge.zCoordinates ℚ A Z z i)) =
    Tensor.power A.tensor Z
      ((PowerCoordinateBridge.xCoordinates ℚ A Z) ((PowerCoordinateBridge.xCoordinates ℚ A Z).symm
        (fun i => squareBaseX r hr (PowerCoordinateBridge.yCoordinates ℚ A Z x i))))
      ((PowerCoordinateBridge.yCoordinates ℚ A Z) ((PowerCoordinateBridge.yCoordinates ℚ A Z).symm
        (fun i => squareBaseY r hr (PowerCoordinateBridge.xCoordinates ℚ A Z y i))))
      ((PowerCoordinateBridge.zCoordinates ℚ A Z) ((PowerCoordinateBridge.zCoordinates ℚ A Z).symm
        (fun i => squareBaseZ r hr (PowerCoordinateBridge.zCoordinates ℚ A Z z i))))
  rw [(PowerCoordinateBridge.xCoordinates ℚ A Z).apply_symm_apply,
    (PowerCoordinateBridge.yCoordinates ℚ A Z).apply_symm_apply,
    (PowerCoordinateBridge.zCoordinates ℚ A Z).apply_symm_apply]
  apply Finset.prod_congr rfl
  intro i _
  exact congrFun (congrFun (congrFun (square_base_identity r hr)
    (PowerCoordinateBridge.yCoordinates ℚ A Z x i)) (PowerCoordinateBridge.xCoordinates ℚ A Z y i))
    (PowerCoordinateBridge.zCoordinates ℚ A Z z i)

set_option maxHeartbeats 1000000 in
def resetSample (negative : Bool) (r Z : Nat) (hr : 2 ≤ r) :
    NormalizedSample (inputFrame (.reset negative r hr Z)) (outputFrame (.reset negative r hr Z))
      (triplingCount Z) (relationCopies (.reset negative r hr Z)) (relationDegree (.reset negative r hr Z)) := by
  classical
  have hr0 : 0 < r := by omega
  let m := TriplingSectorModeBridge.mode Z
  let M := triplingCount Z
  let J := TriplingLocalRecipeBridge.Index Z m
  have hm : DependentSeparator.Tripling.blockCount Z m = M := by
    change TriplingSectorCountBridge.count Z m = M
    exact (row_tripling_count Z).symm
  let ec : J ≃ Fin (M ^ 3) := (cubicCopies _).trans (finCongr (congrArg (fun n : Nat => n ^ 3) hm))
  have hd : ∀ x y z, (triplingOutputPolynomial r Z m M hr0 x y z).natDegree ≤ 3 * (M - 1) := by
    simpa only [M, Nat.min_self] using reset_polynomial_degree r Z M hr0
  cases negative with
  | false =>
    let q := Relation.reset false r hr Z
    let sx := resetInputX false r Z hr
    let sy := resetInputY false r Z hr
    let sz := resetInputZ false r Z hr
    have hs : triplingSource r Z = Tensor.pullback sx sy sz (inputFrame q).tensor :=
      reset_input_identity false r Z hr
    let raw := reindexSourceMaps (positiveResetMaps r Z M hr) (inputFrame q).tensor sx sy sz hs
    have hcpl : ell (DependentSeparator.Tripling.blockCount Z m) M ^ 3 = relationCopies q := reset_copy_count Z M
    rw [hcpl] at raw
    let ex : ((TriplingLocalRecipeBridge.child r Z hr0).X × (Fin M × Fin M)) ≃ (outputFrame q).X := Equiv.refl _
    let ey : ((TriplingLocalRecipeBridge.child r Z hr0).Y × (Fin M × Fin M)) ≃ (outputFrame q).Y := Equiv.refl _
    let ez : ((TriplingLocalRecipeBridge.child r Z hr0).Z × (Fin M × Fin M)) ≃ (outputFrame q).Z := Equiv.refl _
    have hb : Tensor.product (TriplingLocalRecipeBridge.child r Z hr0).tensor (matrix M) =
        Tensor.pullback ex ey ez (outputFrame q).tensor := rfl
    exact normalizeOutput (inputFrame q) (outputFrame q) M (relationCopies q) (relationDegree q)
      (triplingOutputPolynomial r Z m M hr0) raw _
      (tripling_output_constant r Z m M hr0) hd ec ex ey ez hb
  | true =>
    let q := Relation.reset true r hr Z
    let sx := resetInputX true r Z hr
    let sy := resetInputY true r Z hr
    let sz := resetInputZ true r Z hr
    have hs : Tensor.power (TriplingRestrictionBridge.cyclicTriple ℚ
        (convolution ℚ (TriplingRestrictionBridge.sourceWidth r r) r)) Z =
        Tensor.pullback sx sy sz (inputFrame q).tensor := reset_input_identity true r Z hr
    let raw := reindexSourceMaps (negativeResetMaps r Z M hr) (inputFrame q).tensor sx sy sz hs
    have hcpl : ell (DependentSeparator.Tripling.blockCount Z m) M ^ 3 = relationCopies q := reset_copy_count Z M
    rw [hcpl] at raw
    let dx : (TriplingLocalRecipeBridge.child r Z hr0).Y ≃ q.outputResource.X := squarePowerX r Z hr
    let dy : (TriplingLocalRecipeBridge.child r Z hr0).X ≃ q.outputResource.Y := squarePowerY r Z hr
    let dz : (TriplingLocalRecipeBridge.child r Z hr0).Z ≃ q.outputResource.Z := squarePowerZ r Z hr
    let ex := Equiv.prodCongr dx (Equiv.prodComm (Fin M) (Fin M))
    let ey := Equiv.prodCongr dy (Equiv.prodComm (Fin M) (Fin M))
    let ez := Equiv.prodCongr dz (Equiv.prodComm (Fin M) (Fin M))
    have hb : Tensor.product (TriplingRestrictionBridge.transposeInputs ℚ
        (TriplingLocalRecipeBridge.child r Z hr0).tensor)
        (TriplingRestrictionBridge.transposeInputs ℚ (matrix M)) =
        Tensor.pullback ex ey ez (outputFrame q).tensor := by
      funext x y z
      exact congrArg₂ (· * ·)
        (congrFun (congrFun (congrFun (square_power_identity r Z hr) x.1) y.1) z.1)
        (congrFun (congrFun (congrFun (matrix_transpose M) x.2) y.2) z.2)
    have hconst : evaluate (fun y x z => triplingOutputPolynomial r Z m M hr0 x y z) 0 =
        Tensor.directSum (fun _ : J => Tensor.product (TriplingRestrictionBridge.transposeInputs ℚ
          (TriplingLocalRecipeBridge.child r Z hr0).tensor)
          (TriplingRestrictionBridge.transposeInputs ℚ (matrix M))) := by
      simpa only [TriplingLocalRecipeBridge.output, TriplingLocalRecipeBridge.outputBlock,
        TriplingContextBridge.transpose_directSum, TriplingContextBridge.transpose_product,
        TriplingLocalRecipeBridge.auxiliary, matrix]
        using negative_tripling_output_constant r Z m M hr0
    exact normalizeOutput (inputFrame q) (outputFrame q) M (relationCopies q) (relationDegree q)
      (fun y x z => triplingOutputPolynomial r Z m M hr0 x y z) raw _ hconst
      (fun y x z => hd x y z) ec ex ey ez hb

def relationSample (q : Relation) :
    NormalizedSample (inputFrame q) (outputFrame q) q.blocks (relationCopies q) (relationDegree q) := by
  cases q with
  | split negative r hr a => exact splitSample negative r hr a
  | reset negative r hr Z => exact resetSample negative r Z hr

/-- One actual product-copy index, with its proved product cardinality. -/
def copyWords {I : Type} [Fintype I] (L : I → Nat) : (∀ i, Fin (L i)) ≃ Fin (∏ i, L i) :=
  familyIndex L

/-- Independent local target copy words enumerate all product-cubed copies. -/
def outputWords {I : Type} [Fintype I] (M : I → Nat) :
    (∀ i, Fin (M i ^ 3)) ≃ Fin ((∏ i, M i) ^ 3) :=
  (copyWords (fun i => M i ^ 3)).trans (finCongr (by rw [Finset.prod_pow]))

/-- A named source equivalence and a copy-word equivalence act on every copy
without changing its coefficient tensor. -/
theorem named_source_copies {I : Type} [Fintype I] [DecidableEq I]
    (A : I → FullTensor ℚ) (B : FullTensor ℚ) (L : I → Nat) (p : Iso (resourceFamily A) B) :
    Tensor.directSum (fun _ : ∀ i, Fin (L i) => tensorFamily (fun i => (A i).tensor)) =
      Tensor.pullback (Equiv.prodCongr (copyWords L) ((familyX A).trans p.x))
        (Equiv.prodCongr (copyWords L) ((familyY A).trans p.y))
        (Equiv.prodCongr (copyWords L) ((familyZ A).trans p.z)) (Tensor.directSum (fun _ : Fin (∏ i, L i) => B.tensor)) := by
  classical
  funext x y z
  change (if x.1 = y.1 ∧ x.1 = z.1 then tensorFamily (fun i => (A i).tensor) x.2 y.2 z.2 else 0) =
    if copyWords L x.1 = copyWords L y.1 ∧ copyWords L x.1 = copyWords L z.1 then
      B.tensor (((familyX A).trans p.x) x.2) (((familyY A).trans p.y) y.2) (((familyZ A).trans p.z) z.2) else 0
  rw [family_iso_coeff A B p]
  simp only [(copyWords L).injective.eq_iff]

/-- Assemble all actual relation matrices at one parameter and normalize the
complete source and output to the named tensors. -/
def assemble {I : Type} [Fintype I] [DecidableEq I]
    (A B : I → FullTensor ℚ) [∀ i, Fintype (A i).X] [∀ i, Fintype (A i).Y]
    (M L d : I → Nat) (samples : ∀ i, NormalizedSample (A i) (B i) (M i) (L i) (d i))
    (U V : FullTensor ℚ) [Fintype U.X] [Fintype U.Y]
    (sourceIso : Iso (resourceFamily A) U) (outputIso : Iso (resourceFamily B) V) :
    NormalizedSample U V (∏ i, M i) (∏ i, L i) (∑ i, d i) := by
  classical
  let P := tensorFamily (fun i => (samples i).polynomial)
  let fx := fun (x : Fin ((∏ i, M i) ^ 3) × V.X) i =>
    ((outputWords M).symm x.1 i, ((familyX B).trans outputIso.x).symm x.2 i)
  let fy := fun (y : Fin ((∏ i, M i) ^ 3) × V.Y) i =>
    ((outputWords M).symm y.1 i, ((familyY B).trans outputIso.y).symm y.2 i)
  let fz := fun (z : Fin ((∏ i, M i) ^ 3) × V.Z) i =>
    ((outputWords M).symm z.1 i, ((familyZ B).trans outputIso.z).symm z.2 i)
  let ex := Equiv.prodCongr (copyWords L) ((familyX A).trans sourceIso.x)
  let ey := Equiv.prodCongr (copyWords L) ((familyY A).trans sourceIso.y)
  let ez := Equiv.prodCongr (copyWords L) ((familyZ A).trans sourceIso.z)
  let maps := sampleMapsFamily (fun i => (samples i).maps)
  have source_eq := named_source_copies A U L sourceIso
  let raw : SampleMaps (∏ i, L i) U.tensor P := {
    first := fun _ ε x u => jointMatrix L (fun i => maps.first i ε) x (ex.symm u)
    second := fun _ ε y v => jointMatrix L (fun i => maps.second i ε) y (ey.symm v)
    third := fun _ ε z w => jointMatrix L (fun i => maps.third i ε) z (ez.symm w)
    identity := fun ε hε _ => by
      have hp := joint_sample_restriction L (fun i => (A i).tensor)
        (fun i => (samples i).polynomial) maps.first maps.second maps.third ε (maps.identity ε hε)
      rw [source_eq, FamilyPolynomialAssemblyBridge.restriction_reindex] at hp
      rw [← evaluate_family] at hp
      exact hp }
  exact {
    polynomial := Tensor.pullback fx fy fz P
    maps := raw.pullback (fun _ => fx) (fun _ => fy) (fun _ => fz)
    bound := fun x y z => family_degree (fun i => (samples i).polynomial) d
      (fun i => (samples i).bound) (fx x) (fy y) (fz z)
    constant := by
      funext x y z
      change evaluate P 0 (fx x) (fy y) (fz z) = _
      rw [evaluate_family]
      change (∏ i, evaluate (samples i).polynomial 0 (fx x i) (fy y i) (fz z i)) = _
      simp_rw [(samples _).constant]
      have hc := family_copies (fun i => M i ^ 3) (fun i => (B i).tensor)
      have hh := congrFun (congrFun (congrFun hc (fx x)) (fy y)) (fz z)
      change tensorFamily (fun i => Tensor.directSum (fun _ : Fin (M i ^ 3) => (B i).tensor)) (fx x) (fy y) (fz z) = _
      rw [hh]
      change (if (outputWords M).symm x.1 = (outputWords M).symm y.1 ∧
          (outputWords M).symm x.1 = (outputWords M).symm z.1 then
        tensorFamily (fun i => (B i).tensor)
          (((familyX B).trans outputIso.x).symm x.2) (((familyY B).trans outputIso.y).symm y.2)
          (((familyZ B).trans outputIso.z).symm z.2) else 0) = _
      rw [family_iso_coeff B V outputIso]
      simp only [Equiv.symm_apply_eq, Equiv.apply_symm_apply, Tensor.directSum] }

/-- The complete one-pass input keeps the source matrix outside the common catalyst. -/
def familySource (family : Family n K) : FullTensor ℚ :=
  (((sourceFactor ℚ (n + 2) (by omega)).power K).product (familyConsumed ℚ family)).product
    (matrixFull family.dimension)

/-- The complete one-pass output retains that same catalyst and pools every matrix factor. -/
def familyTarget (family : Family n K) : FullTensor ℚ :=
  (familyConsumed ℚ family).product (matrixFull (2 ^ K * family.count))

def familyCopies (family : Family n K) : Nat :=
  ∏ i : Fin (familyRelations family).length, relationCopies ((familyRelations family).get i)
def familyDegree (family : Family n K) : Nat :=
  ∑ i : Fin (familyRelations family).length, relationDegree ((familyRelations family).get i)

local instance familySourceFiniteX (family : Family n K) : Fintype (familySource family).X :=
  Fintype.ofEquiv (resourceFamily (fun i : Fin (familyRelations family).length =>
    inputFrame ((familyRelations family).get i))).X (familyInputWithMatrixIso family).x
local instance familySourceFiniteY (family : Family n K) : Fintype (familySource family).Y :=
  Fintype.ofEquiv (resourceFamily (fun i : Fin (familyRelations family).length =>
    inputFrame ((familyRelations family).get i))).Y (familyInputWithMatrixIso family).y
local instance familyTargetFiniteX (family : Family n K) : Fintype (familyTarget family).X :=
  Fintype.ofEquiv (resourceFamily (fun i : Fin (familyRelations family).length =>
    outputFrame ((familyRelations family).get i))).X (familyPooledOutputIso family).x
local instance familyTargetFiniteY (family : Family n K) : Fintype (familyTarget family).Y :=
  Fintype.ofEquiv (resourceFamily (fun i : Fin (familyRelations family).length =>
    outputFrame ((familyRelations family).get i))).Y (familyPooledOutputIso family).y

theorem family_block_product (family : Family n K) :
    (∏ i : Fin (familyRelations family).length, ((familyRelations family).get i).blocks) = family.count :=
  (fin_list_prod _ Relation.blocks).trans (family_blocks_prod family)

/-- All signed actions and resets are assembled at one parameter. The matrices
start at the complete named source and end at all independent cubic copies of
the complete named output; no local rank certificates enter this construction. -/
def familySample (family : Family n K) :
    NormalizedSample (familySource family) (familyTarget family)
      family.count (familyCopies family) (familyDegree family) := by
  classical
  have h := assemble
    (fun i : Fin (familyRelations family).length => inputFrame ((familyRelations family).get i))
    (fun i => outputFrame ((familyRelations family).get i))
    (fun i => ((familyRelations family).get i).blocks)
    (fun i => relationCopies ((familyRelations family).get i))
    (fun i => relationDegree ((familyRelations family).get i))
    (fun i => relationSample ((familyRelations family).get i))
    (familySource family) (familyTarget family)
    (familyInputWithMatrixIso family) (familyPooledOutputIso family)
  rw [family_block_product family] at h
  exact h

theorem row_block_list (negative : Bool) (r : Nat) (hr : 2 ≤ r)
    (actions : List (Action r)) (Z : Nat) :
    (rowRelations negative r hr actions Z).map Relation.blocks =
      (rowSeparators actions Z).map FreeAuxiliaryBridge.Separator.blocks := by
  simp [rowRelations, rowSeparators, Relation.blocks, actionSeparator, triplingSeparator,
    countedSeparator, List.map_map, Function.comp_def]

theorem lower_block_list (depth : Nat) (rows : LowerRows K n) :
    (lowerRelations depth rows).map Relation.blocks =
      (lowerSeparators rows).map FreeAuxiliaryBridge.Separator.blocks := by
  induction rows generalizing depth with
  | nil => rfl
  | cons row tail ih =>
    simp only [lowerRelations, lowerSeparators, List.map_append, row_block_list, ih]

theorem family_block_list (family : Family n K) :
    (familyRelations family).map Relation.blocks =
      (familySeparators family).map FreeAuxiliaryBridge.Separator.blocks := by
  simp only [familyRelations, familySeparators, List.map_append, row_block_list, lower_block_list]

theorem family_copies_formula (family : Family n K) :
    familyCopies family =
      (((familySeparators family).map (fun s => s.blocks + s.blocks - 1)).prod) ^ 3 := by
  unfold familyCopies relationCopies
  rw [Finset.prod_pow, fin_list_prod (familyRelations family) (fun q => q.blocks + q.blocks - 1)]
  have h := congrArg (fun xs : List Nat => (xs.map (fun M => M + M - 1)).prod) (family_block_list family)
  simpa only [List.map_map, Function.comp_def] using congrArg (fun n : Nat => n ^ 3) h

theorem fin_list_sum {L : Type} (xs : List L) (f : L → Nat) :
    (∑ i : Fin xs.length, f (xs.get i)) = (xs.map f).sum := by
  rw [← Fin.sum_ofFn]
  congr 1
  simpa only [List.ofFn_get, Function.comp_def] using (List.map_ofFn (f := xs.get) (g := f)).symm

theorem family_degree_formula (family : Family n K) :
    familyDegree family = 3 * ((familySeparators family).map (fun s => s.blocks - 1)).sum := by
  unfold familyDegree relationDegree
  rw [← Finset.mul_sum, fin_list_sum (familyRelations family) (fun q => q.blocks - 1)]
  have h := congrArg (fun xs : List Nat => (xs.map (fun M => M - 1)).sum) (family_block_list family)
  simpa only [List.map_map, Function.comp_def] using congrArg (fun n : Nat => 3 * n) h

/-- The assembled matrices are actual restrictions of copies of the complete
original signed source, for every nonzero common parameter. -/
theorem family_sample_restriction (family : Family n K) (ε : ℚ) (hε : ε ≠ 0) :
    Tensor.restrict ((familySample family).maps.first () ε)
      ((familySample family).maps.second () ε) ((familySample family).maps.third () ε)
      (Tensor.directSum (fun _ : Fin (familyCopies family) => (familySource family).tensor)) =
      evaluate (familySample family).polynomial ε :=
  (familySample family).maps.identity ε hε ()

theorem family_constant (family : Family n K) :
    evaluate (familySample family).polynomial 0 =
      Tensor.directSum (fun _ : Fin (family.count ^ 3) => (familyTarget family).tensor) :=
  (familySample family).constant

theorem family_degree (family : Family n K) (x y z) :
    ((familySample family).polynomial x y z).natDegree ≤ familyDegree family :=
  (familySample family).bound x y z

local instance familyTargetDecX (family : Family n K) : DecidableEq (familyTarget family).X := Classical.decEq _
local instance familyTargetDecY (family : Family n K) : DecidableEq (familyTarget family).Y := Classical.decEq _

/-- The powered polynomial uses one actual interpolation restriction, including power zero. -/
theorem family_exactification (family : Family n K) (k : Nat) :
    Tensor.restrict (foldMatrix (exactWeight (k * familyDegree family)))
      (foldMatrix (fun _ : Fin (k * familyDegree family + 1) => (1 : ℚ)))
      (foldMatrix (fun _ : Fin (k * familyDegree family + 1) => (1 : ℚ)))
      (Tensor.directSum (fun e : Fin (k * familyDegree family + 1) =>
        evaluate (Tensor.power (familySample family).polynomial k) (node e))) =
      Tensor.power (Tensor.directSum (fun _ : Fin (family.count ^ 3) => (familyTarget family).tensor)) k := by
  have h := tensor_exactification (Tensor.power (familySample family).polynomial k)
    (k * familyDegree family) (tensor_power_degree _ k _ (familySample family).bound)
  simpa only [FamilyPolynomialAssemblyBridge.evaluate_power, (familySample family).constant] using h

/-- One complete source certificate pays the product copy budget. -/
theorem family_sample_rank (family : Family n K) (ε : ℚ) (hε : ε ≠ 0) (R : Nat)
    (source_rank : Tensor.RankAtMost (familySource family).tensor R) :
    Tensor.RankAtMost (evaluate (familySample family).polynomial ε) (familyCopies family * R) := by
  classical
  have h := directSum_rankAtMost (fun _ : Fin (familyCopies family) => (familySource family).tensor)
    R (fun _ => source_rank)
  simp only [Fintype.card_fin] at h
  have hp := h.restrict ((familySample family).maps.first () ε)
    ((familySample family).maps.second () ε) ((familySample family).maps.third () ε)
  rw [family_sample_restriction family ε hε] at hp
  exact hp

/-- All family relations are exactified together; the output retains the same
catalyst and every auxiliary matrix coordinate in each of the full M^(3k) blocks. -/
theorem family_power_rank (family : Family n K) (k R : Nat)
    (source_rank : Tensor.RankAtMost (familySource family).tensor R) :
    Tensor.RankAtMost (Tensor.directSum (fun _ : Fin k → Fin (family.count ^ 3) =>
      Tensor.power (familyTarget family).tensor k))
      ((k * familyDegree family + 1) * familyCopies family ^ k * R ^ k) := by
  classical
  have hp := tensor_power_exactification_rank (familySample family).polynomial k (familyDegree family)
    (familyCopies family * R) (familySample family).bound (fun e =>
      family_sample_rank family (node e) (Separator.rationalNode_nonzero e.val) R source_rank)
  rw [(familySample family).constant] at hp
  have h := hp.directSum_const_of_power
  convert h using 1
  rw [mul_pow]
  ring

/-- The same output bound on the existing nested FullTensor power coordinates. -/
theorem family_full_power_rank (family : Family n K) (k R : Nat)
    (source_rank : Tensor.RankAtMost (familySource family).tensor R) :
    Tensor.RankAtMost (Tensor.directSum (fun _ : Fin k → Fin (family.count ^ 3) =>
      ((familyTarget family).power k).tensor))
      ((k * familyDegree family + 1) * familyCopies family ^ k * R ^ k) := by
  have h := (family_power_rank family k R source_rank).directSum_pullback
    (PowerCoordinateBridge.xCoordinates ℚ (familyTarget family) k)
    (PowerCoordinateBridge.yCoordinates ℚ (familyTarget family) k)
    (PowerCoordinateBridge.zCoordinates ℚ (familyTarget family) k)
  simpa only [← PowerCoordinateBridge.fullPower_eq_pullback] using h

theorem powered_block_count (family : Family n K) (k : Nat) :
    Fintype.card (Fin k → Fin (family.count ^ 3)) = family.count ^ (3 * k) := by
  simp only [Fintype.card_fun, Fintype.card_fin, ← pow_mul]

end
end MatrixDimensionAudit.GlobalFamilySampleBridge
