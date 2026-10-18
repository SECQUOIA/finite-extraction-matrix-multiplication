import formalization.SignedCatalystLedgerBridge

/-! Pack the actual powered relations into the signed common-catalyst ledger. -/
namespace MatrixDimensionAudit.LedgerRelationPackingBridge
open OAI.MatrixMultiplication.Foundation
open GeneralFlow GeneralRowSector GeneralRowCatalyst AllRowProfile
open TensorRankBridge TensorResourcePoolingBridge SignedCatalystLedgerBridge
open FlowActionTensorBridge DeterminantSplitRecipeBridge
open scoped BigOperators
noncomputable section

/-- One population-expanded split, or one row's complete reset relation. -/
inductive Relation where
  | split (negative : Bool) (r : ℕ) (hr : 2 ≤ r) (a : Action r)
  | reset (negative : Bool) (r : ℕ) (hr : 2 ≤ r) (Z : ℕ)

namespace Relation

def inputResource : Relation → FullTensor ℚ
  | .split negative r hr a => (splitFactor ℚ negative r hr a.x).power a.width
  | .reset negative r hr Z => (resetFactor ℚ negative r hr).power Z

def outputResource : Relation → FullTensor ℚ
  | .split negative r hr a => splitChildResources negative r (actionColumn a) a.h
      (by omega) (action_column_legal a hr) (actionCounts a)
  | .reset _ r hr Z => (sourceFactor ℚ r hr).power Z

def blocks : Relation → ℕ
  | .split _ _ _ a => a.count
  | .reset _ _ _ Z => triplingCount Z

def inputMatrixWidth : Relation → ℕ
  | .split _ _ _ a => a.dimension
  | .reset _ _ _ _ => 1

def inputStates : Relation → List ℕ
  | .split _ _ _ a => a.input
  | .reset _ r _ Z => List.replicate Z (3 * r)

def outputStates : Relation → List ℕ
  | .split _ _ _ a => a.output
  | .reset _ _ _ Z => List.replicate Z 1

def inputLabels : Relation → List Label
  | .split negative r hr a => a.input.map (stateLabel negative r hr)
  | .reset negative r hr Z => (List.replicate Z (3 * r)).map (stateLabel negative r hr)

def outputLabels : Relation → List Label
  | .split negative r hr a => a.output.map (stateLabel negative r hr)
  | .reset negative r hr Z => (List.replicate Z 1).map (stateLabel negative r hr)

end Relation

def rowRelations (negative : Bool) (r : ℕ) (hr : 2 ≤ r) (actions : List (Action r)) (Z : ℕ) : List Relation :=
  actions.map (Relation.split negative r hr) ++ [.reset negative r hr Z]

def lowerRelations (depth : ℕ) : {n : ℕ} → LowerRows K n → List Relation
  | _, .nil => []
  | _, .cons row tail => rowRelations (rowSign depth) _ (by omega) row.actions row.Z ++
      lowerRelations (depth + 1) tail

def familyRelations (family : Family n K) : List Relation :=
  rowRelations false _ (by omega) family.top.actions family.top.Z ++ lowerRelations 1 family.lower

theorem row_blocks_prod (negative : Bool) (r : ℕ) (hr : 2 ≤ r) (actions : List (Action r)) (Z : ℕ) :
    ((rowRelations negative r hr actions Z).map Relation.blocks).prod = actualSectorCount actions Z := by
  simp [rowRelations, Relation.blocks, actualSectorCount, totalCount, List.map_map, Function.comp_def]

theorem row_input_matrix_prod (negative : Bool) (r : ℕ) (hr : 2 ≤ r) (actions : List (Action r)) (Z : ℕ) :
    ((rowRelations negative r hr actions Z).map Relation.inputMatrixWidth).prod = totalDimension actions := by
  simp [rowRelations, Relation.inputMatrixWidth, totalDimension, List.map_map, Function.comp_def]

theorem lower_blocks_prod (depth : ℕ) (rows : LowerRows K n) :
    ((lowerRelations depth rows).map Relation.blocks).prod = rows.count := by
  induction rows generalizing depth with
  | nil => rfl
  | cons row tail ih =>
      simp only [lowerRelations, List.map_append, List.prod_append, row_blocks_prod, ih]
      rfl

theorem lower_input_matrix_prod (depth : ℕ) (rows : LowerRows K n) :
    ((lowerRelations depth rows).map Relation.inputMatrixWidth).prod = rows.dimension := by
  induction rows generalizing depth with
  | nil => rfl
  | cons row tail ih =>
      simp only [lowerRelations, List.map_append, List.prod_append, row_input_matrix_prod, ih]
      rfl

theorem family_blocks_prod (family : Family n K) :
    ((familyRelations family).map Relation.blocks).prod = family.count := by
  simp only [familyRelations, List.map_append, List.prod_append, row_blocks_prod, lower_blocks_prod]
  rfl

theorem family_input_matrix_prod (family : Family n K) :
    ((familyRelations family).map Relation.inputMatrixWidth).prod = family.dimension := by
  simp only [familyRelations, List.map_append, List.prod_append, row_input_matrix_prod, lower_input_matrix_prod]
  rfl

/-- Reindex a finite dependent product while changing every actual factor's coordinates. -/
def resourceFamilyIso {I J : Type} [Fintype I] [Fintype J]
    (A : I → FullTensor ℚ) (B : J → FullTensor ℚ) (e : I ≃ J)
    (p : ∀ i, Iso (A i) (B (e i))) : Iso (resourceFamily A) (resourceFamily B) where
  x := Equiv.piCongr (W := fun i => (A i).X) (Z := fun j => (B j).X) e (fun i => (p i).x)
  y := Equiv.piCongr (W := fun i => (A i).Y) (Z := fun j => (B j).Y) e (fun i => (p i).y)
  z := Equiv.piCongr (W := fun i => (A i).Z) (Z := fun j => (B j).Z) e (fun i => (p i).z)
  coeff := by
    intro x y z
    change (∀ i, (A i).X) at x
    change (∀ i, (A i).Y) at y
    change (∀ i, (A i).Z) at z
    change (∏ i, (A i).tensor (x i) (y i) (z i)) =
      ∏ j, (B j).tensor ((Equiv.piCongr (W := fun i => (A i).X) (Z := fun j => (B j).X) e (fun i => (p i).x)) x j)
        ((Equiv.piCongr (W := fun i => (A i).Y) (Z := fun j => (B j).Y) e (fun i => (p i).y)) y j) ((Equiv.piCongr (W := fun i => (A i).Z) (Z := fun j => (B j).Z) e (fun i => (p i).z)) z j)
    apply Fintype.prod_equiv e
    intro i
    rw [Equiv.piCongr_apply_apply, Equiv.piCongr_apply_apply, Equiv.piCongr_apply_apply]
    exact (p i).coeff (x i) (y i) (z i)


/-- Convert a function-enumerated family to its actual nested list product. -/
def ofFnFamilyIso {L : Type} (A : L → FullTensor ℚ) {n : ℕ} (f : Fin n → L) :
    Iso (resourceFamily (fun i => A (f i))) (listProduct A (List.ofFn f)) :=
  (resourceFamilyIso _ _ (finCongr (List.length_ofFn (f := f)).symm) (fun i =>
    Iso.ofEq (by simp))).trans (listFamilyIso A (List.ofFn f)).symm

def mapListIso {L J : Type} (A : L → FullTensor ℚ) (f : J → L) (xs : List J) :
    Iso (listProduct (fun j => A (f j)) xs) (listProduct A (xs.map f)) := by
  induction xs with
  | nil => exact Iso.refl _
  | cons j xs ih => exact (Iso.refl _).product ih

/-- A real depth word exists even when the action width is zero. -/
def referenceWord (a : Action r) : DeterminantTensorBridge.Word a.h a.width (actionCounts a) :=
  wordEnumeration a.h a.width (actionCounts a) ⟨0, by
    rw [← action_sector_count]
    exact action_count_pos a⟩

theorem reference_encode_perm (a : Action r) :
    (encode a (referenceWord a).val).Perm a.output := by
  apply List.perm_iff_count.mpr
  exact ((WeightedSector.mem_typeSector_iff _ _ _).mp
    ((encode_mem_iff a _).mpr (referenceWord a).property)).2

def splitFactorsListIso (negative : Bool) (r : ℕ) (hr : 2 ≤ r) (xs : List ℕ) :
    Iso (listProduct (splitFactor ℚ negative r hr) xs) (splitFactors ℚ negative r hr xs) := by
  induction xs with
  | nil => exact Iso.refl _
  | cons x xs ih => exact (Iso.refl _).product ih

/-- Grouped positions retain their depth when they enter the population-expanded list. -/
def actionGroupedIso (negative : Bool) (r : ℕ) (hr : 2 ≤ r) (a : Action r) :
    Iso (splitChildResources negative r (actionColumn a) a.h (by omega)
      (action_column_legal a hr) (actionCounts a))
      (splitFactors ℚ negative r hr a.output) := by
  let w := referenceWord a
  let A := fun j : Fin (a.h + 1) => splitFactor ℚ negative r hr (depthState a j)
  have p : ∀ q : GroupedPosition (actionCounts a),
      Iso (signedCyclicConvolution ℚ negative r (actionColumn a + a.h - 2 * q.1.val)
        (by omega) (by have := q.1.isLt; have := action_column_legal a hr; omega))
        (A (w.val (positionEquiv w q))) := by
    intro q
    rw [positionEquiv_depth]
    exact Iso.ofEq (split_child_named_factor negative r a.x a.h hr
      (Nat.le_trans a.h_upper (Nat.min_le_left _ _)) q.1)
  have first := resourceFamilyIso _ (fun i : Fin a.width => A (w.val i)) (positionEquiv w) p
  exact first.trans ((ofFnFamilyIso (splitFactor ℚ negative r hr) (fun i => depthState a (w.val i))).trans
    ((listPermIso (splitFactor ℚ negative r hr) (reference_encode_perm a)).trans (splitFactorsListIso negative r hr a.output)))

namespace Relation

/-- Each powered source is equivalent to precisely its population-expanded input tokens. -/
def inputIso (q : Relation) : Iso q.inputResource (listProduct labelTensor q.inputLabels) := by
  cases q with
  | split negative r hr a =>
      exact ((stateIso negative r hr a.x).power a.width).trans
        (by simpa [inputLabels, Action.input, List.map_replicate] using
          (listReplicateIso labelTensor (stateLabel negative r hr a.x) a.width).symm)
  | reset negative r hr Z =>
      exact ((resetStateIso negative r hr).power Z).trans
        (by simpa [inputLabels, List.map_replicate] using
          (listReplicateIso labelTensor (stateLabel negative r hr (3*r)) Z).symm)

/-- Child positions and reset outputs map to exactly the output token list. -/
def outputIso (q : Relation) : Iso q.outputResource (listProduct labelTensor q.outputLabels) := by
  cases q with
  | split negative r hr a =>
      exact (actionGroupedIso negative r hr a).trans (stateListIso negative r hr a.output)
  | reset negative r hr Z =>
      exact ((sourceStateIso negative r hr).power Z).trans
        (by simpa [outputLabels, List.map_replicate] using
          (listReplicateIso labelTensor (stateLabel negative r hr 1) Z).symm)

end Relation


/-- Flatten a list of heterogeneous relation resources without losing coordinates. -/
def flattenResourceIso (A : Relation → FullTensor ℚ) (tokens : Relation → List Label)
    (p : ∀ q, Iso (A q) (listProduct labelTensor (tokens q))) (qs : List Relation) :
    Iso (listProduct A qs) (listProduct labelTensor (qs.flatMap tokens)) := by
  induction qs with
  | nil => exact Iso.refl _
  | cons q qs ih => exact ((p q).product ih).trans (listAppendIso labelTensor _ _).symm

theorem parents_flatMap_input (actions : List (Action r)) :
    parents actions = actions.flatMap Action.input := by
  induction actions with
  | nil => rfl
  | cons a actions ih =>
      simp only [parents, allEdges, List.flatMap_cons, List.map_append] at ih ⊢
      rw [ih]
      simp [Action.edges, Action.input, List.map_map, Function.comp_def, List.map_const', output_length]

theorem children_flatMap_output (actions : List (Action r)) :
    (allEdges actions).map Edge.dst = actions.flatMap Action.output := by
  induction actions with
  | nil => rfl
  | cons a actions ih =>
      simp only [allEdges, List.flatMap_cons, List.map_append] at ih ⊢
      rw [ih]
      simp [Action.edges, List.map_map, Function.comp_def]

theorem row_input_tokens (negative : Bool) (r : ℕ) (hr : 2 ≤ r) (row : Row r i K) :
    (rowRelations negative r hr row.actions row.Z).flatMap Relation.inputLabels =
      rowInputLabels negative r hr row := by
  simp only [rowRelations, List.flatMap_append, List.flatMap_map, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, Relation.inputLabels, rowInputLabels,
    parents_flatMap_input, List.map_flatMap, List.map_replicate]

theorem row_output_tokens (negative : Bool) (r : ℕ) (hr : 2 ≤ r) (row : Row r i K) :
    (rowRelations negative r hr row.actions row.Z).flatMap Relation.outputLabels =
      rowOutputLabels negative r hr row := by
  simp only [rowRelations, List.flatMap_append, List.flatMap_map, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, Relation.outputLabels, rowOutputLabels,
    children_flatMap_output, List.map_flatMap, List.map_replicate]

theorem lower_input_tokens (depth : ℕ) (rows : LowerRows K n) :
    (lowerRelations depth rows).flatMap Relation.inputLabels = lowerInputLabels depth rows := by
  induction rows generalizing depth with
  | nil => rfl
  | cons row tail ih =>
      simp only [lowerRelations, List.flatMap_append, row_input_tokens, ih, lowerInputLabels]

theorem lower_output_tokens (depth : ℕ) (rows : LowerRows K n) :
    (lowerRelations depth rows).flatMap Relation.outputLabels = lowerOutputLabels depth rows := by
  induction rows generalizing depth with
  | nil => rfl
  | cons row tail ih =>
      simp only [lowerRelations, List.flatMap_append, row_output_tokens, ih, lowerOutputLabels]

theorem family_input_tokens (family : Family n K) :
    (familyRelations family).flatMap Relation.inputLabels = SignedCatalystLedgerBridge.inputLabels family := by
  simp only [familyRelations, List.flatMap_append, row_input_tokens, lower_input_tokens,
    SignedCatalystLedgerBridge.inputLabels]

theorem family_output_tokens (family : Family n K) :
    (familyRelations family).flatMap Relation.outputLabels = SignedCatalystLedgerBridge.outputLabels family := by
  simp only [familyRelations, List.flatMap_append, row_output_tokens, lower_output_tokens,
    SignedCatalystLedgerBridge.outputLabels]

/-- Actual source powers, indexed by the original finite relation list. -/
def familyInputIso (family : Family n K) :
    Iso (resourceFamily (fun i : Fin (familyRelations family).length =>
        ((familyRelations family).get i).inputResource))
      (((sourceFactor ℚ (n+2) (by omega)).power K).product (familyConsumed ℚ family)) :=
  (listFamilyIso Relation.inputResource _).symm.trans
    ((flattenResourceIso _ _ Relation.inputIso _).trans
      ((Iso.ofEq (congrArg (listProduct labelTensor) (family_input_tokens family))).trans
        ((SignedCatalystLedgerBridge.familyInputIso family).symm.trans (inputCommonCatalystIso family))))

/-- Actual grouped child resources, including the whole signed orientation. -/
def familyOutputIso (family : Family n K) :
    Iso (resourceFamily (fun i : Fin (familyRelations family).length =>
        ((familyRelations family).get i).outputResource))
      ((familyConsumed ℚ family).product (matrixFull (2^K))) :=
  (listFamilyIso Relation.outputResource _).symm.trans
    ((flattenResourceIso _ _ Relation.outputIso _).trans
      ((Iso.ofEq (congrArg (listProduct labelTensor) (family_output_tokens family))).trans
        ((SignedCatalystLedgerBridge.familyOutputIso family).symm.trans (outputCommonCatalystIso family))))


/-- Separate two finite resource families by actual coordinate equivalences. -/
def resourceProductIso {I : Type} [Fintype I] (A B : I → FullTensor ℚ) :
    Iso (resourceFamily (fun i => (A i).product (B i)))
      ((resourceFamily A).product (resourceFamily B)) where
  x := splitPairs (fun i => (A i).X) (fun i => (B i).X)
  y := splitPairs (fun i => (A i).Y) (fun i => (B i).Y)
  z := splitPairs (fun i => (A i).Z) (fun i => (B i).Z)
  coeff := by
    intro x y z
    change (∏ i, (A i).tensor (x i).1 (y i).1 (z i).1 *
      (B i).tensor (x i).2 (y i).2 (z i).2) =
      (∏ i, (A i).tensor (x i).1 (y i).1 (z i).1) *
      (∏ i, (B i).tensor (x i).2 (y i).2 (z i).2)
    exact Finset.prod_mul_distrib

/-- Pool the full matrix tensor of every item, without discarding coordinates. -/
def matrixFamilyIso {I : Type} [Fintype I] (a : I → ℕ) :
    Iso (resourceFamily (fun i => matrixFull (a i))) (matrixFull (∏ i, a i)) := by
  classical
  exact {
    x := matrixFamilyCoordinates a
    y := matrixFamilyCoordinates a
    z := matrixFamilyCoordinates a
    coeff := matrix_family a }

def matrixProductIso (a b : ℕ) :
    Iso ((matrixFull a).product (matrixFull b)) (matrixFull (a*b)) where
  x := matrixProductCoordinates a b
  y := matrixProductCoordinates a b
  z := matrixProductCoordinates a b
  coeff := fun x y z => congrFun (congrFun (congrFun (matrix_product a b) x) y) z

theorem fin_list_prod {L : Type} (xs : List L) (f : L → ℕ) :
    (∏ i : Fin xs.length, f (xs.get i)) = (xs.map f).prod := by
  rw [← Fin.prod_ofFn]
  congr 1
  simpa only [List.ofFn_get, Function.comp_def] using (List.map_ofFn (f := xs.get) (g := f)).symm

/-- Canonical full input, with all source-side matrix factors external to the catalyst. -/
def familyInputWithMatrixIso (family : Family n K) :
    Iso (resourceFamily (fun i : Fin (familyRelations family).length =>
        (((familyRelations family).get i).inputResource).product
          (matrixFull (((familyRelations family).get i).inputMatrixWidth))))
      ((((sourceFactor ℚ (n+2) (by omega)).power K).product (familyConsumed ℚ family)).product
        (matrixFull family.dimension)) :=
  (resourceProductIso _ _).trans ((familyInputIso family).product
    ((matrixFamilyIso _).trans (Iso.ofEq (congrArg matrixFull
      ((fin_list_prod _ Relation.inputMatrixWidth).trans (family_input_matrix_prod family))))))

/-- Canonical full output before multiplying the boundary and separator matrices. -/
def familyOutputWithMatrixIso (family : Family n K) :
    Iso (resourceFamily (fun i : Fin (familyRelations family).length =>
        (((familyRelations family).get i).outputResource).product
          (matrixFull (((familyRelations family).get i).blocks))))
      (((familyConsumed ℚ family).product (matrixFull (2^K))).product (matrixFull family.count)) :=
  (resourceProductIso _ _).trans ((familyOutputIso family).product
    ((matrixFamilyIso _).trans (Iso.ofEq (congrArg matrixFull
      ((fin_list_prod _ Relation.blocks).trans (family_blocks_prod family))))))

/-- Complete pooled output: the identical named catalyst and all matrix coordinates. -/
def familyPooledOutputIso (family : Family n K) :
    Iso (resourceFamily (fun i : Fin (familyRelations family).length =>
        (((familyRelations family).get i).outputResource).product
          (matrixFull (((familyRelations family).get i).blocks))))
      ((familyConsumed ℚ family).product (matrixFull (2^K * family.count))) :=
  (familyOutputWithMatrixIso family).trans ((Iso.assoc _ _ _).trans
    ((Iso.refl _).product (matrixProductIso _ _)))

/-- Complete coefficient identity on the original powered-relation input coordinates. -/
theorem family_input_identity (family : Family n K) :
    (resourceFamily (fun i : Fin (familyRelations family).length =>
      ((familyRelations family).get i).inputResource)).tensor =
      Tensor.pullback (familyInputIso family).x (familyInputIso family).y (familyInputIso family).z
        ((((sourceFactor ℚ (n+2) (by omega)).power K).product (familyConsumed ℚ family)).tensor) :=
  (familyInputIso family).tensor_eq

/-- Complete coefficient identity on the actual grouped-child output coordinates. -/
theorem family_output_identity (family : Family n K) :
    (resourceFamily (fun i : Fin (familyRelations family).length =>
      ((familyRelations family).get i).outputResource)).tensor =
      Tensor.pullback (familyOutputIso family).x (familyOutputIso family).y (familyOutputIso family).z
        (((familyConsumed ℚ family).product (matrixFull (2^K))).tensor) :=
  (familyOutputIso family).tensor_eq

/-- The complete source input matrix survives the common-catalyst packing. -/
theorem family_input_with_matrix_identity (family : Family n K) :
    (resourceFamily (fun i : Fin (familyRelations family).length =>
      (((familyRelations family).get i).inputResource).product
        (matrixFull (((familyRelations family).get i).inputMatrixWidth)))).tensor =
      Tensor.pullback (familyInputWithMatrixIso family).x (familyInputWithMatrixIso family).y
        (familyInputWithMatrixIso family).z
        (((((sourceFactor ℚ (n+2) (by omega)).power K).product (familyConsumed ℚ family)).product
          (matrixFull family.dimension)).tensor) :=
  (familyInputWithMatrixIso family).tensor_eq

/-- Separator and boundary matrices are pooled only by full three-leg equivalences. -/
theorem family_pooled_output_identity (family : Family n K) :
    (resourceFamily (fun i : Fin (familyRelations family).length =>
      (((familyRelations family).get i).outputResource).product
        (matrixFull (((familyRelations family).get i).blocks)))).tensor =
      Tensor.pullback (familyPooledOutputIso family).x (familyPooledOutputIso family).y
        (familyPooledOutputIso family).z
        (((familyConsumed ℚ family).product (matrixFull (2^K * family.count))).tensor) :=
  (familyPooledOutputIso family).tensor_eq

end
end MatrixDimensionAudit.LedgerRelationPackingBridge
