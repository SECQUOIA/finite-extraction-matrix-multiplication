import formalization.FlowActionTensorBridge
import formalization.TensorResourcePoolingBridge

/-! Coordinate equivalences for the actual signed common-catalyst ledger. -/
namespace MatrixDimensionAudit.SignedCatalystLedgerBridge
open OAI.MatrixMultiplication.Foundation
open TensorRankBridge TensorResourcePoolingBridge GeneralFlow GeneralRowSector GeneralRowCatalyst AllRowProfile
open scoped BigOperators
noncomputable section

/-- A leg-preserving equivalence of actual coefficient tensors. -/
structure Iso (A B : FullTensor ℚ) where
  x : A.X ≃ B.X
  y : A.Y ≃ B.Y
  z : A.Z ≃ B.Z
  coeff : ∀ a b c, A.tensor a b c = B.tensor (x a) (y b) (z c)

namespace Iso

def refl (A : FullTensor ℚ) : Iso A A := ⟨Equiv.refl _, Equiv.refl _, Equiv.refl _, fun _ _ _ => rfl⟩

def ofEq {A B : FullTensor ℚ} (h : A = B) : Iso A B := by subst B; exact refl A

def trans {A B C : FullTensor ℚ} (p : Iso A B) (q : Iso B C) : Iso A C where
  x := p.x.trans q.x
  y := p.y.trans q.y
  z := p.z.trans q.z
  coeff := fun a b c => (p.coeff a b c).trans (q.coeff _ _ _)

def symm {A B : FullTensor ℚ} (p : Iso A B) : Iso B A where
  x := p.x.symm
  y := p.y.symm
  z := p.z.symm
  coeff := by
    intro a b c
    simpa only [Equiv.apply_symm_apply] using (p.coeff (p.x.symm a) (p.y.symm b) (p.z.symm c)).symm

def product {A B C D : FullTensor ℚ} (p : Iso A B) (q : Iso C D) : Iso (A.product C) (B.product D) where
  x := Equiv.prodCongr p.x q.x
  y := Equiv.prodCongr p.y q.y
  z := Equiv.prodCongr p.z q.z
  coeff := by
    intro a b c
    exact congrArg₂ (· * ·) (p.coeff a.1 b.1 c.1) (q.coeff a.2 b.2 c.2)

def assoc (A B C : FullTensor ℚ) : Iso ((A.product B).product C) (A.product (B.product C)) where
  x := Equiv.prodAssoc _ _ _
  y := Equiv.prodAssoc _ _ _
  z := Equiv.prodAssoc _ _ _
  coeff := fun _ _ _ => mul_assoc _ _ _

def comm (A B : FullTensor ℚ) : Iso (A.product B) (B.product A) where
  x := Equiv.prodComm _ _
  y := Equiv.prodComm _ _
  z := Equiv.prodComm _ _
  coeff := fun _ _ _ => mul_comm _ _

def unitLeftEquiv (X : Type) : Unit × X ≃ X where
  toFun := Prod.snd
  invFun := fun x => ((), x)
  left_inv := by intro x; cases x with | mk u x => cases u; rfl
  right_inv := fun _ => rfl

def unitLeft (A : FullTensor ℚ) : Iso (FullTensor.unit.product A) A where
  x := unitLeftEquiv _
  y := unitLeftEquiv _
  z := unitLeftEquiv _
  coeff := fun _ _ _ => one_mul _

def unitRight (A : FullTensor ℚ) : Iso (A.product FullTensor.unit) A :=
  (comm A FullTensor.unit).trans (unitLeft A)

end Iso

def listProduct {L : Type} (A : L → FullTensor ℚ) : List L → FullTensor ℚ
  | [] => FullTensor.unit
  | x :: xs => (A x).product (listProduct A xs)

def listAppendIso {L : Type} (A : L → FullTensor ℚ) (xs ys : List L) :
    Iso (listProduct A (xs ++ ys)) ((listProduct A xs).product (listProduct A ys)) := by
  induction xs with
  | nil => exact (Iso.unitLeft _).symm
  | cons x xs ih =>
      exact ((Iso.refl (A x)).product ih).trans (Iso.assoc _ _ _).symm

def listReplicateIso {L : Type} (A : L → FullTensor ℚ) (x : L) (n : ℕ) :
    Iso (listProduct A (List.replicate n x)) ((A x).power n) := by
  induction n with
  | zero => exact Iso.refl _
  | succ n ih => exact (Iso.refl (A x)).product ih

/-- A multiset permutation yields three actual coefficient-coordinate equivalences. -/
theorem listPermIso_exists {L : Type} (A : L → FullTensor ℚ) {xs ys : List L} (h : xs.Perm ys) :
    Nonempty (Iso (listProduct A xs) (listProduct A ys)) := by
  induction h with
  | nil => exact ⟨Iso.refl _⟩
  | cons x h ih =>
      obtain ⟨p⟩ := ih
      exact ⟨(Iso.refl (A x)).product p⟩
  | swap x y xs =>
      exact ⟨(Iso.assoc (A y) (A x) (listProduct A xs)).symm.trans
        (((Iso.comm (A y) (A x)).product (Iso.refl _)).trans (Iso.assoc _ _ _))⟩
  | trans h₁ h₂ ih₁ ih₂ =>
      obtain ⟨p⟩ := ih₁
      obtain ⟨q⟩ := ih₂
      exact ⟨p.trans q⟩

def listPermIso {L : Type} (A : L → FullTensor ℚ) {xs ys : List L} (h : xs.Perm ys) :
    Iso (listProduct A xs) (listProduct A ys) := Classical.choice (listPermIso_exists A h)

def listPointwiseIso {L : Type} (A B : L → FullTensor ℚ) (h : ∀ i, Iso (A i) (B i)) (xs : List L) :
    Iso (listProduct A xs) (listProduct B xs) := by
  induction xs with
  | nil => exact Iso.refl _
  | cons x xs ih => exact (h x).product ih


/-- Both possible last-row orientations identify with the complete matrix tensor. -/
def boundaryPositive : Iso (cyclicConvolution ℚ 2 1 (by decide) (by decide)) (matrixFull 2) where
  x := Equiv.prodCongr (Equiv.prodUnique _ (Fin 1)) (Equiv.refl _)
  y := (Equiv.prodCongr ((Equiv.prodComm (Fin 1) (Fin 2)).trans (Equiv.prodUnique _ (Fin 1)))
    (Equiv.refl _)).trans (Equiv.prodComm _ _)
  z := (Equiv.prodUnique _ (Fin 1)).trans (Equiv.prodComm _ _)
  coeff := by
    intro x y z
    change (Fin 2 × Fin 1) × Fin 2 at x
    change (Fin 1 × Fin 2) × Fin 2 at y
    change (Fin 2 × Fin 2) × Fin 1 at z
    have hx : x.1.2 = 0 := Subsingleton.elim _ _
    have hy : y.1.1 = 0 := Subsingleton.elim _ _
    have hz : z.2 = 0 := Subsingleton.elim _ _
    change ((if x.1.1.val + y.1.1.val = z.1.1.val then (1 : ℚ) else 0) *
      (if z.1.2.val + x.1.2.val = y.1.2.val then 1 else 0)) *
      (if y.2.val + z.2.val = x.2.val then 1 else 0) =
      if x.2 = y.2 ∧ y.1.2 = z.1.2 ∧ z.1.1 = x.1.1 then 1 else 0
    simp only [hx, hy, hz, Fin.val_zero, Nat.add_zero]
    by_cases h₁ : x.1.1 = z.1.1 <;> by_cases h₂ : z.1.2 = y.1.2 <;>
      by_cases h₃ : y.2 = x.2 <;> simp_all [← Fin.ext_iff, eq_comm]

def boundaryNegative : Iso (cyclicConvolution ℚ 1 2 (by decide) (by decide)) (matrixFull 2) where
  x := (Equiv.prodCongr ((Equiv.prodComm (Fin 1) (Fin 2)).trans (Equiv.prodUnique _ (Fin 1)))
    (Equiv.refl _)).trans (Equiv.prodComm _ _)
  y := (Equiv.prodUnique _ (Fin 1)).trans (Equiv.prodComm _ _)
  z := Equiv.prodCongr (Equiv.prodUnique _ (Fin 1)) (Equiv.refl _)
  coeff := by
    intro x y z
    change (Fin 1 × Fin 2) × Fin 2 at x
    change (Fin 2 × Fin 2) × Fin 1 at y
    change (Fin 2 × Fin 1) × Fin 2 at z
    have hx : x.1.1 = 0 := Subsingleton.elim _ _
    have hy : y.2 = 0 := Subsingleton.elim _ _
    have hz : z.1.2 = 0 := Subsingleton.elim _ _
    change ((if x.1.1.val + y.1.1.val = z.1.1.val then (1 : ℚ) else 0) *
      (if z.1.2.val + x.1.2.val = y.1.2.val then 1 else 0)) *
      (if y.2.val + z.2.val = x.2.val then 1 else 0) =
      if x.1.2 = y.1.2 ∧ y.1.1 = z.1.1 ∧ z.2 = x.2 then 1 else 0
    simp only [hx, hy, hz, Fin.val_zero, Nat.zero_add]
    by_cases h₁ : y.1.1 = z.1.1 <;> by_cases h₂ : x.1.2 = y.1.2 <;>
      by_cases h₃ : z.2 = x.2 <;> simp_all [← Fin.ext_iff, eq_comm]

abbrev ResourcePair := {p : ℕ × ℕ // 0 < p.1 ∧ 0 < p.2}
/-- None is the matrix-2 boundary; some is a canonical ordered convolution pair. -/
abbrev Label := Option ResourcePair

def labelTensor : Label → FullTensor ℚ
  | none => matrixFull 2
  | some p => cyclicConvolution ℚ p.val.1 p.val.2 p.property.1 p.property.2

def orientedPair (negative : Bool) (r : ℕ) (hr : 2 ≤ r) (x : ℕ) : ResourcePair :=
  if negative then ⟨(r - 1 + x, r), by constructor <;> omega⟩
  else ⟨(r, r - 1 + x), by constructor <;> omega⟩

def stateLabel (negative : Bool) (r : ℕ) (hr : 2 ≤ r) (x : ℕ) : Label :=
  if r = 2 ∧ x = 0 then none else some (orientedPair negative r hr x)

/-- Canonical labels retain the actual signed factor, including both final boundaries. -/
def stateIso (negative : Bool) (r : ℕ) (hr : 2 ≤ r) (x : ℕ) :
    Iso (splitFactor ℚ negative r hr x) (labelTensor (stateLabel negative r hr x)) := by
  by_cases hz : r = 2 ∧ x = 0
  · obtain ⟨rfl, rfl⟩ := hz
    cases negative
    · exact boundaryPositive
    · exact boundaryNegative
  · apply Iso.ofEq
    cases negative <;> simp [splitFactor, signedCyclicConvolution, stateLabel, hz, orientedPair, labelTensor]

def rowInputLabels (negative : Bool) (r : ℕ) (hr : 2 ≤ r) (row : Row r i K) : List Label :=
  (parents row.actions).map (stateLabel negative r hr) ++ List.replicate row.Z (stateLabel negative r hr (3 * r))

def rowOutputLabels (negative : Bool) (r : ℕ) (hr : 2 ≤ r) (row : Row r i K) : List Label :=
  ((allEdges row.actions).map Edge.dst).map (stateLabel negative r hr) ++
    List.replicate row.Z (stateLabel negative r hr 1)

/-- Row balance is used as a parallel resource permutation, not as an execution order. -/
theorem row_label_balance (negative : Bool) (r : ℕ) (hr : 2 ≤ r) (row : Row r i K) :
    (List.replicate K (stateLabel negative r hr i) ++ rowOutputLabels negative r hr row).Perm
      (rowInputLabels negative r hr row ++ List.replicate K (stateLabel negative r hr 0)) := by
  classical
  have hp := row.balance.map (stateLabel negative r hr)
  apply List.perm_iff_count.mpr
  intro v
  have he := hp.count_eq v
  simp only [List.map_append, List.map_replicate, List.count_append] at he
  simp only [rowInputLabels, rowOutputLabels, parents, List.count_append]
  omega


def rowSign (depth : ℕ) : Bool := decide (depth % 2 = 1)

theorem rowSign_next (depth : ℕ) : rowSign (depth + 1) = !rowSign depth := by
  by_cases h : depth % 2 = 1
  · have hn : (depth + 1) % 2 ≠ 1 := by omega
    simp [rowSign, h, hn]
  · have hn : (depth + 1) % 2 = 1 := by omega
    simp [rowSign, h, hn]

theorem stateLabel_one (negative : Bool) (r : ℕ) (hr : 2 ≤ r) :
    stateLabel negative r hr 1 = stateLabel false r hr 1 := by
  have hw : r - 1 + 1 = r := by omega
  cases negative <;> simp [stateLabel, orientedPair, hw]

/-- Adjacent row boundaries agree because their signs alternate. -/
theorem stateLabel_boundary (negative : Bool) (r : ℕ) (hr : 2 ≤ r) :
    stateLabel negative (r + 1) (by omega) 0 = stateLabel (!negative) r hr 2 := by
  have hne : r + 1 ≠ 2 := by omega
  have h₁ : r + 1 - 1 + 0 = r := by omega
  have h₂ : r - 1 + 2 = r + 1 := by omega
  cases negative <;> simp [stateLabel, orientedPair, hne, h₂]

def entryLabel (depth : ℕ) : ℕ → Label
  | 0 => none
  | n + 1 => stateLabel (rowSign depth) (n + 2) (by omega) 2

theorem exit_eq_entry (depth n : ℕ) :
    stateLabel (rowSign depth) (n + 2) (by omega) 0 = entryLabel (depth + 1) n := by
  cases n with
  | zero => simp [stateLabel, entryLabel]
  | succ n =>
      change stateLabel (rowSign depth) ((n + 2) + 1) (by omega) 0 =
        stateLabel (rowSign (depth + 1)) (n + 2) (by omega) 2
      rw [rowSign_next]
      exact stateLabel_boundary _ _ _

def lowerInputLabels (depth : ℕ) : {n : ℕ} → LowerRows K n → List Label
  | _, .nil => []
  | _, .cons row tail => rowInputLabels (rowSign depth) _ (by omega) row ++ lowerInputLabels (depth + 1) tail

def lowerOutputLabels (depth : ℕ) : {n : ℕ} → LowerRows K n → List Label
  | _, .nil => []
  | _, .cons row tail => rowOutputLabels (rowSign depth) _ (by omega) row ++ lowerOutputLabels (depth + 1) tail

/-- Parallel row relations telescope on actual canonical signed labels. -/
theorem lower_label_balance (depth : ℕ) (rows : LowerRows K n) :
    (List.replicate K (entryLabel depth n) ++ lowerOutputLabels depth rows).Perm
      (lowerInputLabels depth rows ++ List.replicate K none) := by
  induction rows generalizing depth with
  | nil => simp [entryLabel, lowerInputLabels, lowerOutputLabels]
  | @cons n row tail ih =>
      have hr := row_label_balance (rowSign depth) _ (by omega) row
      have ht := ih (depth + 1)
      rw [exit_eq_entry] at hr
      have hp := hr.append_right (lowerOutputLabels (depth + 1) tail)
      have hq := ht.append_left (rowInputLabels (rowSign depth) _ (by omega) row)
      simp only [entryLabel, lowerInputLabels, lowerOutputLabels, List.append_assoc] at hp ⊢
      exact hp.trans (by simpa only [entryLabel, List.append_assoc] using hq)

def topCatalystLabels (row : Row r 1 K) (hr : 2 ≤ r) : List Label :=
  (removeInjected K (parents row.actions)).map (stateLabel false r hr) ++
    List.replicate row.Z (stateLabel false r hr (3 * r))

def catalystLabels (family : Family n K) : List Label :=
  topCatalystLabels family.top (by omega) ++ lowerInputLabels 1 family.lower

def inputLabels (family : Family n K) : List Label :=
  rowInputLabels false _ (by omega) family.top ++ lowerInputLabels 1 family.lower

def outputLabels (family : Family n K) : List Label :=
  rowOutputLabels false _ (by omega) family.top ++ lowerOutputLabels 1 family.lower

def sourceLabel (n : ℕ) : Label := stateLabel false (n + 2) (by omega) 1

/-- The source list removes exactly K top-row external factors. -/
theorem input_label_catalyst (family : Family n K) :
    (inputLabels family).Perm (List.replicate K (sourceLabel n) ++ catalystLabels family) := by
  have ht := (removeInjected_ledger (parents family.top.actions) K
    (by have := top_parent_count family.top (by omega); omega)).map (stateLabel false (n + 2) (by omega))
  have hp := ht.append_right (List.replicate family.top.Z (stateLabel false (n + 2) (by omega) (3 * (n + 2))) ++
    lowerInputLabels 1 family.lower)
  simpa only [inputLabels, rowInputLabels, sourceLabel, catalystLabels, topCatalystLabels,
    List.map_append, List.map_replicate, List.append_assoc] using hp

/-- All rows together balance the external source against the final matrix boundary. -/
theorem family_label_balance (family : Family n K) :
    (List.replicate K (sourceLabel n) ++ outputLabels family).Perm
      (inputLabels family ++ List.replicate K none) := by
  have hr := row_label_balance false _ (by omega) family.top
  have ht := lower_label_balance 1 family.lower
  have he : stateLabel false (n + 2) (by omega) 0 = entryLabel 1 n := by
    have hp := exit_eq_entry 0 n
    simpa [rowSign] using hp
  rw [he] at hr
  have hp := hr.append_right (lowerOutputLabels 1 family.lower)
  have hq := ht.append_left (rowInputLabels false _ (by omega) family.top)
  simpa only [sourceLabel, outputLabels, inputLabels, List.append_assoc] using hp.trans
    (by simpa only [List.append_assoc] using hq)

/-- The produced factor multiset is the actual source-side catalyst plus K matrix boundaries. -/
theorem output_label_catalyst (family : Family n K) :
    (outputLabels family).Perm (catalystLabels family ++ List.replicate K none) := by
  classical
  have hp := (family_label_balance family).trans ((input_label_catalyst family).append_right (List.replicate K none))
  apply List.perm_iff_count.mpr
  intro v
  have he := hp.count_eq v
  simp only [List.count_append] at he ⊢
  omega


namespace Iso

def power {A B : FullTensor ℚ} (p : Iso A B) : (n : ℕ) → Iso (A.power n) (B.power n)
  | 0 => refl _
  | n + 1 => p.product (power p n)

end Iso

def stateListIso (negative : Bool) (r : ℕ) (hr : 2 ≤ r) (xs : List ℕ) :
    Iso (splitFactors ℚ negative r hr xs) (listProduct labelTensor (xs.map (stateLabel negative r hr))) := by
  induction xs with
  | nil => exact Iso.refl _
  | cons x xs ih => exact (stateIso negative r hr x).product ih

def sourceStateIso (negative : Bool) (r : ℕ) (hr : 2 ≤ r) :
    Iso (sourceFactor ℚ r hr) (labelTensor (stateLabel negative r hr 1)) :=
  (Iso.ofEq (splitFactor_one negative r hr)).symm.trans (stateIso negative r hr 1)

def resetStateIso (negative : Bool) (r : ℕ) (hr : 2 ≤ r) :
    Iso (resetFactor ℚ negative r hr) (labelTensor (stateLabel negative r hr (3 * r))) :=
  (Iso.ofEq (splitFactor_reset negative r hr)).symm.trans (stateIso negative r hr (3 * r))

def rowInputTensor (negative : Bool) (r : ℕ) (hr : 2 ≤ r) (row : Row r i K) : FullTensor ℚ :=
  (splitFactors ℚ negative r hr (parents row.actions)).product ((resetFactor ℚ negative r hr).power row.Z)

def rowOutputTensor (negative : Bool) (r : ℕ) (hr : 2 ≤ r) (row : Row r i K) : FullTensor ℚ :=
  (splitFactors ℚ negative r hr ((allEdges row.actions).map Edge.dst)).product
    ((sourceFactor ℚ r hr).power row.Z)

def rowInputIso (negative : Bool) (r : ℕ) (hr : 2 ≤ r) (row : Row r i K) :
    Iso (rowInputTensor negative r hr row) (listProduct labelTensor (rowInputLabels negative r hr row)) :=
  ((stateListIso negative r hr _).product
    (((resetStateIso negative r hr).power row.Z).trans (listReplicateIso labelTensor _ _).symm)).trans
      (listAppendIso labelTensor _ _).symm

def rowOutputIso (negative : Bool) (r : ℕ) (hr : 2 ≤ r) (row : Row r i K) :
    Iso (rowOutputTensor negative r hr row) (listProduct labelTensor (rowOutputLabels negative r hr row)) :=
  ((stateListIso negative r hr _).product
    (((sourceStateIso negative r hr).power row.Z).trans (listReplicateIso labelTensor _ _).symm)).trans
      (listAppendIso labelTensor _ _).symm

def topCatalystIso (row : Row r 1 K) (hr : 2 ≤ r) :
    Iso (topConsumed ℚ row hr) (listProduct labelTensor (topCatalystLabels row hr)) :=
  ((stateListIso false r hr _).product
    (((resetStateIso false r hr).power row.Z).trans (listReplicateIso labelTensor _ _).symm)).trans
      (listAppendIso labelTensor _ _).symm

def lowerInputIso (depth : ℕ) (rows : LowerRows K n) :
    Iso (lowerRowsConsumed ℚ depth rows) (listProduct labelTensor (lowerInputLabels depth rows)) := by
  induction rows generalizing depth with
  | nil => exact Iso.refl _
  | @cons n row tail ih =>
      exact ((rowInputIso (rowSign depth) (n + 2) (by omega) row).product (ih (depth + 1))).trans
        (listAppendIso labelTensor _ _).symm

def lowerOutputTensor (depth : ℕ) : {n : ℕ} → LowerRows K n → FullTensor ℚ
  | _, .nil => FullTensor.unit
  | _, .cons row tail => (rowOutputTensor (rowSign depth) _ (by omega) row).product (lowerOutputTensor (depth + 1) tail)

def lowerOutputIso (depth : ℕ) (rows : LowerRows K n) :
    Iso (lowerOutputTensor depth rows) (listProduct labelTensor (lowerOutputLabels depth rows)) := by
  induction rows generalizing depth with
  | nil => exact Iso.refl _
  | @cons n row tail ih =>
      exact ((rowOutputIso (rowSign depth) (n + 2) (by omega) row).product (ih (depth + 1))).trans
        (listAppendIso labelTensor _ _).symm

def familyInputTensor (family : Family n K) : FullTensor ℚ :=
  (rowInputTensor false _ (by omega) family.top).product (lowerRowsConsumed ℚ 1 family.lower)

def familyOutputTensor (family : Family n K) : FullTensor ℚ :=
  (rowOutputTensor false _ (by omega) family.top).product (lowerOutputTensor 1 family.lower)

def familyInputIso (family : Family n K) :
    Iso (familyInputTensor family) (listProduct labelTensor (inputLabels family)) :=
  ((rowInputIso false _ (by omega) family.top).product (lowerInputIso 1 family.lower)).trans
    (listAppendIso labelTensor _ _).symm

def familyOutputIso (family : Family n K) :
    Iso (familyOutputTensor family) (listProduct labelTensor (outputLabels family)) :=
  ((rowOutputIso false _ (by omega) family.top).product (lowerOutputIso 1 family.lower)).trans
    (listAppendIso labelTensor _ _).symm

def familyCatalystIso (family : Family n K) :
    Iso (familyConsumed ℚ family) (listProduct labelTensor (catalystLabels family)) :=
  ((topCatalystIso family.top (by omega)).product (lowerInputIso 1 family.lower)).trans
    (listAppendIso labelTensor _ _).symm

/-- The input factor product is the actual external source and the named catalyst. -/
def inputCommonCatalystIso (family : Family n K) :
    Iso (familyInputTensor family)
      (((sourceFactor ℚ (n + 2) (by omega)).power K).product (familyConsumed ℚ family)) :=
  (familyInputIso family).trans ((listPermIso labelTensor (input_label_catalyst family)).trans
    ((listAppendIso labelTensor _ _).trans
      (((listReplicateIso labelTensor _ _).trans ((sourceStateIso false (n + 2) (by omega)).power K).symm).product
        (familyCatalystIso family).symm)))

def matrixBoundaryPowerIso (K : ℕ) : Iso ((matrixFull 2).power K) (matrixFull (2 ^ K)) where
  x := matrixNestedX 2 K
  y := matrixNestedY 2 K
  z := matrixNestedZ 2 K
  coeff := fun a b c => congrFun (congrFun (congrFun (matrix_nested_power 2 K) a) b) c

/-- The output factor product contains exactly the same named catalyst and T_(2^K). -/
def outputCommonCatalystIso (family : Family n K) :
    Iso (familyOutputTensor family) ((familyConsumed ℚ family).product (matrixFull (2 ^ K))) :=
  (familyOutputIso family).trans ((listPermIso labelTensor (output_label_catalyst family)).trans
    ((listAppendIso labelTensor _ _).trans
      (((familyCatalystIso family).symm).product
        ((listReplicateIso labelTensor none K).trans (matrixBoundaryPowerIso K)))))


/-- Dependent function coordinates for a head and its actual tail. -/
def consPiEquiv {n : ℕ} {A : Fin (n + 1) → Type} {T : Type}
    (e : T ≃ (∀ i : Fin n, A i.succ)) : A 0 × T ≃ (∀ i, A i) where
  toFun := fun x => Fin.cons x.1 (e x.2)
  invFun := fun f => (f 0, e.symm (fun i => f i.succ))
  left_inv := by intro x; simp
  right_inv := by
    intro f
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

def listXCoordinates {L : Type} (A : L → FullTensor ℚ) :
    (xs : List L) → (listProduct A xs).X ≃ (∀ i : Fin xs.length, (A (xs.get i)).X)
  | [] => {
      toFun := fun _ i => Fin.elim0 i
      invFun := fun _ => ()
      left_inv := by intro x; cases x; rfl
      right_inv := by intro f; funext i; exact Fin.elim0 i }
  | a :: xs => by
      change ((A a).X × (listProduct A xs).X) ≃ (∀ i : Fin (xs.length + 1), (A ((a :: xs).get i)).X)
      exact consPiEquiv (A := fun i : Fin (xs.length + 1) => (A ((a :: xs).get i)).X) (listXCoordinates A xs)

def listYCoordinates {L : Type} (A : L → FullTensor ℚ) :
    (xs : List L) → (listProduct A xs).Y ≃ (∀ i : Fin xs.length, (A (xs.get i)).Y)
  | [] => {
      toFun := fun _ i => Fin.elim0 i
      invFun := fun _ => ()
      left_inv := by intro x; cases x; rfl
      right_inv := by intro f; funext i; exact Fin.elim0 i }
  | a :: xs => by
      change ((A a).Y × (listProduct A xs).Y) ≃ (∀ i : Fin (xs.length + 1), (A ((a :: xs).get i)).Y)
      exact consPiEquiv (A := fun i : Fin (xs.length + 1) => (A ((a :: xs).get i)).Y) (listYCoordinates A xs)

def listZCoordinates {L : Type} (A : L → FullTensor ℚ) :
    (xs : List L) → (listProduct A xs).Z ≃ (∀ i : Fin xs.length, (A (xs.get i)).Z)
  | [] => {
      toFun := fun _ i => Fin.elim0 i
      invFun := fun _ => ()
      left_inv := by intro x; cases x; rfl
      right_inv := by intro f; funext i; exact Fin.elim0 i }
  | a :: xs => by
      change ((A a).Z × (listProduct A xs).Z) ≃ (∀ i : Fin (xs.length + 1), (A ((a :: xs).get i)).Z)
      exact consPiEquiv (A := fun i : Fin (xs.length + 1) => (A ((a :: xs).get i)).Z) (listZCoordinates A xs)

theorem list_coordinates_coeff {L : Type} (A : L → FullTensor ℚ) (xs : List L)
    (x : (listProduct A xs).X) (y : (listProduct A xs).Y) (z : (listProduct A xs).Z) :
    (listProduct A xs).tensor x y z =
      ∏ i : Fin xs.length, (A (xs.get i)).tensor
        (listXCoordinates A xs x i) (listYCoordinates A xs y i) (listZCoordinates A xs z i) := by
  induction xs with
  | nil => simp [listProduct, FullTensor.unit]
  | cons a xs ih =>
      change (A a).X × (listProduct A xs).X at x
      change (A a).Y × (listProduct A xs).Y at y
      change (A a).Z × (listProduct A xs).Z at z
      change (A a).tensor x.1 y.1 z.1 * (listProduct A xs).tensor x.2 y.2 z.2 =
        ∏ i : Fin (xs.length + 1), (A ((a :: xs).get i)).tensor
          (Fin.cons (α := fun j : Fin (xs.length + 1) => (A ((a :: xs).get j)).X) x.1 (listXCoordinates A xs x.2) i)
          (Fin.cons (α := fun j : Fin (xs.length + 1) => (A ((a :: xs).get j)).Y) y.1 (listYCoordinates A xs y.2) i)
          (Fin.cons (α := fun j : Fin (xs.length + 1) => (A ((a :: xs).get j)).Z) z.1 (listZCoordinates A xs z.2) i)
      rw [Fin.prod_univ_succ]
      change (A a).tensor x.1 y.1 z.1 * (listProduct A xs).tensor x.2 y.2 z.2 =
        (A a).tensor x.1 y.1 z.1 * ∏ i : Fin xs.length, (A (xs.get i)).tensor
          (listXCoordinates A xs x.2 i) (listYCoordinates A xs y.2 i) (listZCoordinates A xs z.2 i)
      rw [ih]

/-- The assembly API's dependent Fin-list product and the nested named product have identical coefficients. -/
def listFamilyIso {L : Type} (A : L → FullTensor ℚ) (xs : List L) :
    Iso (listProduct A xs) (resourceFamily (fun i : Fin xs.length => A (xs.get i))) where
  x := listXCoordinates A xs
  y := listYCoordinates A xs
  z := listZCoordinates A xs
  coeff := list_coordinates_coeff A xs

/-- Function-coordinate input factors identify with the named source and catalyst. -/
def familyInputResourceIso (family : Family n K) :
    Iso (resourceFamily (fun i : Fin (inputLabels family).length => labelTensor ((inputLabels family).get i)))
      (((sourceFactor ℚ (n + 2) (by omega)).power K).product (familyConsumed ℚ family)) :=
  (listFamilyIso labelTensor (inputLabels family)).symm.trans
    ((familyInputIso family).symm.trans (inputCommonCatalystIso family))

/-- Function-coordinate output factors identify with the same catalyst and complete boundary matrix. -/
def familyOutputResourceIso (family : Family n K) :
    Iso (resourceFamily (fun i : Fin (outputLabels family).length => labelTensor ((outputLabels family).get i)))
      ((familyConsumed ℚ family).product (matrixFull (2 ^ K))) :=
  (listFamilyIso labelTensor (outputLabels family)).symm.trans
    ((familyOutputIso family).symm.trans (outputCommonCatalystIso family))


namespace Iso

theorem tensor_eq {A B : FullTensor ℚ} (p : Iso A B) :
    A.tensor = Tensor.pullback p.x p.y p.z B.tensor := by
  funext a b c
  exact p.coeff a b c

theorem rank_iff {A B : FullTensor ℚ} (p : Iso A B) (R : ℕ) :
    Tensor.RankAtMost A.tensor R ↔ Tensor.RankAtMost B.tensor R :=
  coordinate_rank_iff A.tensor B.tensor p.x p.y p.z p.tensor_eq R

end Iso

/-- Full named input coefficient identity, including every consumed factor. -/
theorem input_common_catalyst_identity (family : Family n K) :
    (familyInputTensor family).tensor = Tensor.pullback
      (inputCommonCatalystIso family).x (inputCommonCatalystIso family).y (inputCommonCatalystIso family).z
      ((((sourceFactor ℚ (n + 2) (by omega)).power K).product (familyConsumed ℚ family)).tensor) :=
  (inputCommonCatalystIso family).tensor_eq

/-- Full named output coefficient identity, with the same catalyst and all boundary matrix coordinates. -/
theorem output_common_catalyst_identity (family : Family n K) :
    (familyOutputTensor family).tensor = Tensor.pullback
      (outputCommonCatalystIso family).x (outputCommonCatalystIso family).y (outputCommonCatalystIso family).z
      (((familyConsumed ℚ family).product (matrixFull (2 ^ K))).tensor) :=
  (outputCommonCatalystIso family).tensor_eq

/-- Input interface on the assembly bridge's actual dependent finite-family coordinates. -/
theorem family_input_resource_identity (family : Family n K) :
    (resourceFamily (fun i : Fin (inputLabels family).length => labelTensor ((inputLabels family).get i))).tensor =
      Tensor.pullback (familyInputResourceIso family).x (familyInputResourceIso family).y (familyInputResourceIso family).z
        ((((sourceFactor ℚ (n + 2) (by omega)).power K).product (familyConsumed ℚ family)).tensor) :=
  (familyInputResourceIso family).tensor_eq

/-- Output interface on the assembly bridge's actual dependent finite-family coordinates. -/
theorem family_output_resource_identity (family : Family n K) :
    (resourceFamily (fun i : Fin (outputLabels family).length => labelTensor ((outputLabels family).get i))).tensor =
      Tensor.pullback (familyOutputResourceIso family).x (familyOutputResourceIso family).y (familyOutputResourceIso family).z
        (((familyConsumed ℚ family).product (matrixFull (2 ^ K))).tensor) :=
  (familyOutputResourceIso family).tensor_eq

end
end MatrixDimensionAudit.SignedCatalystLedgerBridge
