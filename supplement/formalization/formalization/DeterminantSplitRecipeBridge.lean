import formalization.DeterminantTensorBridge
import formalization.DependentSeparatorBridge
import Mathlib.Algebra.MvPolynomial.Coeff

/-! Exact split-sector counts and dependent separator composition. -/
namespace MatrixDimensionAudit.DeterminantSplitRecipeBridge
open OAI.MatrixMultiplication.Foundation
open DeterminantTensorBridge DependentSeparator SeparatorTensor
open scoped BigOperators
noncomputable section

instance wordFintype (h n : ℕ) (counts : Fin (h + 1) → ℕ) :
    Fintype (Word h n counts) := by
  classical
  unfold Word
  infer_instance

def wordCount (h n : ℕ) (counts : Fin (h + 1) → ℕ) : ℕ := Fintype.card (Word h n counts)

def countExponent {h : ℕ} (counts : Fin (h + 1) → ℕ) : Fin (h + 1) →₀ ℕ :=
  Finsupp.ofSupportFinite counts (Set.toFinite _)

@[simp] theorem countExponent_apply {h : ℕ} (counts : Fin (h + 1) → ℕ) (j : Fin (h + 1)) :
    countExponent counts j = counts j := rfl

def wordExponent {h n : ℕ} (w : Fin n → Fin (h + 1)) : Fin (h + 1) →₀ ℕ :=
  ∑ i, Finsupp.single (w i) 1

theorem wordExponent_apply {h n : ℕ} (w : Fin n → Fin (h + 1)) (j : Fin (h + 1)) :
    wordExponent w j = histogram w j := by
  simp [wordExponent, histogram, Finsupp.single_apply]

theorem wordExponent_eq {h n : ℕ} (w : Fin n → Fin (h + 1)) (counts : Fin (h + 1) → ℕ) :
    wordExponent w = countExponent counts ↔ histogram w = counts := by
  constructor
  · intro he; funext j
    simpa only [wordExponent_apply, countExponent_apply] using congrArg (fun f => f j) he
  · intro he; ext j
    simp only [wordExponent_apply, countExponent_apply, he]

/-- Every word contributes exactly its histogram monomial to the universal expansion. -/
theorem word_monomial {h n : ℕ} (w : Fin n → Fin (h + 1)) :
    (∏ i, (MvPolynomial.X (w i) : MvPolynomial (Fin (h + 1)) ℕ)) =
      MvPolynomial.monomial (wordExponent w) 1 := by
  rw [wordExponent, MvPolynomial.monomial_sum_one]
  simp [MvPolynomial.X]

/-- Exact cardinality of the actual word subtype, including impossible count profiles. -/
theorem wordCount_multinomial (h n : ℕ) (counts : Fin (h + 1) → ℕ) :
    wordCount h n counts =
      if ∑ j, counts j = n then Nat.multinomial Finset.univ counts else 0 := by
  let P := MvPolynomial (Fin (h + 1)) ℕ
  have hp : (∑ j, (MvPolynomial.X j : P)) ^ n =
      ∑ w : Fin n → Fin (h + 1), MvPolynomial.monomial (wordExponent w) 1 := by
    calc
      _ = ∏ _i : Fin n, ∑ j, (MvPolynomial.X j : P) := by simp
      _ = ∑ w : Fin n → Fin (h + 1), ∏ i, MvPolynomial.X (w i) := Fintype.prod_sum _
      _ = _ := by simp only [word_monomial]
  have hcoeff := congrArg (fun p : P => p.coeff (countExponent counts)) hp
  rw [MvPolynomial.coeff_sum_X_pow_of_fintype] at hcoeff
  have hs : (countExponent counts).sum (fun _ m => m) = ∑ j, counts j := by
    rw [Finsupp.sum_fintype _ _ (by simp)]
    rfl
  have hm : (countExponent counts).multinomial = Nat.multinomial Finset.univ counts := by
    rw [Finsupp.multinomial_eq_of_support_subset (Finset.subset_univ _)]
    rfl
  rw [hs, hm] at hcoeff
  have hw : (∑ w : Fin n → Fin (h + 1),
      (MvPolynomial.monomial (wordExponent w) 1 : P).coeff (countExponent counts)) =
      wordCount h n counts := by
    simp only [MvPolynomial.coeff_monomial, wordExponent_eq]
    rw [Finset.sum_boole]
    simpa only [Nat.cast_id, wordCount, Word] using
      (Fintype.card_subtype (fun w => histogram w = counts)).symm
  simpa only [MvPolynomial.coeff_sum, hw, Nat.cast_id] using hcoeff.symm

/-- The manuscript's factorial quotient counts all retained sectors exactly. -/
theorem wordCount_factorial (h n : ℕ) (counts : Fin (h + 1) → ℕ) (hs : ∑ j, counts j = n) :
    wordCount h n counts = n.factorial / ∏ j, (counts j).factorial := by
  rw [wordCount_multinomial, ite_eq_left hs, Nat.multinomial, hs]


/-- Enumeration of every actual retained depth word. -/
def wordEnumeration (h n : ℕ) (counts : Fin (h + 1) → ℕ) :
    Fin (wordCount h n counts) ≃ Word h n counts :=
  (Fintype.equivFin (Word h n counts)).symm

abbrev blockY (c h n : ℕ) (counts : Fin (h + 1) → ℕ) (j : Fin (wordCount h n counts)) :=
  sectorInput c h n counts (wordEnumeration h n counts j)

abbrev blockZ (r c h n : ℕ) (counts : Fin (h + 1) → ℕ) (j : Fin (wordCount h n counts)) :=
  sectorOutput r c h n counts (wordEnumeration h n counts j)

instance blockYFinite (c h n : ℕ) (counts : Fin (h + 1) → ℕ) (j : Fin (wordCount h n counts)) :
    Fintype (blockY c h n counts j) := by unfold blockY sectorInput; infer_instance

instance blockZFinite (r c h n : ℕ) (counts : Fin (h + 1) → ℕ) (j : Fin (wordCount h n counts)) :
    Fintype (blockZ r c h n counts j) := by unfold blockZ sectorOutput; infer_instance

/-- Child factors remain in their actual tensor positions while X is shared. -/
def blocks (r c h n : ℕ) (counts : Fin (h + 1) → ℕ) (j : Fin (wordCount h n counts)) :
    Tensor ℚ (Fin n → Fin r) (blockY c h n counts j) (blockZ r c h n counts j) :=
  fun x y z => ∏ i, TensorRankBridge.convolution ℚ r
    (c + h - 2 * ((wordEnumeration h n counts j).val i).val) (x i) (y i) (z i)

def keptEmbeddingY (c h n : ℕ) (counts : Fin (h + 1) → ℕ) :
    Sigma (blockY c h n counts) → keptInput c h n counts :=
  fun y => sectorEmbeddingInput c h n counts (wordEnumeration h n counts y.1) y.2

def keptEmbeddingZ (r c h n : ℕ) (hr : 0 < r) (hc : h + 1 ≤ c) (counts : Fin (h + 1) → ℕ) :
    Sigma (blockZ r c h n counts) → keptOutput r c h n counts :=
  fun z => sectorEmbeddingOutput r c h n hr hc counts (wordEnumeration h n counts z.1) z.2

/-- All diagonal sectors and all cross-sector zeros are identified with the
actual kept tensor, leaving its first leg unchanged. -/
theorem matched_from_kept (r c h n : ℕ) (hr : 0 < r) (hc : h + 1 ≤ c)
    (counts : Fin (h + 1) → ℕ) :
    dependentMatched (blocks r c h n counts) = Tensor.pullback id
      (keptEmbeddingY c h n counts) (keptEmbeddingZ r c h n hr hc counts)
      (restricted ℚ r c h n hc (by omega) counts) := by
  funext x sy sz
  rcases sy with ⟨j, y⟩
  rcases sz with ⟨k, z⟩
  by_cases hjk : j = k
  · subst k
    rw [dependentMatched_same]
    exact (sector_tensor_identity ℚ r c h n hr hc counts
      (wordEnumeration h n counts j) x y z).symm
  · have hw : inputWord (keptEmbeddingY c h n counts ⟨j, y⟩).val ≠
        inputWord (keptEmbeddingZ r c h n hr hc counts ⟨k, z⟩).val := by
      intro he
      have hew : wordEnumeration h n counts j = wordEnumeration h n counts k := Subtype.ext he
      exact hjk ((wordEnumeration h n counts).injective hew)
    simp only [dependentMatched, hjk, dite_false, Tensor.pullback, id_eq]
    rw [restricted_block_diagonal, ite_eq_right hw]

/-- An actual source-power decomposition bounds the dependent matched sum with
no extra sector-count factor. -/
theorem matched_source_rank (r c h n R : ℕ) (hr : 0 < r) (hc : h + 1 ≤ c)
    (counts : Fin (h + 1) → ℕ)
    (hs : Tensor.RankAtMost (Tensor.power (source ℚ r c h) n) R) :
    Tensor.RankAtMost (dependentMatched (blocks r c h n counts)) R := by
  have hk : Tensor.RankAtMost (restricted ℚ r c h n hc (by omega) counts) R := by
    rw [restricted_eq_source_restrict]
    exact hs.restrict _ _ _
  rw [matched_from_kept r c h n hr hc counts]
  exact hk.pullback id _ _

/-- The exact separator is charged to the actual source-power decomposition. -/
theorem source_separator_power_rank (r c h n aux k R : ℕ) (hr : 0 < r) (hc : h + 1 ≤ c)
    (counts : Fin (h + 1) → ℕ)
    (hs : Tensor.RankAtMost (Tensor.power (source ℚ r c h) n) R) :
    Tensor.RankAtMost (Tensor.power (dependentTarget (n := aux) (blocks r c h n counts)) k)
      ((k * min (wordCount h n counts - 1) (aux - 1) + 1) *
        (SeparatorTensor.ell (wordCount h n counts) aux * R) ^ k) := by
  classical
  exact dependent_power_rank (blocks r c h n counts) k R
    (matched_source_rank r c h n R hr hc counts hs)


def rawEmbeddingY (c h n : ℕ) (counts : Fin (h + 1) → ℕ) :
    ((w : Word h n counts) × sectorInput c h n counts w) → keptInput c h n counts :=
  fun y => sectorEmbeddingInput c h n counts y.1 y.2

def rawEmbeddingZ (r c h n : ℕ) (hr : 0 < r) (hc : h + 1 ≤ c) (counts : Fin (h + 1) → ℕ) :
    ((w : Word h n counts) × sectorOutput r c h n counts w) → keptOutput r c h n counts :=
  fun z => sectorEmbeddingOutput r c h n hr hc counts z.1 z.2

theorem rawEmbeddingY_bijective (c h n : ℕ) (counts : Fin (h + 1) → ℕ) :
    Function.Bijective (rawEmbeddingY c h n counts) := by
  constructor
  · intro sy sz he
    rcases sy with ⟨w, y⟩
    rcases sz with ⟨v, z⟩
    have hw : w = v := Subtype.ext
      (congrArg (fun p : keptInput c h n counts => inputWord p.val) he)
    subst v
    have hy : y = z := by
      funext i
      apply Fin.ext
      exact congrArg (fun p : keptInput c h n counts => (p.val i).2.val) he
    subst z
    rfl
  · intro y
    obtain ⟨w, v, hv⟩ := sectorEmbeddingInput_covers c h n counts y
    exact ⟨⟨w, v⟩, hv⟩

theorem rawEmbeddingZ_bijective (r c h n : ℕ) (hr : 0 < r) (hc : h + 1 ≤ c)
    (counts : Fin (h + 1) → ℕ) : Function.Bijective (rawEmbeddingZ r c h n hr hc counts) := by
  constructor
  · intro sy sz he
    rcases sy with ⟨w, y⟩
    rcases sz with ⟨v, z⟩
    have hw : w = v := Subtype.ext
      (congrArg (fun p : keptOutput r c h n counts => inputWord p.val) he)
    subst v
    have hy : y = z := by
      funext i
      apply Fin.ext
      exact congrArg (fun p : keptOutput r c h n counts => (p.val i).2.val) he
    subst z
    rfl
  · intro z
    obtain ⟨w, v, hv⟩ := sectorEmbeddingOutput_covers r c h n hr hc counts z
    exact ⟨⟨w, v⟩, hv⟩

def keptEquivY (c h n : ℕ) (counts : Fin (h + 1) → ℕ) :
    Sigma (blockY c h n counts) ≃ keptInput c h n counts :=
  (Equiv.sigmaCongrLeft (wordEnumeration h n counts)).trans
    (Equiv.ofBijective (rawEmbeddingY c h n counts) (rawEmbeddingY_bijective c h n counts))

def keptEquivZ (r c h n : ℕ) (hr : 0 < r) (hc : h + 1 ≤ c) (counts : Fin (h + 1) → ℕ) :
    Sigma (blockZ r c h n counts) ≃ keptOutput r c h n counts :=
  (Equiv.sigmaCongrLeft (wordEnumeration h n counts)).trans
    (Equiv.ofBijective (rawEmbeddingZ r c h n hr hc counts) (rawEmbeddingZ_bijective r c h n hr hc counts))

theorem keptEmbeddingY_bijective (c h n : ℕ) (counts : Fin (h + 1) → ℕ) :
    Function.Bijective (keptEmbeddingY c h n counts) := (keptEquivY c h n counts).bijective

theorem keptEmbeddingZ_bijective (r c h n : ℕ) (hr : 0 < r) (hc : h + 1 ≤ c)
    (counts : Fin (h + 1) → ℕ) : Function.Bijective (keptEmbeddingZ r c h n hr hc counts) :=
  (keptEquivZ r c h n hr hc counts).bijective


/-- Canonical grouped positions, without selecting a first-leg permutation before separation. -/
def GroupedPosition {h : ℕ} (counts : Fin (h + 1) → ℕ) := (j : Fin (h + 1)) × Fin (counts j)

instance groupedPositionFintype {h : ℕ} (counts : Fin (h + 1) → ℕ) : Fintype (GroupedPosition counts) := by
  unfold GroupedPosition
  infer_instance

def PositionFiber {h n : ℕ} {counts : Fin (h + 1) → ℕ} (w : Word h n counts) (j : Fin (h + 1)) :=
  {i : Fin n // w.val i = j}

instance positionFiberFintype {h n : ℕ} {counts : Fin (h + 1) → ℕ} (w : Word h n counts) (j : Fin (h + 1)) :
    Fintype (PositionFiber w j) := by
  classical
  unfold PositionFiber
  infer_instance

theorem positionFiber_card {h n : ℕ} {counts : Fin (h + 1) → ℕ} (w : Word h n counts) (j : Fin (h + 1)) :
    Fintype.card (PositionFiber w j) = counts j := by
  unfold PositionFiber
  rw [Fintype.card_subtype, ← histogram_card]
  exact congrFun w.property j

def positionFiberEquiv {h n : ℕ} {counts : Fin (h + 1) → ℕ} (w : Word h n counts) (j : Fin (h + 1)) :
    Fin (counts j) ≃ PositionFiber w j :=
  (finCongr (positionFiber_card w j).symm).trans (Fintype.equivFin (PositionFiber w j)).symm

/-- Every word has a depth-preserving bijection from grouped positions. -/
def positionEquiv {h n : ℕ} {counts : Fin (h + 1) → ℕ} (w : Word h n counts) : GroupedPosition counts ≃ Fin n :=
  (Equiv.sigmaCongrRight (positionFiberEquiv w)).trans (Equiv.sigmaFiberEquiv w.val)

theorem positionEquiv_depth {h n : ℕ} {counts : Fin (h + 1) → ℕ} (w : Word h n counts) (p : GroupedPosition counts) :
    w.val (positionEquiv w p) = p.1 :=
  (positionFiberEquiv w p.1 p.2).property

theorem positionEquiv_symm_depth {h n : ℕ} {counts : Fin (h + 1) → ℕ} (w : Word h n counts) (i : Fin n) :
    ((positionEquiv w).symm i).1 = w.val i := by
  have he := positionEquiv_depth w ((positionEquiv w).symm i)
  rw [Equiv.apply_symm_apply] at he
  exact he.symm

def groupedX {h : ℕ} (r : ℕ) (counts : Fin (h + 1) → ℕ) := GroupedPosition counts → Fin r

def groupedY (c h : ℕ) (counts : Fin (h + 1) → ℕ) :=
  (p : GroupedPosition counts) → Fin (c + h - 2 * p.1.val)

def groupedZ (r c h : ℕ) (counts : Fin (h + 1) → ℕ) :=
  (p : GroupedPosition counts) → Fin (r + (c + h - 2 * p.1.val) - 1)

def ungroupX {h n : ℕ} {counts : Fin (h + 1) → ℕ} (r : ℕ) (w : Word h n counts) (x : groupedX r counts) : Fin n → Fin r :=
  fun i => x ((positionEquiv w).symm i)

def ungroupY {n : ℕ} (c h : ℕ) {counts : Fin (h + 1) → ℕ} (w : Word h n counts) (y : groupedY c h counts) :
    sectorInput c h n counts w := fun i =>
  ⟨(y ((positionEquiv w).symm i)).val, by
    have hy := (y ((positionEquiv w).symm i)).isLt
    have he := congrArg Fin.val (positionEquiv_symm_depth w i)
    omega⟩

def ungroupZ {n : ℕ} (r c h : ℕ) {counts : Fin (h + 1) → ℕ} (w : Word h n counts) (z : groupedZ r c h counts) :
    sectorOutput r c h n counts w := fun i =>
  ⟨(z ((positionEquiv w).symm i)).val, by
    have hz := (z ((positionEquiv w).symm i)).isLt
    have he := congrArg Fin.val (positionEquiv_symm_depth w i)
    omega⟩

/-- The canonical child keeps one group for every depth, with exactly counts(j) positions. -/
def groupedChild (r c h : ℕ) (counts : Fin (h + 1) → ℕ) :
    Tensor ℚ (groupedX r counts) (groupedY c h counts) (groupedZ r c h counts) :=
  fun x y z => ∏ p, TensorRankBridge.convolution ℚ r (c + h - 2 * p.1.val) (x p) (y p) (z p)

theorem grouped_child_identity (r c h n : ℕ) (counts : Fin (h + 1) → ℕ)
    (j : Fin (wordCount h n counts))
    (x : groupedX r counts) (y : groupedY c h counts) (z : groupedZ r c h counts) :
    blocks r c h n counts j
      (ungroupX r (wordEnumeration h n counts j) x)
      (ungroupY c h (wordEnumeration h n counts j) y)
      (ungroupZ r c h (wordEnumeration h n counts j) z) = groupedChild r c h counts x y z := by
  unfold blocks groupedChild
  simp only [TensorRankBridge.convolution, ungroupX, ungroupY, ungroupZ]
  exact (positionEquiv (wordEnumeration h n counts j)).symm.prod_comp
    (fun p : GroupedPosition counts => if (x p).val + (y p).val = (z p).val then (1 : ℚ) else 0)


/-- Grouped child coefficients are ordered first by depth, then by its occurrence. -/
theorem groupedChild_depth_product (r c h : ℕ) (counts : Fin (h + 1) → ℕ)
    (x : groupedX r counts) (y : groupedY c h counts) (z : groupedZ r c h counts) :
    groupedChild r c h counts x y z =
      ∏ j, ∏ i : Fin (counts j), TensorRankBridge.convolution ℚ r
        (c + h - 2 * j.val) (x ⟨j, i⟩) (y ⟨j, i⟩) (z ⟨j, i⟩) := by
  exact Fintype.prod_sigma _

def auxiliaryDot (aux : ℕ) : Tensor ℚ Unit (Fin aux) (Fin aux) :=
  fun _ a b => if a = b then 1 else 0

def groupedOutput (r c h n aux : ℕ) (counts : Fin (h + 1) → ℕ) :=
  Tensor.directSum (fun _ : Fin (wordCount h n counts) =>
    Tensor.product (groupedChild r c h counts) (auxiliaryDot aux))

/-- This first-leg permutation is applied only to the separated tensor, where
its word label is an independent first-leg coordinate. -/
def normalizeX (r h n : ℕ) (counts : Fin (h + 1) → ℕ) :
    (Fin (wordCount h n counts) × (groupedX r counts × Unit)) →
      (Fin (wordCount h n counts) × (Fin n → Fin r)) :=
  fun x => (x.1, ungroupX r (wordEnumeration h n counts x.1) x.2.1)

def normalizeY (c h n aux : ℕ) (counts : Fin (h + 1) → ℕ) :
    (Fin (wordCount h n counts) × (groupedY c h counts × Fin aux)) →
      (Fin aux × Sigma (blockY c h n counts)) :=
  fun y => (y.2.2, ⟨y.1, ungroupY c h (wordEnumeration h n counts y.1) y.2.1⟩)

def normalizeZ (r c h n aux : ℕ) (counts : Fin (h + 1) → ℕ) :
    (Fin (wordCount h n counts) × (groupedZ r c h counts × Fin aux)) →
      (Fin aux × Sigma (blockZ r c h n counts)) :=
  fun z => (z.2.2, ⟨z.1, ungroupZ r c h (wordEnumeration h n counts z.1) z.2.1⟩)

/-- Full direct-sum identity after separation, including unmatched-sector zeros. -/
theorem normalized_separator_identity (r c h n aux : ℕ) (counts : Fin (h + 1) → ℕ) :
    Tensor.pullback (normalizeX r h n counts) (normalizeY c h n aux counts)
      (normalizeZ r c h n aux counts)
      (dependentTarget (n := aux) (blocks r c h n counts)) = groupedOutput r c h n aux counts := by
  funext x y z
  rcases x with ⟨j, x, u⟩
  rcases y with ⟨k, y, a⟩
  rcases z with ⟨l, z, b⟩
  change dependentTarget (n := aux) (blocks r c h n counts)
      (j, ungroupX r (wordEnumeration h n counts j) x)
      (a, ⟨k, ungroupY c h (wordEnumeration h n counts k) y⟩)
      (b, ⟨l, ungroupZ r c h (wordEnumeration h n counts l) z⟩) =
    if j = k ∧ j = l then
      groupedChild r c h counts x y z * (if a = b then 1 else 0) else 0
  by_cases hjk : j = k <;> by_cases hjl : j = l
  · subst k
    subst l
    rw [dependentTarget_same, grouped_child_identity]
    by_cases hab : a = b <;> simp [hab]
  · subst k
    simp [dependentTarget, hjl]
  · subst l
    simp [dependentTarget, hjk]
  · simp [dependentTarget, hjk, hjl]

/-- Concrete split recipe from one actual source-power rank certificate. Word
positions are grouped only after the separator frees the first legs. -/
theorem actual_split_recipe (r c h n aux k R : ℕ) (hr : 0 < r) (hc : h + 1 ≤ c)
    (counts : Fin (h + 1) → ℕ)
    (hs : Tensor.RankAtMost (Tensor.power (source ℚ r c h) n) R) :
    Tensor.RankAtMost (Tensor.power (groupedOutput r c h n aux counts) k)
      ((k * min (wordCount h n counts - 1) (aux - 1) + 1) *
        (SeparatorTensor.ell (wordCount h n counts) aux * R) ^ k) := by
  classical
  have hp := source_separator_power_rank r c h n aux k R hr hc counts hs
  have hn := hp.pullback
    (fun (x : Fin k → (Fin (wordCount h n counts) × (groupedX r counts × Unit))) i =>
      normalizeX r h n counts (x i))
    (fun (y : Fin k → (Fin (wordCount h n counts) × (groupedY c h counts × Fin aux))) i =>
      normalizeY c h n aux counts (y i))
    (fun (z : Fin k → (Fin (wordCount h n counts) × (groupedZ r c h counts × Fin aux))) i =>
      normalizeZ r c h n aux counts (z i))
  change Tensor.RankAtMost (Tensor.power
    (Tensor.pullback (normalizeX r h n counts) (normalizeY c h n aux counts)
      (normalizeZ r c h n aux counts) (dependentTarget (n := aux) (blocks r c h n counts))) k)
    _ at hn
  rw [normalized_separator_identity] at hn
  exact hn

end
end MatrixDimensionAudit.DeterminantSplitRecipeBridge
