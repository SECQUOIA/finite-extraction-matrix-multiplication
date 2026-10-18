import formalization.DeterminantSplitRecipeBridge
import formalization.TriplingLocalSourceBridge

/-! A joint cyclic split recipe preserving one source-rank certificate. -/
namespace MatrixDimensionAudit.DeterminantCyclicRecipeBridge
open OAI.MatrixMultiplication.Foundation
open DeterminantTensorBridge DeterminantSplitRecipeBridge
open TriplingRestrictionBridge TriplingLocalSourceBridge
open DependentSeparator SeparatorTensor TensorRankBridge
open scoped BigOperators
noncomputable section

abbrev SepX (r h N : ℕ) (counts : Fin (h + 1) → ℕ) :=
  Fin (wordCount h N counts) × (Fin N → Fin r)
abbrev SepY (c h N aux : ℕ) (counts : Fin (h + 1) → ℕ) :=
  Fin aux × Sigma (blockY c h N counts)
abbrev SepZ (r c h N aux : ℕ) (counts : Fin (h + 1) → ℕ) :=
  Fin aux × Sigma (blockZ r c h N counts)

def separated (r c h N aux : ℕ) (counts : Fin (h + 1) → ℕ) :=
  dependentTarget (n := aux) (blocks r c h N counts)

def localDegree (h N aux : ℕ) (counts : Fin (h + 1) → ℕ) :=
  min (wordCount h N counts - 1) (aux - 1)

def jointFamily (r c h N aux : ℕ) (counts : Fin (h + 1) → ℕ) :=
  let P := dependentFamily (n := aux) (blocks r c h N counts)
  Tensor.product (Tensor.product P (Tensor.cyclic P)) (Tensor.cyclic (Tensor.cyclic P))

theorem jointFamily_degree (r c h N aux : ℕ) (counts : Fin (h + 1) → ℕ)
    (x : (SepX r h N counts × SepY c h N aux counts) × SepZ r c h N aux counts)
    (y : (SepY c h N aux counts × SepZ r c h N aux counts) × SepX r h N counts)
    (z : (SepZ r c h N aux counts × SepX r h N counts) × SepY c h N aux counts) :
    (jointFamily r c h N aux counts x y z).natDegree ≤ 3 * localDegree h N aux counts := by
  let P := dependentFamily (n := aux) (blocks r c h N counts)
  have hd : ∀ x y z, (P x y z).natDegree ≤ localDegree h N aux counts := dependent_degree _
  have hd' : ∀ x y z, (Tensor.cyclic P x y z).natDegree ≤ localDegree h N aux counts :=
    fun x y z => hd z x y
  have hd'' : ∀ x y z, (Tensor.cyclic (Tensor.cyclic P) x y z).natDegree ≤
      localDegree h N aux counts := fun x y z => hd y z x
  have he := tensor_product_degree (Tensor.product P (Tensor.cyclic P))
    (Tensor.cyclic (Tensor.cyclic P)) (localDegree h N aux counts + localDegree h N aux counts)
    (localDegree h N aux counts) (tensor_product_degree P (Tensor.cyclic P) _ _ hd hd') hd'' x y z
  exact he.trans (by omega)

theorem jointFamily_evaluate (r c h N aux : ℕ) (counts : Fin (h + 1) → ℕ) (ε : ℚ) :
    evaluate (jointFamily r c h N aux counts) ε =
      cyclicTriple ℚ (evaluate (dependentFamily (n := aux) (blocks r c h N counts)) ε) := by
  funext x y z
  simp only [evaluate, jointFamily, cyclicTriple, Tensor.product, Tensor.cyclic, Polynomial.eval_mul]

theorem jointFamily_constant (r c h N aux : ℕ) (counts : Fin (h + 1) → ℕ) :
    evaluate (jointFamily r c h N aux counts) 0 = cyclicTriple ℚ (separated r c h N aux counts) := by
  rw [jointFamily_evaluate, dependent_constant]
  rfl

def sourceA (r N : ℕ) : (Fin N → Fin r) → (Fin N → Fin r) → ℚ :=
  fun x' x => if x = x' then 1 else 0

def sourceB (_r c h N : ℕ) (counts : Fin (h + 1) → ℕ) :
    Sigma (blockY c h N counts) → (Fin N → DeterminantBasisBridge.MonomialIndex c h) → ℚ :=
  fun y m => ∏ i, (DeterminantBasisBridge.coordinateMatrix c h (m i)
    ((keptEmbeddingY c h N counts y).val i) : ℚ)

def sourceC (r c h N : ℕ) (hr : 0 < r) (hc : h + 1 ≤ c) (counts : Fin (h + 1) → ℕ) :
    Sigma (blockZ r c h N counts) →
      (Fin N → DeterminantBasisBridge.MonomialIndex (r + c - 1) h) → ℚ :=
  fun z m => ∏ i, (DeterminantBasisBridge.expansionMatrix (r + c - 1) h (by omega)
    ((keptEmbeddingZ r c h N hr hc counts z).val i) (m i) : ℚ)

theorem matched_restriction (r c h N : ℕ) (hr : 0 < r) (hc : h + 1 ≤ c)
    (counts : Fin (h + 1) → ℕ) :
    Tensor.restrict (sourceA r N) (sourceB r c h N counts) (sourceC r c h N hr hc counts)
      (Tensor.power (DeterminantTensorBridge.source ℚ r c h) N) =
      dependentMatched (blocks r c h N counts) := by
  rw [matched_from_kept r c h N hr hc counts, restricted_eq_source_restrict]
  rfl

/-- All three orientations act on the same source decomposition; its rank is not cubed. -/
theorem matched_cyclic_rank (r c h N R : ℕ) (hr : 0 < r) (hc : h + 1 ≤ c)
    (counts : Fin (h + 1) → ℕ)
    (hs : Tensor.RankAtMost (cyclicTriple ℚ (Tensor.power (DeterminantTensorBridge.source ℚ r c h) N)) R) :
    Tensor.RankAtMost (cyclicTriple ℚ (dependentMatched (blocks r c h N counts))) R := by
  let A := sourceA r N
  let B := sourceB r c h N counts
  let C := sourceC r c h N hr hc counts
  have hp := hs.restrict (tripleMatrix A B C) (tripleMatrix B C A) (tripleMatrix C A B)
  rw [triple_restrict, matched_restriction r c h N hr hc counts] at hp
  exact hp

/-- A joint sample costs ell³ source copies, while retaining one original rank R. -/
theorem joint_sample_rank (r c h N aux R : ℕ) (hr : 0 < r) (hc : h + 1 ≤ c)
    (counts : Fin (h + 1) → ℕ) (ε : ℚ) (hε : ε ≠ 0)
    (hs : Tensor.RankAtMost (cyclicTriple ℚ (Tensor.power (DeterminantTensorBridge.source ℚ r c h) N)) R) :
    Tensor.RankAtMost (evaluate (jointFamily r c h N aux counts) ε)
      (ell (wordCount h N counts) aux ^ 3 * R) := by
  classical
  let T := dependentMatched (blocks r c h N counts)
  let S := Tensor.directSum (fun _ : Fin (ell (wordCount h N counts) aux) => T)
  let A := liftMatrix (firstCardinal (wordCount h N counts) aux (X := Fin N → Fin r))
  let B := liftMatrix (dependentSecond (n := aux) (Y := blockY c h N counts) ε)
  let C := liftMatrix (dependentThird (n := aux) (Z := blockZ r c h N counts) ε)
  have hrank := cyclic_copy_rank T (ell (wordCount h N counts) aux) R
    (matched_cyclic_rank r c h N R hr hc counts hs)
  have hp := hrank.restrict (tripleMatrix A B C) (tripleMatrix B C A) (tripleMatrix C A B)
  rw [triple_restrict] at hp
  have he : Tensor.restrict A B C S =
      evaluate (dependentFamily (n := aux) (blocks r c h N counts)) ε :=
    dependent_restriction _ ε hε
  rw [he] at hp
  rw [jointFamily_evaluate]
  exact hp

/-- One shared interpolation parameter yields E=3kd+1, before the output reindexing. -/
theorem separated_cyclic_power_rank (r c h N aux k R : ℕ) (hr : 0 < r) (hc : h + 1 ≤ c)
    (counts : Fin (h + 1) → ℕ)
    (hs : Tensor.RankAtMost (cyclicTriple ℚ (Tensor.power (DeterminantTensorBridge.source ℚ r c h) N)) R) :
    Tensor.RankAtMost (Tensor.power (cyclicTriple ℚ (separated r c h N aux counts)) k)
      ((3 * k * localDegree h N aux counts + 1) * ell (wordCount h N counts) aux ^ (3 * k) * R ^ k) := by
  classical
  rw [← jointFamily_constant r c h N aux counts]
  have hp := tensor_power_exactification_rank (jointFamily r c h N aux counts) k
    (3 * localDegree h N aux counts) (ell (wordCount h N counts) aux ^ 3 * R)
    (jointFamily_degree r c h N aux counts)
    (fun e => joint_sample_rank r c h N aux R hr hc counts (node e)
      (Separator.rationalNode_nonzero e.val) hs)
  convert hp using 1
  simp only [mul_pow, ← pow_mul]
  ring


abbrev Index (h N : ℕ) (counts : Fin (h + 1) → ℕ) :=
  (Fin (wordCount h N counts) × Fin (wordCount h N counts)) × Fin (wordCount h N counts)

def scatterCopies {L : ℕ} {X Y Z : Type} :
    (((Fin L × Fin L) × Fin L) × ((X × Y) × Z)) →
      (((Fin L × X) × (Fin L × Y)) × (Fin L × Z)) :=
  fun q => (((q.1.1.1, q.2.1.1), (q.1.1.2, q.2.1.2)), (q.1.2, q.2.2))

/-- The cyclic product retains every triple of independently chosen sector labels. -/
theorem scatter_cyclic_copies {X Y Z : Type} (T : Tensor ℚ X Y Z) (L : ℕ) :
    Tensor.pullback scatterCopies scatterCopies scatterCopies
      (cyclicTriple ℚ (Tensor.directSum (fun _ : Fin L => T))) =
      Tensor.directSum (fun _ : (Fin L × Fin L) × Fin L => cyclicTriple ℚ T) := by
  rw [cyclic_copy_sum]
  rfl

def matrixAux (aux : ℕ) : Tensor ℚ (Fin aux × Fin aux) (Fin aux × Fin aux) (Fin aux × Fin aux) := Tensor.matrixCoefficients (Fin aux) (Fin aux) (Fin aux)

def dotX {X Y Z : Type} {aux : ℕ} :
    (((X × Y) × Z) × (Fin aux × Fin aux)) →
      (((X × Unit) × (Y × Fin aux)) × (Z × Fin aux)) :=
  fun q => (((q.1.1.1, ()), (q.1.1.2, q.2.2)), (q.1.2, q.2.1))

def dotY {X Y Z : Type} {aux : ℕ} :
    (((Y × Z) × X) × (Fin aux × Fin aux)) →
      (((Y × Fin aux) × (Z × Fin aux)) × (X × Unit)) :=
  fun q => (((q.1.1.1, q.2.2), (q.1.1.2, q.2.1)), (q.1.2, ()))

def dotZ {X Y Z : Type} {aux : ℕ} :
    (((Z × X) × Y) × (Fin aux × Fin aux)) →
      (((Z × Fin aux) × (X × Unit)) × (Y × Fin aux)) :=
  fun q => (((q.1.1.1, q.2.1), (q.1.1.2, ())), (q.1.2, q.2.2))

/-- Three cyclic dot factors are the complete matrix multiplication tensor. -/
theorem cyclic_dot_matrix {X Y Z : Type} (T : Tensor ℚ X Y Z) (aux : ℕ) :
    Tensor.pullback dotX dotY dotZ (cyclicTriple ℚ (Tensor.product T (auxiliaryDot aux))) =
      Tensor.product (cyclicTriple ℚ T) (matrixAux aux) := by
  funext x y z
  by_cases hxy : x.2.2 = y.2.1 <;> by_cases hyz : y.2.2 = z.2.1 <;>
    by_cases hzx : z.2.2 = x.2.1 <;>
    simp [Tensor.pullback, cyclicTriple, Tensor.product, Tensor.cyclic, auxiliaryDot,
      matrixAux, Tensor.matrixCoefficients, dotX, dotY, dotZ, hxy, hyz, hzx]

def cyclicChild (r c h : ℕ) (counts : Fin (h + 1) → ℕ) :=
  cyclicTriple ℚ (groupedChild r c h counts)

def outputBlock (r c h aux : ℕ) (counts : Fin (h + 1) → ℕ) :=
  Tensor.product (cyclicChild r c h counts) (matrixAux aux)

def output (r c h N aux : ℕ) (counts : Fin (h + 1) → ℕ) :=
  Tensor.directSum (fun _ : Index h N counts => outputBlock r c h aux counts)

/-- First normalize only after separation has provided independent first-leg labels. -/
def cyclicNormalizeX (r c h N aux : ℕ) (counts : Fin (h + 1) → ℕ) :=
  fun x : ((Fin (wordCount h N counts) × (groupedX r counts × Unit)) ×
      (Fin (wordCount h N counts) × (groupedY c h counts × Fin aux))) ×
      (Fin (wordCount h N counts) × (groupedZ r c h counts × Fin aux)) => ((normalizeX r h N counts x.1.1, normalizeY c h N aux counts x.1.2),
    normalizeZ r c h N aux counts x.2)

def cyclicNormalizeY (r c h N aux : ℕ) (counts : Fin (h + 1) → ℕ) :=
  fun y : ((Fin (wordCount h N counts) × (groupedY c h counts × Fin aux)) ×
      (Fin (wordCount h N counts) × (groupedZ r c h counts × Fin aux))) ×
      (Fin (wordCount h N counts) × (groupedX r counts × Unit)) => ((normalizeY c h N aux counts y.1.1, normalizeZ r c h N aux counts y.1.2),
    normalizeX r h N counts y.2)

def cyclicNormalizeZ (r c h N aux : ℕ) (counts : Fin (h + 1) → ℕ) :=
  fun z : ((Fin (wordCount h N counts) × (groupedZ r c h counts × Fin aux)) ×
      (Fin (wordCount h N counts) × (groupedX r counts × Unit))) ×
      (Fin (wordCount h N counts) × (groupedY c h counts × Fin aux)) => ((normalizeZ r c h N aux counts z.1.1, normalizeX r h N counts z.1.2),
    normalizeY c h N aux counts z.2)

theorem cyclic_normalized (r c h N aux : ℕ) (counts : Fin (h + 1) → ℕ) :
    Tensor.pullback (cyclicNormalizeX r c h N aux counts) (cyclicNormalizeY r c h N aux counts)
      (cyclicNormalizeZ r c h N aux counts) (cyclicTriple ℚ (separated r c h N aux counts)) =
      cyclicTriple ℚ (groupedOutput r c h N aux counts) := by
  rw [← normalized_separator_identity r c h N aux counts]
  rfl

/-- Explicit maps from all M³ normalized child blocks with all auxiliary coordinates. -/
def outputX (r c h N aux : ℕ) (counts : Fin (h + 1) → ℕ) :=
  fun q : Index h N counts ×
      (((groupedX r counts × groupedY c h counts) × groupedZ r c h counts) × (Fin aux × Fin aux)) =>
    cyclicNormalizeX r c h N aux counts (scatterCopies (q.1, dotX q.2))

def outputY (r c h N aux : ℕ) (counts : Fin (h + 1) → ℕ) :=
  fun q : Index h N counts ×
      (((groupedY c h counts × groupedZ r c h counts) × groupedX r counts) × (Fin aux × Fin aux)) =>
    cyclicNormalizeY r c h N aux counts (scatterCopies (q.1, dotY q.2))

def outputZ (r c h N aux : ℕ) (counts : Fin (h + 1) → ℕ) :=
  fun q : Index h N counts ×
      (((groupedZ r c h counts × groupedX r counts) × groupedY c h counts) × (Fin aux × Fin aux)) =>
    cyclicNormalizeZ r c h N aux counts (scatterCopies (q.1, dotZ q.2))

def labelMap {I A B : Type} (f : A → B) : I × A → I × B :=
  fun x => (x.1, f x.2)

/-- An equality of actual coefficient tensors, including unmatched-sector zeros. -/
theorem full_constant_restriction (r c h N aux : ℕ) (counts : Fin (h + 1) → ℕ) :
    Tensor.pullback (outputX r c h N aux counts) (outputY r c h N aux counts)
      (outputZ r c h N aux counts) (cyclicTriple ℚ (separated r c h N aux counts)) =
      output r c h N aux counts := by
  have hnorm := cyclic_normalized r c h N aux counts
  have hscatter := scatter_cyclic_copies
    (Tensor.product (groupedChild r c h counts) (auxiliaryDot aux)) (wordCount h N counts)
  have hdot := cyclic_dot_matrix (groupedChild r c h counts) aux
  change Tensor.pullback (labelMap dotX) (labelMap dotY) (labelMap dotZ)
    (Tensor.pullback scatterCopies scatterCopies scatterCopies
      (Tensor.pullback (cyclicNormalizeX r c h N aux counts) (cyclicNormalizeY r c h N aux counts)
        (cyclicNormalizeZ r c h N aux counts) (cyclicTriple ℚ (separated r c h N aux counts)))) = _
  rw [hnorm]
  change Tensor.pullback (labelMap dotX) (labelMap dotY) (labelMap dotZ)
    (Tensor.pullback scatterCopies scatterCopies scatterCopies
      (cyclicTriple ℚ (Tensor.directSum
        (fun _ : Fin (wordCount h N counts) => Tensor.product (groupedChild r c h counts) (auxiliaryDot aux))))) = _
  rw [hscatter]
  unfold labelMap
  rw [Tensor.directSum_pullback, hdot]
  rfl


abbrev ChildX (r c h : ℕ) (counts : Fin (h + 1) → ℕ) :=
  (groupedX r counts × groupedY c h counts) × groupedZ r c h counts
abbrev ChildY (r c h : ℕ) (counts : Fin (h + 1) → ℕ) :=
  (groupedY c h counts × groupedZ r c h counts) × groupedX r counts
abbrev ChildZ (r c h : ℕ) (counts : Fin (h + 1) → ℕ) :=
  (groupedZ r c h counts × groupedX r counts) × groupedY c h counts

/-- Each grouped position contributes its actual symmetrized convolution tensor. -/
theorem cyclicChild_depth_product (r c h : ℕ) (counts : Fin (h + 1) → ℕ)
    (x : ChildX r c h counts) (y : ChildY r c h counts) (z : ChildZ r c h counts) :
    cyclicChild r c h counts x y z =
      ∏ j, ∏ i : Fin (counts j),
        cyclicTriple ℚ (TensorRankBridge.convolution ℚ r (c + h - 2 * j.val))
          ((x.1.1 ⟨j, i⟩, x.1.2 ⟨j, i⟩), x.2 ⟨j, i⟩)
          ((y.1.1 ⟨j, i⟩, y.1.2 ⟨j, i⟩), y.2 ⟨j, i⟩)
          ((z.1.1 ⟨j, i⟩, z.1.2 ⟨j, i⟩), z.2 ⟨j, i⟩) := by
  simp only [cyclicChild, cyclicTriple, Tensor.product, Tensor.cyclic,
    groupedChild_depth_product, Finset.prod_mul_distrib]

/-- Powering retains all M^(3k) actual direct-sum summands. -/
theorem powered_output_rank (r c h N aux k R : ℕ) (counts : Fin (h + 1) → ℕ)
    (hs : Tensor.RankAtMost (Tensor.power (cyclicTriple ℚ (separated r c h N aux counts)) k) R) :
    Tensor.RankAtMost (Tensor.directSum
      (fun _ : Fin k → Index h N counts => Tensor.power (outputBlock r c h aux counts) k)) R := by
  have hp := hs.pullback
    (fun (x : Fin k → Index h N counts × (ChildX r c h counts × (Fin aux × Fin aux))) i =>
      outputX r c h N aux counts (x i))
    (fun (y : Fin k → Index h N counts × (ChildY r c h counts × (Fin aux × Fin aux))) i =>
      outputY r c h N aux counts (y i))
    (fun (z : Fin k → Index h N counts × (ChildZ r c h counts × (Fin aux × Fin aux))) i =>
      outputZ r c h N aux counts (z i))
  change Tensor.RankAtMost (Tensor.power
    (Tensor.pullback (outputX r c h N aux counts) (outputY r c h N aux counts)
      (outputZ r c h N aux counts) (cyclicTriple ℚ (separated r c h N aux counts))) k) R at hp
  rw [full_constant_restriction] at hp
  exact hp.directSum_const_of_power

theorem powered_sector_card (h N k : ℕ) (counts : Fin (h + 1) → ℕ) :
    Fintype.card (Fin k → Index h N counts) = wordCount h N counts ^ (3 * k) := by
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_prod]
  rw [pow_mul]
  congr 1
  ring

/-- Complete cyclic local recipe from one actual source decomposition. -/
theorem actual_cyclic_split_recipe (r c h N aux k R : ℕ) (hr : 0 < r) (hc : h + 1 ≤ c)
    (counts : Fin (h + 1) → ℕ)
    (hs : Tensor.RankAtMost (cyclicTriple ℚ (Tensor.power (DeterminantTensorBridge.source ℚ r c h) N)) R) :
    Tensor.RankAtMost (Tensor.directSum
      (fun _ : Fin k → Index h N counts => Tensor.power (outputBlock r c h aux counts) k))
      ((3 * k * localDegree h N aux counts + 1) * ell (wordCount h N counts) aux ^ (3 * k) * R ^ k) := by
  exact powered_output_rank r c h N aux k _ counts
    (separated_cyclic_power_rank r c h N aux k R hr hc counts hs)


/-- The original source is convolution with the entire primed equality factor. -/
theorem source_coefficient (r c h : ℕ) (x : Fin r)
    (y : DeterminantBasisBridge.MonomialIndex c h)
    (z : DeterminantBasisBridge.MonomialIndex (r + c - 1) h) :
    DeterminantTensorBridge.source ℚ r c h x y z =
      TensorRankBridge.convolution ℚ r c x y.1 z.1 * (if y.2 = z.2 then 1 else 0) := by
  by_cases hs : x.val + y.1.val = z.1.val <;> by_cases hp : y.2 = z.2 <;>
    simp [DeterminantTensorBridge.source, TensorRankBridge.convolution, hs, hp]

def sourceLegX (r c h N : ℕ) :=
  fun x : ((Fin N → Fin r) × (Fin N → DeterminantBasisBridge.MonomialIndex c h)) ×
      (Fin N → DeterminantBasisBridge.MonomialIndex (r + c - 1) h) =>
    ((fun i => ((x.1.1 i, (x.1.2 i).1), (x.2 i).1)),
      fun i => ((x.2 i).2, (x.1.2 i).2))

def sourceLegY (r c h N : ℕ) :=
  fun y : ((Fin N → DeterminantBasisBridge.MonomialIndex c h) ×
      (Fin N → DeterminantBasisBridge.MonomialIndex (r + c - 1) h)) × (Fin N → Fin r) =>
    ((fun i => (((y.1.1 i).1, (y.1.2 i).1), y.2 i)),
      fun i => ((y.1.2 i).2, (y.1.1 i).2))

def sourceLegZ (r c h N : ℕ) :=
  fun z : ((Fin N → DeterminantBasisBridge.MonomialIndex (r + c - 1) h) ×
      (Fin N → Fin r)) × (Fin N → DeterminantBasisBridge.MonomialIndex c h) =>
    ((fun i => (((z.1.1 i).1, z.1.2 i), (z.2 i).1)),
      fun i => ((z.1.1 i).2, (z.2 i).2))

/-- The actual cyclic source power is a coordinate pullback of S(r,c)^N × T(h+1)^N. -/
theorem source_identification (r c h N : ℕ) :
    cyclicTriple ℚ (Tensor.power (DeterminantTensorBridge.source ℚ r c h) N) =
      Tensor.pullback (sourceLegX r c h N) (sourceLegY r c h N) (sourceLegZ r c h N)
        (Tensor.product
          (Tensor.power (cyclicTriple ℚ (TensorRankBridge.convolution ℚ r c)) N)
          (Tensor.power (matrixAux (h + 1)) N)) := by
  funext x y z
  simp only [cyclicTriple, Tensor.product, Tensor.cyclic, Tensor.power,
    source_coefficient, Tensor.pullback, sourceLegX, sourceLegY, sourceLegZ,
    Finset.prod_mul_distrib]
  have he : (∏ i, (if (y.1.1 i).2 = (z.1.1 i).2 then (1 : ℚ) else 0)) *
      (∏ i, (if (x.1.2 i).2 = (y.1.2 i).2 then (1 : ℚ) else 0)) *
      (∏ i, (if (z.2 i).2 = (x.2 i).2 then (1 : ℚ) else 0)) =
      ∏ i, matrixAux (h + 1) ((x.2 i).2, (x.1.2 i).2)
        ((y.1.2 i).2, (y.1.1 i).2) ((z.1.1 i).2, (z.2 i).2) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    by_cases ha : (x.1.2 i).2 = (y.1.2 i).2 <;>
      by_cases hb : (y.1.1 i).2 = (z.1.1 i).2 <;>
      by_cases hc : (z.2 i).2 = (x.2 i).2 <;>
      simp [matrixAux, Tensor.matrixCoefficients, ha, hb, hc]
  rw [← he]
  ring

/-- Source identification preserves the single rank certificate. -/
theorem source_identification_rank (r c h N R : ℕ)
    (hs : Tensor.RankAtMost
      (Tensor.product (Tensor.power (cyclicTriple ℚ (TensorRankBridge.convolution ℚ r c)) N)
        (Tensor.power (matrixAux (h + 1)) N)) R) :
    Tensor.RankAtMost (cyclicTriple ℚ (Tensor.power (DeterminantTensorBridge.source ℚ r c h) N)) R := by
  rw [source_identification]
  exact hs.pullback _ _ _

/-- Full local cyclic split, with one actual S(r,c)^N × T(h+1)^N input rank. -/
theorem actual_symmetrized_split_recipe (r c h N aux k R : ℕ) (hr : 0 < r) (hc : h + 1 ≤ c)
    (counts : Fin (h + 1) → ℕ)
    (hs : Tensor.RankAtMost
      (Tensor.product (Tensor.power (cyclicTriple ℚ (TensorRankBridge.convolution ℚ r c)) N)
        (Tensor.power (matrixAux (h + 1)) N)) R) :
    Tensor.RankAtMost (Tensor.directSum
      (fun _ : Fin k → Index h N counts => Tensor.power (outputBlock r c h aux counts) k))
      ((3 * k * localDegree h N aux counts + 1) * ell (wordCount h N counts) aux ^ (3 * k) * R ^ k) := by
  exact actual_cyclic_split_recipe r c h N aux k R hr hc counts
    (source_identification_rank r c h N R hs)


/-- All source coordinates are retained by the source factorization. -/
theorem sourceLegX_bijective (r c h N : ℕ) : Function.Bijective (sourceLegX r c h N) := by
  let inverse := fun q : (Fin N → (Fin r × Fin c) × Fin (r + c - 1)) ×
      (Fin N → Fin (h + 1) × Fin (h + 1)) =>
    (((fun i => (q.1 i).1.1), (fun i => ((q.1 i).1.2, (q.2 i).2))),
      fun i => ((q.1 i).2, (q.2 i).1))
  exact Function.bijective_iff_has_inverse.mpr ⟨inverse, (by intro x; rfl), (by intro x; rfl)⟩

theorem sourceLegY_bijective (r c h N : ℕ) : Function.Bijective (sourceLegY r c h N) := by
  let inverse := fun q : (Fin N → (Fin c × Fin (r + c - 1)) × Fin r) ×
      (Fin N → Fin (h + 1) × Fin (h + 1)) =>
    (((fun i => ((q.1 i).1.1, (q.2 i).2)), (fun i => ((q.1 i).1.2, (q.2 i).1))),
      fun i => (q.1 i).2)
  exact Function.bijective_iff_has_inverse.mpr ⟨inverse, (by intro x; rfl), (by intro x; rfl)⟩

theorem sourceLegZ_bijective (r c h N : ℕ) : Function.Bijective (sourceLegZ r c h N) := by
  let inverse := fun q : (Fin N → (Fin (r + c - 1) × Fin r) × Fin c) ×
      (Fin N → Fin (h + 1) × Fin (h + 1)) =>
    (((fun i => ((q.1 i).1.1, (q.2 i).1)), (fun i => (q.1 i).1.2)),
      fun i => ((q.1 i).2, (q.2 i).2))
  exact Function.bijective_iff_has_inverse.mpr ⟨inverse, (by intro x; rfl), (by intro x; rfl)⟩

/-- Zipping two word factors commutes with tensor powers. -/
def zipFactors {A B : Type} {k : ℕ} : (Fin k → A) × (Fin k → B) → (Fin k → A × B) :=
  fun x i => (x.1 i, x.2 i)

theorem power_product_coordinates {X Y Z U V W : Type}
    (T : Tensor ℚ X Y Z) (S : Tensor ℚ U V W) (k : ℕ) :
    Tensor.pullback zipFactors zipFactors zipFactors (Tensor.power (Tensor.product T S) k) =
      Tensor.product (Tensor.power T k) (Tensor.power S k) := by
  funext x y z
  change (∏ i, T (x.1 i) (y.1 i) (z.1 i) * S (x.2 i) (y.2 i) (z.2 i)) =
    (∏ i, T (x.1 i) (y.1 i) (z.1 i)) * (∏ i, S (x.2 i) (y.2 i) (z.2 i))
  exact Finset.prod_mul_distrib

/-- The auxiliary factor in the powered output is the entire T_aux^k. -/
theorem split_powered_output_rank (r c h N aux k R : ℕ) (counts : Fin (h + 1) → ℕ)
    (hs : Tensor.RankAtMost (Tensor.directSum
      (fun _ : Fin k → Index h N counts => Tensor.power (outputBlock r c h aux counts) k)) R) :
    Tensor.RankAtMost (Tensor.directSum (fun _ : Fin k → Index h N counts =>
      Tensor.product (Tensor.power (cyclicChild r c h counts) k) (Tensor.power (matrixAux aux) k))) R := by
  have hp := hs.pullback
    (labelMap (zipFactors (A := ChildX r c h counts) (B := Fin aux × Fin aux)))
    (labelMap (zipFactors (A := ChildY r c h counts) (B := Fin aux × Fin aux)))
    (labelMap (zipFactors (A := ChildZ r c h counts) (B := Fin aux × Fin aux)))
  unfold labelMap at hp
  rw [Tensor.directSum_pullback] at hp
  simp only [outputBlock, power_product_coordinates] at hp
  exact hp

/-- The number of actual output summands is the requested multinomial power. -/
theorem powered_sector_card_factorial (h N k : ℕ) (counts : Fin (h + 1) → ℕ)
    (hs : ∑ j, counts j = N) :
    Fintype.card (Fin k → Index h N counts) =
      (N.factorial / ∏ j, (counts j).factorial) ^ (3 * k) := by
  rw [powered_sector_card, wordCount_factorial h N counts hs]

/-- The named full convolution tensor has precisely the cyclic coefficients used here. -/
theorem symmetrized_coefficients (r c : ℕ) (hr : 0 < r) (hc : 0 < c) :
    (cyclicConvolution ℚ r c hr hc).tensor = cyclicTriple ℚ (TensorRankBridge.convolution ℚ r c) := rfl

/-- Complete local endpoint: one source rank, every sector triple and the full auxiliary power. -/
theorem actual_full_split_recipe (r c h N aux k R : ℕ) (hr : 0 < r) (hc : h + 1 ≤ c)
    (counts : Fin (h + 1) → ℕ)
    (hs : Tensor.RankAtMost
      (Tensor.product (Tensor.power (cyclicConvolution ℚ r c hr (by omega)).tensor N)
        (Tensor.power (matrixAux (h + 1)) N)) R) :
    Tensor.RankAtMost (Tensor.directSum (fun _ : Fin k → Index h N counts =>
      Tensor.product (Tensor.power (cyclicChild r c h counts) k) (Tensor.power (matrixAux aux) k)))
      ((3 * k * localDegree h N aux counts + 1) * ell (wordCount h N counts) aux ^ (3 * k) * R ^ k) := by
  apply split_powered_output_rank r c h N aux k _ counts
  exact actual_symmetrized_split_recipe r c h N aux k R hr hc counts hs


/-- The child is the product of the named S(r,c+h−2j) tensors with multiplicities counts j. -/
theorem cyclicChild_symmetrized_depth_product (r c h : ℕ) (hr : 0 < r) (hc : h + 1 ≤ c)
    (counts : Fin (h + 1) → ℕ)
    (x : ChildX r c h counts) (y : ChildY r c h counts) (z : ChildZ r c h counts) :
    cyclicChild r c h counts x y z =
      ∏ j, ∏ i : Fin (counts j),
        (cyclicConvolution ℚ r (c + h - 2 * j.val) hr (by have := j.isLt; omega)).tensor
          ((x.1.1 ⟨j, i⟩, x.1.2 ⟨j, i⟩), x.2 ⟨j, i⟩)
          ((y.1.1 ⟨j, i⟩, y.1.2 ⟨j, i⟩), y.2 ⟨j, i⟩)
          ((z.1.1 ⟨j, i⟩, z.1.2 ⟨j, i⟩), z.2 ⟨j, i⟩) :=
  cyclicChild_depth_product r c h counts x y z

/-- Every powered child factor is retained in the final direct sum. -/
theorem powered_child_coefficients (r c h k : ℕ) (hr : 0 < r) (hc : h + 1 ≤ c)
    (counts : Fin (h + 1) → ℕ)
    (x : Fin k → ChildX r c h counts) (y : Fin k → ChildY r c h counts)
    (z : Fin k → ChildZ r c h counts) :
    Tensor.power (cyclicChild r c h counts) k x y z =
      ∏ t, ∏ j, ∏ i : Fin (counts j),
        (cyclicConvolution ℚ r (c + h - 2 * j.val) hr (by have := j.isLt; omega)).tensor
          (((x t).1.1 ⟨j, i⟩, (x t).1.2 ⟨j, i⟩), (x t).2 ⟨j, i⟩)
          (((y t).1.1 ⟨j, i⟩, (y t).1.2 ⟨j, i⟩), (y t).2 ⟨j, i⟩)
          (((z t).1.1 ⟨j, i⟩, (z t).1.2 ⟨j, i⟩), (z t).2 ⟨j, i⟩) := by
  exact Finset.prod_congr rfl (fun t _ => cyclicChild_symmetrized_depth_product r c h hr hc counts (x t) (y t) (z t))

end
end MatrixDimensionAudit.DeterminantCyclicRecipeBridge
