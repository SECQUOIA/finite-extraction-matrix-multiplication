import formalization.SeparatorTensorBridge
import formalization.TriplingRestrictionBridge

/-!
Polynomial separation for a common first leg and sector-dependent second and
third coordinate types. Padding is used only to reuse the polynomial family;
the actual source maps and rank bounds use the unpadded dependent matched sum.
The separator is that of H. Lü, arXiv:2610.18914, Proposition 2.1, over ℚ.
-/

namespace MatrixDimensionAudit.DependentSeparator

open OAI.MatrixMultiplication.Foundation
open MatrixDimensionAudit.Separator MatrixDimensionAudit.SeparatorTensor
open scoped BigOperators

noncomputable section

variable {M n : ℕ} {X : Type*} {Y Z : Fin M → Type*}

/-- The actual matched tensor with sector-dependent second and third legs. -/
def dependentMatched (T : (h : Fin M) → Tensor ℚ X (Y h) (Z h)) :
    Tensor ℚ X (Sigma Y) (Sigma Z) :=
  fun x sy sz => if h : sy.1 = sz.1 then T sy.1 x sy.2 (h.symm ▸ sz.2) else 0

@[simp] theorem dependentMatched_same
    (T : (h : Fin M) → Tensor ℚ X (Y h) (Z h))
    (h : Fin M) (x : X) (y : Y h) (z : Z h) :
    dependentMatched T x ⟨h, y⟩ ⟨h, z⟩ = T h x y z := by
  simp [dependentMatched]

/-- Actual zero extension of a sector tensor into common sigma-coordinate spaces. -/
def paddedTensor (T : (h : Fin M) → Tensor ℚ X (Y h) (Z h))
    (h : Fin M) : Tensor ℚ X (Sigma Y) (Sigma Z) :=
  fun x sy sz => if h = sy.1 ∧ h = sz.1 then dependentMatched T x sy sz else 0

@[simp] theorem paddedTensor_same
    (T : (h : Fin M) → Tensor ℚ X (Y h) (Z h))
    (h : Fin M) (x : X) (y : Y h) (z : Z h) :
    paddedTensor T h x ⟨h, y⟩ ⟨h, z⟩ = T h x y z := by
  simp [paddedTensor]

/-- Selecting consistent outer and inner sector labels removes all padding. -/
theorem padded_matched_selected
    (T : (h : Fin M) → Tensor ℚ X (Y h) (Z h))
    (x : X) (sy : Sigma Y) (sz : Sigma Z) :
    matchedTensor (paddedTensor T) x (sy.1, sy) (sz.1, sz) =
      dependentMatched T x sy sz := by
  by_cases h : sy.1 = sz.1
  · simp [matchedTensor, paddedTensor, h]
  · simp [matchedTensor, h, dependentMatched]

/-- Add the redundant outer sector label required by the frozen uniform interface. -/
def embedSecond : (Fin n × Sigma Y) → (Fin n × (Fin M × Sigma Y)) :=
  fun jy => (jy.1, (jy.2.1, jy.2))

def embedThird : (Fin n × Sigma Z) → (Fin n × (Fin M × Sigma Z)) :=
  fun rz => (rz.1, (rz.2.1, rz.2))

/-- This polynomial family is transported from the frozen uniform-coordinate theorem. -/
def dependentFamily (T : (h : Fin M) → Tensor ℚ X (Y h) (Z h)) :
    Tensor (Polynomial ℚ) (Fin M × X) (Fin n × Sigma Y) (Fin n × Sigma Z) :=
  Tensor.pullback id embedSecond embedThird (separatorFamily (n := n) (paddedTensor T))

/-- Second-leg copy coefficients use the coordinate's own sector label. -/
def dependentSecond (ε : ℚ) : Fin n → Sigma Y → Fin (ell M n) → ℚ :=
  fun j sy b => secondLaurent M n ε j (sy.1, sy) b

/-- Third-leg Taylor coefficients use the coordinate's own sector label. -/
def dependentThird (ε : ℚ) : Fin n → Sigma Z → Fin (ell M n) → ℚ :=
  fun r sz b => thirdTaylor M n ε r (sz.1, sz) b

/-- The full direct-sum coefficient tensor on the unpadded dependent coordinates. -/
def dependentTarget (T : (h : Fin M) → Tensor ℚ X (Y h) (Z h)) :
    Tensor ℚ (Fin M × X) (Fin n × Sigma Y) (Fin n × Sigma Z) :=
  fun gx jy rz => if gx.1 = jy.2.1 ∧ gx.1 = rz.2.1 ∧ jy.1 = rz.1 then
    dependentMatched T gx.2 jy.2 rz.2 else 0

/-- Every matching sector entry is its original block times the auxiliary dot product. -/
@[simp] theorem dependentTarget_same
    (T : (h : Fin M) → Tensor ℚ X (Y h) (Z h))
    (h : Fin M) (x : X) (y : Y h) (z : Z h) (j r : Fin n) :
    dependentTarget T (h, x) (j, ⟨h, y⟩) (r, ⟨h, z⟩) =
      if j = r then T h x y z else 0 := by
  simp [dependentTarget]

/-- No outer padding label survives in the actual three-map restriction.
The source consists of ell copies of dependentMatched, without an extra M factor. -/
theorem dependent_restriction
    [Fintype X] [DecidableEq X]
    [∀ h, Fintype (Y h)] [∀ h, Fintype (Z h)]
    [∀ h, DecidableEq (Y h)] [∀ h, DecidableEq (Z h)]
    (T : (h : Fin M) → Tensor ℚ X (Y h) (Z h)) (ε : ℚ) (hε : ε ≠ 0) :
    Tensor.restrict (liftMatrix (firstCardinal M n))
      (liftMatrix (dependentSecond (Y := Y) ε))
      (liftMatrix (dependentThird (Z := Z) ε))
      (Tensor.directSum (fun _ : Fin (ell M n) => dependentMatched T)) =
      evaluate (dependentFamily (n := n) T) ε := by
  funext gx jy rz
  have hf := congrFun (congrFun (congrFun
    (separator_restriction (n := n) (paddedTensor T) ε hε) gx)
      (embedSecond jy)) (embedThird rz)
  rw [restrict_copies] at hf
  dsimp [embedSecond, embedThird] at hf
  rw [padded_matched_selected] at hf
  rw [restrict_copies]
  simpa only [dependentSecond, dependentThird, embedSecond, embedThird,
    evaluate, dependentFamily, Tensor.pullback, id_eq] using hf

/-- Every dependent-family coefficient has the same improved local degree. -/
theorem dependent_degree
    (T : (h : Fin M) → Tensor ℚ X (Y h) (Z h))
    (gx : Fin M × X) (jy : Fin n × Sigma Y) (rz : Fin n × Sigma Z) :
    (dependentFamily (n := n) T gx jy rz).natDegree ≤ min (M - 1) (n - 1) :=
  separator_degree (paddedTensor T) gx (embedSecond jy) (embedThird rz)

/-- Full constant tensor identity, including cross-sector and auxiliary zeros. -/
theorem dependent_constant
    (T : (h : Fin M) → Tensor ℚ X (Y h) (Z h)) :
    evaluate (dependentFamily (n := n) T) 0 = dependentTarget (n := n) T := by
  funext gx jy rz
  have hc := congrFun (congrFun (congrFun
    (separator_constant (n := n) (paddedTensor T)) gx)
      (embedSecond jy)) (embedThird rz)
  change (separatorFamily (n := n) (paddedTensor T) gx
    (embedSecond jy) (embedThird rz)).eval 0 = _ at hc
  change (separatorFamily (n := n) (paddedTensor T) gx
    (embedSecond jy) (embedThird rz)).eval 0 = _
  rw [hc]
  dsimp [separatedTarget, embedSecond, embedThird, dependentTarget]
  split_ifs with h
  · simp only [paddedTensor]
    rw [ite_eq_left ⟨h.1, h.2.1⟩]
  · rfl

/-- Source rank is charged for the actual dependent matched tensor, with ell
copies per evaluation and no rank contribution from zero padding. -/
theorem dependent_sample_rank
    [Fintype X] [DecidableEq X]
    [∀ h, Fintype (Y h)] [∀ h, Fintype (Z h)]
    [∀ h, DecidableEq (Y h)] [∀ h, DecidableEq (Z h)]
    (T : (h : Fin M) → Tensor ℚ X (Y h) (Z h)) (R : ℕ)
    (hr : Tensor.RankAtMost (dependentMatched T) R) (ε : ℚ) (hε : ε ≠ 0) :
    Tensor.RankAtMost (evaluate (dependentFamily (n := n) T) ε) (ell M n * R) := by
  have h := directSum_rankAtMost (fun _ : Fin (ell M n) => dependentMatched T) R
    (fun _ => hr)
  have ht := h.restrict (liftMatrix (firstCardinal M n))
    (liftMatrix (dependentSecond (Y := Y) ε)) (liftMatrix (dependentThird (Z := Z) ε))
  simpa only [dependent_restriction T ε hε, Fintype.card_fin] using ht

/-- General dependent-sector separator and exactification, valid also when
individual sector coordinate types are empty. -/
theorem dependent_power_rank
    [Fintype X] [DecidableEq X]
    [∀ h, Fintype (Y h)] [∀ h, Fintype (Z h)]
    [∀ h, DecidableEq (Y h)] [∀ h, DecidableEq (Z h)]
    (T : (h : Fin M) → Tensor ℚ X (Y h) (Z h)) (k R : ℕ)
    (hr : Tensor.RankAtMost (dependentMatched T) R) :
    Tensor.RankAtMost (Tensor.power (dependentTarget (n := n) T) k)
      ((k * min (M - 1) (n - 1) + 1) * (ell M n * R) ^ k) := by
  rw [← dependent_constant T]
  apply tensor_power_exactification_rank _ _ _ _ (dependent_degree T)
  intro e
  exact dependent_sample_rank T R hr (node e) (rationalNode_nonzero e.val)

/-- Bundled second-leg map on the unpadded dependent coordinate space. -/
def secondMap [∀ h, Fintype (Y h)] [∀ h, DecidableEq (Y h)] (ε : ℚ) :=
  coordinateMap (liftMatrix (dependentSecond (n := n) (Y := Y) ε))

/-- Bundled third-leg map on the unpadded dependent coordinate space. -/
def thirdMap [∀ h, Fintype (Z h)] [∀ h, DecidableEq (Z h)] (ε : ℚ) :=
  coordinateMap (liftMatrix (dependentThird (n := n) (Z := Z) ε))

namespace Tripling
open MatrixDimensionAudit.TriplingRestrictionBridge

local instance labelFintype : Fintype Label where
  elems := {Label.left, Label.middle, Label.right}
  complete s := by cases s <;> simp

local instance wordFintype (N m : ℕ) : Fintype (Word N m) := by
  classical
  unfold Word
  infer_instance

/-- All retained words, without assuming a closed sector-count formula. -/
def blockCount (N m : ℕ) : ℕ := Fintype.card (Word N m)

def blockWord (N m : ℕ) : Fin (blockCount N m) → Word N m :=
  (Fintype.equivFin (Word N m)).symm

abbrev blockY (r b N m : ℕ) (h : Fin (blockCount N m)) :=
  sectorY r b N m (blockWord N m h)

abbrev blockZ (r b N m : ℕ) (h : Fin (blockCount N m)) :=
  sectorZ r b N m (blockWord N m h)

/-- The actual unnormalized tripling sector tensors, with their dependent widths. -/
def blocks (r b N m : ℕ) (h : Fin (blockCount N m)) :
    Tensor ℚ (Fin N → Fin r) (blockY r b N m h) (blockZ r b N m h) :=
  fun x y z => ∏ i, block ℚ r b ((blockWord N m h).val i) (x i) (y i) (z i)

def keptEmbeddingY (r b N m : ℕ) (hr : 0 < r) (hb : 0 < b) :
    Sigma (blockY r b N m) → keptY r b N m :=
  fun sy => sectorEmbeddingY r b N m hr hb (blockWord N m sy.1) sy.2

def keptEmbeddingZ (r b N m : ℕ) (hr : 0 < r) (hb : 0 < b) :
    Sigma (blockZ r b N m) → keptZ r b N m :=
  fun sz => sectorEmbeddingZ r b N m hr hb (blockWord N m sz.1) sz.2

/-- The dependent matched source is an actual coordinate restriction of the
kept tripling tensor. Diagonal and cross-sector identities are both proved. -/
theorem matched_from_kept (r b N m : ℕ) (hr : 0 < r) (hb : 0 < b) :
    dependentMatched (blocks r b N m) = Tensor.pullback id
      (keptEmbeddingY r b N m hr hb) (keptEmbeddingZ r b N m hr hb)
      (restricted ℚ r b N m) := by
  funext x sy sz
  rcases sy with ⟨h, y⟩
  rcases sz with ⟨q, z⟩
  by_cases hh : h = q
  · subst q
    rw [dependentMatched_same]
    exact (sector_tensor_identity ℚ r b N m hr hb (blockWord N m h) x y z).symm
  · have hw : blockWord N m h ≠ blockWord N m q := by
      intro he
      exact hh ((Fintype.equivFin (Word N m)).symm.injective he)
    simp only [dependentMatched, hh, dite_false, Tensor.pullback, id_eq,
      keptEmbeddingY, keptEmbeddingZ]
    exact (cross_sector_zero ℚ r b N m hr hb (blockWord N m h)
      (blockWord N m q) hw x y z).symm

/-- Apply the dependent separator directly to actual kept tripling sectors,
without a uniform-coordinate padding charge or an assumed matched identity. -/
theorem kept_separator_power_rank (r b N m n k R : ℕ) (hr : 0 < r) (hb : 0 < b)
    (hsource : Tensor.RankAtMost (restricted ℚ r b N m) R) :
    Tensor.RankAtMost (Tensor.power (dependentTarget (n := n) (blocks r b N m)) k)
      ((k * min (blockCount N m - 1) (n - 1) + 1) *
        (ell (blockCount N m) n * R) ^ k) := by
  classical
  have hs := hsource.pullback id (keptEmbeddingY r b N m hr hb)
    (keptEmbeddingZ r b N m hr hb)
  rw [← matched_from_kept r b N m hr hb] at hs
  let : (h : Fin (blockCount N m)) → Fintype (blockY r b N m h) := fun h => by
    dsimp [blockY, sectorY]
    infer_instance
  let : (h : Fin (blockCount N m)) → Fintype (blockZ r b N m h) := fun h => by
    dsimp [blockZ, sectorZ]
    infer_instance
  exact dependent_power_rank (blocks r b N m) k R hs

/-- A decomposition of the original tripling source power supplies the same
rank bound after the actual kept-coordinate projection and separator maps. -/
theorem source_separator_power_rank (r b N m n k R : ℕ) (hr : 0 < r) (hb : 0 < b)
    (hsource : Tensor.RankAtMost (Tensor.power (source ℚ r b) N) R) :
    Tensor.RankAtMost (Tensor.power (dependentTarget (n := n) (blocks r b N m)) k)
      ((k * min (blockCount N m - 1) (n - 1) + 1) *
        (ell (blockCount N m) n * R) ^ k) := by
  classical
  apply kept_separator_power_rank r b N m n k R hr hb
  exact hsource.pullback id Subtype.val Subtype.val

end Tripling

#print axioms dependent_restriction
#print axioms dependent_degree
#print axioms dependent_constant
#print axioms dependent_power_rank
#print axioms Tripling.matched_from_kept
#print axioms Tripling.kept_separator_power_rank
#print axioms Tripling.source_separator_power_rank

end
end MatrixDimensionAudit.DependentSeparator
