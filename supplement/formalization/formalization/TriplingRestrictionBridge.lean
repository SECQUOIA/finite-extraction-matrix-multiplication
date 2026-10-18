import formalization.TensorRankBridge

namespace MatrixDimensionAudit.TriplingRestrictionBridge
open OAI.MatrixMultiplication.Foundation
open TensorRankBridge
open scoped BigOperators

noncomputable section
variable (F : Type) [Field F]

/-- The shifted tripling includes the manuscript case `b = r`. -/
def sourceWidth (r b : Nat) := 3 * b + r - 1

def source (r b : Nat) := convolution F r (sourceWidth r b)

inductive Label | left | middle | right deriving DecidableEq

def labelY (r b : Nat) (j : Fin (sourceWidth r b)) : Label :=
  if j.val < b then .left else if j.val < 2 * b + r - 1 then .middle else .right

def labelZ (r b : Nat) (k : Fin (r + sourceWidth r b - 1)) : Label :=
  if k.val < b + r - 1 then .left else if k.val < 2 * b + r - 1 then .middle else .right

/-- A supported coefficient can cross blocks only from middle Y to outer Z. -/
theorem local_label_rule (r b : Nat) (_hr : 0 < r) (hb : 0 < b)
    (i : Fin r) (j : Fin (sourceWidth r b))
    (k : Fin (r + sourceWidth r b - 1)) (h : i.val + j.val = k.val) :
    (labelZ r b k = .middle → labelY r b j = .middle) ∧
    (labelY r b j ≠ .middle → labelY r b j = labelZ r b k) := by
  have hi := i.isLt
  unfold labelY labelZ
  split_ifs <;> simp_all <;> omega

def yWidth (r b : Nat) : Label → Nat
  | .left | .right => b
  | .middle => r + b - 1

def zWidth (r b : Nat) : Label → Nat
  | .left | .right => r + b - 1
  | .middle => b

/-- Explicit inclusions of the three Y windows. -/
def windowY (r b : Nat) (hr : 0 < r) (hb : 0 < b) (s : Label)
    (j : Fin (yWidth r b s)) : Fin (sourceWidth r b) :=
  ⟨match s with
    | .left => j.val
    | .middle => b + j.val
    | .right => 2 * b + r - 1 + j.val, by
      cases s <;> simp only [yWidth] at j ⊢ <;>
        have hj := j.isLt <;> unfold sourceWidth <;> omega⟩

/-- Explicit inclusions of the three Z windows. -/
def windowZ (r b : Nat) (hr : 0 < r) (hb : 0 < b) (s : Label)
    (k : Fin (zWidth r b s)) : Fin (r + sourceWidth r b - 1) :=
  ⟨match s with
    | .left => k.val
    | .middle => b + r - 1 + k.val
    | .right => 2 * b + r - 1 + k.val, by
      cases s <;> simp only [zWidth] at k ⊢ <;>
        have hk := k.isLt <;> unfold sourceWidth <;> omega⟩

@[simp] theorem windowY_label (r b : Nat) (hr : 0 < r) (hb : 0 < b)
    (s : Label) (j : Fin (yWidth r b s)) : labelY r b (windowY r b hr hb s j) = s := by
  cases s with
  | left =>
      have hj : j.val < b := j.isLt
      simp [labelY, windowY, hj]
  | middle =>
      have hj : j.val < r + b - 1 := j.isLt
      have h₁ : ¬ b + j.val < b := by omega
      have h₂ : b + j.val < 2 * b + r - 1 := by omega
      simp [labelY, windowY, h₁, h₂]
  | right =>
      have h₁ : ¬ 2 * b + r - 1 + j.val < b := by omega
      have h₂ : ¬ 2 * b + r - 1 + j.val < 2 * b + r - 1 := by omega
      simp [labelY, windowY, h₁, h₂]

@[simp] theorem windowZ_label (r b : Nat) (hr : 0 < r) (hb : 0 < b)
    (s : Label) (k : Fin (zWidth r b s)) : labelZ r b (windowZ r b hr hb s k) = s := by
  cases s with
  | left =>
      have hk : k.val < r + b - 1 := k.isLt
      have h : k.val < b + r - 1 := by omega
      simp [labelZ, windowZ, h]
  | middle =>
      have hk : k.val < b := k.isLt
      have h₁ : ¬ b + r - 1 + k.val < b + r - 1 := by omega
      have h₂ : b + r - 1 + k.val < 2 * b + r - 1 := by omega
      simp [labelZ, windowZ, h₁, h₂]
  | right =>
      have h₁ : ¬ 2 * b + r - 1 + k.val < b + r - 1 := by omega
      have h₂ : ¬ 2 * b + r - 1 + k.val < 2 * b + r - 1 := by omega
      simp [labelZ, windowZ, h₁, h₂]

def reverseFirst (r : Nat) (i : Fin r) : Fin r :=
  ⟨r - 1 - i.val, by have := i.isLt; omega⟩

@[simp] theorem reverseFirst_involutive (r : Nat) (i : Fin r) :
    reverseFirst r (reverseFirst r i) = i := by
  apply Fin.ext
  have hi := i.isLt
  simp only [reverseFirst]
  omega

/-- The windows cover every coordinate carrying the corresponding label. -/
theorem windowY_covers (r b : Nat) (hr : 0 < r) (hb : 0 < b)
    (s : Label) (j : Fin (sourceWidth r b)) (h : labelY r b j = s) :
    ∃ j', windowY r b hr hb s j' = j := by
  have hj := j.isLt
  unfold sourceWidth at hj
  cases s with
  | left =>
      have h₁ : j.val < b := by
        by_contra hn
        simp only [labelY, ite_eq_right hn] at h
        split_ifs at h
      exact ⟨⟨j.val, h₁⟩, rfl⟩
  | middle =>
      have h₁ : ¬ j.val < b := by
        intro hn
        simp [labelY, hn] at h
      have h₂ : j.val < 2 * b + r - 1 := by
        by_contra hn
        simp [labelY, h₁, hn] at h
      refine ⟨⟨j.val - b, by simp only [yWidth]; omega⟩, ?_⟩
      apply Fin.ext
      simp only [windowY]
      omega
  | right =>
      have h₁ : ¬ j.val < b := by
        intro hn
        simp [labelY, hn] at h
      have h₂ : ¬ j.val < 2 * b + r - 1 := by
        intro hn
        simp [labelY, h₁, hn] at h
      refine ⟨⟨j.val - (2 * b + r - 1), by simp only [yWidth]; omega⟩, ?_⟩
      apply Fin.ext
      simp only [windowY]
      omega

theorem windowZ_covers (r b : Nat) (hr : 0 < r) (hb : 0 < b)
    (s : Label) (k : Fin (r + sourceWidth r b - 1)) (h : labelZ r b k = s) :
    ∃ k', windowZ r b hr hb s k' = k := by
  have hk := k.isLt
  unfold sourceWidth at hk
  cases s with
  | left =>
      have h₁ : k.val < b + r - 1 := by
        by_contra hn
        simp only [labelZ, ite_eq_right hn] at h
        split_ifs at h
      exact ⟨⟨k.val, by simp only [zWidth]; omega⟩, rfl⟩
  | middle =>
      have h₁ : ¬ k.val < b + r - 1 := by
        intro hn
        simp [labelZ, hn] at h
      have h₂ : k.val < 2 * b + r - 1 := by
        by_contra hn
        simp [labelZ, h₁, hn] at h
      refine ⟨⟨k.val - (b + r - 1), by simp only [zWidth]; omega⟩, ?_⟩
      apply Fin.ext
      simp only [windowZ]
      omega

  | right =>
      have h₁ : ¬ k.val < b + r - 1 := by
        intro hn
        simp [labelZ, hn] at h
      have h₂ : ¬ k.val < 2 * b + r - 1 := by
        intro hn
        simp [labelZ, h₁, hn] at h
      refine ⟨⟨k.val - (2 * b + r - 1), by simp only [zWidth]; omega⟩, ?_⟩
      apply Fin.ext
      simp only [windowZ]
      omega


theorem windowY_injective (r b : Nat) (hr : 0 < r) (hb : 0 < b) (s : Label) :
    Function.Injective (windowY r b hr hb s) := by
  intro j k h
  apply Fin.ext
  have hv := congrArg Fin.val h
  cases s <;> simp only [windowY] at hv <;> omega

theorem windowZ_injective (r b : Nat) (hr : 0 < r) (hb : 0 < b) (s : Label) :
    Function.Injective (windowZ r b hr hb s) := by
  intro j k h
  apply Fin.ext
  have hv := congrArg Fin.val h
  cases s <;> simp only [windowZ] at hv <;> omega
/-- Each block is a convolution, with only the middle block exchanging Y and Z
and reversing X. X remains shared until the sectors have been separated. -/
def block (r b : Nat) (s : Label) :
    Tensor F (Fin r) (Fin (yWidth r b s)) (Fin (zWidth r b s)) :=
  match s with
  | .left | .right => convolution F r b
  | .middle => fun i j k => convolution F r b (reverseFirst r i) k j

theorem window_block (r b : Nat) (hr : 0 < r) (hb : 0 < b) (s : Label) :
    Tensor.pullback id (windowY r b hr hb s) (windowZ r b hr hb s) (source F r b) =
      block F r b s := by
  funext i j k
  cases s with
  | left => rfl
  | middle =>
      change (if i.val + (b + j.val) = b + r - 1 + k.val then (1 : F) else 0) =
        (if r - 1 - i.val + k.val = j.val then 1 else 0)
      have hi := i.isLt
      have he : i.val + (b + j.val) = b + r - 1 + k.val ↔
          r - 1 - i.val + k.val = j.val := by omega
      simp only [he]

  | right =>
      change (if i.val + (2 * b + r - 1 + j.val) = 2 * b + r - 1 + k.val
        then (1 : F) else 0) = (if i.val + j.val = k.val then 1 else 0)
      have he : i.val + (2 * b + r - 1 + j.val) = 2 * b + r - 1 + k.val ↔
          i.val + j.val = k.val := by omega
      simp only [he]


/-- The sector-local first-index permutation is its own inverse. -/
def normalizeFirst (r : Nat) (s : Label) (i : Fin r) : Fin r :=
  match s with
  | .middle => reverseFirst r i
  | .left | .right => i

@[simp] theorem normalizeFirst_involutive (r : Nat) (s : Label) (i : Fin r) :
    normalizeFirst r s (normalizeFirst r s i) = i := by
  cases s <;> simp [normalizeFirst]

/-- Ordinary convolution on the outer blocks; the Y/Z exchange in the middle. -/
def orientedBlock (r b : Nat) (s : Label) :
    Tensor F (Fin r) (Fin (yWidth r b s)) (Fin (zWidth r b s)) :=
  match s with
  | .left | .right => convolution F r b
  | .middle => fun i j k => convolution F r b i k j

theorem block_normalized (r b : Nat) (s : Label) (i : Fin r)
    (j : Fin (yWidth r b s)) (k : Fin (zWidth r b s)) :
    block F r b s (normalizeFirst r s i) j k = orientedBlock F r b s i j k := by
  cases s <;> simp [block, orientedBlock, normalizeFirst]
def middlePositions {n : Nat} (w : Fin n → Label) : Finset (Fin n) :=
  Finset.univ.filter (fun i => w i = .middle)

def middleCount {n : Nat} (w : Fin n → Label) : Nat := (middlePositions w).card

/-- Equal middle counts force equal label words on every supported tensor-power term. -/
theorem supported_words_equal (r b n : Nat) (hr : 0 < r) (hb : 0 < b)
    (x : Fin n → Fin r) (y : Fin n → Fin (sourceWidth r b))
    (z : Fin n → Fin (r + sourceWidth r b - 1))
    (hs : ∀ i, (x i).val + (y i).val = (z i).val)
    (hc : middleCount (fun i => labelY r b (y i)) =
      middleCount (fun i => labelZ r b (z i))) :
    (fun i => labelY r b (y i)) = (fun i => labelZ r b (z i)) := by
  have sub : middlePositions (fun i => labelZ r b (z i)) ⊆
      middlePositions (fun i => labelY r b (y i)) := by
    intro i hi
    simp only [middlePositions, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact (local_label_rule r b hr hb (x i) (y i) (z i) (hs i)).1 hi
  have sets := Finset.eq_of_subset_of_card_le sub (Nat.le_of_eq hc)
  funext i
  by_cases hy : labelY r b (y i) = .middle
  · have mem : i ∈ middlePositions (fun i => labelY r b (y i)) := by
      simp [middlePositions, hy]
    rw [← sets] at mem
    have hz : labelZ r b (z i) = .middle := by simpa [middlePositions] using mem
    exact hy.trans hz.symm
  · exact (local_label_rule r b hr hb (x i) (y i) (z i) (hs i)).2 hy

/-- The actual second-leg coordinate projection keeps exactly m middle labels. -/
def keptY (r b n m : Nat) :=
  {y : Fin n → Fin (sourceWidth r b) // middleCount (fun i => labelY r b (y i)) = m}

/-- The actual third-leg coordinate projection uses the same middle count. -/
def keptZ (r b n m : Nat) :=
  {z : Fin n → Fin (r + sourceWidth r b - 1) // middleCount (fun i => labelZ r b (z i)) = m}

def restricted (r b n m : Nat) :
    Tensor F (Fin n → Fin r) (keptY r b n m) (keptZ r b n m) :=
  Tensor.pullback id Subtype.val Subtype.val (Tensor.power (source F r b) n)

/-- Coefficient identity after the fixed-middle projection. Sectors share X;
coefficients between distinct words are zero. No sector-count or rank premise occurs. -/
theorem restricted_block_diagonal (r b n m : Nat) (hr : 0 < r) (hb : 0 < b)
    (x : Fin n → Fin r) (y : keptY r b n m) (z : keptZ r b n m) :
    restricted F r b n m x y z =
      if (fun i => labelY r b (y.val i)) = (fun i => labelZ r b (z.val i))
      then ∏ i, source F r b (x i) (y.val i) (z.val i) else 0 := by
  classical
  by_cases hw : (fun i => labelY r b (y.val i)) = (fun i => labelZ r b (z.val i))
  · simp [restricted, Tensor.pullback, Tensor.power, hw]
  · simp only [restricted, Tensor.pullback, id_eq, Tensor.power, ite_eq_right hw]
    by_contra hn
    have hs : ∀ i, (x i).val + (y.val i).val = (z.val i).val := by
      intro i
      have hi : source F r b (x i) (y.val i) (z.val i) ≠ 0 :=
        (Finset.prod_ne_zero_iff.mp hn) i (Finset.mem_univ i)
      simpa only [source, convolution, ne_eq, ite_eq_right_iff, one_ne_zero,
        imp_false, not_not] using hi
    exact hw (supported_words_equal r b n hr hb x y.val z.val hs (y.property.trans z.property.symm))

/-- This pullback is the external API's ordinary linear restriction, using
Kronecker delta matrices on the three legs. -/
theorem restricted_eq_restrict (r b n m : Nat) : restricted F r b n m =
    Tensor.restrict
      (fun x' x => if x = x' then (1 : F) else 0)
      (fun (y' : keptY r b n m) y => if y = y'.val then (1 : F) else 0)
      (fun (z' : keptZ r b n m) z => if z = z'.val then (1 : F) else 0)
      (Tensor.power (source F r b) n) := by
  exact Tensor.pullback_eq_restrict id Subtype.val Subtype.val _

def Word (n m : Nat) := {w : Fin n → Label // middleCount w = m}

def sectorY (r b n m : Nat) (w : Word n m) := (i : Fin n) → Fin (yWidth r b (w.val i))
def sectorZ (r b n m : Nat) (w : Word n m) := (i : Fin n) → Fin (zWidth r b (w.val i))

def sectorEmbeddingY (r b n m : Nat) (hr : 0 < r) (hb : 0 < b)
    (w : Word n m) (y : sectorY r b n m w) : keptY r b n m :=
  ⟨fun i => windowY r b hr hb (w.val i) (y i), by
    have h : (fun i => labelY r b (windowY r b hr hb (w.val i) (y i))) = w.val :=
      funext (fun i => windowY_label r b hr hb (w.val i) (y i))
    rw [h]
    exact w.property⟩

def sectorEmbeddingZ (r b n m : Nat) (hr : 0 < r) (hb : 0 < b)
    (w : Word n m) (z : sectorZ r b n m w) : keptZ r b n m :=
  ⟨fun i => windowZ r b hr hb (w.val i) (z i), by
    have h : (fun i => labelZ r b (windowZ r b hr hb (w.val i) (z i))) = w.val :=
      funext (fun i => windowZ_label r b hr hb (w.val i) (z i))
    rw [h]
    exact w.property⟩

/-- Every diagonal sector is exactly the product of the stated convolution blocks. -/
theorem sector_tensor_identity (r b n m : Nat) (hr : 0 < r) (hb : 0 < b)
    (w : Word n m) (x : Fin n → Fin r) (y : sectorY r b n m w)
    (z : sectorZ r b n m w) :
    restricted F r b n m x (sectorEmbeddingY r b n m hr hb w y)
      (sectorEmbeddingZ r b n m hr hb w z) =
      ∏ i, block F r b (w.val i) (x i) (y i) (z i) := by
  change (∏ i, source F r b (x i)
    (windowY r b hr hb (w.val i) (y i)) (windowZ r b hr hb (w.val i) (z i))) = _
  apply Finset.prod_congr rfl
  intro i _
  exact congrFun (congrFun (congrFun (window_block F r b hr hb (w.val i)) (x i)) (y i)) (z i)

/-- Applying the reversible X permutation inside one sector identifies its
factors with C(r,b) or C(r,b)^(23), as specified by its word. -/
theorem sector_normalized_tensor_identity (r b n m : Nat) (hr : 0 < r) (hb : 0 < b)
    (w : Word n m) (x : Fin n → Fin r) (y : sectorY r b n m w)
    (z : sectorZ r b n m w) :
    restricted F r b n m (fun i => normalizeFirst r (w.val i) (x i))
      (sectorEmbeddingY r b n m hr hb w y) (sectorEmbeddingZ r b n m hr hb w z) =
      ∏ i, orientedBlock F r b (w.val i) (x i) (y i) (z i) := by
  rw [sector_tensor_identity F r b n m hr hb]
  exact Finset.prod_congr rfl (fun i _ => block_normalized F r b (w.val i) (x i) (y i) (z i))

/-- Distinct words give zero coefficients, even though the first input is shared. -/
theorem cross_sector_zero (r b n m : Nat) (hr : 0 < r) (hb : 0 < b)
    (w v : Word n m) (h : w ≠ v) (x : Fin n → Fin r)
    (y : sectorY r b n m w) (z : sectorZ r b n m v) :
    restricted F r b n m x (sectorEmbeddingY r b n m hr hb w y)
      (sectorEmbeddingZ r b n m hr hb v z) = 0 := by
  rw [restricted_block_diagonal F r b n m hr hb]
  have hn : (fun i => labelY r b ((sectorEmbeddingY r b n m hr hb w y).val i)) ≠
      (fun i => labelZ r b ((sectorEmbeddingZ r b n m hr hb v z).val i)) := by
    intro he
    apply h
    apply Subtype.ext
    funext i
    simpa only [sectorEmbeddingY, sectorEmbeddingZ, windowY_label, windowZ_label] using congrFun he i
  simp [hn]

/-- No retained coordinate is lost in the sector description. -/
theorem sectorEmbeddingY_covers (r b n m : Nat) (hr : 0 < r) (hb : 0 < b)
    (y : keptY r b n m) :
    ∃ (w : Word n m) (v : sectorY r b n m w), sectorEmbeddingY r b n m hr hb w v = y := by
  let w : Word n m := ⟨fun i => labelY r b (y.val i), y.property⟩
  have h : ∀ i, ∃ j, windowY r b hr hb (w.val i) j = y.val i :=
    fun i => windowY_covers r b hr hb (w.val i) (y.val i) rfl
  refine ⟨w, fun i => Classical.choose (h i), ?_⟩
  apply Subtype.ext
  funext i
  exact Classical.choose_spec (h i)

theorem sectorEmbeddingZ_covers (r b n m : Nat) (hr : 0 < r) (hb : 0 < b)
    (z : keptZ r b n m) :
    ∃ (w : Word n m) (v : sectorZ r b n m w), sectorEmbeddingZ r b n m hr hb w v = z := by
  let w : Word n m := ⟨fun i => labelZ r b (z.val i), z.property⟩
  have h : ∀ i, ∃ k, windowZ r b hr hb (w.val i) k = z.val i :=
    fun i => windowZ_covers r b hr hb (w.val i) (z.val i) rfl
  refine ⟨w, fun i => Classical.choose (h i), ?_⟩
  apply Subtype.ext
  funext i
  exact Classical.choose_spec (h i)

/-- Three cyclic orientations, using the same OAI product convention as the rank bridge. -/
def cyclicTriple {X Y Z : Type} (T : Tensor F X Y Z) :=
  Tensor.product (Tensor.product T (Tensor.cyclic T)) (Tensor.cyclic (Tensor.cyclic T))

/-- The concrete restriction maps compose on all three cyclic orientations.
Instantiate T with the source power and fx/fy/fz with id/Subtype.val/Subtype.val. -/
theorem cyclicTriple_pullback {X Y Z X' Y' Z' : Type} (T : Tensor F X Y Z)
    (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z) :
    cyclicTriple F (Tensor.pullback fx fy fz T) =
      Tensor.pullback
        (fun x : (X' × Y') × Z' => ((fx x.1.1, fy x.1.2), fz x.2))
        (fun y : (Y' × Z') × X' => ((fy y.1.1, fz y.1.2), fx y.2))
        (fun z : (Z' × X') × Y' => ((fz z.1.1, fx z.1.2), fy z.2))
        (cyclicTriple F T) := rfl

def transposeInputs {X Y Z : Type} (T : Tensor F X Y Z) : Tensor F Y X Z :=
  fun y x z => T x y z

omit [Field F] in
/-- Exchanging two legs transports the same restriction to the odd orientations. -/
theorem transposeInputs_pullback {X Y Z X' Y' Z' : Type} (T : Tensor F X Y Z)
    (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z) :
    transposeInputs F (Tensor.pullback fx fy fz T) =
      Tensor.pullback fy fx fz (transposeInputs F T) := rfl

end
end MatrixDimensionAudit.TriplingRestrictionBridge

#print axioms MatrixDimensionAudit.TriplingRestrictionBridge.local_label_rule
#print axioms MatrixDimensionAudit.TriplingRestrictionBridge.window_block
#print axioms MatrixDimensionAudit.TriplingRestrictionBridge.supported_words_equal
#print axioms MatrixDimensionAudit.TriplingRestrictionBridge.restricted_block_diagonal
#print axioms MatrixDimensionAudit.TriplingRestrictionBridge.restricted_eq_restrict
#print axioms MatrixDimensionAudit.TriplingRestrictionBridge.sector_tensor_identity
#print axioms MatrixDimensionAudit.TriplingRestrictionBridge.sector_normalized_tensor_identity
#print axioms MatrixDimensionAudit.TriplingRestrictionBridge.cross_sector_zero
#print axioms MatrixDimensionAudit.TriplingRestrictionBridge.sectorEmbeddingY_covers
#print axioms MatrixDimensionAudit.TriplingRestrictionBridge.sectorEmbeddingZ_covers
#print axioms MatrixDimensionAudit.TriplingRestrictionBridge.cyclicTriple_pullback
#print axioms MatrixDimensionAudit.TriplingRestrictionBridge.transposeInputs_pullback
