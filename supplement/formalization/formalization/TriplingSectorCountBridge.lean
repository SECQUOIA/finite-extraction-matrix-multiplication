import formalization.PowerCoordinateBridge

namespace MatrixDimensionAudit.TriplingSectorCountBridge
open OAI.MatrixMultiplication.Foundation
open TriplingRestrictionBridge PowerCoordinateBridge
open scoped BigOperators

noncomputable section

instance labelFintype : Fintype Label :=
  ⟨{.left, .middle, .right}, by intro s; cases s <;> simp⟩

@[simp] theorem card_label : Fintype.card Label = 3 := by
  change ({Label.left, Label.middle, Label.right} : Finset Label).card = 3
  decide

instance wordFintype (n m : Nat) : Fintype (Word n m) := by
  classical
  unfold Word
  infer_instance

def count (n m : Nat) : Nat := Fintype.card (Word n m)

def outerLabel (b : Bool) : Label := if b then .right else .left

def outerCode : Label → Bool
  | .right => true
  | .left | .middle => false

@[simp] theorem outerLabel_ne_middle (b : Bool) : outerLabel b ≠ .middle := by
  cases b <;> simp [outerLabel]

@[simp] theorem outerCode_outerLabel (b : Bool) : outerCode (outerLabel b) = b := by
  cases b <;> rfl

theorem outerLabel_outerCode (s : Label) (h : s ≠ .middle) : outerLabel (outerCode s) = s := by
  cases s <;> simp_all [outerCode, outerLabel]

/-- A word is determined by its middle-position set and a binary outer label
at each remaining position. -/
def positionWord {n : Nat} (s : Finset (Fin n)) (c : {i // i ∉ s} → Bool) : Fin n → Label :=
  fun i => if hi : i ∈ s then .middle else outerLabel (c ⟨i, hi⟩)

@[simp] theorem middlePositions_positionWord {n : Nat} (s : Finset (Fin n))
    (c : {i // i ∉ s} → Bool) : middlePositions (positionWord s c) = s := by
  ext i
  by_cases hi : i ∈ s <;> simp [middlePositions, positionWord, hi]

def outerAssignmentEquiv {n : Nat} (s : Finset (Fin n)) :
    {w : Fin n → Label // middlePositions w = s} ≃ ({i // i ∉ s} → Bool) where
  toFun := fun w i => outerCode (w.val i.val)
  invFun := fun c => ⟨positionWord s c, middlePositions_positionWord s c⟩
  left_inv := by
    intro w
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ s
    · have hw : w.val i = .middle := by
        rw [← w.property] at hi
        simpa [middlePositions] using hi
      simp [positionWord, hi, hw]
    · have hw : w.val i ≠ .middle := by
        intro hm
        apply hi
        rw [← w.property]
        simp [middlePositions, hm]
      simpa [positionWord, hi] using outerLabel_outerCode (w.val i) hw
  right_inv := by
    intro c
    funext i
    simp [positionWord, i.property]

theorem card_middle_fiber {n : Nat} (s : Finset (Fin n)) :
    Fintype.card {w : Fin n → Label // middlePositions w = s} = 2 ^ (n - s.card) := by
  rw [Fintype.card_congr (outerAssignmentEquiv s), Fintype.card_fun, Fintype.card_bool]
  congr 1
  rw [Fintype.card_subtype_compl (fun i : Fin n => i ∈ s)]
  simp

/-- Exact cardinality of the actual retained-word subtype used by the tripling
restriction. The formula also holds when m > n, with choose(n,m) = 0. -/
theorem count_eq_choose (n m : Nat) : count n m = n.choose m * 2 ^ (n - m) := by
  classical
  let e := Equiv.sigmaSubtypeFiberEquivSubtype
    (middlePositions (n := n))
    (p := fun w => middleCount w = m) (q := fun s => s.card = m) (fun _ => Iff.rfl)
  change Fintype.card {w : Fin n → Label // middleCount w = m} = _
  rw [← Fintype.card_congr e, Fintype.card_sigma]
  calc
    _ = ∑ _s : {s : Finset (Fin n) // s.card = m}, 2 ^ (n - m) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [card_middle_fiber, s.property]
    _ = n.choose m * 2 ^ (n - m) := by simp

theorem count_eq_zero_of_lt {n m : Nat} (h : n < m) : count n m = 0 := by
  simp [count_eq_choose, Nat.choose_eq_zero_of_lt h]

/-- The complete fixed-middle classes partition all 3^n label words. -/
theorem sum_count (n : Nat) : ∑ m ∈ Finset.range (n + 1), count n m = 3 ^ n := by
  have h := add_pow (1 : Nat) 2 n
  simpa only [show (1 : Nat) + 2 = 3 from rfl, one_pow, one_mul,
    count_eq_choose, Nat.mul_comm, Nat.cast_id] using h.symm

/-- An actual largest retained-word family achieves the integer average bound.
This includes n = 0 and makes no divisibility assumption. -/
theorem exists_max_sector (n : Nat) :
    ∃ m, m ≤ n ∧ (∀ j, j ≤ n → count n j ≤ count n m) ∧
      3 ^ n ≤ (n + 1) * count n m := by
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image (Finset.range (n + 1)) (count n) (by simp)
  refine ⟨m, by simpa using hm, ?_, ?_⟩
  · intro j hj
    exact hmax j (by simpa using hj)
  · calc
      3 ^ n = ∑ j ∈ Finset.range (n + 1), count n j := (sum_count n).symm
      _ ≤ ∑ _j ∈ Finset.range (n + 1), count n m :=
        Finset.sum_le_sum (fun j hj => hmax j hj)
      _ = (n + 1) * count n m := by simp

/-- The finite sector indices enumerate exactly the actual retained words. -/
def sectorEnumeration (n m : Nat) : Fin (n.choose m * 2 ^ (n - m)) ≃ Word n m :=
  (finCongr (count_eq_choose n m).symm).trans (Fintype.equivFin (Word n m)).symm

/-- The counted indices cover every retained second-leg coordinate. -/
theorem enumeratedY_covers (r b n m : Nat) (hr : 0 < r) (hb : 0 < b)
    (y : keptY r b n m) :
    ∃ (j : Fin (n.choose m * 2 ^ (n - m)))
      (v : sectorY r b n m (sectorEnumeration n m j)),
      sectorEmbeddingY r b n m hr hb (sectorEnumeration n m j) v = y := by
  obtain ⟨w, v, hv⟩ := sectorEmbeddingY_covers r b n m hr hb y
  refine ⟨(sectorEnumeration n m).symm w, ?_⟩
  rw [Equiv.apply_symm_apply]
  exact ⟨v, hv⟩

theorem enumeratedZ_covers (r b n m : Nat) (hr : 0 < r) (hb : 0 < b)
    (z : keptZ r b n m) :
    ∃ (j : Fin (n.choose m * 2 ^ (n - m)))
      (v : sectorZ r b n m (sectorEnumeration n m j)),
      sectorEmbeddingZ r b n m hr hb (sectorEnumeration n m j) v = z := by
  obtain ⟨w, v, hv⟩ := sectorEmbeddingZ_covers r b n m hr hb z
  refine ⟨(sectorEnumeration n m).symm w, ?_⟩
  rw [Equiv.apply_symm_apply]
  exact ⟨v, hv⟩

variable (F : Type) [Field F]

/-- The counted indices select the actual block tensors of the FullTensor source. -/
theorem counted_sector_identity (r b n m : Nat) (hr : 0 < r) (hb : 0 < b)
    (j : Fin (n.choose m * 2 ^ (n - m))) (x : Fin n → Fin r)
    (y : sectorY r b n m (sectorEnumeration n m j))
    (z : sectorZ r b n m (sectorEnumeration n m j)) :
    triplingFromFull F r b n m hr hb x
      (sectorEmbeddingY r b n m hr hb (sectorEnumeration n m j) y)
      (sectorEmbeddingZ r b n m hr hb (sectorEnumeration n m j) z) =
      ∏ i, block F r b ((sectorEnumeration n m j).val i) (x i) (y i) (z i) :=
  triplingFromFull_sector_identity F r b n m hr hb (sectorEnumeration n m j) x y z

theorem counted_cross_sector_zero (r b n m : Nat) (hr : 0 < r) (hb : 0 < b)
    (j k : Fin (n.choose m * 2 ^ (n - m))) (h : j ≠ k) (x : Fin n → Fin r)
    (y : sectorY r b n m (sectorEnumeration n m j))
    (z : sectorZ r b n m (sectorEnumeration n m k)) :
    triplingFromFull F r b n m hr hb x
      (sectorEmbeddingY r b n m hr hb (sectorEnumeration n m j) y)
      (sectorEmbeddingZ r b n m hr hb (sectorEnumeration n m k) z) = 0 := by
  apply triplingFromFull_cross_sector_zero F r b n m hr hb
  exact fun he => h ((sectorEnumeration n m).injective he)

private def zeroY (r b : Nat) (hr : 0 < r) (hb : 0 < b) (s : Label) :
    Fin (yWidth r b s) := ⟨0, by cases s <;> simp only [yWidth] <;> omega⟩

private def zeroZ (r b : Nat) (hr : 0 < r) (hb : 0 < b) (s : Label) :
    Fin (zWidth r b s) := ⟨0, by cases s <;> simp only [zWidth] <;> omega⟩

private theorem orientedBlock_zero (r b : Nat) (hr : 0 < r) (hb : 0 < b) (s : Label) :
    orientedBlock F r b s ⟨0, hr⟩ (zeroY r b hr hb s) (zeroZ r b hr hb s) = 1 := by
  cases s <;> simp [orientedBlock, TensorRankBridge.convolution, zeroY, zeroZ]

/-- Every counted sector is an actual nonzero block, with a coefficient equal
to one; the shared first-input witness may depend on the sector. -/
theorem counted_sector_nonzero (r b n m : Nat) (hr : 0 < r) (hb : 0 < b)
    (j : Fin (n.choose m * 2 ^ (n - m))) :
    ∃ (x : Fin n → Fin r)
      (y : sectorY r b n m (sectorEnumeration n m j))
      (z : sectorZ r b n m (sectorEnumeration n m j)),
      triplingFromFull F r b n m hr hb x
        (sectorEmbeddingY r b n m hr hb (sectorEnumeration n m j) y)
        (sectorEmbeddingZ r b n m hr hb (sectorEnumeration n m j) z) = 1 := by
  let w := sectorEnumeration n m j
  let x : Fin n → Fin r := fun _ => ⟨0, hr⟩
  let y : sectorY r b n m w := fun i => zeroY r b hr hb (w.val i)
  let z : sectorZ r b n m w := fun i => zeroZ r b hr hb (w.val i)
  refine ⟨fun i => normalizeFirst r (w.val i) (x i), y, z, ?_⟩
  rw [triplingFromFull_normalized_sector F r b n m hr hb w x y z]
  simp only [x, y, z, orientedBlock_zero, Finset.prod_const_one]

end
end MatrixDimensionAudit.TriplingSectorCountBridge

#print axioms MatrixDimensionAudit.TriplingSectorCountBridge.card_middle_fiber
#print axioms MatrixDimensionAudit.TriplingSectorCountBridge.count_eq_choose
#print axioms MatrixDimensionAudit.TriplingSectorCountBridge.count_eq_zero_of_lt
#print axioms MatrixDimensionAudit.TriplingSectorCountBridge.sum_count
#print axioms MatrixDimensionAudit.TriplingSectorCountBridge.exists_max_sector
#print axioms MatrixDimensionAudit.TriplingSectorCountBridge.counted_sector_identity
#print axioms MatrixDimensionAudit.TriplingSectorCountBridge.counted_cross_sector_zero
#print axioms MatrixDimensionAudit.TriplingSectorCountBridge.counted_sector_nonzero
#print axioms MatrixDimensionAudit.TriplingSectorCountBridge.enumeratedY_covers
#print axioms MatrixDimensionAudit.TriplingSectorCountBridge.enumeratedZ_covers
