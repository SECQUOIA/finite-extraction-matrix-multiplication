import formalization.WeightedActionCountBridge
import formalization.OccupationFamilyBridge
import formalization.ScalarProfileGrowthBridge

/-! Actual all-row gain lower bounds with an explicit finite polynomial loss. -/
namespace MatrixDimensionAudit.FamilyTypeGainBridge
open GeneralRowSector AllRowProfile WeightedActionCountBridge FamilyScalingBridge
noncomputable section

/-- Exact profile proportions on all actions of one actual row. -/
def RowProportional (row : Row r i K) : Prop :=
  ∀ a ∈ row.actions, ProfileProportional a

def lowerProportional : {n : ℕ} → LowerRows K n → Prop
  | _, .nil => True
  | _, .cons row tail => RowProportional row ∧ lowerProportional tail

def familyProportional (family : Family n K) : Prop :=
  RowProportional family.top ∧ lowerProportional family.lower

def rowLoss (row : Row r i K) : ℕ := typeLoss row.actions * (row.Z+1)

def lowerLoss : {n : ℕ} → LowerRows K n → ℕ
  | _, .nil => 1
  | _, .cons row tail => rowLoss row * lowerLoss tail

def familyLoss (family : Family n K) : ℕ := rowLoss family.top * lowerLoss family.lower

def rowDegree (row : Row r i K) : ℕ := lossDegree row.actions+1

def lowerDegree : {n : ℕ} → LowerRows K n → ℕ
  | _, .nil => 0
  | _, .cons row tail => rowDegree row + lowerDegree tail

def familyDegree (family : Family n K) : ℕ := rowDegree family.top + lowerDegree family.lower

theorem rowLoss_pos (row : Row r i K) : 0<rowLoss row :=
  Nat.mul_pos (typeLoss_pos _) (Nat.succ_pos _)

theorem lowerLoss_pos (rows : LowerRows K n) : 0<lowerLoss rows := by
  induction rows with
  | nil => exact Nat.zero_lt_one
  | cons row tail ih => exact Nat.mul_pos (rowLoss_pos row) ih

theorem familyLoss_pos (family : Family n K) : 0<familyLoss family :=
  Nat.mul_pos (rowLoss_pos family.top) (lowerLoss_pos family.lower)

theorem lower_count_lower_bound (rows : LowerRows K n)
    (occupation : lowerProportional rows) :
    rows.dimension * lowerNumerator n ^ K ≤
      lowerLoss rows * rows.count * lowerDenominator n ^ K := by
  induction rows with
  | nil => exact Nat.le_refl _
  | @cons n row tail ih =>
    have hr := actual_row_count_lower_bound row (by omega) occupation.1
    have hp : profile (n+2) 2 = 3*(n+2)+1 := by unfold profile; omega
    have hz : profile (n+2) 0 = 3*(n+2)-3 := by simp [profile]
    rw [hp,hz] at hr
    have h := Nat.mul_le_mul hr (ih occupation.2)
    simpa [LowerRows.dimension, LowerRows.count, lowerNumerator, lowerDenominator,
      lowerLoss, rowLoss, Nat.mul_pow, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h

/-- Multiplying the actual row estimates gives the full sharp profile, with
no family gain or sector-count lower bound as a hypothesis. -/
theorem family_count_lower_bound (family : Family n K)
    (occupation : familyProportional family) :
    family.dimension * rowNumerator n ^ K ≤
      familyLoss family * family.count * denominator n ^ K := by
  have ht := actual_row_count_lower_bound family.top (by omega) occupation.1
  have hp : profile (n+2) 1 = 3*(n+2)-1 := by unfold profile; omega
  have hz : profile (n+2) 0 = 3*(n+2)-3 := by simp [profile]
  rw [hp,hz] at ht
  have h := Nat.mul_le_mul ht (lower_count_lower_bound family.lower occupation.2)
  simpa [Family.dimension, Family.count, familyLoss, rowLoss, rowNumerator, denominator,
    Nat.mul_pow, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h

/-- The external factor two is retained exactly in the natural cleared gain. -/
theorem family_gain_lower_bound (family : Family n K)
    (occupation : familyProportional family) :
    family.dimension * numerator n ^ K ≤
      familyLoss family * (2^K * family.count) * denominator n ^ K := by
  have h := Nat.mul_le_mul_left (2^K) (family_count_lower_bound family occupation)
  simpa [numerator, Nat.mul_pow, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h

theorem scaleRow_proportional (s : ℕ) (row : Row r i K)
    (occupation : RowProportional row) : RowProportional (scaleRow s row) :=
  scaleRow_profile_proportional s row occupation

theorem scaleLowerRows_proportional (s : ℕ) (rows : LowerRows K n)
    (occupation : lowerProportional rows) : lowerProportional (scaleLowerRows s rows) := by
  induction rows with
  | nil => trivial
  | cons row tail ih => exact ⟨scaleRow_proportional s row occupation.1, ih occupation.2⟩

theorem scaleFamily_proportional (s : ℕ) (family : Family n K)
    (occupation : familyProportional family) : familyProportional (scaleFamily s family) :=
  ⟨scaleRow_proportional s family.top occupation.1,
    scaleLowerRows_proportional s family.lower occupation.2⟩

theorem rowLoss_scale_le (s : ℕ) (row : Row r i K) :
    rowLoss (scaleRow s row) ≤ (s+1)^rowDegree row * rowLoss row :=
  row_loss_scale_le s row

theorem lowerLoss_scale_le (s : ℕ) (rows : LowerRows K n) :
    lowerLoss (scaleLowerRows s rows) ≤ (s+1)^lowerDegree rows * lowerLoss rows := by
  induction rows with
  | nil => simp [scaleLowerRows, lowerLoss, lowerDegree]
  | cons row tail ih =>
    have h := Nat.mul_le_mul (rowLoss_scale_le s row) ih
    simpa [scaleLowerRows, lowerLoss, lowerDegree, Nat.pow_add,
      Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h

/-- For each fixed seed family, the entire count loss grows polynomially in
its exact natural scale. The seed-dependent degree is explicit. -/
theorem familyLoss_scale_le (s : ℕ) (family : Family n K) :
    familyLoss (scaleFamily s family) ≤
      (s+1)^familyDegree family * familyLoss family := by
  have h := Nat.mul_le_mul (rowLoss_scale_le s family.top) (lowerLoss_scale_le s family.lower)
  simpa [scaleFamily, familyLoss, familyDegree, Nat.pow_add,
    Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h

/-- Every multiple of a proportional seed is an actual family satisfying
the sharp cleared gain inequality up to the explicit polynomial loss. -/
theorem scaled_family_gain_lower_bound (s : ℕ) (family : Family n K)
    (occupation : familyProportional family) :
    family.dimension^s * numerator n ^ (s*K) ≤
      ((s+1)^familyDegree family * familyLoss family) *
        (2^(s*K) * (scaleFamily s family).count) * denominator n ^ (s*K) := by
  have h := family_gain_lower_bound (scaleFamily s family)
    (scaleFamily_proportional s family occupation)
  rw [family_dimension_scale] at h
  exact h.trans (Nat.mul_le_mul_right _
    (Nat.mul_le_mul_right _ (familyLoss_scale_le s family)))

/-- Every constructed occupation row has the required exact ratios on its
actual action list, including its inactive states and zero reset action. -/
theorem occupationRow_proportional (r : ℕ) (hr : 2 ≤ r) (start : Fin (3*r)) :
    RowProportional (OccupationFamilyBridge.occupationRow r hr start) := by
  intro a ha
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
  exact OccupationFamilyBridge.action_profile_proportional r hr start i

/-- Positive-scale rows with exact empirical proportions are constructed,
not supplied by the caller. -/
theorem exists_proportional_row (r : ℕ) (hr : 2 ≤ r) (i : ℕ)
    (hi : 1 ≤ i) (hir : i < 3*r) :
    ∃ K : ℕ, 0<K ∧ ∃ row : Row r i K, RowProportional row := by
  let start : Fin (3*r) := ⟨i-1, by omega⟩
  have he : start.val+1=i := by dsimp [start]; omega
  rw [← he]
  exact ⟨OccupationFamilyBridge.scale r hr start, OccupationFamilyBridge.scale_pos r hr start,
    OccupationFamilyBridge.occupationRow r hr start, occupationRow_proportional r hr start⟩

theorem rowAtProduct_proportional (row : Row r i K) (s : ℕ)
    (occupation : RowProportional row) :
    RowProportional (FamilySynchronizationBridge.rowAtProduct row s) :=
  scaleRow_profile_proportional s row occupation

/-- Proportions are retained through every common-scale synchronization. -/
theorem exists_proportional_lowerRows (n : ℕ) :
    ∃ K : ℕ, 0<K ∧ ∃ rows : LowerRows K n, lowerProportional rows := by
  induction n with
  | zero => exact ⟨1, Nat.zero_lt_one, .nil, trivial⟩
  | succ n ih =>
    obtain ⟨Kt, hKt, tail, ht⟩ := ih
    obtain ⟨Kr, hKr, row, hr⟩ := exists_proportional_row (n+2) (by omega) 2 (by omega) (by omega)
    exact ⟨Kr*Kt, Nat.mul_pos hKr hKt,
      .cons (FamilySynchronizationBridge.rowAtProduct row Kt) (scaleLowerRows Kr tail),
      rowAtProduct_proportional row Kt hr, scaleLowerRows_proportional Kr tail ht⟩

/-- An actual proportional seed family exists for every row cutoff, at a
single positive common injection scale. -/
theorem exists_proportional_family (n : ℕ) :
    ∃ K : ℕ, 0<K ∧ ∃ family : Family n K, familyProportional family := by
  obtain ⟨Kl, hKl, lower, hl⟩ := exists_proportional_lowerRows n
  obtain ⟨Kt, hKt, top, ht⟩ := exists_proportional_row (n+2) (by omega) 1 (by omega) (by omega)
  exact ⟨Kt*Kl, Nat.mul_pos hKt hKl,
    FamilySynchronizationBridge.synchronizeFamily top lower,
    rowAtProduct_proportional top Kl ht, scaleLowerRows_proportional Kt lower hl⟩

/-- The finite all-family gain theorem has no seed, occupation, row balance,
or gain premise: all of them are obtained from the rational walk. -/
theorem exists_seed_with_scaled_gain (n : ℕ) :
    ∃ K : ℕ, 0<K ∧ ∃ family : Family n K, ∀ s : ℕ,
      family.dimension^s * numerator n ^ (s*K) ≤
        ((s+1)^familyDegree family * familyLoss family) *
          (2^(s*K) * (scaleFamily s family).count) * denominator n ^ (s*K) := by
  obtain ⟨K,hK,family,hf⟩ := exists_proportional_family n
  exact ⟨K,hK,family,fun s => scaled_family_gain_lower_bound s family hf⟩

private theorem list_range_prod_cast (f : ℕ → ℕ) (m : ℕ) :
    ((((List.range m).map f).prod : ℕ) : ℝ) = ∏ h ∈ Finset.range m, (f h : ℝ) := by
  rw [← List.prod_toFinset f (List.nodup_range : (List.range m).Nodup)]
  simp only [List.toFinset_range, Nat.cast_prod]

/-- The natural cleared profile uses exactly the manuscript's finite product. -/
theorem s_times_denominator (n : ℕ) :
    ScalarProfileGrowthBridge.s (n+2) * (denominator n : ℝ) =
      ∏ h ∈ Finset.range (n+1), (3*((h : ℝ)+1)+1) := by
  rw [denominator_eq_product, list_range_prod_cast]
  simp only [ScalarProfileGrowthBridge.s, show n+2-1=n+1 by omega]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro h _
  push_cast
  have hd : 3*((h : ℝ)+1) ≠ 0 := by positivity
  field_simp

/-- Exact normalization: numerator/denominator is the diagonal scalar
profile F(a,a), with a=n+2. -/
theorem diagonal_profile_cleared (n : ℕ) :
    ScalarProfileGrowthBridge.profile (n+2) (n+2) * (denominator n : ℝ) =
      (numerator n : ℝ) := by
  have h := congrArg (fun t : ℕ => (t : ℝ)) (numerator_eq_diagonal_product n)
  have hsub : (((3*(n+2)-1 : ℕ) : ℝ)) = 3*((n+2 : ℕ) : ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 1≤3*(n+2))]
    push_cast
    ring
  simp only [Nat.cast_mul, Nat.cast_ofNat, hsub, list_range_prod_cast] at h
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] at h
  rw [ScalarProfileGrowthBridge.profile_diagonal]
  have hs := s_times_denominator n
  push_cast
  nlinarith

/-- The actual gain approaches the exact scalar profile up to the finite
family loss; this real-valued statement is obtained by clearing positive
natural denominators in the proved cardinality bound. -/
theorem family_scalar_gain_lower_bound (family : Family n K)
    (occupation : familyProportional family) :
    (family.dimension : ℝ) * ScalarProfileGrowthBridge.profile (n+2) (n+2) ^ K ≤
      (familyLoss family : ℝ) * (2^K * family.count : ℕ) := by
  have h : (family.dimension : ℝ) * (numerator n : ℝ)^K ≤
      (familyLoss family : ℝ) * (2^K * family.count : ℕ) * (denominator n : ℝ)^K := by
    exact_mod_cast family_gain_lower_bound family occupation
  rw [← diagonal_profile_cleared, mul_pow] at h
  have hd : (0 : ℝ) < denominator n := by exact_mod_cast denominator_pos n
  apply (mul_le_mul_iff_right₀ (pow_pos hd K)).mp
  simpa only [mul_assoc, mul_comm, mul_left_comm] using h

/-- The scalar-profile lower bound for every natural multiple of an actual
proportional seed, with an explicit polynomial loss in that multiple. -/
theorem scaled_family_scalar_gain_lower_bound (s : ℕ) (family : Family n K)
    (occupation : familyProportional family) :
    (family.dimension : ℝ)^s * ScalarProfileGrowthBridge.profile (n+2) (n+2) ^ (s*K) ≤
      (((s+1)^familyDegree family * familyLoss family : ℕ) : ℝ) *
        (2^(s*K) * (scaleFamily s family).count : ℕ) := by
  have h := family_scalar_gain_lower_bound (scaleFamily s family)
    (scaleFamily_proportional s family occupation)
  rw [family_dimension_scale, Nat.cast_pow] at h
  have hl : (familyLoss (scaleFamily s family) : ℝ) ≤
      (((s+1)^familyDegree family * familyLoss family : ℕ) : ℝ) := by
    exact_mod_cast familyLoss_scale_le s family
  exact h.trans (mul_le_mul_of_nonneg_right hl (Nat.cast_nonneg _))

/-- The existing sharp upper count estimate uses the same scalar profile,
for every actual family whether or not its histograms are proportional. -/
theorem family_scalar_gain_upper_bound (family : Family n K) :
    (2^K * family.count : ℕ) ≤
      (family.dimension : ℝ) * ScalarProfileGrowthBridge.profile (n+2) (n+2)^K := by
  have h : (2^K * family.count : ℕ) * (denominator n : ℝ)^K ≤
      (family.dimension : ℝ) * (numerator n : ℝ)^K := by
    exact_mod_cast family.sharp_actual_gain
  rw [← diagonal_profile_cleared, mul_pow] at h
  have hd : (0 : ℝ) < denominator n := by exact_mod_cast denominator_pos n
  apply (mul_le_mul_iff_right₀ (pow_pos hd K)).mp
  simpa only [mul_assoc, mul_comm, mul_left_comm] using h

end
end MatrixDimensionAudit.FamilyTypeGainBridge

#print axioms MatrixDimensionAudit.FamilyTypeGainBridge.RowProportional
#print axioms MatrixDimensionAudit.FamilyTypeGainBridge.lowerProportional
#print axioms MatrixDimensionAudit.FamilyTypeGainBridge.familyProportional
#print axioms MatrixDimensionAudit.FamilyTypeGainBridge.rowLoss
#print axioms MatrixDimensionAudit.FamilyTypeGainBridge.lowerLoss
#print axioms MatrixDimensionAudit.FamilyTypeGainBridge.familyLoss
#print axioms MatrixDimensionAudit.FamilyTypeGainBridge.rowDegree
#print axioms MatrixDimensionAudit.FamilyTypeGainBridge.lowerDegree
#print axioms MatrixDimensionAudit.FamilyTypeGainBridge.familyDegree
#print axioms MatrixDimensionAudit.FamilyTypeGainBridge.rowLoss_pos
#print axioms MatrixDimensionAudit.FamilyTypeGainBridge.lowerLoss_pos
#print axioms MatrixDimensionAudit.FamilyTypeGainBridge.familyLoss_pos
#print axioms MatrixDimensionAudit.FamilyTypeGainBridge.lower_count_lower_bound
#print axioms MatrixDimensionAudit.FamilyTypeGainBridge.family_count_lower_bound
#print axioms MatrixDimensionAudit.FamilyTypeGainBridge.family_gain_lower_bound
#print axioms MatrixDimensionAudit.FamilyTypeGainBridge.scaleRow_proportional
#print axioms MatrixDimensionAudit.FamilyTypeGainBridge.scaleLowerRows_proportional
#print axioms MatrixDimensionAudit.FamilyTypeGainBridge.scaleFamily_proportional
#print axioms MatrixDimensionAudit.FamilyTypeGainBridge.rowLoss_scale_le
#print axioms MatrixDimensionAudit.FamilyTypeGainBridge.lowerLoss_scale_le
#print axioms MatrixDimensionAudit.FamilyTypeGainBridge.familyLoss_scale_le
#print axioms MatrixDimensionAudit.FamilyTypeGainBridge.scaled_family_gain_lower_bound
#print axioms MatrixDimensionAudit.FamilyTypeGainBridge.occupationRow_proportional
#print axioms MatrixDimensionAudit.FamilyTypeGainBridge.exists_proportional_row
#print axioms MatrixDimensionAudit.FamilyTypeGainBridge.rowAtProduct_proportional
#print axioms MatrixDimensionAudit.FamilyTypeGainBridge.exists_proportional_lowerRows
#print axioms MatrixDimensionAudit.FamilyTypeGainBridge.exists_proportional_family
#print axioms MatrixDimensionAudit.FamilyTypeGainBridge.exists_seed_with_scaled_gain
#print axioms MatrixDimensionAudit.FamilyTypeGainBridge.s_times_denominator
#print axioms MatrixDimensionAudit.FamilyTypeGainBridge.diagonal_profile_cleared
#print axioms MatrixDimensionAudit.FamilyTypeGainBridge.family_scalar_gain_lower_bound
#print axioms MatrixDimensionAudit.FamilyTypeGainBridge.scaled_family_scalar_gain_lower_bound
#print axioms MatrixDimensionAudit.FamilyTypeGainBridge.family_scalar_gain_upper_bound
