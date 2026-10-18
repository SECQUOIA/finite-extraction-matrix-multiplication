import formalization.FamilyTypeGainBridge

/-! The actual scaled-family log gain converges to the finite scalar profile. -/
namespace MatrixDimensionAudit.ScaledFamilyGainLimitBridge
open scoped Topology
open Filter AllRowProfile FamilyTypeGainBridge FamilyScalingBridge
noncomputable section

/-- A fixed polynomial counting loss has vanishing log cost per scaled injection. -/
def polynomialPenalty (C K : ℝ) (d s : ℕ) : ℝ :=
  Real.log (((s : ℝ) + 1)^d * C) / ((s : ℝ) * K)

theorem polynomialPenalty_tendsto (C K : ℝ) (d : ℕ)
    (hC : 0 < C) (hK : 0 < K) :
    Tendsto (polynomialPenalty C K d) atTop (𝓝 0) := by
  have hshift : Tendsto (fun s : ℕ => (s : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun s : ℕ => Real.log ((s : ℝ) + 1) / ((s : ℝ) * K))
      atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop K (-K) 1 (ne_of_gt hK)).comp hshift
    convert h using 1
    simp only [pow_one]
    funext s
    congr 1
    ring
  have hconstant : Tendsto (fun s : ℕ => Real.log C / ((s : ℝ) * K))
      atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_mul_const hK)
  have h := (hlog.const_mul (d : ℝ)).add hconstant
  convert h using 1
  · funext s
    unfold polynomialPenalty
    rw [Real.log_mul (pow_ne_zero _ (by positivity)) (ne_of_gt hC), Real.log_pow]
    ring
  · simp

private theorem actual_actions_count_pos (actions : List (GeneralRowSector.Action r)) :
    0 < GeneralRowSector.totalCount actions := by
  induction actions with
  | nil => simp [GeneralRowSector.totalCount]
  | cons a tail ih =>
    simpa [GeneralRowSector.totalCount] using
      Nat.mul_pos (FlowActionTensorBridge.action_count_pos a) ih

private theorem actual_row_count_pos (row : Row r i K) : 0 < row.count :=
  Nat.mul_pos (actual_actions_count_pos row.actions)
    (FlowActionTensorBridge.row_tripling_count_pos row.Z)

private theorem actual_lower_count_pos (rows : LowerRows K n) : 0 < rows.count := by
  induction rows with
  | nil => exact Nat.zero_lt_one
  | cons row tail ih => exact Nat.mul_pos (actual_row_count_pos row) ih

private theorem actual_family_count_pos (family : Family n K) : 0 < family.count :=
  Nat.mul_pos (actual_row_count_pos family.top) (actual_lower_count_pos family.lower)

private theorem actual_family_dimension_pos (family : Family n K) : 0 < family.dimension :=
  lt_of_lt_of_le (Nat.pow_pos (Nat.mul_pos (by decide) (Nat.pow_pos (by decide))))
    (GeneralRowDimension.family_branch_baseline family)

/-- The actual count and dimension, retaining the external factor two. At
scale zero the real quotient is interpreted by Lean's usual total division. -/
def normalizedLogGain (family : Family n K) (s : ℕ) : ℝ :=
  Real.log ((2^(s*K) * (scaleFamily s family).count : ℕ) /
    ((scaleFamily s family).dimension : ℝ)) / ((s*K : ℕ) : ℝ)

theorem normalizedLogGain_bounds (family : Family n K)
    (occupation : familyProportional family) (hK : 0 < K) (s : ℕ) (hs : 0 < s) :
    Real.log (ScalarProfileGrowthBridge.profile (n+2) (n+2)) -
      polynomialPenalty (familyLoss family) K (familyDegree family) s ≤
        normalizedLogGain family s ∧
    normalizedLogGain family s ≤
      Real.log (ScalarProfileGrowthBridge.profile (n+2) (n+2)) := by
  let F := ScalarProfileGrowthBridge.profile (n+2) (n+2)
  let D : ℝ := (family.dimension : ℝ)^s
  let H : ℝ := (2^(s*K) * (scaleFamily s family).count : ℕ)
  let P : ℝ := (((s+1)^familyDegree family * familyLoss family : ℕ) : ℝ)
  have hF : 0 < F := ScalarProfileGrowthBridge.profile_pos _ _ (by omega) (by omega)
  have hD : 0 < D := pow_pos (by exact_mod_cast actual_family_dimension_pos family) _
  have hH : 0 < H := by
    dsimp [H]
    exact_mod_cast Nat.mul_pos (Nat.pow_pos (by decide : 0 < 2))
      (actual_family_count_pos (scaleFamily s family))
  have hP : 0 < P := by
    dsimp [P]
    exact_mod_cast Nat.mul_pos (Nat.pow_pos (Nat.succ_pos s)) (familyLoss_pos family)
  have hN : (0 : ℝ) < (s*K : ℕ) := by exact_mod_cast Nat.mul_pos hs hK
  have hlo : D * F^(s*K) ≤ P * H :=
    scaled_family_scalar_gain_lower_bound s family occupation
  have hup : H ≤ D * F^(s*K) := by
    have h := family_scalar_gain_upper_bound (scaleFamily s family)
    simpa only [family_dimension_scale, Nat.cast_pow] using h
  have hgain : 0 < H / D := div_pos hH hD
  have hlow : F^(s*K) ≤ P * (H / D) := by
    rw [← mul_div_assoc]
    exact (le_div_iff₀ hD).mpr (by simpa only [mul_comm] using hlo)
  have hhigh : H / D ≤ F^(s*K) :=
    (div_le_iff₀ hD).mpr (by simpa only [mul_comm] using hup)
  have hll := Real.log_le_log (pow_pos hF _) hlow
  rw [Real.log_pow, Real.log_mul (ne_of_gt hP) (ne_of_gt hgain)] at hll
  have hlu := Real.log_le_log hgain hhigh
  rw [Real.log_pow] at hlu
  have heq : normalizedLogGain family s = Real.log (H / D) / ((s*K : ℕ) : ℝ) := by
    simp only [normalizedLogGain, family_dimension_scale, Nat.cast_pow]
    rfl
  have hpen : polynomialPenalty (familyLoss family) K (familyDegree family) s =
      Real.log P / ((s*K : ℕ) : ℝ) := by
    simp only [polynomialPenalty, P, Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one]
  rw [heq, hpen]
  constructor
  · apply (le_div_iff₀ hN).mpr
    have hne : ((s*K : ℕ) : ℝ) ≠ 0 := ne_of_gt hN
    rw [sub_mul, div_mul_cancel₀ _ hne]
    linarith
  · exact (div_le_iff₀ hN).mpr (by simpa only [mul_comm] using hlu)

/-- For each actual proportional seed, normalized log gain converges to the
literal scalar profile. The polynomial loss is derived from actual counts. -/
theorem normalizedLogGain_tendsto (family : Family n K)
    (occupation : familyProportional family) (hK : 0 < K) :
    Tendsto (normalizedLogGain family) atTop
      (𝓝 (Real.log (ScalarProfileGrowthBridge.profile (n+2) (n+2)))) := by
  let L := Real.log (ScalarProfileGrowthBridge.profile (n+2) (n+2))
  have hp := polynomialPenalty_tendsto (familyLoss family) K (familyDegree family)
    (by exact_mod_cast familyLoss_pos family) (by exact_mod_cast hK)
  have hdiff : Tendsto (fun s => L - normalizedLogGain family s) atTop (𝓝 0) := by
    apply squeeze_zero' _ _ hp
    · filter_upwards [eventually_ge_atTop 1] with s hs
      exact sub_nonneg.mpr (normalizedLogGain_bounds family occupation hK s (by omega)).2
    · filter_upwards [eventually_ge_atTop 1] with s hs
      have h := (normalizedLogGain_bounds family occupation hK s (by omega)).1
      dsimp [L]
      linarith
  have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => L) atTop (𝓝 L)).sub hdiff
  simpa only [sub_zero, sub_sub_cancel] using h

/-- At every row cutoff, an actual positive-scale seed with this limit exists;
neither the seed nor a gain premise is supplied by the caller. -/
theorem exists_seed_with_gain_limit (n : ℕ) :
    ∃ K : ℕ, 0 < K ∧ ∃ family : Family n K,
      Tendsto (normalizedLogGain family) atTop
        (𝓝 (Real.log (ScalarProfileGrowthBridge.profile (n+2) (n+2)))) := by
  obtain ⟨K, hK, family, occupation⟩ := exists_proportional_family n
  exact ⟨K, hK, family, normalizedLogGain_tendsto family occupation hK⟩

/-- Every strict threshold below the scalar log profile is achieved by one
finite actual legal family at a positive injection scale. -/
theorem exists_actual_family_gain_gt (n : ℕ) (c : ℝ)
    (hc : c < Real.log (ScalarProfileGrowthBridge.profile (n+2) (n+2))) :
    ∃ K : ℕ, 0 < K ∧ ∃ family : Family n K,
      c < Real.log ((2^K * family.count : ℕ) / (family.dimension : ℝ)) / (K : ℝ) := by
  obtain ⟨K, hK, family, hlimit⟩ := exists_seed_with_gain_limit n
  have hevent : ∀ᶠ s in atTop, c < normalizedLogGain family s :=
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => c) atTop (𝓝 c)).eventually_lt hlimit hc
  obtain ⟨s, hs, hgain⟩ := ((eventually_ge_atTop 1).and hevent).exists
  exact ⟨s*K, Nat.mul_pos (by omega) hK, scaleFamily s family, hgain⟩

#print axioms polynomialPenalty
#print axioms polynomialPenalty_tendsto
#print axioms normalizedLogGain
#print axioms normalizedLogGain_bounds
#print axioms normalizedLogGain_tendsto
#print axioms exists_seed_with_gain_limit
#print axioms exists_actual_family_gain_gt

end
end MatrixDimensionAudit.ScaledFamilyGainLimitBridge
