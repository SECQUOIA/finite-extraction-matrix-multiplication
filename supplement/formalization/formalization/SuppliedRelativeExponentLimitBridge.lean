import formalization.AsymptoticPooledCostBridge
import Mathlib

/-! The interpolation and reuse limits of the actual supplied relative maps. -/
namespace MatrixDimensionAudit.SuppliedRelativeExponentLimitBridge
open Filter
open scoped Topology
open AllRowProfile GlobalFamilySampleBridge SuppliedGlobalRestrictionBridge
open OAI.MatrixMultiplication.Arithmetic
noncomputable section

/-- The actual logarithmic width gain per joint source power. -/
def gain (family : Family n K) : ℝ :=
  (K : ℝ) * Real.log 2 + Real.log (family.count : ℝ) - Real.log (family.dimension : ℝ)

/-- The limiting exponent retains every local copy cost and the external source
rank charge; the catalyst and interpolation costs are removed only by limits. -/
def limitingExponent (family : Family n K) : ℝ :=
  (3 * (K : ℝ) * Real.log ((2 * (n + 2) - 1 : ℕ) : ℝ) +
    Real.log (familyCopies family : ℝ) - 3 * Real.log (family.count : ℝ)) / gain family

/-- At fixed tensor power k, reuse removes only the common-catalyst charge. -/
def exactifiedExponent (family : Family n K) (k : ℕ) : ℝ :=
  limitingExponent family + Real.log (exactification family k : ℝ) / ((k : ℝ) * gain family)

theorem family_cost_pos (family : Family n K) : 0 < FamilyRankSupplyBridge.familyCost family := by
  simpa only [sourceRank, Nat.mul_zero, pow_zero, pow_one, one_mul] using source_rank_pos family 1 0

theorem exactification_pos (family : Family n K) (k : ℕ) : 0 < exactification family k := by
  unfold exactification
  omega

/-- The actual target matrix base contributes K*log 2+log M. -/
theorem log_output_base (family : Family n K) :
    Real.log ((2 ^ K * family.count : ℕ) : ℝ) =
      (K : ℝ) * Real.log 2 + Real.log (family.count : ℝ) := by
  have hM : (0 : ℝ) < family.count := by exact_mod_cast count_pos family
  rw [Nat.cast_mul, Nat.cast_pow,
    Real.log_mul (by positivity) (ne_of_gt hM), Real.log_pow]
  norm_num

/-- Expand the supplied joint-source and exactification copy charge from its
proved actual resource formula, not a caller-supplied asymptotic expression. -/
theorem log_input_copies (family : Family n K) (k j : ℕ) :
    Real.log (inputCopies family k j : ℝ) =
      (k : ℝ) * Real.log (FamilyRankSupplyBridge.familyCost family : ℝ) +
      (j : ℝ) * Real.log (exactification family k : ℝ) +
      (k : ℝ) * j * Real.log (familyCopies family : ℝ) +
      3 * (K : ℝ) * k * j * Real.log ((2 * (n + 2) - 1 : ℕ) : ℝ) := by
  have hC : (0 : ℝ) < FamilyRankSupplyBridge.familyCost family := by exact_mod_cast family_cost_pos family
  have hL : (0 : ℝ) < familyCopies family := by exact_mod_cast copies_pos family
  have hE : (0 : ℝ) < exactification family k := by exact_mod_cast exactification_pos family k
  have hU : (0 : ℝ) < ((2 * (n + 2) - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 2 * (n+2)-1)
  rw [input_copies_formula]
  simp only [Nat.cast_mul, Nat.cast_pow]
  change Real.log (((FamilyRankSupplyBridge.familyCost family : ℝ) ^ k *
    (exactification family k : ℝ) ^ j * (familyCopies family : ℝ) ^ (k*j)) *
      (((2 * (n+2)-1 : ℕ) : ℝ) ^ (3*K*k*j))) = _
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity)]
  simp only [Real.log_pow, Nat.cast_mul, Nat.cast_ofNat]

/-- The actual independent target copy count has logarithm 3kj*log M. -/
theorem log_output_copies (family : Family n K) (k j : ℕ) :
    Real.log (outputCopies family k j : ℝ) =
      3 * (k : ℝ) * j * Real.log (family.count : ℝ) := by
  simp only [outputCopies, Nat.cast_pow, Real.log_pow, Nat.cast_mul, Nat.cast_ofNat]

/-- Both complete matrix widths contribute exactly kj times the actual gain. -/
theorem log_width_gap (family : Family n K) (k j : ℕ) :
    Real.log (outputWidth family k j : ℝ) - Real.log (inputWidth family k j : ℝ) =
      (k : ℝ) * j * gain family := by
  rw [outputWidth, inputWidth, Nat.cast_pow, Nat.cast_pow]
  simp only [Real.log_pow]
  rw [log_output_base]
  push_cast
  unfold gain
  ring

/-- Positive log gain gives positive gain for every actual positive k,j. -/
theorem actual_width_gain (family : Family n K) (hg : 0 < gain family)
    (k j : ℕ) (hk : 0 < k) (hj : 0 < j) :
    inputWidth family k j < outputWidth family k j := by
  have hA : (0 : ℝ) < inputWidth family k j := by exact_mod_cast input_width_pos family k j
  have hB : (0 : ℝ) < outputWidth family k j := by exact_mod_cast output_width_pos family k j
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  have hgap : 0 < Real.log (outputWidth family k j : ℝ) - Real.log (inputWidth family k j : ℝ) := by
    rw [log_width_gap]
    positivity
  have h := (Real.log_lt_log_iff hA hB).mp (sub_pos.mp hgap)
  exact_mod_cast h

/-- Exact decomposition of the actual supplied pooled exponent. Each overhead
is present at finite k,j; only its own limit can remove it. -/
theorem relative_exponent_formula (family : Family n K) (hg : 0 < gain family)
    (k j : ℕ) (hk : 0 < k) (hj : 0 < j) :
    relativeExponent family k j = exactifiedExponent family k +
      Real.log (FamilyRankSupplyBridge.familyCost family : ℝ) / ((j : ℝ) * gain family) := by
  unfold relativeExponent
  rw [log_input_copies, log_output_copies, log_width_gap]
  unfold exactifiedExponent limitingExponent
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  have hjR : (j : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hj
  field_simp [hkR, hjR, ne_of_gt hg]
  ring

/-- Exactification has affine natural degree k*d+1, whose logarithm costs
sublinearly in k, including d=0. -/
theorem tendsto_log_affine_div_nat (d : ℕ) :
    Tendsto (fun k : ℕ => Real.log ((k * d + 1 : ℕ) : ℝ) / (k : ℝ))
      atTop (𝓝 0) := by
  have hlog : Tendsto (fun k : ℕ => Real.log (k : ℝ) / (k : ℝ)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hconst := tendsto_const_div_atTop_nhds_zero_nat (Real.log ((d : ℝ) + 1))
  have hupper : Tendsto
      (fun k : ℕ => Real.log (k : ℝ) / (k : ℝ) +
        Real.log ((d : ℝ) + 1) / (k : ℝ)) atTop (𝓝 0) := by
    simpa only [add_zero] using hlog.add hconst
  apply squeeze_zero' _ _ hupper
  · filter_upwards [] with k
    apply div_nonneg
    · exact Real.log_nonneg (by exact_mod_cast Nat.le_add_left 1 (k * d))
    · positivity
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with k hk
    have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hkpos : (0 : ℝ) < k := lt_of_lt_of_le zero_lt_one hkr
    have hdpos : 0 < (d : ℝ) + 1 := by positivity
    rw [← add_div, ← Real.log_mul (ne_of_gt hkpos) (ne_of_gt hdpos)]
    apply div_le_div_of_nonneg_right _ (le_of_lt hkpos)
    apply Real.log_le_log (by positivity)
    push_cast
    nlinarith

theorem tendsto_const_div_nat_mul (c g : ℝ) :
    Tendsto (fun j : ℕ => c / ((j : ℝ) * g)) atTop (𝓝 0) := by
  simpa only [div_div, mul_comm] using tendsto_const_div_atTop_nhds_zero_nat (c / g)

/-- Reuse removes the charged common-catalyst factor at fixed positive k. -/
theorem reuse_tendsto (family : Family n K) (hg : 0 < gain family)
    (k : ℕ) (hk : 0 < k) :
    Tendsto (fun j : ℕ => relativeExponent family k j) atTop
      (𝓝 (exactifiedExponent family k)) := by
  have h := (tendsto_const_nhds (x := exactifiedExponent family k)).add
    (tendsto_const_div_nat_mul (Real.log (FamilyRankSupplyBridge.familyCost family : ℝ))
      (gain family))
  simp only [add_zero] at h
  apply (tendsto_congr' ?_).mpr h
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with j hj
  exact relative_exponent_formula family hg k j hk (by omega)

/-- Powering removes the actual affine exactification cost, after reuse. -/
theorem exactification_tendsto (family : Family n K) :
    Tendsto (exactifiedExponent family) atTop (𝓝 (limitingExponent family)) := by
  have h := (tendsto_const_nhds (x := limitingExponent family)).add
    ((tendsto_log_affine_div_nat (familyDegree family)).div_const (gain family))
  change Tendsto (fun k : ℕ => limitingExponent family +
    Real.log ((k * familyDegree family + 1 : ℕ) : ℝ) / ((k : ℝ) * gain family))
      atTop (𝓝 (limitingExponent family))
  simpa only [div_div, zero_div, add_zero] using h

/-- Every strict improvement target above the derived limit is achieved by
finite positive tensor and reuse powers of the actual supplied maps. -/
theorem exists_positive_parameters_below (family : Family n K) (hg : 0 < gain family)
    (p : ℝ) (hp : limitingExponent family < p) :
    ∃ k : ℕ, 0 < k ∧ ∃ j : ℕ, 0 < j ∧
      inputWidth family k j < outputWidth family k j ∧ relativeExponent family k j < p := by
  have hk_event : ∀ᶠ k : ℕ in atTop, exactifiedExponent family k < p :=
    (tendsto_order.mp (exactification_tendsto family)).2 p hp
  obtain ⟨k, hk, hkp⟩ := ((eventually_ge_atTop (1 : ℕ)).and hk_event).exists
  have hkpos : 0 < k := by omega
  have hj_event : ∀ᶠ j : ℕ in atTop, relativeExponent family k j < p :=
    (tendsto_order.mp (reuse_tendsto family hg k hkpos)).2 p hkp
  obtain ⟨j, hj, hjp⟩ := ((eventually_ge_atTop (1 : ℕ)).and hj_event).exists
  have hjpos : 0 < j := by omega
  exact ⟨k, hkpos, j, hjpos, actual_width_gain family hg k j hkpos hjpos, hjp⟩

/-- The actual finite maps and the already proved pooled executor give every
strictly larger exponent. No caller supplies a resource formula or a limit. -/
theorem admissibleExponent_of_limit_lt (family : Family n K) (hg : 0 < gain family)
    (p : ℝ) (hp : limitingExponent family < p) : AdmissibleExponent ℚ p := by
  obtain ⟨k, hk, j, hj, hgain, hrho⟩ := exists_positive_parameters_below family hg p hp
  have h := AsymptoticPooledCostBridge.supplied_pooledExponent_admissible family k j hgain
  change AdmissibleExponent ℚ (relativeExponent family k j) at h
  exact h.mono hrho.le

/-- Arbitrarily close actual algorithms bound the ordinary arithmetic exponent. -/
theorem omega_le_limitingExponent (family : Family n K) (hg : 0 < gain family) :
    omega ℚ ≤ limitingExponent family := by
  apply le_of_forall_pos_le_add
  intro ε hε
  exact omega_le_of_admissibleExponent (admissibleExponent_of_limit_lt family hg
    (limitingExponent family + ε) (by linarith))

/-- Admissibility uses arbitrarily small positive slack, so the limit itself
is admissible in the library's sense, without one finite map attaining it. -/
theorem limitingExponent_admissible (family : Family n K) (hg : 0 < gain family) :
    AdmissibleExponent ℚ (limitingExponent family) :=
  admissibleExponent_iff_omega_le.mpr (omega_le_limitingExponent family hg)

/-- The lower bound two is derived from actual arithmetic algorithms. -/
theorem limitingExponent_ge_two (family : Family n K) (hg : 0 < gain family) :
    2 ≤ limitingExponent family :=
  omega_two_le.trans (omega_le_limitingExponent family hg)

#print axioms gain
#print axioms limitingExponent
#print axioms exactifiedExponent
#print axioms family_cost_pos
#print axioms exactification_pos
#print axioms log_output_base
#print axioms log_input_copies
#print axioms log_output_copies
#print axioms log_width_gap
#print axioms actual_width_gain
#print axioms relative_exponent_formula
#print axioms tendsto_log_affine_div_nat
#print axioms tendsto_const_div_nat_mul
#print axioms reuse_tendsto
#print axioms exactification_tendsto
#print axioms exists_positive_parameters_below
#print axioms admissibleExponent_of_limit_lt
#print axioms omega_le_limitingExponent
#print axioms limitingExponent_admissible
#print axioms limitingExponent_ge_two

end
end MatrixDimensionAudit.SuppliedRelativeExponentLimitBridge
