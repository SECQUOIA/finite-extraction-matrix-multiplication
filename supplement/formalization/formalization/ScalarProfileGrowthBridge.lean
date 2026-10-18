module
public import Mathlib

public section

/-! Exact finite scalar profile and its diagonal logarithmic growth. -/
namespace MatrixDimensionAudit.ScalarProfileGrowthBridge
open scoped BigOperators Topology
open Filter
noncomputable section

/-- The manuscript's finite product, with its intended domain a ≥ 1. -/
def s (a : ℕ) : ℝ :=
  ∏ h ∈ Finset.range (a - 1), (1 + 1 / (3 * ((h : ℝ) + 1)))

@[simp] theorem s_one : s 1 = 1 := by simp [s]

theorem s_pos (a : ℕ) : 0 < s a := by
  unfold s
  apply Finset.prod_pos
  intro i _
  positivity

theorem s_succ (a : ℕ) (ha : 1 ≤ a) :
    s (a + 1) = s a * (1 + 1 / (3 * (a : ℝ))) := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a ≠ 0)
  simp [s, Finset.prod_range_succ]

private theorem factor_cube_lower (a : ℝ) (ha : 1 ≤ a) :
    a + 1 ≤ a * (1 + 1 / (3 * a)) ^ 3 := by
  have hapos : 0 < a := by linarith
  have identity : (a * (1 + 1 / (3 * a)) ^ 3 - (a + 1)) * (27 * a ^ 2) =
      9 * a + 1 := by field_simp; ring
  have hden : 0 < 27 * a ^ 2 := by positivity
  have hmul : 0 ≤ (a * (1 + 1 / (3 * a)) ^ 3 - (a + 1)) * (27 * a ^ 2) := by
    rw [identity]
    positivity
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_right hden).mp hmul)

private theorem factor_cube_upper (a : ℝ) (ha : 1 ≤ a) :
    ((3 * a - 1) / 2) * (1 + 1 / (3 * a)) ^ 3 ≤ (3 * (a + 1) - 1) / 2 := by
  have hapos : 0 < a := by linarith
  have identity : ((3 * (a + 1) - 1) / 2 -
      ((3 * a - 1) / 2) * (1 + 1 / (3 * a)) ^ 3) * (54 * a ^ 3) =
      6 * a + 1 := by field_simp; ring
  have hden : 0 < 54 * a ^ 3 := by positivity
  have hmul : 0 ≤ ((3 * (a + 1) - 1) / 2 -
      ((3 * a - 1) / 2) * (1 + 1 / (3 * a)) ^ 3) * (54 * a ^ 3) := by
    rw [identity]
    positivity
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_right hden).mp hmul)

/-- Elementary cubic bounds on the actual product. No asymptotic estimate is
assumed: both bounds follow by induction on the finite product recurrence. -/
theorem s_cube_bounds (a : ℕ) (ha : 1 ≤ a) :
    (a : ℝ) ≤ s a ^ 3 ∧ s a ^ 3 ≤ (3 * (a : ℝ) - 1) / 2 := by
  induction a, ha using Nat.le_induction with
  | base => norm_num
  | succ a ha ih =>
      have har : (1 : ℝ) ≤ a := by exact_mod_cast ha
      rw [s_succ a ha, mul_pow]
      push_cast
      constructor
      · exact (factor_cube_lower a har).trans
          (mul_le_mul_of_nonneg_right ih.1 (by positivity))
      · exact (mul_le_mul_of_nonneg_right ih.2 (by positivity)).trans (factor_cube_upper a har)

/-- The manuscript's symmetric two-parameter scalar formula. -/
def profile (a b : ℕ) : ℝ :=
  s (min a b) * ((max a b : ℕ) + ((min a b : ℕ) - (1 : ℝ)) / 2)

theorem profile_symm (a b : ℕ) : profile a b = profile b a := by
  simp only [profile, Nat.min_comm, Nat.max_comm]

theorem profile_pos (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) : 0 < profile a b := by
  have hmin : (1 : ℝ) ≤ (min a b : ℕ) := by exact_mod_cast (le_min ha hb)
  have hmax : (0 : ℝ) < (max a b : ℕ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (ha.trans (le_max_left _ _)))
  unfold profile
  exact mul_pos (s_pos _) (by linarith)

@[simp] theorem profile_diagonal (a : ℕ) :
    profile a a = s a * ((3 * (a : ℝ) - 1) / 2) := by
  simp only [profile, min_self, max_self]
  ring

@[simp] theorem profile_one (b : ℕ) (hb : 1 ≤ b) : profile 1 b = b := by
  simp [profile, min_eq_left hb, max_eq_right hb]

theorem log_s_bounds (a : ℕ) (ha : 1 ≤ a) :
    Real.log (a : ℝ) ≤ 3 * Real.log (s a) ∧
      3 * Real.log (s a) ≤ Real.log ((3 * (a : ℝ) - 1) / 2) := by
  have hapos : (0 : ℝ) < a := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one ha)
  have hb := s_cube_bounds a ha
  constructor
  · have h := Real.log_le_log hapos hb.1
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  · have h := Real.log_le_log (pow_pos (s_pos a) 3) hb.2
    simpa only [Real.log_pow, Nat.cast_ofNat] using h

/-- An explicit bounded remainder in the diagonal logarithmic growth. -/
theorem log_profile_bounds (a : ℕ) (ha : 1 ≤ a) :
    (4 / 3 : ℝ) * Real.log (a : ℝ) ≤ Real.log (profile a a) ∧
      Real.log (profile a a) ≤ (4 / 3 : ℝ) * Real.log (a : ℝ) +
        (4 / 3 : ℝ) * Real.log (3 / 2 : ℝ) := by
  have har : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hapos : (0 : ℝ) < a := by linarith
  have hfactor : 0 < (3 * (a : ℝ) - 1) / 2 := by linarith
  have hs := log_s_bounds a ha
  have hlo := Real.log_le_log hapos (by linarith : (a : ℝ) ≤ (3 * (a : ℝ) - 1) / 2)
  have hhi := Real.log_le_log hfactor
    (by linarith : (3 * (a : ℝ) - 1) / 2 ≤ (3 / 2 : ℝ) * a)
  rw [Real.log_mul (by norm_num : (3 / 2 : ℝ) ≠ 0) (ne_of_gt hapos)] at hhi
  rw [profile_diagonal, Real.log_mul (ne_of_gt (s_pos a)) (ne_of_gt hfactor)]
  constructor <;> linarith

/-- The diagonal profile exponent, meaningful on a ≥ 2. -/
def tau (a : ℕ) : ℝ :=
  3 * Real.log (2 * (a : ℝ) - 1) / Real.log (profile a a)

theorem log_profile_pos (a : ℕ) (ha : 2 ≤ a) : 0 < Real.log (profile a a) := by
  have hlog : 0 < Real.log (a : ℝ) := Real.log_pos (by exact_mod_cast ha)
  have hb := (log_profile_bounds a (by omega)).1
  linarith

theorem log_profile_lt_external (a : ℕ) (ha : 2 ≤ a) :
    Real.log (profile a a) < (4 / 3 : ℝ) * Real.log (2 * (a : ℝ) - 1) := by
  have har : (2 : ℝ) ≤ a := by exact_mod_cast ha
  have hfactor : 0 < (3 * (a : ℝ) - 1) / 2 := by linarith
  have hs := (log_s_bounds a (by omega)).2
  have hf := Real.log_lt_log hfactor
    (by linarith : (3 * (a : ℝ) - 1) / 2 < 2 * (a : ℝ) - 1)
  rw [profile_diagonal, Real.log_mul (ne_of_gt (s_pos a)) (ne_of_gt hfactor)]
  linarith

theorem tau_gt_nine_fourths (a : ℕ) (ha : 2 ≤ a) : (9 / 4 : ℝ) < tau a := by
  have hd := log_profile_pos a ha
  have hb := log_profile_lt_external a ha
  unfold tau
  apply (lt_div_iff₀ hd).mpr
  linarith

/-- A uniform quantitative convergence bound. The error is strictly positive,
and its upper bound is a fixed constant divided by log a. -/
theorem tau_error_bound (a : ℕ) (ha : 2 ≤ a) :
    0 < tau a - (9 / 4 : ℝ) ∧
      tau a - (9 / 4 : ℝ) ≤ (9 / 4 : ℝ) * Real.log 2 / Real.log (a : ℝ) := by
  have har : (2 : ℝ) ≤ a := by exact_mod_cast ha
  have hapos : (0 : ℝ) < a := by linarith
  have hL : 0 < Real.log (a : ℝ) := Real.log_pos (by linarith)
  have hD := log_profile_pos a ha
  have hDlower := (log_profile_bounds a (by omega)).1
  have hlogtwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hN : Real.log (2 * (a : ℝ) - 1) ≤ Real.log (a : ℝ) + Real.log 2 := by
    have hh := Real.log_le_log (by linarith : 0 < 2 * (a : ℝ) - 1)
      (by linarith : 2 * (a : ℝ) - 1 ≤ 2 * (a : ℝ))
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hapos)] at hh
    linarith
  have hco : 0 ≤ (9 / 4 : ℝ) + (9 / 4 : ℝ) * Real.log 2 / Real.log (a : ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hDlower hco
  have identity : ((9 / 4 : ℝ) + (9 / 4 : ℝ) * Real.log 2 / Real.log (a : ℝ)) *
      ((4 / 3 : ℝ) * Real.log (a : ℝ)) = 3 * (Real.log (a : ℝ) + Real.log 2) := by
    field_simp
    ring
  have hupper : tau a ≤ (9 / 4 : ℝ) + (9 / 4 : ℝ) * Real.log 2 / Real.log (a : ℝ) := by
    unfold tau
    apply (div_le_iff₀ hD).mpr
    calc
      3 * Real.log (2 * (a : ℝ) - 1) ≤ 3 * (Real.log (a : ℝ) + Real.log 2) := by linarith
      _ = _ := identity.symm
      _ ≤ _ := hmul
  exact ⟨sub_pos.mpr (tau_gt_nine_fourths a ha), by linarith⟩

/-- The scalar exponent converges to 9/4 along the positive integer indices.
This statement alone makes no assertion about legal tensor-flow families. -/
theorem tau_tendsto : Tendsto tau atTop (𝓝 (9 / 4 : ℝ)) := by
  have hlog : Tendsto (fun a : ℕ => Real.log (a : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hzero : Tendsto (fun a : ℕ => (9 / 4 : ℝ) * Real.log 2 / Real.log (a : ℝ))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hlog
  have hdiff : Tendsto (fun a : ℕ => tau a - (9 / 4 : ℝ)) atTop (𝓝 0) := by
    apply squeeze_zero' _ _ hzero
    · filter_upwards [eventually_ge_atTop 2] with a ha
      exact (tau_error_bound a ha).1.le
    · filter_upwards [eventually_ge_atTop 2] with a ha
      exact (tau_error_bound a ha).2
  simpa using hdiff.add_const (9 / 4 : ℝ)

#print axioms s_succ
#print axioms s_cube_bounds
#print axioms profile_pos
#print axioms log_s_bounds
#print axioms log_profile_bounds
#print axioms tau_gt_nine_fourths
#print axioms tau_error_bound
#print axioms tau_tendsto

end
end MatrixDimensionAudit.ScalarProfileGrowthBridge
