import formalization.PooledExecutorBridge
import OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.Exponent

/-! Polynomial arithmetic cost of the actual rounded pooled executor. -/
namespace MatrixDimensionAudit.AsymptoticPooledCostBridge
open scoped BigOperators
open PooledBatchRecurrence PooledExecutorBridge
open OAI.MatrixMultiplication.Arithmetic
noncomputable section

/-- Before the first ideal cover, the additive rounding error is absorbed by
one fixed multiplicative side constant. -/
theorem side_before_cover (A B n i : ℕ) (hAB : A < B)
    (hprev : B ^ i < A ^ i * n) :
    B ^ i * side A B n i ≤ sideConstant A B * A ^ i * n := by
  have hd : 0 < B - A := Nat.sub_pos_of_lt hAB
  have h := side_affine_invariant A B n i hAB
  have he : B ^ i * side A B n i ≤ (B - A) * B ^ i * side A B n i := by
    simpa only [Nat.mul_assoc] using Nat.le_mul_of_pos_left (B ^ i * side A B n i) hd
  have hp := Nat.mul_le_mul_left (A * B) (Nat.le_of_lt hprev)
  calc
    B ^ i * side A B n i ≤ (B - A) * B ^ i * side A B n i := he
    _ ≤ (B - A) * A ^ i * n + A * B * B ^ i :=
      (Nat.le_add_right _ _).trans h
    _ ≤ (B - A) * A ^ i * n + A * B * (A ^ i * n) := Nat.add_le_add_left hp _
    _ = sideConstant A B * A ^ i * n := by unfold sideConstant; ring

theorem ceil_le_self (t d : ℕ) (hd : 0 < d) : t ⌈/⌉ d ≤ t := by
  apply (ceilDiv_le_iff_le_mul hd).mpr
  simpa only [Nat.mul_comm] using Nat.le_mul_of_pos_right t hd

private theorem real_quotient_power_bound (a b t C : ℕ) (hb : 0 < b) (i : ℕ)
    (h : b ^ i * t ≤ C * a ^ i) :
    (t : ℝ) ≤ (C : ℝ) * ((a : ℝ) / b) ^ i := by
  have hbr : (0 : ℝ) < b := by exact_mod_cast hb
  have hc : (b : ℝ) ^ i * t ≤ (C : ℝ) * (a : ℝ) ^ i := by exact_mod_cast h
  rw [div_pow, ← mul_div_assoc]
  apply (le_div_iff₀ (pow_pos hbr i)).mpr
  nlinarith

private theorem geom_sum_bound (z : ℝ) (hz : 1 < z) (l : ℕ) :
    (∑ i ∈ Finset.range l, z ^ i) ≤ z ^ l / (z - 1) := by
  have identity : (z - 1) * (∑ i ∈ Finset.range l, z ^ i) = z ^ l - 1 := by
    induction l with
    | zero => simp
    | succ l ih => rw [Finset.sum_range_succ, pow_succ]; nlinarith
  apply (le_div_iff₀ (sub_pos.mpr hz)).mpr
  nlinarith

/-- A real geometric cost estimate. A strict exponent above two pays for all
quadratic linear stages through a geometric sum, with no depth factor. -/
theorem geometric_profile_bound (R y p Ct Cs H n : ℝ) (l : ℕ)
    (hR : 1 < R) (hy : 0 ≤ y) (hp : 2 < p)
    (hCt : 0 ≤ Ct) (_hCs : 0 ≤ Cs) (hH : 0 ≤ H) (hn : 1 ≤ n)
    (hrate : y ≤ R ^ p) (hcover : R ^ l ≤ R * n)
    (T S : ℕ → ℝ)
    (hSpos : ∀ i, 0 ≤ S i)
    (hT : ∀ i, T i ≤ Ct * y ^ i)
    (hS : ∀ i < l, S i ≤ Cs * n / R ^ i)
    (hleaf : S l ≤ Cs) :
    2 * T l * S l ^ 3 + H * ∑ i ∈ Finset.range l, T i * S i ^ 2 ≤
      (2 * Ct * Cs ^ 3 * R ^ p +
        H * Ct * Cs ^ 2 * R ^ (p - 2) / (R ^ (p - 2) - 1)) * n ^ p := by
  have hRpos : 0 < R := by linarith
  have hnpos : 0 < n := by linarith
  let z := R ^ (p - 2)
  have hz : 1 < z := Real.one_lt_rpow hR (by linarith)
  have hzpos : 0 < z := by linarith
  have hsplit : R ^ p = z * R ^ (2 : ℕ) := by
    dsimp [z]
    rw [← Real.rpow_natCast, ← Real.rpow_add hRpos]
    congr 1
    ring
  have hratio : y / R ^ 2 ≤ z := (div_le_iff₀ (pow_pos hRpos 2)).mpr (by nlinarith)
  have hstage : ∀ i < l, T i * S i ^ 2 ≤ Ct * Cs ^ 2 * n ^ 2 * z ^ i := by
    intro i hi
    have hfirst := mul_le_mul (hT i) (pow_le_pow_left₀ (hSpos i) (hS i hi) 2)
      (sq_nonneg (S i)) (mul_nonneg hCt (pow_nonneg hy i))
    have hr := pow_le_pow_left₀ (div_nonneg hy (sq_nonneg R)) hratio i
    have hid : Ct * y ^ i * (Cs * n / R ^ i) ^ 2 =
        Ct * Cs ^ 2 * n ^ 2 * (y / R ^ 2) ^ i := by
      rw [div_pow, div_pow, ← pow_mul, ← pow_mul]
      ring
    rw [hid] at hfirst
    exact hfirst.trans (mul_le_mul_of_nonneg_left hr (by positivity))
  have hsum : (∑ i ∈ Finset.range l, T i * S i ^ 2) ≤
      Ct * Cs ^ 2 * n ^ 2 * (z ^ l / (z - 1)) := by
    calc
      _ ≤ ∑ i ∈ Finset.range l, Ct * Cs ^ 2 * n ^ 2 * z ^ i :=
        Finset.sum_le_sum (fun i hi => hstage i (Finset.mem_range.mp hi))
      _ = Ct * Cs ^ 2 * n ^ 2 * (∑ i ∈ Finset.range l, z ^ i) := by
        rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (geom_sum_bound z hz l) (by positivity)
  have hpower (t : ℝ) (ht : 0 ≤ t) : (R ^ t) ^ l ≤ R ^ t * n ^ t := by
    rw [← Real.rpow_mul_natCast hRpos.le, mul_comm t,
      Real.rpow_natCast_mul hRpos.le]
    have hh := Real.rpow_le_rpow (pow_nonneg hRpos.le l) hcover ht
    exact hh.trans_eq (Real.mul_rpow hRpos.le hnpos.le)
  have hleafcost : 2 * T l * S l ^ 3 ≤ 2 * Ct * Cs ^ 3 * R ^ p * n ^ p := by
    have hpow := (pow_le_pow_left₀ hy hrate l).trans (hpower p (by linarith))
    have ht := (hT l).trans (mul_le_mul_of_nonneg_left hpow hCt)
    have hs := pow_le_pow_left₀ (hSpos l) hleaf 3
    nlinarith [mul_le_mul ht hs (pow_nonneg (hSpos l) 3) (by positivity)]
  have hzbound : z ^ l ≤ R ^ (p - 2) * n ^ (p - 2) := hpower (p - 2) (by linarith)
  have hnsplit : n ^ (2 : ℕ) * n ^ (p - 2) = n ^ p := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hnpos]
    congr 1
    ring
  have hsumcost : H * (∑ i ∈ Finset.range l, T i * S i ^ 2) ≤
      (H * Ct * Cs ^ 2 * R ^ (p - 2) / (R ^ (p - 2) - 1)) * n ^ p := by
    have hh := hsum.trans (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hzbound (by linarith : 0 ≤ z - 1)) (by positivity))
    have hm := mul_le_mul_of_nonneg_left hh hH
    convert hm using 1
    dsimp [z]
    rw [← hnsplit]
    ring
  nlinarith

/-- A uniform cost constant, depending on the fixed restriction and exponent,
and independent of the requested matrix side. -/
def costConstant (q m A B : ℕ) (p : ℝ) : ℝ :=
  let R := (B : ℝ) / A
  let Ct := (taskConstant q m : ℝ)
  let Cs := (sideConstant A B : ℝ)
  let H := (6 * q * m * A ^ 2 * B ^ 2 : ℕ)
  2 * Ct * Cs ^ 3 * R ^ p +
    H * Ct * Cs ^ 2 * R ^ (p - 2) / (R ^ (p - 2) - 1)

theorem rate_of_pooledExponent_le (q m A B : ℕ)
    (hq : 0 < q) (hm : 0 < m) (hA : 0 < A) (hAB : A < B)
    (p : ℝ) (hp : RelativeAlgorithmBridge.pooledExponent q A m B ≤ p) :
    (q : ℝ) / m ≤ ((B : ℝ) / A) ^ p := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hAr : (0 : ℝ) < A := by exact_mod_cast hA
  have hBr : (0 : ℝ) < B := by exact_mod_cast (hA.trans hAB)
  have hABr : (A : ℝ) < B := by exact_mod_cast hAB
  apply (Real.log_le_log_iff (div_pos hqr hmr)
    (Real.rpow_pos_of_pos (div_pos hBr hAr) p)).mp
  rw [Real.log_div (ne_of_gt hqr) (ne_of_gt hmr),
    Real.log_rpow (div_pos hBr hAr),
    Real.log_div (ne_of_gt hBr) (ne_of_gt hAr)]
  exact (div_le_iff₀ (sub_pos.mpr (Real.log_lt_log hAr hABr))).mp hp

private theorem cover_scale (A B n l : ℕ) (hA : 0 < A) (hAB : A < B)
    (hn : 1 ≤ n) (hprev : ∀ i < l, B ^ i < A ^ i * n) :
    ((B : ℝ) / A) ^ l ≤ ((B : ℝ) / A) * n := by
  have hAr : (0 : ℝ) < A := by exact_mod_cast hA
  have hBr : (0 : ℝ) < B := by exact_mod_cast (hA.trans hAB)
  have hR : (1 : ℝ) ≤ (B : ℝ) / A := by
    apply (one_le_div hAr).mpr
    exact_mod_cast hAB.le
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  cases l with
  | zero => simp only [pow_zero]; nlinarith
  | succ i =>
      have hi : (B : ℝ) ^ i ≤ (A : ℝ) ^ i * n := by
        exact_mod_cast (hprev i (Nat.lt_succ_self i)).le
      have hh : ((B : ℝ) / A) ^ i ≤ n := by
        rw [div_pow]
        exact (div_le_iff₀ (pow_pos hAr i)).mpr (by nlinarith)
      rw [pow_succ]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_right hh (div_nonneg hBr.le hAr.le)

/-- The full numerical executor work, including every linear stage and the
classical leaf, has a uniform polynomial bound at its selected cover depth. -/
theorem stopped_work_bound (q m A B : ℕ) (hm : 0 < m) (hqm : m < q)
    (hA : 0 < A) (hAB : A < B) (p : ℝ) (hp : 2 < p)
    (hrate : (q : ℝ) / m ≤ ((B : ℝ) / A) ^ p)
    (n : ℕ) (hn : 1 ≤ n) :
    (work q A m B (coverDepth A B n hA hAB) 1 n : ℝ) ≤
      costConstant q m A B p * (n : ℝ) ^ p := by
  let l := coverDepth A B n hA hAB
  let T := fun i => (tasks q m i : ℝ)
  let S := fun i => (side A B n i : ℝ)
  have hAr : (0 : ℝ) < A := by exact_mod_cast hA
  have hBr : (0 : ℝ) < B := by exact_mod_cast (hA.trans hAB)
  have hR : (1 : ℝ) < (B : ℝ) / A := by
    apply (one_lt_div hAr).mpr
    exact_mod_cast hAB
  have hprev := coverDepth_previous A B n hA hAB
  have ht : ∀ i, T i ≤ (taskConstant q m : ℝ) * ((q : ℝ) / m) ^ i := by
    intro i
    exact real_quotient_power_bound q m (tasks q m i) (taskConstant q m) hm i
      (tasks_upper q m i hqm)
  have hs : ∀ i < l, S i ≤ (sideConstant A B : ℝ) * n / ((B : ℝ) / A) ^ i := by
    intro i hi
    have hh := real_quotient_power_bound A B (side A B n i) (sideConstant A B * n)
      (hA.trans hAB) i (by simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        using side_before_cover A B n i hAB (hprev i hi))
    dsimp [S]
    convert hh using 1
    push_cast
    rw [div_pow, div_pow]
    field_simp
  have hleaf : S l ≤ (sideConstant A B : ℝ) := by
    dsimp [S]
    exact_mod_cast side_bounded_at_cover A B n l hA hAB (coverDepth_cover A B n hA hAB)
  have hprofile := geometric_profile_bound ((B : ℝ) / A) ((q : ℝ) / m) p
    (taskConstant q m) (sideConstant A B) (6 * q * m * A ^ 2 * B ^ 2 : ℕ) n l
    hR (by positivity) hp (by positivity) (by positivity) (by positivity)
    (by exact_mod_cast hn) hrate (cover_scale A B n l hA hAB hn hprev)
    T S (by intro i; exact Nat.cast_nonneg _) ht hs hleaf
  change _ ≤ costConstant q m A B p * (n : ℝ) ^ p
  have hwork : (work q A m B l 1 n : ℝ) ≤
      2 * T l * S l ^ 3 + (6 * q * m * A ^ 2 * B ^ 2 : ℕ) *
        ∑ i ∈ Finset.range l, T i * S i ^ 2 := by
    rw [work_profile]
    simp only [stateAfter_initial]
    push_cast
    dsimp [T, S]
    apply add_le_add le_rfl
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Finset.sum_le_sum
    intro i _
    have htceil : ((tasks q m i ⌈/⌉ m : ℕ) : ℝ) ≤ T i := by
      dsimp [T]
      exact_mod_cast ceil_le_self (tasks q m i) m hm
    have hsceil : ((side A B n i ⌈/⌉ B : ℕ) : ℝ) ≤ S i := by
      dsimp [S]
      exact_mod_cast ceil_le_self (side A B n i) B (hA.trans hAB)
    exact mul_le_mul htceil (pow_le_pow_left₀ (by positivity) hsceil 2)
      (by positivity) (by positivity)
  exact hwork.trans hprofile

theorem costConstant_pos (q m A B : ℕ) (hqm : m < q) (hAB : A < B)
    (hA : 0 < A) (p : ℝ) (hp : 2 < p) : 0 < costConstant q m A B p := by
  have ht : 0 < taskConstant q m := by
    unfold taskConstant
    have := Nat.sub_pos_of_lt hqm
    omega
  have hs : 0 < sideConstant A B := by
    unfold sideConstant
    have := Nat.sub_pos_of_lt hAB
    omega
  have htr : (0 : ℝ) < taskConstant q m := by exact_mod_cast ht
  have hsr : (0 : ℝ) < sideConstant A B := by exact_mod_cast hs
  have hAr : (0 : ℝ) < A := by exact_mod_cast hA
  have hR : (1 : ℝ) < (B : ℝ) / A := by
    apply (one_lt_div hAr).mpr
    exact_mod_cast hAB
  have hRpos : (0 : ℝ) < (B : ℝ) / A := by linarith
  have hz : 0 < ((B : ℝ) / A) ^ (p - 2) - 1 :=
    sub_pos.mpr (Real.one_lt_rpow hR (by linarith))
  unfold costConstant
  dsimp
  positivity

/-- The bound concerns the actual correct arithmetic program selected by the
executor, with the same constant at every positive matrix side. -/
theorem stoppedAlgorithm_cost_bound {q A m B : ℕ}
    (maps : RelativeAlgorithmBridge.MatrixTensorMaps q A m B)
    (hm : 0 < m) (hA : 0 < A) (hAB : A < B)
    (p : ℝ) (hp : 2 < p) (hrho : RelativeAlgorithmBridge.pooledExponent q A m B ≤ p)
    (n : ℕ) (hn : 1 ≤ n) :
    ((stoppedAlgorithm maps hm hA hAB n).cost : ℝ) ≤
      costConstant q m A B p * (n : ℝ) ^ p := by
  have hqm := RelativeAlgorithmBridge.source_copies_gt_target maps hm hAB
  rw [stoppedAlgorithm_cost]
  exact stopped_work_bound q m A B hm hqm hA hAB p hp
    (rate_of_pooledExponent_le q m A B (hm.trans hqm) hm hA hAB p hrho) n hn

/-- An actual positive-gain relative matrix restriction supplies an admissible
arithmetic exponent over the rationals, in the library's slack-based sense. -/
theorem pooledExponent_admissible {q A m B : ℕ}
    (maps : RelativeAlgorithmBridge.MatrixTensorMaps q A m B)
    (hm : 0 < m) (hA : 0 < A) (hAB : A < B) :
    AdmissibleExponent ℚ (RelativeAlgorithmBridge.pooledExponent q A m B) := by
  have hqm := RelativeAlgorithmBridge.source_copies_gt_target maps hm hAB
  have hrho := RelativeAlgorithmBridge.pooledExponent_ge_two maps hA (hA.trans hAB)
    (hm.trans hqm) hm hAB
  intro ε hε
  let p := RelativeAlgorithmBridge.pooledExponent q A m B + ε
  have hp : 2 < p := by dsimp [p]; linarith
  refine ⟨costConstant q m A B p, costConstant_pos q m A B hqm hAB hA p hp, ?_⟩
  intro n hn
  refine ⟨stoppedAlgorithm maps hm hA hAB n, stoppedAlgorithm_correct maps hm hA hAB n, ?_⟩
  exact stoppedAlgorithm_cost_bound maps hm hA hAB p hp (by dsimp [p]; linarith) n hn

theorem omega_le_pooledExponent {q A m B : ℕ}
    (maps : RelativeAlgorithmBridge.MatrixTensorMaps q A m B)
    (hm : 0 < m) (hA : 0 < A) (hAB : A < B) :
    omega ℚ ≤ RelativeAlgorithmBridge.pooledExponent q A m B :=
  omega_le_of_admissibleExponent (pooledExponent_admissible maps hm hA hAB)

/-- Specialization to the already supplied concrete flow-family maps. This
does not assert that those parameters attain any separately chosen exponent. -/
theorem supplied_pooledExponent_admissible (family : AllRowProfile.Family n K) (k j : ℕ)
    (hgain : SuppliedGlobalRestrictionBridge.inputWidth family k j <
      SuppliedGlobalRestrictionBridge.outputWidth family k j) :
    AdmissibleExponent ℚ (RelativeAlgorithmBridge.pooledExponent
      (SuppliedGlobalRestrictionBridge.inputCopies family k j)
      (SuppliedGlobalRestrictionBridge.inputWidth family k j)
      (SuppliedGlobalRestrictionBridge.outputCopies family k j)
      (SuppliedGlobalRestrictionBridge.outputWidth family k j)) :=
  pooledExponent_admissible (SuppliedGlobalRestrictionBridge.suppliedMaps family k j)
    (SuppliedGlobalRestrictionBridge.output_copies_pos family k j)
    (SuppliedGlobalRestrictionBridge.input_width_pos family k j) hgain

#print axioms side_before_cover
#print axioms geometric_profile_bound
#print axioms rate_of_pooledExponent_le
#print axioms stopped_work_bound
#print axioms costConstant_pos
#print axioms stoppedAlgorithm_cost_bound
#print axioms pooledExponent_admissible
#print axioms omega_le_pooledExponent
#print axioms supplied_pooledExponent_admissible

end
end MatrixDimensionAudit.AsymptoticPooledCostBridge
