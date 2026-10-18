import formalization.RelativeAlgorithmBridge

/-!
Numerical rounded recurrences only. This module does not construct cross-batch
execution, a padding algorithm, or a recursive matrix multiplication program.
-/

namespace MatrixDimensionAudit.PooledBatchRecurrence

open scoped BigOperators

/-- The abstract number of tasks after l rounded pooling steps. -/
def tasks (q m : ℕ) : ℕ → ℕ
  | 0 => 1
  | l + 1 => q * (tasks q m l ⌈/⌉ m)

/-- The abstract blockside after l rounded dimension-reduction steps. -/
def side (A B n : ℕ) : ℕ → ℕ
  | 0 => n
  | l + 1 => A * (side A B n l ⌈/⌉ B)

def taskConstant (q m : ℕ) : ℕ := q - m + q * m

def sideConstant (A B : ℕ) : ℕ := B - A + A * B

theorem ceil_lower (t m : ℕ) (hm : 0 < m) : t ≤ m * (t ⌈/⌉ m) := by
  exact (ceilDiv_le_iff_le_mul hm).mp le_rfl

theorem ceil_upper (t m : ℕ) : m * (t ⌈/⌉ m) ≤ t + m := by
  rw [Nat.ceilDiv_eq_add_pred_div]
  have h := Nat.div_mul_le_self (t + m - 1) m
  have ht : (t + m - 1) / m * m ≤ t + m := h.trans (by omega)
  simpa only [Nat.mul_comm] using ht

theorem task_step_lower (q m l : ℕ) (hm : 0 < m) :
    q * tasks q m l ≤ m * tasks q m (l + 1) := by
  simpa [tasks, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
    Nat.mul_le_mul_left q (ceil_lower (tasks q m l) m hm)

theorem task_step_upper (q m l : ℕ) :
    m * tasks q m (l + 1) ≤ q * tasks q m l + q * m := by
  simpa [tasks, Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
    Nat.mul_le_mul_left q (ceil_upper (tasks q m l) m)

/-- The ideal geometric task growth is always a lower bound after clearing m^l. -/
theorem tasks_lower (q m l : ℕ) (hm : 0 < m) : q ^ l ≤ m ^ l * tasks q m l := by
  induction l with
  | zero => simp [tasks]
  | succ l ih =>
      calc
        q ^ (l + 1) = q * q ^ l := by rw [pow_succ]; ring
        _ ≤ q * (m ^ l * tasks q m l) := Nat.mul_le_mul_left q ih
        _ ≤ m ^ l * (m * tasks q m (l + 1)) := by
          simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
            Nat.mul_le_mul_left (m ^ l) (task_step_lower q m l hm)
        _ = m ^ (l + 1) * tasks q m (l + 1) := by rw [pow_succ]; ring

private theorem task_affine_invariant (q m l : ℕ) (hqm : m < q) :
    (q - m) * m ^ l * tasks q m l + q * m ^ (l + 1) ≤
      taskConstant q m * q ^ l := by
  let d := q - m
  change d * m ^ l * tasks q m l + q * m ^ (l + 1) ≤ taskConstant q m * q ^ l
  have hd : d + m = q := Nat.sub_add_cancel (Nat.le_of_lt hqm)
  induction l with
  | zero => simp [tasks, taskConstant, d]
  | succ l ih =>
      calc
        d * m ^ (l + 1) * tasks q m (l + 1) + q * m ^ (l + 1 + 1) =
            (d * m ^ l) * (m * tasks q m (l + 1)) + q * m ^ l * m * m := by
              simp only [pow_succ]; ring
        _ ≤ (d * m ^ l) * (q * tasks q m l + q * m) + q * m ^ l * m * m :=
          Nat.add_le_add_right (Nat.mul_le_mul_left _ (task_step_upper q m l)) _
        _ = q * (d * m ^ l * tasks q m l + q * m ^ (l + 1)) := by
          rw [← hd]
          simp only [pow_succ]
          ring
        _ ≤ q * (taskConstant q m * q ^ l) := Nat.mul_le_mul_left q ih
        _ = taskConstant q m * q ^ (l + 1) := by rw [pow_succ]; ring

/-- Rounding changes task growth by at most a fixed natural multiplicative
constant: q^l <= m^l*T_l <= C*q^l whenever q>m>0. -/
theorem tasks_upper (q m l : ℕ) (hqm : m < q) :
    m ^ l * tasks q m l ≤ taskConstant q m * q ^ l := by
  have hp : 0 < q - m := Nat.sub_pos_of_lt hqm
  have hbase : m ^ l * tasks q m l ≤ (q - m) * m ^ l * tasks q m l := by
    simpa [Nat.mul_assoc] using Nat.le_mul_of_pos_left (m ^ l * tasks q m l) hp
  exact hbase.trans ((Nat.le_add_right _ _).trans (task_affine_invariant q m l hqm))

theorem side_step_upper (A B n l : ℕ) :
    B * side A B n (l + 1) ≤ A * side A B n l + A * B := by
  simpa [side, Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
    Nat.mul_le_mul_left A (ceil_upper (side A B n l) B)

/-- Integer-cleared affine bound for the rounded blockside recurrence. -/
theorem side_affine_invariant (A B n l : ℕ) (hAB : A < B) :
    (B - A) * B ^ l * side A B n l + A * B * A ^ l ≤
      (B - A) * A ^ l * n + A * B * B ^ l := by
  let d := B - A
  change d * B ^ l * side A B n l + A * B * A ^ l ≤ d * A ^ l * n + A * B * B ^ l
  have hd : d + A = B := Nat.sub_add_cancel (Nat.le_of_lt hAB)
  induction l with
  | zero => simp [side]
  | succ l ih =>
      calc
        d * B ^ (l + 1) * side A B n (l + 1) + A * B * A ^ (l + 1) =
            (d * B ^ l) * (B * side A B n (l + 1)) + A * B * A ^ (l + 1) := by
              rw [pow_succ]; ring
        _ ≤ (d * B ^ l) * (A * side A B n l + A * B) + A * B * A ^ (l + 1) :=
          Nat.add_le_add_right (Nat.mul_le_mul_left _ (side_step_upper A B n l)) _
        _ = A * (d * B ^ l * side A B n l + A * B * A ^ l) +
            d * A * B * B ^ l := by rw [pow_succ]; ring
        _ ≤ A * (d * A ^ l * n + A * B * B ^ l) +
            d * A * B * B ^ l :=
          Nat.add_le_add_right (Nat.mul_le_mul_left A ih) _
        _ = d * A ^ (l + 1) * n + A * B * B ^ (l + 1) := by
          rw [← hd]
          simp only [pow_succ]
          ring

/-- Once the ideal geometric scale covers n, the rounded side is bounded by
one constant depending only on A,B. -/
theorem side_bounded_at_cover (A B n l : ℕ) (hA : 0 < A) (hAB : A < B)
    (hcover : A ^ l * n ≤ B ^ l) : side A B n l ≤ sideConstant A B := by
  have hp : 0 < B - A := Nat.sub_pos_of_lt hAB
  have hi := side_affine_invariant A B n l hAB
  have hc := Nat.mul_le_mul_left (B - A) hcover
  have hbase : B ^ l * side A B n l ≤ (B - A) * B ^ l * side A B n l := by
    simpa [Nat.mul_assoc] using Nat.le_mul_of_pos_left (B ^ l * side A B n l) hp
  have hbound : B ^ l * side A B n l ≤ B ^ l * sideConstant A B := by
    have h := hbase.trans ((Nat.le_add_right _ _).trans hi)
    exact h.trans (by simpa [sideConstant, Nat.mul_add, Nat.mul_assoc, Nat.mul_comm,
      Nat.mul_left_comm] using Nat.add_le_add_right hc (A * B * B ^ l))
  exact Nat.le_of_mul_le_mul_left hbound (Nat.pow_pos (by omega))

/-- The ideal cover depth exists by elementary rational power growth. -/
theorem exists_cover (A B n : ℕ) (hA : 0 < A) (hAB : A < B) :
    ∃ l : ℕ, A ^ l * n ≤ B ^ l := by
  have hAq : (0 : ℚ) < A := by exact_mod_cast hA
  have hratio : (1 : ℚ) < (B : ℚ) / A := by
    apply (one_lt_div hAq).mpr
    exact_mod_cast hAB
  obtain ⟨l, hl⟩ := pow_unbounded_of_one_lt (n : ℚ) hratio
  rw [div_pow] at hl
  have hp : (n : ℚ) * (A : ℚ) ^ l < (B : ℚ) ^ l :=
    (lt_div_iff₀ (pow_pos hAq l)).mp hl
  have hn : n * A ^ l < B ^ l := by exact_mod_cast hp
  exact ⟨l, by simpa only [Nat.mul_comm] using hn.le⟩

/-- A minimal ideal geometric cover depth has both an explicit cover and the
strict previous-level condition needed to control overshoot. -/
theorem exists_minimal_cover (A B n : ℕ) (hA : 0 < A) (hAB : A < B) :
    ∃ l : ℕ, A ^ l * n ≤ B ^ l ∧ ∀ i < l, B ^ i < A ^ i * n := by
  have hex := exists_cover A B n hA hAB
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  intro i hi
  exact Nat.lt_of_not_ge (Nat.find_min hex hi)

/-- A rational-exponent comparison, expressed entirely with natural powers,
controls every task level after clearing the geometric side scale. -/
theorem tasks_power_envelope (q m A B r s l : ℕ) (hm : 0 < m) (hqm : m < q)
    (hrate : q ^ s * A ^ r ≤ m ^ s * B ^ r) :
    A ^ (r * l) * tasks q m l ^ s ≤ taskConstant q m ^ s * B ^ (r * l) := by
  have ht := Nat.pow_le_pow_left (tasks_upper q m l hqm) s
  have hr := Nat.pow_le_pow_left hrate l
  have h₁ : m ^ (s * l) * (A ^ (r * l) * tasks q m l ^ s) ≤
      taskConstant q m ^ s * (q ^ (s * l) * A ^ (r * l)) := by
    have h := Nat.mul_le_mul_left (A ^ (r * l)) ht
    simpa only [mul_pow, ← pow_mul, Nat.mul_comm l s,
      Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
  have h₂ : taskConstant q m ^ s * (q ^ (s * l) * A ^ (r * l)) ≤
      m ^ (s * l) * (taskConstant q m ^ s * B ^ (r * l)) := by
    have h := Nat.mul_le_mul_left (taskConstant q m ^ s) hr
    simpa only [mul_pow, ← pow_mul, Nat.mul_assoc, Nat.mul_comm,
      Nat.mul_left_comm] using h
  exact Nat.le_of_mul_le_mul_left (h₁.trans h₂) (Nat.pow_pos hm)

/-- At a minimal cover depth, one extra factor B^r bounds the geometric
overshoot. This is an integer-cleared polynomial growth bound for the abstract
recurrence, with exponent r/s when s is positive. -/
theorem tasks_at_minimal_cover (q m A B n r s l : ℕ) (hm : 0 < m)
    (hqm : m < q) (hA : 0 < A) (hAB : A < B) (hn : 0 < n)
    (hrate : q ^ s * A ^ r ≤ m ^ s * B ^ r)
    (hprev : ∀ i < l, B ^ i < A ^ i * n) :
    A ^ r * tasks q m l ^ s ≤ taskConstant q m ^ s * B ^ r * n ^ r := by
  cases l with
  | zero =>
      simp only [tasks, one_pow, Nat.mul_one]
      have hC : 0 < taskConstant q m := by
        unfold taskConstant
        have := Nat.sub_pos_of_lt hqm
        omega
      have hAq : A ^ r ≤ B ^ r := Nat.pow_le_pow_left (Nat.le_of_lt hAB) r
      have hfac : 1 ≤ taskConstant q m ^ s * n ^ r :=
        Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (Nat.ne_of_gt (Nat.pow_pos hC))
          (Nat.ne_of_gt (Nat.pow_pos hn)))
      calc
        A ^ r ≤ B ^ r := hAq
        _ ≤ B ^ r * (taskConstant q m ^ s * n ^ r) := Nat.le_mul_of_pos_right _ (by omega)
        _ = taskConstant q m ^ s * B ^ r * n ^ r := by ring
  | succ l =>
      have he := tasks_power_envelope q m A B r s (l + 1) hm hqm hrate
      have hp := Nat.pow_le_pow_left (Nat.le_of_lt (hprev l (Nat.lt_succ_self l))) r
      have hbound : A ^ (r * l) * (A ^ r * tasks q m (l + 1) ^ s) ≤
          A ^ (r * l) * (taskConstant q m ^ s * B ^ r * n ^ r) := by
        calc
          A ^ (r * l) * (A ^ r * tasks q m (l + 1) ^ s) =
              A ^ (r * (l + 1)) * tasks q m (l + 1) ^ s := by
                rw [Nat.mul_add, Nat.mul_one, pow_add]; ring
          _ ≤ taskConstant q m ^ s * B ^ (r * (l + 1)) := he
          _ = taskConstant q m ^ s * B ^ r * (B ^ l) ^ r := by
            rw [Nat.mul_add, Nat.mul_one, pow_add, ← pow_mul, Nat.mul_comm l r]; ring
          _ ≤ taskConstant q m ^ s * B ^ r * ((A ^ l) ^ r * n ^ r) := by
            simpa only [mul_pow] using Nat.mul_le_mul_left (taskConstant q m ^ s * B ^ r) hp
          _ = A ^ (r * l) * (taskConstant q m ^ s * B ^ r * n ^ r) := by
            rw [← pow_mul, Nat.mul_comm l r]; ring
      exact Nat.le_of_mul_le_mul_left hbound (Nat.pow_pos hA)

/-- The abstract recurrence reaches a constant side while satisfying the
integer-cleared power bound at that same depth. -/
theorem exists_stopped_power_bound (q m A B n r s : ℕ) (hm : 0 < m)
    (hqm : m < q) (hA : 0 < A) (hAB : A < B) (hn : 0 < n)
    (hrate : q ^ s * A ^ r ≤ m ^ s * B ^ r) :
    ∃ l : ℕ, side A B n l ≤ sideConstant A B ∧
      A ^ r * tasks q m l ^ s ≤ taskConstant q m ^ s * B ^ r * n ^ r := by
  obtain ⟨l, hc, hp⟩ := exists_minimal_cover A B n hA hAB
  exact ⟨l, side_bounded_at_cover A B n l hA hAB hc,
    tasks_at_minimal_cover q m A B n r s l hm hqm hA hAB hn hrate hp⟩

/-- The integer power comparison is exactly the statement that the relative
logarithmic exponent is at most the rational number r/s. -/
theorem relative_exponent_le_iff (q m A B r s : ℕ) (hq : 0 < q) (hm : 0 < m)
    (hA : 0 < A) (hAB : A < B) (hs : 0 < s) :
    (Real.log (q : ℝ) - Real.log (m : ℝ)) /
        (Real.log (B : ℝ) - Real.log (A : ℝ)) ≤ (r : ℝ) / s ↔
      q ^ s * A ^ r ≤ m ^ s * B ^ r := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hAr : (0 : ℝ) < A := by exact_mod_cast hA
  have hBr : (0 : ℝ) < B := by exact_mod_cast (hA.trans hAB)
  have hABr : (A : ℝ) < B := by exact_mod_cast hAB
  have hsr : (0 : ℝ) < s := by exact_mod_cast hs
  have hd : 0 < Real.log (B : ℝ) - Real.log (A : ℝ) :=
    sub_pos.mpr (Real.log_lt_log hAr hABr)
  have hleft : (0 : ℝ) < (q : ℝ) ^ s * (A : ℝ) ^ r :=
    mul_pos (pow_pos hqr _) (pow_pos hAr _)
  have hright : (0 : ℝ) < (m : ℝ) ^ s * (B : ℝ) ^ r :=
    mul_pos (pow_pos hmr _) (pow_pos hBr _)
  have hconv :
      (Real.log (q : ℝ) - Real.log (m : ℝ)) /
          (Real.log (B : ℝ) - Real.log (A : ℝ)) ≤ (r : ℝ) / s ↔
        (q : ℝ) ^ s * (A : ℝ) ^ r ≤ (m : ℝ) ^ s * (B : ℝ) ^ r := by
    calc
      _ ↔ Real.log ((q : ℝ) ^ s * (A : ℝ) ^ r) ≤
          Real.log ((m : ℝ) ^ s * (B : ℝ) ^ r) := by
        rw [div_le_div_iff₀ hd hsr,
          Real.log_mul (ne_of_gt (pow_pos hqr s)) (ne_of_gt (pow_pos hAr r)),
          Real.log_mul (ne_of_gt (pow_pos hmr s)) (ne_of_gt (pow_pos hBr r)),
          Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow]
        constructor <;> intro h <;> nlinarith
      _ ↔ _ := Real.log_le_log_iff hleft hright
  exact_mod_cast hconv

/-- Actual relative matrix maps with positive target multiplicity and gain
supply the strict task-growth condition q>m. -/
theorem actual_copies_gt {q A m B : ℕ}
    (p : RelativeAlgorithmBridge.MatrixTensorMaps q A m B) (hm : 0 < m) (hAB : A < B) :
    m < q := RelativeAlgorithmBridge.source_copies_gt_target p hm hAB

/-- Actual relative matrix maps provide the growth hypothesis. The conclusion
still concerns only the two numerical recurrences, not their execution. -/
theorem actual_stopped_power_bound {q A m B : ℕ}
    (p : RelativeAlgorithmBridge.MatrixTensorMaps q A m B) (n r s : ℕ)
    (hm : 0 < m) (hA : 0 < A) (hAB : A < B) (hn : 0 < n)
    (hrate : q ^ s * A ^ r ≤ m ^ s * B ^ r) :
    ∃ l : ℕ, side A B n l ≤ sideConstant A B ∧
      A ^ r * tasks q m l ^ s ≤ taskConstant q m ^ s * B ^ r * n ^ r :=
  exists_stopped_power_bound q m A B n r s hm (actual_copies_gt p hm hAB)
    hA hAB hn hrate

/-- The recurrence bounds specialize to the actual closed family restriction;
no source-rank certificate or copy-payment premise is added. -/
theorem supplied_stopped_power_bound {n K : ℕ}
    (family : AllRowProfile.Family n K) (k j t r s : ℕ)
    (hgain : SuppliedGlobalRestrictionBridge.inputWidth family k j <
      SuppliedGlobalRestrictionBridge.outputWidth family k j) (ht : 0 < t)
    (hrate : SuppliedGlobalRestrictionBridge.inputCopies family k j ^ s *
        SuppliedGlobalRestrictionBridge.inputWidth family k j ^ r ≤
      SuppliedGlobalRestrictionBridge.outputCopies family k j ^ s *
        SuppliedGlobalRestrictionBridge.outputWidth family k j ^ r) :
    let q := SuppliedGlobalRestrictionBridge.inputCopies family k j
    let m := SuppliedGlobalRestrictionBridge.outputCopies family k j
    let A := SuppliedGlobalRestrictionBridge.inputWidth family k j
    let B := SuppliedGlobalRestrictionBridge.outputWidth family k j
    ∃ l : ℕ, side A B t l ≤ sideConstant A B ∧
      A ^ r * tasks q m l ^ s ≤ taskConstant q m ^ s * B ^ r * t ^ r :=
  actual_stopped_power_bound (SuppliedGlobalRestrictionBridge.suppliedMaps family k j) t r s
    (SuppliedGlobalRestrictionBridge.output_copies_pos family k j)
    (SuppliedGlobalRestrictionBridge.input_width_pos family k j) hgain ht hrate

#print axioms tasks_power_envelope
#print axioms tasks_at_minimal_cover
#print axioms tasks_upper
#print axioms side_affine_invariant
#print axioms side_bounded_at_cover
#print axioms exists_minimal_cover
#print axioms actual_copies_gt
#print axioms actual_stopped_power_bound
#print axioms relative_exponent_le_iff
#print axioms supplied_stopped_power_bound

end MatrixDimensionAudit.PooledBatchRecurrence
