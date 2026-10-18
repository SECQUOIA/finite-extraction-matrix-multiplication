module
public import Mathlib

public section

/-! Exact multinomial modes and polynomial type-mass lower bounds. -/
namespace MatrixDimensionAudit.MultinomialTypeBoundBridge
open scoped BigOperators Nat

/-- For integer intensity n, the Poisson weight n^k/k! is maximized at k=n.
The cleared inequality also covers n=0 without dividing by zero. -/
theorem factorial_mode (n k : ℕ) : n ^ k * n ! ≤ n ^ n * k ! := by
  rcases le_total n k with hnk | hkn
  · calc
      n ^ k * n ! = n ^ (n + (k - n)) * n ! := by rw [Nat.add_sub_of_le hnk]
      _ = n ^ n * (n ! * n ^ (k - n)) := by rw [pow_add]; ring
      _ ≤ n ^ n * k ! := Nat.mul_le_mul_left _ (Nat.factorial_mul_pow_sub_le_factorial hnk)
  · have hfact : n ! ≤ k ! * n ^ (n - k) := by
      have h := Nat.mul_le_mul_left (k !) (Nat.ascFactorial_le_pow_add k (n - k))
      simpa only [Nat.factorial_mul_ascFactorial, Nat.add_sub_of_le hkn] using h
    calc
      n ^ k * n ! ≤ n ^ k * (k ! * n ^ (n - k)) := Nat.mul_le_mul_left _ hfact
      _ = n ^ (k + (n - k)) * k ! := by rw [pow_add]; ring
      _ = n ^ n * k ! := by rw [Nat.add_sub_of_le hkn]

/-- Coordinatewise factorial modes multiply over any finite set of categories. -/
theorem product_factorial_mode {α : Type*} (s : Finset α) (n k : α → ℕ) :
    (∏ i ∈ s, n i ^ k i) * (∏ i ∈ s, (n i)!) ≤
      (∏ i ∈ s, n i ^ n i) * (∏ i ∈ s, (k i)!) := by
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  exact Finset.prod_le_prod (fun i _ => factorial_mode (n i) (k i))

/-- The empirical histogram n is a multinomial mode. Both histograms have
the same total; weights n_i are integers, so no probabilities are approximated. -/
theorem multinomial_mode {α : Type*} (s : Finset α) (n k : α → ℕ)
    (hsum : ∑ i ∈ s, k i = ∑ i ∈ s, n i) :
    Nat.multinomial s k * (∏ i ∈ s, n i ^ k i) ≤
      Nat.multinomial s n * (∏ i ∈ s, n i ^ n i) := by
  have hn := Nat.multinomial_spec s n
  have hk := Nat.multinomial_spec s k
  rw [hsum] at hk
  have hp := Nat.mul_le_mul_left (Nat.multinomial s k * Nat.multinomial s n)
    (product_factorial_mode s n k)
  have left : (Nat.multinomial s k * Nat.multinomial s n) *
      ((∏ i ∈ s, n i ^ k i) * (∏ i ∈ s, (n i)!)) =
      (∑ i ∈ s, n i)! * (Nat.multinomial s k * (∏ i ∈ s, n i ^ k i)) := by
    calc
      _ = ((∏ i ∈ s, (n i)!) * Nat.multinomial s n) *
          (Nat.multinomial s k * (∏ i ∈ s, n i ^ k i)) := by ring
      _ = _ := by rw [hn]
  have right : (Nat.multinomial s k * Nat.multinomial s n) *
      ((∏ i ∈ s, n i ^ n i) * (∏ i ∈ s, (k i)!)) =
      (∑ i ∈ s, n i)! * (Nat.multinomial s n * (∏ i ∈ s, n i ^ n i)) := by
    calc
      _ = ((∏ i ∈ s, (k i)!) * Nat.multinomial s k) *
          (Nat.multinomial s n * (∏ i ∈ s, n i ^ n i)) := by ring
      _ = _ := by rw [hk]
  rw [left, right] at hp
  exact Nat.le_of_mul_le_mul_left hp (Nat.factorial_pos _)

/-- There are at most (N+1)^d histograms on d categories with total N. -/
theorem histogram_card_bound {α : Type*} [Fintype α] [DecidableEq α] (N : ℕ) :
    (Finset.piAntidiag (Finset.univ : Finset α) N).card ≤ (N + 1) ^ Fintype.card α := by
  classical
  have hs : Finset.piAntidiag (Finset.univ : Finset α) N ⊆
      Fintype.piFinset (fun _ : α => Finset.range (N + 1)) := by
    intro k hk
    apply Fintype.mem_piFinset.mpr
    intro i
    have he : (∑ j : α, k j) = N := (Finset.mem_piAntidiag.mp hk).1
    have hi : k i ≤ ∑ j : α, k j := Finset.single_le_sum (fun j _ => Nat.zero_le (k j)) (Finset.mem_univ i)
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le (hi.trans_eq he)
  simpa only [Fintype.card_piFinset, Finset.card_range, Finset.prod_const,
    Finset.card_univ] using Finset.card_le_card hs

/-- Exact polynomial type-mass lower bound. This is the cleared form of the
empirical multinomial probability being at least (N+1)^(-d). Zero categories
and even the empty alphabet are included using the natural convention 0^0=1. -/
theorem empirical_type_lower_bound {α : Type*} [Fintype α] (n : α → ℕ) :
    (∑ i, n i) ^ (∑ i, n i) ≤
      ((∑ i, n i) + 1) ^ Fintype.card α * Nat.multinomial Finset.univ n *
        (∏ i, n i ^ n i) := by
  classical
  let N := ∑ i, n i
  let W := Nat.multinomial Finset.univ n * ∏ i, n i ^ n i
  have hsum : N ^ N = ∑ k ∈ Finset.piAntidiag (Finset.univ : Finset α) N,
      Nat.multinomial Finset.univ k * ∏ i, n i ^ k i := by
    exact Finset.sum_pow_eq_sum_piAntidiag Finset.univ n N
  have hm : ∀ k ∈ Finset.piAntidiag (Finset.univ : Finset α) N,
      Nat.multinomial Finset.univ k * (∏ i, n i ^ k i) ≤ W := by
    intro k hk
    exact multinomial_mode Finset.univ n k (Finset.mem_piAntidiag.mp hk).1
  calc
    N ^ N ≤ ∑ _k ∈ Finset.piAntidiag (Finset.univ : Finset α) N, W := by
      rw [hsum]
      exact Finset.sum_le_sum hm
    _ = (Finset.piAntidiag (Finset.univ : Finset α) N).card * W := by simp
    _ ≤ (N + 1) ^ Fintype.card α * W := Nat.mul_le_mul_right W (histogram_card_bound (α := α) N)
    _ = _ := by dsimp [N, W]; ring

/-- Exact occupation proportions transfer the empirical bound to arbitrary
natural category weights. The only proportionality premise is n_i*S=N*w_i;
the weighted type lower bound is derived rather than assumed. -/
theorem weighted_type_lower_bound {α : Type*} [Fintype α] (n w : α → ℕ)
    (hN : 0 < ∑ i, n i)
    (occupation : ∀ i, n i * (∑ j, w j) = (∑ j, n j) * w i) :
    (∑ i, w i) ^ (∑ i, n i) ≤
      ((∑ i, n i) + 1) ^ Fintype.card α * Nat.multinomial Finset.univ n *
        (∏ i, w i ^ n i) := by
  let N := ∑ i, n i
  let S := ∑ i, w i
  let C := (N + 1) ^ Fintype.card α * Nat.multinomial Finset.univ n
  have identity : (∏ i, n i ^ n i) * S ^ N = N ^ N * (∏ i, w i ^ n i) := by
    calc
      _ = ∏ i, (n i * S) ^ n i := by
        simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, N]
      _ = ∏ i, (N * w i) ^ n i := by
        apply Finset.prod_congr rfl
        intro i _
        rw [occupation i]
      _ = _ := by simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, N]
  have h : N ^ N * S ^ N ≤ N ^ N * (C * ∏ i, w i ^ n i) := by
    calc
      _ ≤ (C * ∏ i, n i ^ n i) * S ^ N :=
        Nat.mul_le_mul_right (S ^ N) (empirical_type_lower_bound n)
      _ = C * ((∏ i, n i ^ n i) * S ^ N) := by ring
      _ = _ := by rw [identity]; ring
  exact Nat.le_of_mul_le_mul_left h (Nat.pow_pos hN)

/-- The corresponding entropy-numerator lower bound on the logarithmic type
count, derived from the exact integer theorem without Stirling estimates.
Zero category counts contribute 0*log 0=0. -/
theorem log_multinomial_lower_bound {α : Type*} [Fintype α] (n : α → ℕ)
    (hN : 0 < ∑ i, n i) :
    (∑ i, (n i : ℝ)) * Real.log (∑ i, (n i : ℝ)) -
        (∑ i, (n i : ℝ) * Real.log (n i : ℝ)) -
        (Fintype.card α : ℝ) * Real.log ((∑ i, (n i : ℝ)) + 1) ≤
      Real.log (Nat.multinomial Finset.univ n : ℝ) := by
  classical
  let N := ∑ i, n i
  let M := Nat.multinomial Finset.univ n
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hMr : (0 : ℝ) < M := by exact_mod_cast Nat.multinomial_pos Finset.univ n
  have hpow : ∀ i, (0 : ℝ) < (n i : ℝ) ^ n i := by
    intro i
    by_cases hi : n i = 0
    · simp [hi]
    · exact pow_pos (by exact_mod_cast Nat.pos_of_ne_zero hi) _
  have hCr : (0 : ℝ) < (N + 1 : ℕ) ^ Fintype.card α := by positivity
  have hP : 0 < ∏ i, (n i : ℝ) ^ n i := Finset.prod_pos (fun i _ => hpow i)
  have hbound : (N : ℝ) ^ N ≤ ((N + 1 : ℕ) : ℝ) ^ Fintype.card α * M *
      (∏ i, (n i : ℝ) ^ n i) := by
    exact_mod_cast empirical_type_lower_bound n
  have hlog := Real.log_le_log (pow_pos hNr N) hbound
  rw [Real.log_mul (ne_of_gt (mul_pos hCr hMr)) (ne_of_gt hP),
    Real.log_mul (ne_of_gt hCr) (ne_of_gt hMr), Real.log_pow, Real.log_pow,
    Real.log_prod (fun i _ => ne_of_gt (hpow i))] at hlog
  simp only [Real.log_pow] at hlog
  dsimp [N, M] at hlog
  push_cast at hlog
  linarith

#print axioms factorial_mode
#print axioms product_factorial_mode
#print axioms multinomial_mode
#print axioms histogram_card_bound
#print axioms empirical_type_lower_bound
#print axioms weighted_type_lower_bound
#print axioms log_multinomial_lower_bound

end MatrixDimensionAudit.MultinomialTypeBoundBridge
