import formalization.TriplingSectorCountBridge

/-!
The exact maximizing fixed-middle count, including the adjacent tie case,
for the actual retained tripling-word cardinalities.
-/

namespace MatrixDimensionAudit.TriplingSectorModeBridge

open TriplingSectorCountBridge
open scoped BigOperators

/-- The manuscript's chosen maximizing middle count. -/
def mode (N : ℕ) : ℕ := (N + 1) / 3

theorem mode_le (N : ℕ) : mode N ≤ N := by unfold mode; omega

theorem count_pos {N m : ℕ} (hm : m ≤ N) : 0 < count N m := by
  rw [count_eq_choose]
  exact Nat.mul_pos (Nat.choose_pos hm) (Nat.pow_pos (by decide))

/-- Exact cross-multiplied ratio, without rational division. -/
theorem adjacent_recurrence (N m : ℕ) (hm : m < N) :
    2 * (m + 1) * count N (m + 1) = (N - m) * count N m := by
  have hp : 2 ^ (N - m) = 2 ^ (N - (m + 1)) * 2 := by
    rw [show N - m = (N - (m + 1)) + 1 by omega, pow_succ]
  simp only [count_eq_choose]
  calc
    2 * (m + 1) * (N.choose (m + 1) * 2 ^ (N - (m + 1))) =
        2 * (N.choose (m + 1) * (m + 1)) * 2 ^ (N - (m + 1)) := by ring
    _ = 2 * (N.choose m * (N - m)) * 2 ^ (N - (m + 1)) := by
      rw [Nat.choose_succ_right_eq]
    _ = (N - m) * (N.choose m * 2 ^ (N - m)) := by rw [hp]; ring

/-- Counts increase exactly up to the cross-multiplied ratio threshold. -/
theorem adjacent_increase_iff (N m : ℕ) (hm : m < N) :
    count N m ≤ count N (m + 1) ↔ 3 * m + 2 ≤ N := by
  have hr := adjacent_recurrence N m hm
  have hc := count_pos (Nat.le_of_lt hm)
  constructor
  · intro h
    have hmul := Nat.mul_le_mul_left (2 * (m + 1)) h
    rw [hr] at hmul
    have hh := Nat.le_of_mul_le_mul_right hmul hc
    omega
  · intro h
    have hh : 2 * (m + 1) ≤ N - m := by omega
    have hmul := Nat.mul_le_mul_right (count N m) hh
    rw [← hr] at hmul
    exact Nat.le_of_mul_le_mul_left hmul (by omega)

/-- Counts decrease exactly after the cross-multiplied ratio threshold. -/
theorem adjacent_decrease_iff (N m : ℕ) (hm : m < N) :
    count N (m + 1) ≤ count N m ↔ N ≤ 3 * m + 2 := by
  have hr := adjacent_recurrence N m hm
  have hc := count_pos (Nat.le_of_lt hm)
  constructor
  · intro h
    have hmul := Nat.mul_le_mul_left (2 * (m + 1)) h
    rw [hr] at hmul
    have hh := Nat.le_of_mul_le_mul_right hmul hc
    omega
  · intro h
    have hh : N - m ≤ 2 * (m + 1) := by omega
    have hmul := Nat.mul_le_mul_right (count N m) hh
    rw [← hr] at hmul
    exact Nat.le_of_mul_le_mul_left hmul (by omega)

/-- Adjacent supported sectors tie precisely when N=3m+2. -/
theorem adjacent_tie_iff (N m : ℕ) (hm : m < N) :
    count N m = count N (m + 1) ↔ N = 3 * m + 2 := by
  constructor
  · intro h
    have hi := (adjacent_increase_iff N m hm).mp h.le
    have hd := (adjacent_decrease_iff N m hm).mp h.ge
    omega
  · intro h
    exact Nat.le_antisymm ((adjacent_increase_iff N m hm).mpr (by omega))
      ((adjacent_decrease_iff N m hm).mpr (by omega))

/-- The supported sequence is monotone up to the chosen mode. -/
theorem increasing_to_mode (N a b : ℕ) (hab : a ≤ b) (hb : b ≤ mode N) :
    count N a ≤ count N b := by
  have hs : Monotone (fun m => count N (min m (mode N))) := by
    apply monotone_nat_of_le_succ
    intro m
    by_cases hm : m < mode N
    · rw [Nat.min_eq_left (by omega : m ≤ mode N),
        Nat.min_eq_left (by omega : m + 1 ≤ mode N)]
      apply (adjacent_increase_iff N m (by have := mode_le N; omega)).mpr
      unfold mode at hm
      omega
    · rw [Nat.min_eq_right (by omega : mode N ≤ m),
        Nat.min_eq_right (by omega : mode N ≤ m + 1)]
  have h := hs hab
  simpa only [Nat.min_eq_left (hab.trans hb), Nat.min_eq_left hb] using h

/-- Counts are antitone after the chosen mode, including the zero tail m>N. -/
theorem decreasing_from_mode (N a b : ℕ) (ha : mode N ≤ a) (hab : a ≤ b) :
    count N b ≤ count N a := by
  have hs : AntitoneOn (count N) {m | mode N ≤ m} := by
    apply antitoneOn_nat_Ici_of_succ_le
    intro m hm
    by_cases hmn : m < N
    · apply (adjacent_decrease_iff N m hmn).mpr
      unfold mode at hm
      omega
    · rw [count_eq_zero_of_lt (by omega : N < m + 1)]
      exact Nat.zero_le _
  exact hs ha (ha.trans hab) hab

/-- The explicit floor((N+1)/3) maximizes every actual retained-word count.
The quantifier includes m>N and N=0. -/
theorem mode_maximizes (N m : ℕ) : count N m ≤ count N (mode N) := by
  by_cases hm : m ≤ mode N
  · exact increasing_to_mode N m (mode N) hm le_rfl
  · exact decreasing_from_mode N (mode N) m le_rfl (by omega)

/-- Exact integer average lower bound at the manuscript's explicit choice. -/
theorem mode_average_bound (N : ℕ) : 3 ^ N ≤ (N + 1) * count N (mode N) := by
  calc
    3 ^ N = ∑ m ∈ Finset.range (N + 1), count N m := (sum_count N).symm
    _ ≤ ∑ _m ∈ Finset.range (N + 1), count N (mode N) :=
      Finset.sum_le_sum (fun m _ => mode_maximizes N m)
    _ = (N + 1) * count N (mode N) := by simp

/-- Complete tie characterization: the preceding index is also maximal only
when N+1 is a multiple of three. There are no other maximizers, even in the tail. -/
theorem maximizer_iff (N m : ℕ) :
    count N m = count N (mode N) ↔
      m = mode N ∨ (m + 1 = mode N ∧ N + 1 = 3 * mode N) := by
  constructor
  · intro h
    have hc := count_pos (mode_le N)
    have hmN : m ≤ N := by
      by_contra hn
      have hz := count_eq_zero_of_lt (by omega : N < m)
      omega
    by_cases hm : m < mode N
    · by_cases he : m + 1 = mode N
      · right
        refine ⟨he, ?_⟩
        have ht : count N m = count N (m + 1) := by rw [he]; exact h
        have hn := (adjacent_tie_iff N m (by have := mode_le N; omega)).mp ht
        omega
      · have hmn : m < N := by have := mode_le N; omega
        have hs := (adjacent_increase_iff N m hmn).mpr
          (by unfold mode at hm; omega)
        have hne : count N m ≠ count N (m + 1) := by
          intro ht
          have hn := (adjacent_tie_iff N m hmn).mp ht
          unfold mode at he
          omega
        have ht : count N m < count N (m + 1) := by omega
        have hu := mode_maximizes N (m + 1)
        omega
    · by_cases he : m = mode N
      · exact Or.inl he
      · have hmn : mode N < N := by omega
        have hs := (adjacent_decrease_iff N (mode N) hmn).mpr
          (by unfold mode; omega)
        have hne : count N (mode N + 1) ≠ count N (mode N) := by
          intro ht
          have hn := (adjacent_tie_iff N (mode N) hmn).mp ht.symm
          unfold mode at hn
          omega
        have ht : count N (mode N + 1) < count N (mode N) := by omega
        have hu := decreasing_from_mode N (mode N + 1) m (by omega) (by omega)
        omega
  · intro h
    rcases h with hm | ⟨hm, hn⟩
    · rw [hm]
    · have hmn : m < N := by have := mode_le N; omega
      have ht := (adjacent_tie_iff N m hmn).mpr (by omega)
      simpa only [hm] using ht

/-- The explicit chosen sector cardinality satisfies the requested integer
lower bound; no division or divisibility convention is needed. -/
theorem mode_card_bound (N : ℕ) :
    3 ^ N ≤ count N ((N + 1) / 3) * (N + 1) := by
  simpa only [mode, Nat.mul_comm] using mode_average_bound N

/-- The same bound with the exact binomial cardinality substituted. -/
theorem explicit_binomial_bound (N : ℕ) :
    3 ^ N ≤ (N.choose ((N + 1) / 3) * 2 ^ (N - (N + 1) / 3)) * (N + 1) := by
  simpa only [count_eq_choose] using mode_card_bound N

@[simp] theorem mode_zero : mode 0 = 0 := rfl

@[simp] theorem mode_count_zero : count 0 (mode 0) = 1 := by
  simp [count_eq_choose]

#print axioms adjacent_recurrence
#print axioms adjacent_tie_iff
#print axioms mode_maximizes
#print axioms maximizer_iff
#print axioms mode_average_bound
#print axioms mode_card_bound
#print axioms explicit_binomial_bound

end MatrixDimensionAudit.TriplingSectorModeBridge
