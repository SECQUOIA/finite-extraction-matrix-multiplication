import formalization.GeneralFlowCore

/-!
An integer-power bridge from a concrete pooled-rank recipe to the row-two
dimension obstruction. Exact sector-count upper bounds and the catalyst
charge remain explicit hypotheses; the gain/reuse inequalities do not.
-/

namespace MatrixDimensionAudit
namespace GeneralFlow

/-- The unnormalized pooled-rank comparison, after dropping no overhead. -/
def PowerSubcubic (catalyst overhead U V k j : Nat) : Prop :=
  catalyst ^ k * overhead * (U ^ j) ^ (3 * k) < (V ^ j) ^ (3 * k)

def rowTwoDeclaredRank (catalyst overhead N K k j : Nat) : Nat :=
  catalyst ^ k * overhead * 27 ^ (N * K * k * j)

def rowTwoSourceSide (D N k j : Nat) : Nat := D ^ (N * k * j)

def rowTwoTargetSide (N K k j : Nat) : Nat := 2 ^ (N * K * k * j)

def rowTwoTargetMultiplicity (M k j : Nat) : Nat := M ^ (3 * k * j)

/-- Exact regrouping of the relaxed comparison after cancelling a sector-sized
separator charge. These are not the manuscript's original r,m,B separately. -/
theorem rowTwo_pooledComparison_iff (catalyst overhead D M N K k j : Nat) :
    rowTwoDeclaredRank catalyst overhead N K k j * (rowTwoSourceSide D N k j) ^ 3 <
      rowTwoTargetMultiplicity M k j * (rowTwoTargetSide N K k j) ^ 3 ↔
    PowerSubcubic catalyst overhead (3 ^ (N * K) * D ^ N)
      (2 ^ (N * K) * M) k j := by
  unfold rowTwoDeclaredRank rowTwoSourceSide rowTwoTargetMultiplicity
    rowTwoTargetSide PowerSubcubic
  rw [show 27 = 3 ^ 3 by decide]
  simp only [Nat.mul_pow, ← Nat.pow_mul]
  simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-- Dropping a cost that already pays for all the output multiplicity. -/
theorem cancel_paid_multiplicity (R H A m B : Nat)
    (paid : m ≤ H) (raw : R * H * A ^ 3 < m * B ^ 3) :
    R * A ^ 3 < B ^ 3 := by
  have lower := Nat.mul_le_mul_left (R * A ^ 3) paid
  have raw' : (R * A ^ 3) * H < m * B ^ 3 := by
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using raw
  have comparison : m * (R * A ^ 3) < m * B ^ 3 := by
    have h := Nat.lt_of_le_of_lt lower raw'
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
  exact Nat.lt_of_mul_lt_mul_left comparison

/-- The original integer pooled comparison, with both the sector multiplicity
and its occurrence in B, implies the relaxed PowerSubcubic condition. -/
theorem rowTwo_actual_to_powerSubcubic
    (catalyst exactification copies D M N K k j : Nat)
    (exactification_pos : 0 < exactification)
    (copies_paid : M ^ 3 ≤ copies)
    (raw :
      (catalyst ^ k * exactification ^ j * copies ^ (k * j) *
        27 ^ (N * K * k * j)) * (D ^ (N * k * j)) ^ 3 <
      M ^ (3 * k * j) * ((2 ^ (N * K) * M) ^ (k * j)) ^ 3) :
    PowerSubcubic catalyst 1 (3 ^ (N * K) * D ^ N)
      (2 ^ (N * K) * M) k j := by
  have copied := Nat.pow_le_pow_left copies_paid (k * j)
  have overhead : M ^ (3 * k * j) ≤ exactification ^ j * copies ^ (k * j) := by
    have he : 0 < exactification ^ j := Nat.pow_pos exactification_pos
    have hc : M ^ (3 * k * j) ≤ copies ^ (k * j) := by
      simpa [← Nat.pow_mul, Nat.mul_assoc] using copied
    exact Nat.le_trans hc (Nat.le_mul_of_pos_left _ he)
  have canonical :
      (catalyst ^ k * 27 ^ (N * K * k * j)) *
        (exactification ^ j * copies ^ (k * j)) * (D ^ (N * k * j)) ^ 3 <
      M ^ (3 * k * j) * ((2 ^ (N * K) * M) ^ (k * j)) ^ 3 := by
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using raw
  have relaxed := cancel_paid_multiplicity _ _ _ _ _ overhead canonical
  unfold PowerSubcubic
  rw [show 27 = 3 ^ 3 by decide] at relaxed
  simp only [Nat.mul_pow, ← Nat.pow_mul, Nat.mul_one] at relaxed ⊢
  simpa only [Nat.mul_assoc, Nat.mul_comm,
    Nat.mul_left_comm] using relaxed

/-- Removing the positive overhead and taking the exact integer power root. -/
theorem powerSubcubic_catalytic_gain (catalyst overhead U V C k j : Nat)
    (overhead_pos : 0 < overhead)
    (charge : C ^ 3 ≤ catalyst)
    (subcubic : PowerSubcubic catalyst overhead U V k j) :
    C * U ^ j < V ^ j := by
  have hm : C ^ (3 * k) * (U ^ j) ^ (3 * k) ≤
      catalyst ^ k * overhead * (U ^ j) ^ (3 * k) := by
    have hc := Nat.pow_le_pow_left charge k
    rw [← Nat.pow_mul] at hc
    have ho : catalyst ^ k ≤ catalyst ^ k * overhead :=
      Nat.le_mul_of_pos_right _ overhead_pos
    exact Nat.mul_le_mul_right _ (Nat.le_trans hc ho)
  have hpow : (C * U ^ j) ^ (3 * k) < (V ^ j) ^ (3 * k) := by
    rw [Nat.mul_pow]
    exact Nat.lt_of_le_of_lt hm subcubic
  exact Nat.lt_of_not_ge (by
    intro h
    exact Nat.not_lt_of_ge (Nat.pow_le_pow_left h (3 * k)) hpow)

theorem catalytic_gain_positive (U V C j : Nat)
    (C_pos : 0 < C) (h : C * U ^ j < V ^ j) : U < V := by
  apply Nat.lt_of_not_ge
  intro reverse
  have hp := Nat.pow_le_pow_left reverse j
  have hc : U ^ j ≤ C * U ^ j := Nat.le_mul_of_pos_left _ C_pos
  exact Nat.not_lt_of_ge (Nat.le_trans hp hc) h

/-- A polynomial sector bound turns actual gain into the coarse reset test. -/
theorem rowTwo_gain_from_count (D M N K Z U V : Nat)
    (N_pos : 0 < N)
    (U_def : U = 3 ^ (N * K) * D ^ N)
    (V_def : V = 2 ^ (N * K) * M)
    (coarse_count : M ≤ D ^ N * 3 ^ (N * Z))
    (gain : U < V) : 3 ^ K < 3 ^ Z * 2 ^ K := by
  rw [U_def, V_def] at gain
  have he : 3 ^ (N * K) * D ^ N <
      (2 ^ (N * K) * 3 ^ (N * Z)) * D ^ N := by
    have h := Nat.lt_of_lt_of_le gain (Nat.mul_le_mul_left (2 ^ (N * K)) coarse_count)
    simpa [U_def, V_def, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
  have hsmall := Nat.lt_of_mul_lt_mul_right he
  have hp : (3 ^ K) ^ N < (3 ^ Z * 2 ^ K) ^ N := by
    simpa [Nat.mul_pow, ← Nat.pow_mul, Nat.mul_comm] using hsmall
  exact (Nat.pow_lt_pow_iff_left (Nat.ne_of_gt N_pos)).mp hp

/-- Integer profile values P(0)=3 and P(1)=5 yield the required ratio bound. -/
theorem rowTwo_profile_count_to_ratio (D M N K : Nat)
    (profile_count : 3 ^ (N * K) * M ≤ 5 ^ (N * K) * D ^ N) :
    (2 ^ (N * K) * M) * 9 ^ (N * K) ≤
      10 ^ (N * K) * (3 ^ (N * K) * D ^ N) := by
  have h := Nat.mul_le_mul_left (2 ^ (N * K) * 3 ^ (N * K)) profile_count
  rw [show 9 = 3 * 3 by decide, show 10 = 2 * 5 by decide]
  simp only [Nat.mul_pow]
  simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h

/-- The sharp rational profile count bound implies the exact reuse test. -/
theorem rowTwo_reuse_from_profile (U V N K Z j : Nat)
    (N_pos : 0 < N)
    (profile : V * 9 ^ (N * K) ≤ 10 ^ (N * K) * U)
    (gain : 24 ^ (N * Z) * U ^ j < V ^ j) :
    9 ^ (j * K) * 24 ^ Z < 10 ^ (j * K) := by
  have hprofile := Nat.pow_le_pow_left profile j
  simp only [Nat.mul_pow, ← Nat.pow_mul] at hprofile
  have nine_pos : 0 < 9 ^ (N * K * j) := Nat.pow_pos (by decide)
  have hm := Nat.mul_lt_mul_of_pos_right gain nine_pos
  have ht := Nat.lt_of_lt_of_le hm hprofile
  have hs : (9 ^ (N * K * j) * 24 ^ (N * Z)) * U ^ j <
      10 ^ (N * K * j) * U ^ j := by
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using ht
  have hc := Nat.lt_of_mul_lt_mul_right hs
  have hp : (9 ^ (j * K) * 24 ^ Z) ^ N < (10 ^ (j * K)) ^ N := by
    simpa [Nat.mul_pow, ← Nat.pow_mul, Nat.mul_assoc, Nat.mul_comm,
      Nat.mul_left_comm] using hc
  exact (Nat.pow_lt_pow_iff_left (Nat.ne_of_gt N_pos)).mp hp

/-- The exact recipe data used by the integer-power numerical bridge. -/
structure RowTwoPowerRecipe (D K Z N k j : Nat) where
  sectors : Nat
  catalyst : Nat
  exactification : Nat
  copies : Nat
  exactification_pos : 0 < exactification
  copies_paid : sectors ^ 3 ≤ copies
  coarse_count : sectors ≤ D ^ N * 3 ^ (N * Z)
  profile_count : (2 ^ (N * K) * sectors) * 9 ^ (N * K) ≤
    10 ^ (N * K) * (3 ^ (N * K) * D ^ N)
  catalyst_charge : (24 ^ (N * Z)) ^ 3 ≤ catalyst
  pooled_rank :
    (catalyst ^ k * exactification ^ j * copies ^ (k * j) *
      27 ^ (N * K * k * j)) * (D ^ (N * k * j)) ^ 3 <
    sectors ^ (3 * k * j) * ((2 ^ (N * K) * sectors) ^ (k * j)) ^ 3

/-- No gain or reuse test is assumed: both follow from the recipe counts. -/
theorem rowTwo_recipe_necessary (D K Z N k j : Nat)
    (D_pos : 0 < D) (N_pos : 0 < N)
    (recipe : RowTwoPowerRecipe D K Z N k j) :
    3 ^ K < 3 ^ Z * 2 ^ K ∧
      9 ^ (j * K) * 24 ^ Z < 10 ^ (j * K) := by
  have powerCondition := rowTwo_actual_to_powerSubcubic _ _ _ _ _ _ _ _ _
    recipe.exactification_pos recipe.copies_paid recipe.pooled_rank
  have h := powerSubcubic_catalytic_gain _ _ _ _ _ _ _
    (by decide) recipe.catalyst_charge powerCondition
  have U_pos : 0 < 3 ^ (N * K) * D ^ N :=
    Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.pow_pos D_pos)
  have VU := catalytic_gain_positive _ _ _ _ (Nat.pow_pos (by decide)) h
  exact ⟨rowTwo_gain_from_count D recipe.sectors N K Z _ _ N_pos
      rfl rfl recipe.coarse_count VU,
    rowTwo_reuse_from_profile _ _ N K Z j N_pos recipe.profile_count h⟩

/-- Legal conserved flow and the specified rank/count recipe force A >= 2^96. -/
theorem rowTwo_recipe_sourceSide_bound (splits : List RowTwoSplit)
    (K Z N k j : Nat) (hK : 0 < K) (hN : 0 < N) (hk : 0 < k) (hj : 0 < j)
    (balance : Balanced (List.replicate (K + Z) 1)
      (List.replicate K 0 ++ List.replicate Z 6) (splits.map RowTwoSplit.edge))
    (recipe : RowTwoPowerRecipe (splits.map RowTwoSplit.dimension).prod K Z N k j) :
    2 ^ 96 ≤ (splits.map RowTwoSplit.dimension).prod ^ (N * k * j) := by
  have base := rowTwo_dimension_bound splits K Z balance
  have D_pos : 0 < (splits.map RowTwoSplit.dimension).prod :=
    Nat.lt_of_lt_of_le (Nat.mul_pos (Nat.pow_pos (by decide))
      (Nat.pow_pos (by decide))) base
  obtain ⟨gain, reuse⟩ := rowTwo_recipe_necessary _ K Z N k j D_pos hN recipe
  have hZ : 0 < Z := by
    apply Nat.pos_of_ne_zero
    intro zero
    have impossible : 3 ^ K < 2 ^ K := by simpa [zero] using gain
    exact Nat.not_lt_of_ge (Nat.pow_le_pow_left (by decide : 2 ≤ 3) K) impossible
  exact rowTwo_conditional_sourceSide_bound splits K Z N k j hK hZ hN hk hj
    balance gain reuse

#print axioms powerSubcubic_catalytic_gain
#print axioms rowTwo_pooledComparison_iff
#print axioms rowTwo_actual_to_powerSubcubic
#print axioms rowTwo_gain_from_count
#print axioms rowTwo_reuse_from_profile
#print axioms rowTwo_recipe_necessary
#print axioms rowTwo_recipe_sourceSide_bound

end GeneralFlow
end MatrixDimensionAudit
