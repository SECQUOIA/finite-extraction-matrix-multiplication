import formalization.GeneralRowDimension
import formalization.GeneralRowCatalyst

namespace MatrixDimensionAudit
namespace JointDimensionCertificate

open WeightedSector GeneralFlow GeneralRowSector AllRowProfile GeneralRowDimension GeneralRowCatalyst

private def rowTwoPositive (x : Nat) : Nat :=
  if x ≤ 6 then rowTwoPotential x else 1

private theorem rowTwoPositive_pos (x : Nat) : 0 < rowTwoPositive x := by
  unfold rowTwoPositive
  split
  · have : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6 := by omega
    rcases this with h | h | h | h | h | h | h <;> subst x <;> decide
  · exact Nat.zero_lt_one

private theorem rowTwoPositive_local (a : Action 2) (child : Nat) (hc : child ∈ a.children) :
    rowTwoPositive child ≤ (a.h + 1) * rowTwoPositive a.x := by
  obtain ⟨t, ht, heq⟩ := List.mem_map.mp hc
  have ht' : t ≤ a.h := by simpa only [List.mem_range, Nat.lt_succ_iff] using ht
  have hx := a.x_lower
  have hxu := a.x_upper
  have hh := a.h_lower
  have hhu := a.h_upper
  have hb : child ≤ 6 := by omega
  have hxl : a.x < 7 := by omega
  have hhl : a.h < 7 := by omega
  have htl : t < 7 := by omega
  have hf := rowTwoPotential_legalSplits ⟨a.x, hxl⟩ ⟨a.h, hhl⟩ ⟨t, htl⟩
    hx hxu hh hhu ht'
  simp only [rowTwoPositive, hb, show a.x ≤ 6 by omega, ↓reduceIte]
  simpa [heq] using hf

/-- The stronger row-two reset cost follows from the actual general-row actions. -/
theorem rowTwo_actual_baseline (row : Row 2 1 K) :
    2 ^ K * 16 ^ row.Z ≤ row.dimension := by
  have h := boundary_potential_bound row.actions rowTwoPositive _ _ row.balance
    rowTwoPositive_pos (by intro a _ y hy; exact rowTwoPositive_local a y hy)
  simpa [wordWeight, List.map_append, List.prod_append, List.map_replicate,
    wordWeight_replicate, rowTwoPositive, rowTwoPotential, Row.dimension] using h


/-- Cleared scalar necessities for the joint source-flattening rank comparison. -/
def Necessary (n K j Z : Nat) : Prop :=
  sourceLeg (n + 2) ^ (K * j) * lowerSourceProduct n ^ K * 1344 ^ Z *
      denominator n ^ (3 * K * j) < numerator n ^ (3 * K * j) ∧
  sourceLeg (n + 2) ^ (K * j) * lowerSourceProduct n ^ K * 1344 ^ Z <
      2 ^ (3 * K * j) * 3 ^ (3 * Z * j)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- Every possible tuple below the dimension threshold is checked exactly. -/
theorem bounded_search :
    ∀ K : Fin 24, ∀ j : Fin (24 / K.val + 1), ∀ Z : Fin (10 / j.val + 1),
    ∀ n : Fin 15,
    0 < K.val → 0 < j.val → K.val * j.val < 24 → Z.val * j.val < 10 →
    (2 * 3 ^ n.val) ^ (K.val * j.val) < 2 ^ 24 →
    (2 ^ K.val * 6 ^ Z.val) ^ j.val < 2 ^ 24 →
    (n.val = 0 → (2 ^ K.val * 16 ^ Z.val) ^ j.val < 2 ^ 24) →
    ¬ Necessary n.val K.val j.val Z.val := by
  unfold Necessary
  decide

/-- The finite search covers all natural parameters, including zero resets. -/
theorem scalar_obstruction (n K j Z : Nat) (hK : 0 < K) (hj : 0 < j)
    (branch : (2 * 3 ^ n) ^ (K * j) < 2 ^ 24)
    (reset : (2 ^ K * 6 ^ Z) ^ j < 2 ^ 24)
    (rowTwo : n = 0 → (2 ^ K * 16 ^ Z) ^ j < 2 ^ 24) :
    ¬ Necessary n K j Z := by
  have hm : 0 < K * j := Nat.mul_pos hK hj
  have hmBase : 2 ^ (K * j) ≤ (2 * 3 ^ n) ^ (K * j) :=
    Nat.pow_le_pow_left (by have := Nat.one_le_pow n 3 (by decide); omega) _
  have hmLt : K * j < 24 := by
    apply Nat.lt_of_not_ge
    intro h
    have := Nat.le_trans (Nat.pow_le_pow_right (by decide : 0 < 2) h) hmBase
    omega
  have hnBase : 2 * 3 ^ n ≤ (2 * 3 ^ n) ^ (K * j) := by
    simpa using Nat.pow_le_pow_right
      (by have := Nat.one_le_pow n 3 (by decide); omega : 0 < 2 * 3 ^ n) hm
  have hnLt : n < 15 := by
    apply Nat.lt_of_not_ge
    intro h
    have hh := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by decide : 0 < 3) h)
    have hc : 2 ^ 24 < 2 * 3 ^ 15 := by decide
    omega
  have hzBase : 6 ^ (Z * j) ≤ (2 ^ K * 6 ^ Z) ^ j := by
    rw [Nat.pow_mul]
    apply Nat.pow_le_pow_left
    have := Nat.one_le_pow K 2 (by decide)
    exact Nat.le_mul_of_pos_left _ (by omega)
  have hzLt : Z * j < 10 := by
    apply Nat.lt_of_not_ge
    intro h
    have hh := Nat.le_trans (Nat.pow_le_pow_right (by decide : 0 < 6) h) hzBase
    have hc : 2 ^ 24 < 6 ^ 10 := by decide
    omega
  have hkLt : K < 24 := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right _ hj) hmLt
  have hjLt : j < 24 / K + 1 := by
    have := (Nat.le_div_iff_mul_le hK).mpr (show j * K ≤ 24 by rw [Nat.mul_comm]; omega)
    omega
  have hzLt' : Z < 10 / j + 1 := by
    have := (Nat.le_div_iff_mul_le hj).mpr (show Z * j ≤ 10 by omega)
    omega
  exact bounded_search ⟨K, hkLt⟩ ⟨j, hjLt⟩ ⟨Z, hzLt'⟩ ⟨n, hnLt⟩
    hK hj hmLt hzLt branch reset rowTwo

/-- Numeric dimensions obey the threshold once the two cleared necessities hold. -/
theorem dimension_bound (n D K k j Z : Nat) (hK : 0 < K) (hk : 0 < k) (hj : 0 < j)
    (branch : (2 * 3 ^ n) ^ K ≤ D)
    (reset : 2 ^ K * 6 ^ Z ≤ D)
    (rowTwo : n = 0 → 2 ^ K * 16 ^ Z ≤ D)
    (necessary : Necessary n K j Z) :
    2 ^ 24 ≤ D ^ (k * j) := by
  apply Nat.le_of_not_lt
  intro small
  have dpos : 0 < D := Nat.lt_of_lt_of_le
    (Nat.pow_pos (by have := Nat.one_le_pow n 3 (by decide); omega)) branch
  have hpow : D ^ j ≤ D ^ (k * j) :=
    Nat.pow_le_pow_right dpos (Nat.le_mul_of_pos_left _ hk)
  have hb : (2 * 3 ^ n) ^ (K * j) < 2 ^ 24 := by
    rw [Nat.pow_mul]
    exact Nat.lt_of_le_of_lt (Nat.pow_le_pow_left branch j) (Nat.lt_of_le_of_lt hpow small)
  have hr : (2 ^ K * 6 ^ Z) ^ j < 2 ^ 24 :=
    Nat.lt_of_le_of_lt (Nat.pow_le_pow_left reset j) (Nat.lt_of_le_of_lt hpow small)
  have htwo : n = 0 → (2 ^ K * 16 ^ Z) ^ j < 2 ^ 24 := by
    intro hn
    exact Nat.lt_of_le_of_lt (Nat.pow_le_pow_left (rowTwo hn) j)
      (Nat.lt_of_le_of_lt hpow small)
  exact scalar_obstruction n K j Z hK hj hb hr htwo necessary

private theorem family_rowTwo_baseline (family : Family 0 K) :
    2 ^ K * 16 ^ family.triplings ≤ family.dimension := by
  obtain ⟨top, lower⟩ := family
  cases lower
  simpa [Family.dimension, Family.triplings, LowerRows.dimension, LowerRows.triplings]
    using rowTwo_actual_baseline top

/-- All indices and actual dimensions; only the displayed scalar necessities
remain hypotheses. No tensor-rank or algorithm interpretation is asserted. -/
theorem actual_family_dimension_bound (family : Family n K) (k j : Nat)
    (hK : 0 < K) (hk : 0 < k) (hj : 0 < j)
    (necessary : Necessary n K j family.triplings) :
    2 ^ 24 ≤ family.dimension ^ (k * j) := by
  apply dimension_bound n family.dimension K k j family.triplings hK hk hj
    (family_branch_baseline family) (family_reset_baseline family) _ necessary
  intro hn
  subst n
  exact family_rowTwo_baseline family

/-- Derived scalar necessities from the actual counts and a numerical rank floor. -/
theorem actual_count_necessary (family : Family n K) (j : Nat)
    (comparison : sourceLeg (n + 2) ^ (K * j) * familyCharge family *
      (family.dimension ^ j) ^ 3 < ((2 ^ K * family.count) ^ j) ^ 3) :
    Necessary n K j family.triplings := by
  let R := sourceLeg (n + 2) ^ (K * j) * lowerSourceProduct n ^ K * 1344 ^ family.triplings
  have floor : R ≤ sourceLeg (n + 2) ^ (K * j) * familyCharge family := by
    simpa [R, Nat.mul_assoc] using Nat.mul_le_mul_left
      (sourceLeg (n + 2) ^ (K * j)) (family_charge_floor family)
  have strict : R * family.dimension ^ (3 * j) < (2 ^ K * family.count) ^ (3 * j) := by
    have h := Nat.lt_of_le_of_lt (Nat.mul_le_mul_right ((family.dimension ^ j) ^ 3) floor) comparison
    simpa [← Nat.pow_mul, Nat.mul_comm j 3] using h
  have coarse : 2 ^ K * family.count ≤ family.dimension * (2 ^ K * 3 ^ family.triplings) := by
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
      Nat.mul_le_mul_left (2 ^ K) family.coarse_actual_count
  have hcoarse := Nat.lt_of_lt_of_le strict (Nat.pow_le_pow_left coarse (3 * j))
  have cl : R < 2 ^ (3 * K * j) * 3 ^ (3 * family.triplings * j) := by
    have hs : R * family.dimension ^ (3 * j) <
        (2 ^ (3 * K * j) * 3 ^ (3 * family.triplings * j)) * family.dimension ^ (3 * j) := by
      simpa [Nat.mul_pow, ← Nat.pow_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hcoarse
    exact Nat.lt_of_mul_lt_mul_right hs
  have denpos : 0 < denominator n ^ (3 * K * j) := Nat.pow_pos (denominator_pos n)
  have strictDen := Nat.mul_lt_mul_of_pos_right strict denpos
  have profile := Nat.pow_le_pow_left family.sharp_actual_gain (3 * j)
  have hp : (2 ^ K * family.count) ^ (3 * j) * denominator n ^ (3 * K * j) ≤
      family.dimension ^ (3 * j) * numerator n ^ (3 * K * j) := by
    simpa [Nat.mul_pow, ← Nat.pow_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using profile
  have hprofile := Nat.lt_of_lt_of_le strictDen hp
  have pl : R * denominator n ^ (3 * K * j) < numerator n ^ (3 * K * j) := by
    have hs : (R * denominator n ^ (3 * K * j)) * family.dimension ^ (3 * j) <
        numerator n ^ (3 * K * j) * family.dimension ^ (3 * j) := by
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hprofile
    exact Nat.lt_of_mul_lt_mul_right hs
  exact ⟨pl, cl⟩

/-- A matched-sector pooled comparison yields the numerical comparison used above. -/
theorem pooled_to_count_comparison (family : Family n K) (rank exactification copies k j : Nat)
    (exactification_pos : 0 < exactification)
    (copies_paid : family.count ^ 3 ≤ copies)
    (rank_floor : sourceLeg (n + 2) ^ (K * k * j) * familyCharge family ^ k ≤ rank)
    (raw : (rank * exactification ^ j * copies ^ (k * j)) *
      (family.dimension ^ (k * j)) ^ 3 <
      family.count ^ (3 * k * j) * ((2 ^ K * family.count) ^ (k * j)) ^ 3) :
    sourceLeg (n + 2) ^ (K * j) * familyCharge family *
      (family.dimension ^ j) ^ 3 < ((2 ^ K * family.count) ^ j) ^ 3 := by
  have copied := Nat.pow_le_pow_left copies_paid (k * j)
  have paid : family.count ^ (3 * k * j) ≤ exactification ^ j * copies ^ (k * j) := by
    have hc : family.count ^ (3 * k * j) ≤ copies ^ (k * j) := by
      simpa [← Nat.pow_mul, Nat.mul_assoc] using copied
    exact Nat.le_trans hc (Nat.le_mul_of_pos_left _ (Nat.pow_pos exactification_pos))
  have raw' : rank * (exactification ^ j * copies ^ (k * j)) *
      (family.dimension ^ (k * j)) ^ 3 <
      family.count ^ (3 * k * j) * ((2 ^ K * family.count) ^ (k * j)) ^ 3 := by
    simpa [Nat.mul_assoc] using raw
  have relaxed := cancel_paid_multiplicity _ _ _ _ _ paid raw'
  have lower := Nat.mul_le_mul_right ((family.dimension ^ (k * j)) ^ 3) rank_floor
  have h := Nat.lt_of_le_of_lt lower relaxed
  have hp : (sourceLeg (n + 2) ^ (K * j) * familyCharge family *
      (family.dimension ^ j) ^ 3) ^ k < (((2 ^ K * family.count) ^ j) ^ 3) ^ k := by
    simpa [Nat.mul_pow, ← Nat.pow_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
  apply Nat.lt_of_not_ge
  intro reverse
  exact Nat.not_lt_of_ge (Nat.pow_le_pow_left reverse k) hp

/-- The actual count/dimension data and explicit pooled numerical resources
force the threshold. The source-flattening rank floor remains a hypothesis. -/
theorem actual_pooled_dimension_bound (family : Family n K) (rank exactification copies k j : Nat)
    (hK : 0 < K) (hk : 0 < k) (hj : 0 < j)
    (exactification_pos : 0 < exactification)
    (copies_paid : family.count ^ 3 ≤ copies)
    (rank_floor : sourceLeg (n + 2) ^ (K * k * j) * familyCharge family ^ k ≤ rank)
    (raw : (rank * exactification ^ j * copies ^ (k * j)) *
      (family.dimension ^ (k * j)) ^ 3 <
      family.count ^ (3 * k * j) * ((2 ^ K * family.count) ^ (k * j)) ^ 3) :
    2 ^ 24 ≤ family.dimension ^ (k * j) := by
  apply actual_family_dimension_bound family k j hK hk hj
  exact actual_count_necessary family j (pooled_to_count_comparison family rank
    exactification copies k j exactification_pos copies_paid rank_floor raw)

end JointDimensionCertificate
end MatrixDimensionAudit

#print axioms MatrixDimensionAudit.JointDimensionCertificate.bounded_search
#print axioms MatrixDimensionAudit.JointDimensionCertificate.scalar_obstruction

#print axioms MatrixDimensionAudit.JointDimensionCertificate.rowTwo_actual_baseline
#print axioms MatrixDimensionAudit.JointDimensionCertificate.dimension_bound
#print axioms MatrixDimensionAudit.JointDimensionCertificate.actual_family_dimension_bound

#print axioms MatrixDimensionAudit.JointDimensionCertificate.actual_count_necessary
#print axioms MatrixDimensionAudit.JointDimensionCertificate.pooled_to_count_comparison
#print axioms MatrixDimensionAudit.JointDimensionCertificate.actual_pooled_dimension_bound
