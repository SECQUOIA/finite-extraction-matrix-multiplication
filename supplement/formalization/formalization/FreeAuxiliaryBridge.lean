import formalization.JointDimensionCertificate

/-!
Numerical cancellation for independent auxiliary separator dimensions. The
target multiplicity is the actual block count, not the auxiliary dimension.
The source-rank floor and the strict pooled comparison remain hypotheses.
-/

namespace MatrixDimensionAudit
namespace FreeAuxiliaryBridge

open GeneralFlow AllRowProfile GeneralRowCatalyst JointDimensionCertificate

/-- Local numerical resources for one polynomial separator. -/
structure Separator where
  blocks : Nat
  auxiliary : Nat
  localCopies : Nat
  blocks_pos : 0 < blocks
  auxiliary_pos : 0 < auxiliary
  local_bound : blocks + auxiliary - 1 ≤ localCopies

def blockCount (separators : List Separator) : Nat :=
  (separators.map Separator.blocks).prod

def auxiliaryCount (separators : List Separator) : Nat :=
  (separators.map Separator.auxiliary).prod

/-- Three cyclic orientations of the local copy budgets. -/
def cyclicCopies (separators : List Separator) : Nat :=
  (separators.map Separator.localCopies).prod ^ 3

/-- The exactification budget for power k of the three cyclic families. -/
def polynomialExactification (separators : List Separator) (k : Nat) : Nat :=
  k * (3 * (separators.map (fun s => min (s.blocks - 1) (s.auxiliary - 1))).sum) + 1

theorem local_auxiliary_paid (s : Separator) : s.auxiliary ≤ s.localCopies := by
  have := s.blocks_pos
  have := s.local_bound
  omega

/-- The auxiliary dimensions alone are paid by the cyclic copy budget. -/
theorem auxiliary_copies_paid (separators : List Separator) :
    auxiliaryCount separators ^ 3 ≤ cyclicCopies separators := by
  have base : auxiliaryCount separators ≤ (separators.map Separator.localCopies).prod := by
    induction separators with
    | nil => simp [auxiliaryCount]
    | cons s tail ih =>
      simpa [auxiliaryCount] using Nat.mul_le_mul (local_auxiliary_paid s) ih
  exact Nat.pow_le_pow_left base 3

/-- Move the auxiliary power out of the target side and cancel its paid cost.
The resulting comparison uses the actual block count on the target side. -/
theorem free_auxiliary_to_count_comparison (family : Family n K)
    (auxiliary rank exactification copies k j : Nat)
    (exactification_pos : 0 < exactification)
    (copies_paid : auxiliary ^ 3 ≤ copies)
    (rank_floor : sourceLeg (n + 2) ^ (K * k * j) * familyCharge family ^ k ≤ rank)
    (raw : (rank * exactification ^ j * copies ^ (k * j)) *
      (family.dimension ^ (k * j)) ^ 3 <
      family.count ^ (3 * k * j) * ((2 ^ K * auxiliary) ^ (k * j)) ^ 3) :
    sourceLeg (n + 2) ^ (K * j) * familyCharge family *
      (family.dimension ^ j) ^ 3 < ((2 ^ K * family.count) ^ j) ^ 3 := by
  have copied := Nat.pow_le_pow_left copies_paid (k * j)
  have paid : auxiliary ^ (3 * k * j) ≤ exactification ^ j * copies ^ (k * j) := by
    have hc : auxiliary ^ (3 * k * j) ≤ copies ^ (k * j) := by
      simpa [← Nat.pow_mul, Nat.mul_assoc] using copied
    exact Nat.le_trans hc (Nat.le_mul_of_pos_left _ (Nat.pow_pos exactification_pos))
  have raw' : rank * (exactification ^ j * copies ^ (k * j)) *
      (family.dimension ^ (k * j)) ^ 3 <
      auxiliary ^ (3 * k * j) * ((2 ^ K * family.count) ^ (k * j)) ^ 3 := by
    simpa [Nat.mul_pow, ← Nat.pow_mul, Nat.mul_assoc, Nat.mul_comm,
      Nat.mul_left_comm] using raw
  have relaxed := cancel_paid_multiplicity _ _ _ _ _ paid raw'
  have lower := Nat.mul_le_mul_right ((family.dimension ^ (k * j)) ^ 3) rank_floor
  have h := Nat.lt_of_le_of_lt lower relaxed
  have hp : (sourceLeg (n + 2) ^ (K * j) * familyCharge family *
      (family.dimension ^ j) ^ 3) ^ k < (((2 ^ K * family.count) ^ j) ^ 3) ^ k := by
    simpa [Nat.mul_pow, ← Nat.pow_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
  apply Nat.lt_of_not_ge
  intro reverse
  exact Nat.not_lt_of_ge (Nat.pow_le_pow_left reverse k) hp

/-- Independent auxiliary dimensions do not change the actual-family numerical
dimension threshold, provided the copies pay their cubic product. -/
theorem actual_free_auxiliary_dimension_bound (family : Family n K)
    (auxiliary rank exactification copies k j : Nat)
    (hK : 0 < K) (hk : 0 < k) (hj : 0 < j)
    (exactification_pos : 0 < exactification)
    (copies_paid : auxiliary ^ 3 ≤ copies)
    (rank_floor : sourceLeg (n + 2) ^ (K * k * j) * familyCharge family ^ k ≤ rank)
    (raw : (rank * exactification ^ j * copies ^ (k * j)) *
      (family.dimension ^ (k * j)) ^ 3 <
      family.count ^ (3 * k * j) * ((2 ^ K * auxiliary) ^ (k * j)) ^ 3) :
    2 ^ 24 ≤ family.dimension ^ (k * j) := by
  apply actual_family_dimension_bound family k j hK hk hj
  exact actual_count_necessary family j (free_auxiliary_to_count_comparison family
    auxiliary rank exactification copies k j exactification_pos copies_paid rank_floor raw)

/-- Concrete positive local separator data derive the copy and exactification
premises. Local block counts multiply to the actual family count; auxiliary
dimensions remain independent of these block counts. -/
theorem polynomial_auxiliary_dimension_bound (family : Family n K)
    (separators : List Separator) (rank k j : Nat)
    (hK : 0 < K) (hk : 0 < k) (hj : 0 < j)
    (count_eq : blockCount separators = family.count)
    (rank_floor : sourceLeg (n + 2) ^ (K * k * j) * familyCharge family ^ k ≤ rank)
    (raw : (rank * polynomialExactification separators k ^ j *
      cyclicCopies separators ^ (k * j)) * (family.dimension ^ (k * j)) ^ 3 <
      blockCount separators ^ (3 * k * j) *
        ((2 ^ K * auxiliaryCount separators) ^ (k * j)) ^ 3) :
    2 ^ 24 ≤ family.dimension ^ (k * j) := by
  apply actual_free_auxiliary_dimension_bound family (auxiliaryCount separators) rank
    (polynomialExactification separators k) (cyclicCopies separators) k j hK hk hj
    (by simp [polynomialExactification]) (auxiliary_copies_paid separators) rank_floor
  simpa only [count_eq] using raw

end FreeAuxiliaryBridge
end MatrixDimensionAudit

#print axioms MatrixDimensionAudit.FreeAuxiliaryBridge.local_auxiliary_paid
#print axioms MatrixDimensionAudit.FreeAuxiliaryBridge.auxiliary_copies_paid
#print axioms MatrixDimensionAudit.FreeAuxiliaryBridge.free_auxiliary_to_count_comparison
#print axioms MatrixDimensionAudit.FreeAuxiliaryBridge.actual_free_auxiliary_dimension_bound
#print axioms MatrixDimensionAudit.FreeAuxiliaryBridge.polynomial_auxiliary_dimension_bound
