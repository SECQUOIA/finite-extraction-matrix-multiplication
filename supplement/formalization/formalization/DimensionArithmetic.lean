import Std

/-!
Small kernel-checked arithmetic certificates from the dimension obstruction.
This file does not prove the conserved-flow theorem or its algorithm bridge.
It uses only Std and ordinary `decide`, without native_decide or extra axioms.

Check with:
  elan run leanprover/lean4:v4.34.1 lean formalization/DimensionArithmetic.lean
-/

namespace MatrixDimensionAudit

def rowTwoPotential : Nat → Nat
  | 0 => 2
  | 1 => 1
  | 2 => 2
  | 3 => 4
  | 4 => 6
  | 5 => 12
  | 6 => 16
  | _ => 0

theorem rowTwoPotential_legalSplits :
    ∀ x h t : Fin 7,
      1 ≤ x.val → x.val < 6 →
      1 ≤ h.val → h.val ≤ min x.val (6 - x.val) →
      t.val ≤ h.val →
      rowTwoPotential (x.val + h.val - 2 * t.val) ≤
        (h.val + 1) * rowTwoPotential x.val := by
  decide

theorem sourceSide_gt_twoPow64 :
    (2 : Nat) ^ 64 < 12 ^ 18 := by
  decide

theorem indexThree_reuseComparison :
    (56 : Nat) ^ 102 < 3 ^ 6 * 24 ^ 5 * 45 ^ 102 := by
  decide

theorem indexFive_reuseComparison :
    (3185 : Nat) ^ 12 < 105 * 2187 ^ 12 := by
  decide

theorem materializedMatrixBytes_gt_twoPow132 :
    (2 : Nat) ^ 132 < 8 * 12 ^ 36 := by
  decide

theorem retainedWork_is_exactCube :
    (27 : Nat) * (12 ^ 18) ^ 2 = (3 * 12 ^ 12) ^ 3 := by
  decide

#print axioms rowTwoPotential_legalSplits
#print axioms sourceSide_gt_twoPow64
#print axioms indexThree_reuseComparison
#print axioms indexFive_reuseComparison
#print axioms materializedMatrixBytes_gt_twoPow132
#print axioms retainedWork_is_exactCube

end MatrixDimensionAudit
