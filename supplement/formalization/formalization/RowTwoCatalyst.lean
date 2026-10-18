import formalization.GeneralFlowCore

/-!
The row-two catalyst charge from the actual consumed-factor multiset.
K copies of state 1 are supplied by the external input; removing those copies
from the split-parent list leaves the split factors in the catalyst. Every reset
also consumes one state-6 factor. Conservation itself forces the residual list
to contain at least Z copies of state 1.
-/

namespace MatrixDimensionAudit
namespace GeneralFlow

/-- Remove exactly K external source factors, one occurrence at a time. -/
def removeInjected : Nat → List Nat → List Nat
  | 0, parents => parents
  | K + 1, parents => removeInjected K (parents.erase 1)

theorem removeInjected_ledger (parents : List Nat) (K : Nat)
    (available : K ≤ parents.count 1) :
    parents.Perm (List.replicate K 1 ++ removeInjected K parents) := by
  induction K generalizing parents with
  | zero => simp [removeInjected]
  | succ K ih =>
    have member : 1 ∈ parents := List.count_pos_iff.mp (by omega)
    have tailAvailable : K ≤ (parents.erase 1).count 1 := by
      simp only [List.count_erase_self]
      omega
    have tailLedger := ih (parents.erase 1) tailAvailable
    have whole := (List.perm_cons_erase member).trans (tailLedger.cons 1)
    simpa only [List.replicate_succ, List.cons_append, removeInjected] using whole

/-- Conservation supplies at least K+Z split-parent occurrences at state 1. -/
theorem rowTwo_parent_count (edges : List (Edge Nat)) (K Z : Nat)
    (balance : Balanced (List.replicate (K + Z) 1)
      (List.replicate K 0 ++ List.replicate Z 6) edges) :
    K + Z ≤ (edges.map Edge.src).count 1 := by
  have h := (balanced_iff_counts.mp balance) 1
  simp only [List.count_replicate, List.count_append] at h
  simp at h
  omega

theorem rowTwo_residual_count (edges : List (Edge Nat)) (K Z : Nat)
    (balance : Balanced (List.replicate (K + Z) 1)
      (List.replicate K 0 ++ List.replicate Z 6) edges) :
    Z ≤ (removeInjected K (edges.map Edge.src)).count 1 := by
  have parentCount := rowTwo_parent_count edges K Z balance
  have ledger := removeInjected_ledger (edges.map Edge.src) K (by omega)
  have counted := ledger.count_eq 1
  simp only [List.count_append, List.count_replicate, beq_self_eq_true,
    ite_true] at counted
  omega

/-- A state-1 residual factor has supplied rank 3^3; all other factors are
positive. This bound needs no separate lower bound on the residual length. -/
theorem residual_rank_bound (residual : List Nat) :
    27 ^ residual.count 1 ≤ (residual.map (fun x => (x + 2) ^ 3)).prod := by
  induction residual with
  | nil => simp
  | cons x tail ih =>
    by_cases one : x = 1
    · subst x
      simpa [Nat.pow_succ, Nat.mul_comm] using Nat.mul_le_mul_left 27 ih
    · have factorPositive : 0 < (x + 2) ^ 3 := Nat.pow_pos (by omega)
      have lower : (tail.map (fun x => (x + 2) ^ 3)).prod ≤
          (x + 2) ^ 3 * (tail.map (fun x => (x + 2) ^ 3)).prod :=
        Nat.le_mul_of_pos_left _ factorPositive
      simpa [List.count_cons, one] using Nat.le_trans ih lower

/-- The catalyst prescribed by the consumed tensor-factor ledger, not an
assumed rank floor. Its split factors have base x+2; reset factors have base 8. -/
def rowTwoActualCatalyst (edges : List (Edge Nat)) (K Z : Nat) : Nat :=
  ((removeInjected K (edges.map Edge.src)).map (fun x => (x + 2) ^ 3)).prod *
    8 ^ (3 * Z)

theorem rowTwo_actualCatalyst_charge (edges : List (Edge Nat)) (K Z : Nat)
    (balance : Balanced (List.replicate (K + Z) 1)
      (List.replicate K 0 ++ List.replicate Z 6) edges) :
    (24 ^ Z) ^ 3 ≤ rowTwoActualCatalyst edges K Z := by
  have countBound := rowTwo_residual_count edges K Z balance
  have rankBound := residual_rank_bound (removeInjected K (edges.map Edge.src))
  have resetBound := Nat.mul_le_mul_right (8 ^ (3 * Z))
    (Nat.le_trans (Nat.pow_le_pow_right (by decide : 0 < 27) countBound) rankBound)
  have identity : 27 ^ Z * 8 ^ (3 * Z) = (24 ^ Z) ^ 3 := by
    calc
      27 ^ Z * 8 ^ (3 * Z) = (27 * 512) ^ Z := by
        rw [Nat.mul_pow, Nat.pow_mul]
      _ = (24 ^ 3) ^ Z := rfl
      _ = (24 ^ Z) ^ 3 := by
        simp only [← Nat.pow_mul]
        rw [Nat.mul_comm]
  rw [identity] at resetBound
  exact resetBound

end GeneralFlow
end MatrixDimensionAudit

#print axioms MatrixDimensionAudit.GeneralFlow.removeInjected_ledger
#print axioms MatrixDimensionAudit.GeneralFlow.rowTwo_parent_count
#print axioms MatrixDimensionAudit.GeneralFlow.rowTwo_residual_count
#print axioms MatrixDimensionAudit.GeneralFlow.residual_rank_bound
#print axioms MatrixDimensionAudit.GeneralFlow.rowTwo_actualCatalyst_charge
