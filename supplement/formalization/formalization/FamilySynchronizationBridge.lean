import formalization.FamilyScalingBridge

/-!
Common positive injection scales for actual families, derived from independent
positive-scale rows. The product synchronization preserves grouped histograms.
No occupation, sector-count lower bound, or asymptotic exponent is assumed.
-/
namespace MatrixDimensionAudit.FamilySynchronizationBridge
open GeneralRowSector AllRowProfile FamilyScalingBridge

/-- Scale an actual row, placing its original scale first in the product. -/
def rowAtProduct (row : Row r i K) (s : Nat) : Row r i (K * s) :=
  { actions := scaleActions s row.actions, Z := s * row.Z,
    balance := by simpa only [Nat.mul_comm s K] using row_balance_scale s row }

theorem rowAtProduct_actions (row : Row r i K) (s : Nat) :
    (rowAtProduct row s).actions = scaleActions s row.actions := rfl

theorem rowAtProduct_resets (row : Row r i K) (s : Nat) :
    (rowAtProduct row s).Z = s * row.Z := rfl

theorem rowAtProduct_dimension (row : Row r i K) (s : Nat) :
    (rowAtProduct row s).dimension = row.dimension ^ s := by
  simpa [Row.dimension, rowAtProduct_actions] using actions_dimension_scale s row.actions

/-- Top and lower rows meet at the product of their independently chosen scales. -/
def synchronizeFamily (top : Row (n + 2) 1 Ktop) (lower : LowerRows Klower n) :
    Family n (Ktop * Klower) :=
  ⟨rowAtProduct top Klower, scaleLowerRows Ktop lower⟩

theorem synchronizeFamily_dimension (top : Row (n + 2) 1 Ktop)
    (lower : LowerRows Klower n) :
    (synchronizeFamily top lower).dimension =
      top.dimension ^ Klower * lower.dimension ^ Ktop := by
  simp [synchronizeFamily, Family.dimension, rowAtProduct_dimension, lower_dimension_scale]

theorem synchronizeFamily_triplings (top : Row (n + 2) 1 Ktop)
    (lower : LowerRows Klower n) :
    (synchronizeFamily top lower).triplings =
      Klower * top.Z + Ktop * lower.triplings := by
  simp [synchronizeFamily, Family.triplings, rowAtProduct_resets, lower_triplings_scale]

/-- Independent positive-scale rows at state two give all lower rows at one
positive scale. The empty lower family uses scale one. -/
theorem exists_lowerRows
    (H : ∀ r : Nat, 2 ≤ r → ∃ K : Nat, 0 < K ∧ Nonempty (Row r 2 K))
    (n : Nat) : ∃ K : Nat, 0 < K ∧ Nonempty (LowerRows K n) := by
  induction n with
  | zero => exact ⟨1, Nat.zero_lt_one, ⟨.nil⟩⟩
  | succ n ih =>
    obtain ⟨Ktail, htail, ⟨tail⟩⟩ := ih
    obtain ⟨Krow, hrow, ⟨row⟩⟩ := H (n + 2) (by omega)
    exact ⟨Krow * Ktail, Nat.mul_pos hrow htail,
      ⟨.cons (rowAtProduct row Ktail) (scaleLowerRows Krow tail)⟩⟩

/-- Actual rows at separate positive scales suffice to construct an actual
family. Its common scale and every row's boundary proof are derived. -/
theorem exists_family
    (H : ∀ r : Nat, 2 ≤ r → ∀ i : Nat, 1 ≤ i → i < 3 * r →
      ∃ K : Nat, 0 < K ∧ Nonempty (Row r i K))
    (n : Nat) : ∃ K : Nat, 0 < K ∧ Nonempty (Family n K) := by
  obtain ⟨Klower, hlower, ⟨lower⟩⟩ := exists_lowerRows
    (fun r hr => H r hr 2 (by omega) (by omega)) n
  obtain ⟨Ktop, htop, ⟨top⟩⟩ := H (n + 2) (by omega) 1 (by omega) (by omega)
  exact ⟨Ktop * Klower, Nat.mul_pos htop hlower, ⟨synchronizeFamily top lower⟩⟩

end MatrixDimensionAudit.FamilySynchronizationBridge
