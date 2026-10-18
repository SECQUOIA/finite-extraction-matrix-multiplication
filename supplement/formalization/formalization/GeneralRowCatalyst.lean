import formalization.AllRowProfile

/-!
Leg-dimension arithmetic for the actual population-expanded consumed-factor
ledger at every row. The full-flattening tensor interpretation is a separate
obligation: no tensor-rank or supplied-decomposition equality is asserted here.
-/

namespace MatrixDimensionAudit
namespace GeneralRowCatalyst

open GeneralFlow GeneralRowSector AllRowProfile

/-- Leg dimension of a consumed interior split factor with b=r-1+x. -/
def splitLeg (r x : Nat) : Nat := r * (r - 1 + x) * (2 * r - 2 + x)

/-- The smallest interior split-factor leg dimension. -/
def sourceLeg (r : Nat) : Nat := r * r * (2 * r - 1)

/-- Leg dimension of the consumed reset factor, at b=4r-1. -/
def resetLeg (r : Nat) : Nat := r * (4 * r - 1) * (5 * r - 2)

/-- One parent per consumed copy, including every child population. -/
def parents (actions : List (Action r)) : List Nat := (allEdges actions).map Edge.src

theorem parents_interior (actions : List (Action r)) (x : Nat) (hx : x ∈ parents actions) :
    1 ≤ x ∧ x < 3 * r := by
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
  obtain ⟨a, ha, he⟩ := List.mem_flatMap.mp he
  obtain ⟨child, hc, he⟩ := List.mem_map.mp he
  cases he
  exact ⟨a.x_lower, a.x_upper⟩

theorem splitLeg_floor (r x : Nat) (hr : 2 ≤ r) (hx : 1 ≤ x) :
    sourceLeg r ≤ splitLeg r x := by
  have h₁ : r ≤ r - 1 + x := by omega
  have h₂ : 2 * r - 1 ≤ 2 * r - 2 + x := by omega
  exact Nat.mul_le_mul (Nat.mul_le_mul_left r h₁) h₂

theorem sourceLeg_floor (r : Nat) (hr : 2 ≤ r) : 12 ≤ sourceLeg r := by
  exact Nat.mul_le_mul (Nat.mul_le_mul hr hr) (by omega : 3 ≤ 2 * r - 1)

theorem resetLeg_floor (r : Nat) (hr : 2 ≤ r) : 112 ≤ resetLeg r := by
  exact Nat.mul_le_mul (Nat.mul_le_mul hr (by omega : 7 ≤ 4 * r - 1))
    (by omega : 8 ≤ 5 * r - 2)

theorem resetPair_floor (r : Nat) (hr : 2 ≤ r) :
    1344 ≤ sourceLeg r * resetLeg r :=
  Nat.mul_le_mul (sourceLeg_floor r hr) (resetLeg_floor r hr)

theorem removeInjected_subset (K : Nat) (word : List Nat) :
    removeInjected K word ⊆ word := by
  induction K generalizing word with
  | zero => exact fun _ h => h
  | succ K ih =>
    exact fun _ h => List.mem_of_mem_erase (ih (word.erase 1) h)

/-- Every top boundary source at state 1 must be consumed as a split parent. -/
theorem top_parent_count (row : Row r 1 K) (hr : 2 ≤ r) :
    K + row.Z ≤ (parents row.actions).count 1 := by
  have h := (balanced_iff_counts.mp row.balance) 1
  have hne : 3 * r ≠ 1 := by omega
  simp [List.count_append, List.count_replicate, hne] at h
  change K + row.Z ≤ (allEdges row.actions |>.map Edge.src).count 1
  omega

/-- Removing the K external source copies leaves at least Z catalyst copies. -/
theorem top_residual_count (row : Row r 1 K) (hr : 2 ≤ r) :
    row.Z ≤ (removeInjected K (parents row.actions)).count 1 := by
  have hp := top_parent_count row hr
  have ledger := removeInjected_ledger (parents row.actions) K (by omega)
  have h := ledger.count_eq 1
  simp only [List.count_append, List.count_replicate, beq_self_eq_true, ite_true] at h
  omega

theorem count_one_add_count_two_le_length (word : List Nat) :
    word.count 1 + word.count 2 ≤ word.length := by
  induction word with
  | nil => simp
  | cons x tail ih =>
    by_cases h₁ : x = 1
    · subst x
      simp only [List.count_cons, beq_self_eq_true, reduceIte,
        show (1 == 2) = false from rfl, Bool.false_eq_true, List.length_cons]
      omega
    · by_cases h₂ : x = 2
      · subst x; simpa [Nat.add_assoc] using Nat.succ_le_succ ih
      · simp [h₁, h₂]
        omega

/-- Lower rows keep all their consumed parents, including their K state-2 inputs. -/
theorem lower_parent_length (row : Row r 2 K) (hr : 2 ≤ r) :
    K + row.Z ≤ (parents row.actions).length := by
  have h₁ := (balanced_iff_counts.mp row.balance) 1
  have h₂ := (balanced_iff_counts.mp row.balance) 2
  have ne₁ : 3 * r ≠ 1 := by omega
  have ne₂ : 3 * r ≠ 2 := by omega
  simp [List.count_append, List.count_replicate, ne₁, ne₂] at h₁ h₂
  have bound := count_one_add_count_two_le_length (parents row.actions)
  change _ ≤ (allEdges row.actions |>.map Edge.src).length
  dsimp [parents] at bound
  omega

/-- A factor-by-factor product bound on the actual consumed list. -/
theorem split_product_floor (r : Nat) (hr : 2 ≤ r) (word : List Nat)
    (valid : ∀ x ∈ word, 1 ≤ x) :
    sourceLeg r ^ word.length ≤ (word.map (splitLeg r)).prod := by
  induction word with
  | nil => exact Nat.le_refl _
  | cons x tail ih =>
    have hf := splitLeg_floor r x hr (valid x (by simp))
    have ht := ih (by intro y hy; exact valid y (by simp [hy]))
    simpa [Nat.pow_succ, Nat.mul_comm] using Nat.mul_le_mul hf ht

/-- Top-row ledger removes only the K externally supplied state-1 factors. -/
def topCharge (row : Row r 1 K) : Nat :=
  ((removeInjected K (parents row.actions)).map (splitLeg r)).prod * resetLeg r ^ row.Z

/-- Lower-row ledger includes every consumed factor; no external copy is removed. -/
def lowerCharge (row : Row r 2 K) : Nat :=
  ((parents row.actions).map (splitLeg r)).prod * resetLeg r ^ row.Z

theorem top_charge_floor (row : Row r 1 K) (hr : 2 ≤ r) :
    (sourceLeg r * resetLeg r) ^ row.Z ≤ topCharge row := by
  have len : row.Z ≤ (removeInjected K (parents row.actions)).length :=
    Nat.le_trans (top_residual_count row hr) List.count_le_length
  have prod := split_product_floor r hr (removeInjected K (parents row.actions)) (by
    intro x hx
    exact (parents_interior row.actions x (removeInjected_subset K _ hx)).1)
  have pow := Nat.pow_le_pow_right (by have := sourceLeg_floor r hr; omega : 0 < sourceLeg r) len
  simpa [topCharge, Nat.mul_pow] using
    Nat.mul_le_mul_right (resetLeg r ^ row.Z) (Nat.le_trans pow prod)

theorem lower_charge_floor (row : Row r 2 K) (hr : 2 ≤ r) :
    sourceLeg r ^ K * (sourceLeg r * resetLeg r) ^ row.Z ≤ lowerCharge row := by
  have prod := split_product_floor r hr (parents row.actions) (by
    intro x hx; exact (parents_interior row.actions x hx).1)
  have pow := Nat.pow_le_pow_right (by have := sourceLeg_floor r hr; omega : 0 < sourceLeg r)
    (lower_parent_length row hr)
  simpa [lowerCharge, Nat.pow_add, Nat.mul_pow, Nat.mul_assoc] using
    Nat.mul_le_mul_right (resetLeg r ^ row.Z) (Nat.le_trans pow prod)

/-- Product of g_r for precisely the lower rows r=2,...,n+1. -/
def lowerSourceProduct : Nat → Nat
  | 0 => 1
  | n + 1 => sourceLeg (n + 2) * lowerSourceProduct n

theorem lowerSourceProduct_eq_product (n : Nat) :
    lowerSourceProduct n = ((List.range n).map (fun j => sourceLeg (j + 2))).prod := by
  induction n with
  | zero => rfl
  | succ n ih => simp [lowerSourceProduct, List.range_succ, ih, Nat.mul_comm]

def lowerRowsCharge : {n : Nat} → LowerRows K n → Nat
  | _, .nil => 1
  | _, .cons row tail => lowerCharge row * lowerRowsCharge tail

theorem lowerRows_charge_floor (rows : LowerRows K n) :
    lowerSourceProduct n ^ K * 1344 ^ rows.triplings ≤ lowerRowsCharge rows := by
  induction rows with
  | nil => simp [lowerSourceProduct, LowerRows.triplings, lowerRowsCharge]
  | @cons n row tail ih =>
    have hp := Nat.pow_le_pow_left (resetPair_floor (n + 2) (by omega)) row.Z
    have hr := Nat.le_trans (Nat.mul_le_mul_left (sourceLeg (n + 2) ^ K) hp)
      (lower_charge_floor row (by omega))
    simpa [lowerSourceProduct, LowerRows.triplings, lowerRowsCharge, Nat.mul_pow,
      Nat.pow_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using Nat.mul_le_mul hr ih

/-- Product of the actual top residual and all lower consumed-factor ledgers. -/
def familyCharge (family : Family n K) : Nat :=
  topCharge family.top * lowerRowsCharge family.lower

/-- For every a=n+2, the consumed-factor leg product is at least Q_a^K*1344^sumZ. -/
theorem family_charge_floor (family : Family n K) :
    lowerSourceProduct n ^ K * 1344 ^ family.triplings ≤ familyCharge family := by
  have ht := Nat.le_trans
    (Nat.pow_le_pow_left (resetPair_floor (n + 2) (by omega)) family.top.Z)
    (top_charge_floor family.top (by omega))
  simpa [familyCharge, Family.triplings, Nat.pow_add, Nat.mul_assoc,
    Nat.mul_comm, Nat.mul_left_comm] using Nat.mul_le_mul ht (lowerRows_charge_floor family.lower)

end GeneralRowCatalyst
end MatrixDimensionAudit

#print axioms MatrixDimensionAudit.GeneralRowCatalyst.parents_interior
#print axioms MatrixDimensionAudit.GeneralRowCatalyst.top_residual_count
#print axioms MatrixDimensionAudit.GeneralRowCatalyst.lower_parent_length
#print axioms MatrixDimensionAudit.GeneralRowCatalyst.split_product_floor
#print axioms MatrixDimensionAudit.GeneralRowCatalyst.top_charge_floor
#print axioms MatrixDimensionAudit.GeneralRowCatalyst.lower_charge_floor
#print axioms MatrixDimensionAudit.GeneralRowCatalyst.lowerSourceProduct_eq_product
#print axioms MatrixDimensionAudit.GeneralRowCatalyst.family_charge_floor
