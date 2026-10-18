import formalization.GeneralRowSector

namespace MatrixDimensionAudit
namespace AllRowProfile

open GeneralFlow GeneralRowSector

/-- Concrete actions and their exact boundary balance at one row. No count
inequality is part of this data. Populations include any type scale. -/
structure Row (r i K : Nat) where
  actions : List (Action r)
  Z : Nat
  balance : Balanced (List.replicate K i ++ List.replicate Z 1)
    (List.replicate K 0 ++ List.replicate Z (3 * r)) (allEdges actions)

def Row.count (row : Row r i K) : Nat := actualSectorCount row.actions row.Z

def Row.dimension (row : Row r i K) : Nat := totalDimension row.actions

theorem Row.sharp (row : Row r i K) (hr : 2 ≤ r) :
    row.count * (3 * r - 3) ^ K ≤ row.dimension * (3 * r - 3 + 2 * i) ^ K :=
  sharp_actual_total_count row.actions hr i K row.Z row.balance

theorem Row.coarse (row : Row r i K) :
    row.count ≤ row.dimension * 3 ^ row.Z :=
  coarse_actual_total_count row.actions row.Z

/-- Exactly n lower rows, numbered 2 through n+1. The common K is in
the type, so it cannot vary from one row to another. -/
inductive LowerRows (K : Nat) : Nat → Type where
  | nil : LowerRows K 0
  | cons {n : Nat} (row : Row (n + 2) 2 K) (tail : LowerRows K n) :
      LowerRows K (n + 1)

def LowerRows.count : {n : Nat} → LowerRows K n → Nat
  | _, .nil => 1
  | _, .cons row tail => row.count * tail.count

def LowerRows.dimension : {n : Nat} → LowerRows K n → Nat
  | _, .nil => 1
  | _, .cons row tail => row.dimension * tail.dimension

def LowerRows.triplings : {n : Nat} → LowerRows K n → Nat
  | _, .nil => 0
  | _, .cons row tail => row.Z + tail.triplings

/-- Product of 3r+1 over lower rows r=2,...,n+1. -/
def lowerNumerator : Nat → Nat
  | 0 => 1
  | n + 1 => (3 * (n + 2) + 1) * lowerNumerator n

/-- Product of 3r-3 over lower rows r=2,...,n+1. -/
def lowerDenominator : Nat → Nat
  | 0 => 1
  | n + 1 => (3 * (n + 2) - 3) * lowerDenominator n

theorem lowerNumerator_eq_product (n : Nat) :
    lowerNumerator n = ((List.range n).map (fun j => 3 * (j + 2) + 1)).prod := by
  induction n with
  | zero => rfl
  | succ n ih => simp [lowerNumerator, List.range_succ, ih, Nat.mul_comm]

theorem lowerDenominator_eq_product (n : Nat) :
    lowerDenominator n = ((List.range n).map (fun j => 3 * (j + 2) - 3)).prod := by
  induction n with
  | zero => rfl
  | succ n ih => simp [lowerDenominator, List.range_succ, ih, Nat.mul_comm]

theorem lowerNumerator_pos (n : Nat) : 0 < lowerNumerator n := by
  induction n with
  | zero => exact Nat.zero_lt_one
  | succ n ih => exact Nat.mul_pos (by omega) ih

theorem lowerDenominator_pos (n : Nat) : 0 < lowerDenominator n := by
  induction n with
  | zero => exact Nat.zero_lt_one
  | succ n ih => exact Nat.mul_pos (by omega) ih

/-- Multiplication of derived row inequalities, not a per-row hypothesis. -/
theorem LowerRows.sharp (rows : LowerRows K n) :
    rows.count * lowerDenominator n ^ K ≤ rows.dimension * lowerNumerator n ^ K := by
  induction rows with
  | nil => exact Nat.le_refl _
  | @cons n row tail ih =>
    have hr := row.sharp (by omega)
    have heq : 3 * (n + 2) - 3 + 2 * 2 = 3 * (n + 2) + 1 := by omega
    rw [heq] at hr
    have h := Nat.mul_le_mul hr ih
    simpa [LowerRows.count, LowerRows.dimension, lowerNumerator, lowerDenominator,
      Nat.mul_pow, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h

theorem LowerRows.coarse (rows : LowerRows K n) :
    rows.count ≤ rows.dimension * 3 ^ rows.triplings := by
  induction rows with
  | nil => exact Nat.le_refl _
  | cons row tail ih =>
    have h := Nat.mul_le_mul row.coarse ih
    simpa [LowerRows.count, LowerRows.dimension, LowerRows.triplings, Nat.pow_add,
      Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h

/-- The top row is a=n+2 and injects at state one; all n lower rows
inject at state two. The parameterization covers every a>=2. -/
structure Family (n K : Nat) where
  top : Row (n + 2) 1 K
  lower : LowerRows K n

/-- Actual product of all split-histogram and ternary tripling counts. -/
def Family.count (family : Family n K) : Nat := family.top.count * family.lower.count

def Family.dimension (family : Family n K) : Nat :=
  family.top.dimension * family.lower.dimension

def Family.triplings (family : Family n K) : Nat :=
  family.top.Z + family.lower.triplings

/-- Numerator of the row-count ratio, before the separate factor 2^K. -/
def rowNumerator (n : Nat) : Nat := (3 * (n + 2) - 1) * lowerNumerator n

/-- The unreduced denominator is kept as a product of natural factors. -/
def denominator (n : Nat) : Nat := (3 * (n + 2) - 3) * lowerDenominator n

/-- Numerator of the full gain profile: the 2 is the external gain factor. -/
def numerator (n : Nat) : Nat := 2 * rowNumerator n

theorem denominator_pos (n : Nat) : 0 < denominator n :=
  Nat.mul_pos (by omega) (lowerDenominator_pos n)

theorem numerator_pos (n : Nat) : 0 < numerator n :=
  Nat.mul_pos (by decide) (Nat.mul_pos (by omega) (lowerNumerator_pos n))

/-- The denominator is exactly the product of 3h for h=1,...,a-1,
where a=n+2. Natural subtraction has not removed a factor. -/
theorem denominator_eq_product (n : Nat) :
    denominator n = ((List.range (n + 1)).map (fun j => 3 * (j + 1))).prod := by
  have heq : (fun j : Nat => 3 * (j + 2) - 3) = (fun j => 3 * (j + 1)) := by
    funext j
    omega
  simp only [denominator, lowerDenominator_eq_product, heq, List.range_succ,
    List.map_append, List.prod_append, List.map_cons, List.prod_cons,
    List.map_nil, List.prod_nil, Nat.mul_one]
  have ht : 3 * (n + 2) - 3 = 3 * (n + 1) := by omega
  rw [ht, Nat.mul_comm]

/-- Exact natural cleared form of the diagonal product formula. Its
right-hand product includes the h=1 factor 4. -/
theorem numerator_eq_diagonal_product (n : Nat) :
    2 * numerator n = (3 * (n + 2) - 1) *
      ((List.range (n + 1)).map (fun j => 3 * (j + 1) + 1)).prod := by
  have hp : ((List.range (n + 1)).map (fun j => 3 * (j + 1) + 1)).prod =
      4 * lowerNumerator n := by
    rw [List.range_succ_eq_map]
    simp [List.map_map, Function.comp_def, Nat.succ_eq_add_one, Nat.add_assoc,
      lowerNumerator_eq_product]
  rw [hp]
  simp only [numerator, rowNumerator, ← Nat.mul_assoc]
  rw [show 2 * 2 = 4 from rfl, Nat.mul_comm 4]

/-- The two displayed product descriptions of F_a agree after clearing
their natural denominators; this theorem does not use rational division. -/
theorem cleared_diagonal_identity (n : Nat) :
    numerator n * (2 * ((List.range (n + 1)).map (fun j => 3 * (j + 1))).prod) =
      denominator n * ((3 * (n + 2) - 1) *
        ((List.range (n + 1)).map (fun j => 3 * (j + 1) + 1)).prod) := by
  rw [← denominator_eq_product, ← numerator_eq_diagonal_product]
  simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-- The stronger raw count bound has no external factor 2 in its numerator. -/
theorem Family.sharp_actual_count (family : Family n K) :
    family.count * denominator n ^ K ≤ family.dimension * rowNumerator n ^ K := by
  have ht := family.top.sharp (by omega)
  have heq : 3 * (n + 2) - 3 + 2 * 1 = 3 * (n + 2) - 1 := by omega
  rw [heq] at ht
  have h := Nat.mul_le_mul ht family.lower.sharp
  simpa [Family.count, Family.dimension, rowNumerator, denominator, Nat.mul_pow,
    Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h

/-- Exact cleared profile for the gain 2^K*M/D, where M is the actual
product of all row sectors. No row inequality or gain inequality is assumed. -/
theorem Family.sharp_actual_gain (family : Family n K) :
    (2 ^ K * family.count) * denominator n ^ K ≤
      family.dimension * numerator n ^ K := by
  have h := Nat.mul_le_mul_left (2 ^ K) family.sharp_actual_count
  simpa [numerator, Nat.mul_pow, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h

theorem Family.coarse_actual_count (family : Family n K) :
    family.count ≤ family.dimension * 3 ^ family.triplings := by
  have h := Nat.mul_le_mul family.top.coarse family.lower.coarse
  simpa [Family.count, Family.dimension, Family.triplings, Nat.pow_add,
    Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h

end AllRowProfile
end MatrixDimensionAudit

#print axioms MatrixDimensionAudit.AllRowProfile.lowerNumerator_eq_product
#print axioms MatrixDimensionAudit.AllRowProfile.lowerDenominator_eq_product
#print axioms MatrixDimensionAudit.AllRowProfile.cleared_diagonal_identity
#print axioms MatrixDimensionAudit.AllRowProfile.LowerRows.sharp
#print axioms MatrixDimensionAudit.AllRowProfile.Family.sharp_actual_count
#print axioms MatrixDimensionAudit.AllRowProfile.Family.sharp_actual_gain
#print axioms MatrixDimensionAudit.AllRowProfile.Family.coarse_actual_count
