import formalization.AllRowProfile

namespace MatrixDimensionAudit
namespace GeneralRowDimension

open WeightedSector GeneralFlow GeneralRowSector AllRowProfile

variable {r : Nat}

private theorem product_bound (word : List Nat) (p : Nat → Nat) (bound : Nat)
    (edgeBound : ∀ y ∈ word, p y ≤ bound) : wordWeight p word ≤ bound ^ word.length := by
  induction word with
  | nil => exact Nat.le_refl _
  | cons y tail ih =>
    have hy := edgeBound y (by simp)
    have ht := ih (by intro z hz; exact edgeBound z (by simp [hz]))
    simpa [wordWeight_cons, Nat.pow_succ, Nat.mul_comm] using Nat.mul_le_mul hy ht

/-- The actual population-expanded output pays the existing action dimension. -/
theorem Action.potential_bound (a : Action r) (p : Nat → Nat)
    (edgeBound : ∀ y ∈ a.children, p y ≤ (a.h + 1) * p a.x) :
    wordWeight p a.output ≤ a.dimension * wordWeight p a.input := by
  have h := product_bound a.output p ((a.h + 1) * p a.x) (by
    intro y hy
    obtain ⟨symbol, hs, hy⟩ := List.mem_flatMap.mp hy
    have he := List.eq_of_mem_replicate hy
    exact he ▸ edgeBound symbol hs)
  simpa [GeneralRowSector.Action.output, populationWord_length,
    GeneralRowSector.Action.width, GeneralRowSector.Action.dimension,
    GeneralRowSector.Action.input, wordWeight_replicate, Nat.mul_pow] using h

private theorem weight_append (p : Nat → Nat) (left right : List Nat) :
    wordWeight p (left ++ right) = wordWeight p left * wordWeight p right := by
  simp [wordWeight, List.map_append, List.prod_append]

/-- Width labels remain attached to their actions when the edge bounds multiply. -/
theorem product_potential_bound (actions : List (Action r)) (p : Nat → Nat)
    (edgeBound : ∀ a ∈ actions, ∀ y ∈ a.children, p y ≤ (a.h + 1) * p a.x) :
    wordWeight p ((allEdges actions).map Edge.dst) ≤
      totalDimension actions * wordWeight p ((allEdges actions).map Edge.src) := by
  induction actions with
  | nil => exact Nat.le_refl _
  | cons a tail ih =>
    have ha := Action.potential_bound a p (edgeBound a (by simp))
    have ht := ih (by intro b hb; exact edgeBound b (by simp [hb]))
    simpa [allEdges, List.flatMap_cons, List.map_append, weight_append,
      a.sourceWord, a.targetWord, totalDimension,
      Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using Nat.mul_le_mul ha ht

/-- Multiplicative flow duality for the actual action dimensions. -/
theorem boundary_potential_bound (actions : List (Action r)) (p : Nat → Nat)
    (sources sinks : List Nat) (balance : Balanced sources sinks (allEdges actions))
    (positive : ∀ x, 0 < p x)
    (edgeBound : ∀ a ∈ actions, ∀ y ∈ a.children, p y ≤ (a.h + 1) * p a.x) :
    wordWeight p sinks ≤ totalDimension actions * wordWeight p sources := by
  have he := product_potential_bound actions p edgeBound
  have hb := multiplicative_balance balance p
  change wordWeight p sources * wordWeight p ((allEdges actions).map Edge.dst) =
    wordWeight p sinks * wordWeight p ((allEdges actions).map Edge.src) at hb
  have hs : 0 < wordWeight p ((allEdges actions).map Edge.src) :=
    natProduct_pos _ p (by intro x _; exact positive x)
  apply Nat.le_of_mul_le_mul_right (c := wordWeight p ((allEdges actions).map Edge.src)) _ hs
  rw [← hb]
  simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
    Nat.mul_le_mul_left (wordWeight p sources) he

/-- Reset-neutral potential that charges 2 per top injection and 3 per lower injection. -/
def branchPotential (r x : Nat) : Nat :=
  if x = 0 then 6 else if x = 1 ∨ x = 3 * r then 3 else 2

theorem branchPotential_pos (r x : Nat) : 0 < branchPotential r x := by
  unfold branchPotential
  repeat first | split | omega

theorem branch_local (r x h t : Nat) (hx : 1 ≤ x) (hxr : x < 3 * r)
    (hh : 1 ≤ h) (hhx : h ≤ x) (ht : t ≤ h) :
    branchPotential r (x + h - 2 * t) ≤ (h + 1) * branchPotential r x := by
  unfold branchPotential
  repeat first | split | omega

/-- Linear potential that retains the row-dependent reset cost. -/
def resetPotential (x : Nat) : Nat := if x = 0 then 2 else x

theorem resetPotential_pos (x : Nat) : 0 < resetPotential x := by
  unfold resetPotential
  repeat first | split | omega

theorem reset_local (x h t : Nat) (hx : 1 ≤ x) (hh : 1 ≤ h) :
    resetPotential (x + h - 2 * t) ≤ (h + 1) * resetPotential x := by
  have hx0 : x ≠ 0 := by omega
  have hm : h ≤ h * x := by simpa using Nat.mul_le_mul_left h hx
  have hd : 2 ≤ (h + 1) * x := by
    have := Nat.mul_le_mul (show 2 ≤ h + 1 by omega) hx
    simpa using this
  simp only [resetPotential, hx0, ↓reduceIte, Nat.add_mul, Nat.one_mul]
  split <;> omega

private theorem child_witness (a : Action r) (child : Nat) (hc : child ∈ a.children) :
    ∃ t, t ≤ a.h ∧ child = a.x + a.h - 2 * t := by
  obtain ⟨t, ht, heq⟩ := List.mem_map.mp hc
  exact ⟨t, by simpa only [List.mem_range, Nat.lt_succ_iff] using ht, heq.symm⟩

theorem branch_action_bound (a : Action r) (child : Nat) (hc : child ∈ a.children) :
    branchPotential r child ≤ (a.h + 1) * branchPotential r a.x := by
  obtain ⟨t, ht, rfl⟩ := child_witness a child hc
  exact branch_local r a.x a.h t a.x_lower a.x_upper a.h_lower
    (Nat.le_trans a.h_upper (Nat.min_le_left _ _)) ht

theorem reset_action_bound (a : Action r) (child : Nat) (hc : child ∈ a.children) :
    resetPotential child ≤ (a.h + 1) * resetPotential a.x := by
  obtain ⟨t, ht, rfl⟩ := child_witness a child hc
  exact reset_local a.x a.h t a.x_lower a.h_lower


private theorem branch_values (r : Nat) (hr : 2 ≤ r) :
    branchPotential r 0 = 6 ∧ branchPotential r 1 = 3 ∧
    branchPotential r 2 = 2 ∧ branchPotential r (3 * r) = 3 := by
  simp [branchPotential, show 2 ≠ 3 * r by omega, show 3 * r ≠ 0 by omega]

/-- The reset-neutral potential gives the exact injected-factor charge. -/
theorem row_branch_bound (row : Row r i K) (hr : 2 ≤ r) :
    6 ^ K ≤ row.dimension * branchPotential r i ^ K := by
  have h := boundary_potential_bound row.actions (branchPotential r) _ _ row.balance
    (branchPotential_pos r) (by intro a _ y hy; exact branch_action_bound a y hy)
  obtain ⟨h0, h1, h2, hend⟩ := branch_values r hr
  simp only [weight_append, wordWeight_replicate, h0, h1, hend] at h
  have h' : 6 ^ K * 3 ^ row.Z ≤
      (row.dimension * branchPotential r i ^ K) * 3 ^ row.Z := by
    simpa [Row.dimension, Nat.mul_assoc] using h
  exact Nat.le_of_mul_le_mul_right h' (Nat.pow_pos (by decide))

theorem top_branch_bound (row : Row r 1 K) (hr : 2 ≤ r) : 2 ^ K ≤ row.dimension := by
  have h := row_branch_bound row hr
  rw [(branch_values r hr).2.1, show 6 = 2 * 3 by decide, Nat.mul_pow] at h
  exact Nat.le_of_mul_le_mul_right h (Nat.pow_pos (by decide))

theorem lower_branch_bound (row : Row r 2 K) (hr : 2 ≤ r) : 3 ^ K ≤ row.dimension := by
  have h := row_branch_bound row hr
  rw [(branch_values r hr).2.2.1, show 6 = 3 * 2 by decide, Nat.mul_pow] at h
  exact Nat.le_of_mul_le_mul_right h (Nat.pow_pos (by decide))

/-- The linear potential gives the full row-dependent reset charge. -/
theorem row_reset_bound (row : Row r i K) (hr : 2 ≤ r) :
    2 ^ K * (3 * r) ^ row.Z ≤ row.dimension * resetPotential i ^ K := by
  have h := boundary_potential_bound row.actions resetPotential _ _ row.balance
    resetPotential_pos (by intro a _ y hy; exact reset_action_bound a y hy)
  have hr0 : 3 * r ≠ 0 := by omega
  simpa [weight_append, wordWeight_replicate, resetPotential, hr0, Row.dimension] using h

theorem top_reset_bound (row : Row r 1 K) (hr : 2 ≤ r) :
    2 ^ K * (3 * r) ^ row.Z ≤ row.dimension := by
  simpa [resetPotential] using row_reset_bound row hr

theorem lower_reset_bound (row : Row r 2 K) (hr : 2 ≤ r) :
    (3 * r) ^ row.Z ≤ row.dimension := by
  have h := row_reset_bound row hr
  have h' : (3 * r) ^ row.Z * 2 ^ K ≤ row.dimension * 2 ^ K := by
    simpa [resetPotential, Nat.mul_comm] using h
  exact Nat.le_of_mul_le_mul_right h' (Nat.pow_pos (by decide))

/-- Every lower row contributes a factor 3 per common injected occurrence. -/
theorem lower_branch_product (rows : LowerRows K n) :
    3 ^ (n * K) ≤ rows.dimension := by
  induction rows with
  | nil => simp [LowerRows.dimension]
  | @cons n row tail ih =>
    have h := Nat.mul_le_mul (lower_branch_bound row (by omega)) ih
    simpa [LowerRows.dimension, Nat.add_mul, Nat.mul_add, Nat.pow_add,
      Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h

/-- The smallest lower-row reset ratio is 6, attained at row two. -/
theorem lower_reset_product (rows : LowerRows K n) :
    6 ^ rows.triplings ≤ rows.dimension := by
  induction rows with
  | nil => exact Nat.le_refl _
  | @cons n row tail ih =>
    have hr := lower_reset_bound row (by omega)
    have hs : 6 ^ row.Z ≤ row.dimension :=
      Nat.le_trans (Nat.pow_le_pow_left (by omega : 6 ≤ 3 * (n + 2)) row.Z) hr
    simpa [LowerRows.dimension, LowerRows.triplings, Nat.pow_add] using
      Nat.mul_le_mul hs ih

/-- With top index a=n+2, every actual family pays at least (2*3^(a-2))^K. -/
theorem family_branch_baseline (family : Family n K) :
    (2 * 3 ^ n) ^ K ≤ family.dimension := by
  have h := Nat.mul_le_mul (top_branch_bound family.top (by omega))
    (lower_branch_product family.lower)
  simpa [Family.dimension, Nat.mul_pow, ← Nat.pow_mul] using h

/-- A second independent baseline retains every row's reset occurrences. -/
theorem family_reset_baseline (family : Family n K) :
    2 ^ K * 6 ^ family.triplings ≤ family.dimension := by
  have ht := top_reset_bound family.top (by omega)
  have hs : 2 ^ K * 6 ^ family.top.Z ≤ family.top.dimension :=
    Nat.le_trans (Nat.mul_le_mul_left (2 ^ K)
      (Nat.pow_le_pow_left (by omega : 6 ≤ 3 * (n + 2)) family.top.Z)) ht
  have h := Nat.mul_le_mul hs (lower_reset_product family.lower)
  simpa [Family.dimension, Family.triplings, Nat.pow_add, Nat.mul_assoc] using h

end GeneralRowDimension
end MatrixDimensionAudit

#print axioms MatrixDimensionAudit.GeneralRowDimension.branch_local
#print axioms MatrixDimensionAudit.GeneralRowDimension.reset_local
#print axioms MatrixDimensionAudit.GeneralRowDimension.top_branch_bound
#print axioms MatrixDimensionAudit.GeneralRowDimension.lower_branch_bound
#print axioms MatrixDimensionAudit.GeneralRowDimension.top_reset_bound
#print axioms MatrixDimensionAudit.GeneralRowDimension.lower_reset_bound
#print axioms MatrixDimensionAudit.GeneralRowDimension.family_branch_baseline
#print axioms MatrixDimensionAudit.GeneralRowDimension.family_reset_baseline
