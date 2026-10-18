import formalization.AllRowProfile

/-!
Exact natural scaling of actual population-expanded row families. All children
at each action stay in one histogram. No asymptotic sector-count lower bound
or exponent conclusion is assumed or asserted.
-/
namespace MatrixDimensionAudit.FamilyScalingBridge
open WeightedSector GeneralFlow GeneralRowSector AllRowProfile

/-- Multiply every child population of an action by the same natural scale. -/
def scaleAction (s : Nat) (a : Action r) : Action r :=
  { x := a.x, h := a.h, x_lower := a.x_lower, x_upper := a.x_upper,
    h_lower := a.h_lower, h_upper := a.h_upper,
    population := fun y => s * a.population y }

theorem children_scale (s : Nat) (a : Action r) :
    (scaleAction s a).children = a.children := rfl

/-- Every supported output count scales, without splitting its histogram. -/
theorem output_count_scale (s : Nat) (a : Action r) (y : Nat) :
    (scaleAction s a).output.count y = s * a.output.count y := by
  simp only [Action.output, populationWord_count _ _ a.children_nodup, children_scale]
  split <;> simp [scaleAction]

theorem width_scale (s : Nat) (a : Action r) :
    (scaleAction s a).width = s * a.width := by
  simpa [Action.width, scaleAction, Action.children, List.map_map, Function.comp_def]
    using sum_mul_left s (a.children.map a.population)

theorem dimension_scale (s : Nat) (a : Action r) :
    (scaleAction s a).dimension = a.dimension ^ s := by
  rw [Action.dimension, width_scale, Nat.mul_comm s, Nat.pow_mul]
  rfl

def scaleActions (s : Nat) (actions : List (Action r)) : List (Action r) :=
  actions.map (scaleAction s)

private theorem replicate_count_scale (s n a v : Nat) :
    (List.replicate (s * n) a).count v = s * (List.replicate n a).count v := by
  simp only [List.count_replicate]
  split <;> simp

theorem source_count_scale (s : Nat) (actions : List (Action r)) (v : Nat) :
    ((allEdges (scaleActions s actions)).map Edge.src).count v =
      s * ((allEdges actions).map Edge.src).count v := by
  induction actions with
  | nil => simp [scaleActions, allEdges]
  | cons a tail ih =>
    simp only [scaleActions, List.map_cons, allEdges, List.flatMap_cons,
      List.map_append, List.count_append] at ih ⊢
    rw [(scaleAction s a).sourceWord, a.sourceWord]
    simp only [Action.input, width_scale, show (scaleAction s a).x = a.x from rfl]
    rw [replicate_count_scale, ih, Nat.mul_add]

theorem target_count_scale (s : Nat) (actions : List (Action r)) (v : Nat) :
    ((allEdges (scaleActions s actions)).map Edge.dst).count v =
      s * ((allEdges actions).map Edge.dst).count v := by
  induction actions with
  | nil => simp [scaleActions, allEdges]
  | cons a tail ih =>
    simp only [scaleActions, List.map_cons, allEdges, List.flatMap_cons,
      List.map_append, List.count_append] at ih ⊢
    rw [(scaleAction s a).targetWord, a.targetWord, output_count_scale, ih, Nat.mul_add]

theorem actions_dimension_scale (s : Nat) (actions : List (Action r)) :
    totalDimension (scaleActions s actions) = totalDimension actions ^ s := by
  induction actions with
  | nil => simp [totalDimension, scaleActions]
  | cons a tail ih =>
    simpa [totalDimension, scaleActions, dimension_scale, Nat.mul_pow] using
      congrArg (fun x => a.dimension ^ s * x) ih

/-- Conservation is derived at the scaled injection/reset counts. -/
theorem row_balance_scale (s : Nat) (row : Row r i K) :
    Balanced (List.replicate (s * K) i ++ List.replicate (s * row.Z) 1)
      (List.replicate (s * K) 0 ++ List.replicate (s * row.Z) (3 * r))
      (allEdges (scaleActions s row.actions)) := by
  apply balanced_iff_counts.mpr
  intro v
  have h := (balanced_iff_counts.mp row.balance) v
  rw [source_count_scale, target_count_scale]
  simp only [List.count_append] at h ⊢
  rw [replicate_count_scale, replicate_count_scale, replicate_count_scale,
    replicate_count_scale]
  simpa only [Nat.mul_add] using congrArg (fun x => s * x) h

/-- Scale an actual row, deriving its new boundary proof. Zero is allowed. -/
def scaleRow (s : Nat) (row : Row r i K) : Row r i (s * K) :=
  { actions := scaleActions s row.actions, Z := s * row.Z,
    balance := row_balance_scale s row }

theorem row_dimension_scale (s : Nat) (row : Row r i K) :
    (scaleRow s row).dimension = row.dimension ^ s :=
  actions_dimension_scale s row.actions

def scaleLowerRows (s : Nat) : {n : Nat} → LowerRows K n → LowerRows (s * K) n
  | _, .nil => .nil
  | _, .cons row tail => .cons (scaleRow s row) (scaleLowerRows s tail)

theorem lower_dimension_scale (s : Nat) (rows : LowerRows K n) :
    (scaleLowerRows s rows).dimension = rows.dimension ^ s := by
  induction rows with
  | nil => simp [scaleLowerRows, LowerRows.dimension]
  | cons row tail ih =>
    simpa [scaleLowerRows, LowerRows.dimension, row_dimension_scale, Nat.mul_pow] using
      congrArg (fun x => row.dimension ^ s * x) ih

theorem lower_triplings_scale (s : Nat) (rows : LowerRows K n) :
    (scaleLowerRows s rows).triplings = s * rows.triplings := by
  induction rows with
  | nil => simp [scaleLowerRows, LowerRows.triplings]
  | cons row tail ih => simp [scaleLowerRows, LowerRows.triplings, scaleRow, ih, Nat.mul_add]

/-- A concrete actual family at every multiple of the original common K. -/
def scaleFamily (s : Nat) (family : Family n K) : Family n (s * K) :=
  ⟨scaleRow s family.top, scaleLowerRows s family.lower⟩

theorem family_dimension_scale (s : Nat) (family : Family n K) :
    (scaleFamily s family).dimension = family.dimension ^ s := by
  simp [scaleFamily, Family.dimension, row_dimension_scale, lower_dimension_scale, Nat.mul_pow]

theorem family_triplings_scale (s : Nat) (family : Family n K) :
    (scaleFamily s family).triplings = s * family.triplings := by
  simp [scaleFamily, Family.triplings, scaleRow, lower_triplings_scale, Nat.mul_add]

end MatrixDimensionAudit.FamilyScalingBridge
#print axioms MatrixDimensionAudit.FamilyScalingBridge.output_count_scale
#print axioms MatrixDimensionAudit.FamilyScalingBridge.row_balance_scale
#print axioms MatrixDimensionAudit.FamilyScalingBridge.family_dimension_scale
#print axioms MatrixDimensionAudit.FamilyScalingBridge.family_triplings_scale
