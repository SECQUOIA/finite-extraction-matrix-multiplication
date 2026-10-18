import formalization.AllRowProfile

/-!
A finite construction adapter from supported integer row circulations to the
actual row-action model. Occupation existence and circulation rounding are
not assumed to have been proved here.
-/
namespace MatrixDimensionAudit.IntegerRowConstruction

open WeightedSector GeneralFlow GeneralRowSector AllRowProfile

/-- One legal split site, before specifying any integer transition counts. -/
structure Site (r : Nat) where
  x : Nat
  h : Nat
  x_lower : 1 ≤ x
  x_upper : x < 3 * r
  h_lower : 1 ≤ h
  h_upper : h ≤ min x (3 * r - x)

/-- All outgoing counts at one site stay grouped into a single histogram. -/
def Site.action (site : Site r) (population : Nat → Nat) : Action r :=
  { x := site.x, h := site.h, x_lower := site.x_lower,
    x_upper := site.x_upper, h_lower := site.h_lower,
    h_upper := site.h_upper, population := population }

/-- A split graph recorded by site and child multiplicity, not by a chosen
list permutation or a desired count/profile inequality. -/
structure IntegerSplit (r : Nat) where
  site : Site r
  population : Nat → Nat

def IntegerSplit.action (split : IntegerSplit r) : Action r :=
  split.site.action split.population

/-- The explicit transition arcs, with their nonnegative integer multiplicities. -/
def IntegerSplit.transitions (split : IntegerSplit r) : List (Edge Nat) :=
  split.action.children.flatMap (fun y =>
    List.replicate (split.population y) ⟨split.site.x, y⟩)

def actions (splits : List (IntegerSplit r)) : List (Action r) :=
  splits.map IntegerSplit.action

def transitions (splits : List (IntegerSplit r)) : List (Edge Nat) :=
  splits.flatMap IntegerSplit.transitions

theorem IntegerSplit.transitions_eq (split : IntegerSplit r) :
    split.transitions = split.action.edges := by
  simp [IntegerSplit.transitions, Action.edges, Action.output, populationWord,
    List.map_flatMap, List.map_replicate, IntegerSplit.action, Site.action]

theorem transitions_eq (splits : List (IntegerSplit r)) :
    transitions splits = allEdges (actions splits) := by
  induction splits with
  | nil => rfl
  | cons split tail ih =>
    simp only [transitions, List.flatMap_cons, actions, List.map_cons, allEdges] at ih ⊢
    rw [split.transitions_eq, ih]

/-- Add the reset arcs and the fixed return arcs to close the row graph. -/
def closedGraph (splits : List (IntegerSplit r)) (i K Z : Nat) : List (Edge Nat) :=
  transitions splits ++ List.replicate Z ⟨3 * r, 1⟩ ++ List.replicate K ⟨0, i⟩

/-- The incoming and outgoing multiplicities agree at every vertex. This is
an ordinary integer-circulation equation, including loops and opposing arcs. -/
def IsCirculation (edges : List (Edge Nat)) : Prop :=
  ∀ v, (edges.map Edge.dst).count v = (edges.map Edge.src).count v

/-- Removing fixed return arcs and reset arcs gives exactly the boundary
balance required by the actual row model. -/
theorem balance_of_circulation (splits : List (IntegerSplit r)) (i K Z : Nat)
    (closed : IsCirculation (closedGraph splits i K Z)) :
    Balanced (List.replicate K i ++ List.replicate Z 1)
      (List.replicate K 0 ++ List.replicate Z (3 * r)) (allEdges (actions splits)) := by
  apply balanced_iff_counts.mpr
  intro v
  have h := closed v
  simp only [closedGraph, List.map_append, List.map_replicate, List.count_append,
    ] at h
  rw [transitions_eq] at h
  simp only [List.count_append]
  omega

/-- Construct an actual row from integer graph data; the Row.balance field
is derived, rather than an input to the constructor. -/
def rowOfCirculation (splits : List (IntegerSplit r)) (i K Z : Nat)
    (closed : IsCirculation (closedGraph splits i K Z)) : Row r i K :=
  { actions := actions splits, Z := Z,
    balance := balance_of_circulation splits i K Z closed }

/-- The constructor retains each site's full child histogram. -/
theorem action_output_count (split : IntegerSplit r) (y : Nat) :
    split.action.output.count y =
      if y ∈ split.action.children then split.population y else 0 := by
  exact populationWord_count _ _ split.action.children_nodup y

/-- The manuscript's maximal width is legal at every interior state. -/
def maximalSite (r x : Nat) (hx : 1 ≤ x) (hxr : x < 3 * r) : Site r :=
  { x := x, h := min x (3 * r - x), x_lower := hx, x_upper := hxr,
    h_lower := by omega, h_upper := Nat.le_refl _ }

/-- The exact K=15 top-row-two occupation table, with all child counts
kept in three grouped splits. States three and five are inactive. -/
def rowTwoSplits : List (IntegerSplit 2) :=
  [ ⟨maximalSite 2 1 (by decide) (by decide), fun y =>
      match y with | 0 => 9 | 2 => 21 | _ => 0⟩,
    ⟨maximalSite 2 2 (by decide) (by decide), fun y =>
      match y with | 0 => 6 | 2 => 14 | 4 => 22 | _ => 0⟩,
    ⟨maximalSite 2 4 (by decide) (by decide), fun y =>
      match y with | 2 => 7 | 4 => 11 | 6 => 15 | _ => 0⟩ ]

/-- The explicit table is a circulation, including its self-loops, fifteen
resets, and fifteen returns. No rounded-row balance is assumed. -/
theorem rowTwo_closed : IsCirculation (closedGraph rowTwoSplits 1 15 15) := by
  have hd : (closedGraph rowTwoSplits 1 15 15).map Edge.dst =
      List.replicate 21 2 ++ List.replicate 9 0 ++ List.replicate 22 4 ++
      List.replicate 14 2 ++ List.replicate 6 0 ++ List.replicate 15 6 ++
      List.replicate 11 4 ++ List.replicate 7 2 ++ List.replicate 30 1 := by decide
  have hs : (closedGraph rowTwoSplits 1 15 15).map Edge.src =
      List.replicate 30 1 ++ List.replicate 42 2 ++ List.replicate 33 4 ++
      List.replicate 15 6 ++ List.replicate 15 0 := by decide
  intro v
  rw [hd, hs]
  simp only [List.count_append, List.count_replicate]
  split <;> split <;> split <;> split <;> split <;> omega

/-- A concrete actual row, usable by the existing all-row/tensor interfaces. -/
def exactRowTwo : Row 2 1 15 := rowOfCirculation rowTwoSplits 1 15 15 rowTwo_closed

/-- The adapter preserves the source dimension of the exact table. -/
theorem exactRowTwo_dimension : exactRowTwo.dimension = 2 ^ 30 * 3 ^ 75 := by
  decide

/-- The same concrete row is a one-row actual Family. -/
def exactFamilyTwo : Family 0 15 := ⟨exactRowTwo, .nil⟩

end MatrixDimensionAudit.IntegerRowConstruction

#print axioms MatrixDimensionAudit.IntegerRowConstruction.balance_of_circulation
#print axioms MatrixDimensionAudit.IntegerRowConstruction.action_output_count
#print axioms MatrixDimensionAudit.IntegerRowConstruction.rowTwo_closed
#print axioms MatrixDimensionAudit.IntegerRowConstruction.exactRowTwo_dimension
