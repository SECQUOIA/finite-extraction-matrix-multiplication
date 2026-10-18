import formalization.RationalOccupationBridge
import formalization.RationalCirculationBridge
import formalization.IntegerRowConstruction
import formalization.FamilyScalingBridge
import formalization.FamilySynchronizationBridge

/-! Actual grouped row actions from the manuscript's rational occupation walk. -/
namespace MatrixDimensionAudit.OccupationFamilyBridge
open scoped BigOperators
open WeightedSector GeneralFlow GeneralRowSector AllRowProfile
open RationalOccupationBridge
noncomputable section

variable (r : ℕ) (hr : 2 ≤ r) (start : Fin (3*r))

abbrev FlowEdge := Fin (3*r) × Fin (3*r+1)

def weight (e : FlowEdge r) : ℚ := transitionFlow (rowWalk r hr) start e.1 e.2

theorem weight_nonnegative (e : FlowEdge r) : 0 ≤ weight r hr start e :=
  transition_nonnegative (rowWalk r hr) start e.1 e.2

def scale : ℕ := RationalCirculationBridge.commonDenominator (weight r hr start)

theorem scale_pos : 0 < scale r hr start :=
  RationalCirculationBridge.commonDenominator_pos _

def counts (i : Fin (3*r)) (y : Fin (3*r+1)) : ℕ :=
  RationalCirculationBridge.integerCounts (weight r hr start) (i,y)

theorem counts_cast (i : Fin (3*r)) (y : Fin (3*r+1)) :
    (counts r hr start i y : ℚ) = (scale r hr start : ℚ) *
      occupation (rowWalk r hr) start i * rowProbability r hr i y := by
  simpa only [counts, scale, weight, transitionFlow, rowWalk, mul_assoc] using
    RationalCirculationBridge.integerCounts_cast (weight r hr start)
      (weight_nonnegative r hr start) (i,y)

/-- The reset state contributes a zero-width dummy action at state one.
All genuine interior states keep one complete child histogram. -/
def site (i : Fin (3*r)) : IntegerRowConstruction.Site r :=
  if hi : i.val+1 < 3*r then
    IntegerRowConstruction.maximalSite r (i.val+1) (by omega) hi
  else IntegerRowConstruction.maximalSite r 1 (by omega) (by omega)

def population (i : Fin (3*r)) (y : ℕ) : ℕ :=
  if _hi : i.val+1 < 3*r then
    if hy : y < 3*r+1 then counts r hr start i ⟨y,hy⟩ else 0
  else 0

def action (i : Fin (3*r)) : Action r :=
  (site r hr i).action (population r hr start i)

def rowActions : List (Action r) := List.ofFn (action r hr start)

/-- Exact rational population of every interior transition, with zero outside
its finite target interval. -/
theorem population_cast (i : Fin (3*r)) (y : ℕ) :
    (population r hr start i y : ℚ) =
      if _hi : i.val+1 < 3*r then
        if hy : y < 3*r+1 then (scale r hr start : ℚ) *
          occupation (rowWalk r hr) start i * rowProbability r hr i ⟨y,hy⟩ else 0
      else 0 := by
  unfold population
  split_ifs <;> first | exact counts_cast r hr start _ _ | rfl

theorem action_population (i : Fin (3*r)) :
    (action r hr start i).population = population r hr start i := rfl

theorem children_eq (i : Fin (3*r)) (hi : i.val+1 < 3*r) :
    (action r hr start i).children =
      (List.range (rowWidth r (i.val+1)+1)).map
        (fun t => i.val+1+rowWidth r (i.val+1)-2*t) := by
  simp [action, site, hi, IntegerRowConstruction.Site.action,
    IntegerRowConstruction.maximalSite, Action.children, rowWidth]

theorem rowProbability_zero_off_children (i : Fin (3*r)) (hi : i.val+1 < 3*r)
    (y : Fin (3*r+1)) (hy : y.val ∉ (action r hr start i).children) :
    rowProbability r hr i y = 0 := by
  apply rowProbability_off_children r hr i (by omega) y
  intro t he
  apply hy
  rw [children_eq r hr start i hi]
  apply List.mem_map.mpr
  refine ⟨t.val, List.mem_range.mpr t.isLt, ?_⟩
  exact congrArg Fin.val he.symm

theorem population_zero_off_children (i : Fin (3*r)) (y : ℕ)
    (hy : y ∉ (action r hr start i).children) : population r hr start i y = 0 := by
  by_cases hi : i.val+1 < 3*r
  · by_cases hyv : y < 3*r+1
    · have h := counts_cast r hr start i ⟨y,hyv⟩
      rw [rowProbability_zero_off_children r hr start i hi ⟨y,hyv⟩ hy, mul_zero] at h
      simpa [population, hi, hyv] using (show counts r hr start i ⟨y,hyv⟩ = 0 from by exact_mod_cast h)
    · simp [population, hi, hyv]
  · simp [population, hi]

theorem action_output_count (i : Fin (3*r)) (y : ℕ) :
    (action r hr start i).output.count y = population r hr start i y := by
  rw [Action.output, populationWord_count _ _ (action r hr start i).children_nodup]
  by_cases hy : y ∈ (action r hr start i).children
  · simp only [hy, ite_true, action_population]
  · simp only [hy, ite_false, action_population]
    exact (population_zero_off_children r hr start i y hy).symm

theorem action_width_eq_sum (i : Fin (3*r)) :
    (action r hr start i).width = ∑ y : Fin (3*r+1), population r hr start i y.val := by
  let a := action r hr start i
  have ho : ∀ y ∈ a.output, y < 3*r+1 := by
    intro y hy
    have hc : y ∈ a.children := by
      obtain ⟨c,hc,hyc⟩ := List.mem_flatMap.mp hy
      have hey := (List.mem_replicate.mp hyc).2
      simpa only [hey] using hc
    exact Nat.lt_succ_of_le (a.child_upper y hc)
  calc
    a.width = a.output.length := by simp [a, Action.output, populationWord_length, Action.width]
    _ = ∑ y : Fin (3*r+1), a.output.count y.val := by
      have helper : ∀ (l : List ℕ), (∀ y ∈ l, y < 3*r+1) →
          (∑ y : Fin (3*r+1), l.count y.val) = l.length := by
        intro l
        induction l with
        | nil => simp
        | cons x l ih =>
          intro h
          have hx := h x (by simp)
          have hl := ih (fun y hy => h y (by simp [hy]))
          simp only [List.count_cons, beq_iff_eq, Finset.sum_add_distrib, List.length_cons]
          rw [hl]
          have he : (∑ y : Fin (3*r+1), if x=y.val then 1 else 0) = 1 := by
            have hh : ∀ y : Fin (3*r+1), x=y.val ↔ (⟨x,hx⟩ : Fin (3*r+1))=y := by
              intro y; exact ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
            simp only [hh]
            simp
          rw [he]
      exact (helper a.output ho).symm
    _ = _ := by simp only [a, action_output_count]

theorem action_source_count (i : Fin (3*r)) (v : ℕ) :
    ((action r hr start i).edges.map Edge.src).count v =
      if i.val+1=v then (action r hr start i).width else 0 := by
  rw [Action.sourceWord]
  simp only [Action.input, List.count_replicate, beq_iff_eq]
  by_cases hi : i.val+1 < 3*r
  · simp [action, site, hi, IntegerRowConstruction.Site.action,
      IntegerRowConstruction.maximalSite]
  · have hz : (action r hr start i).width=0 := by
      rw [action_width_eq_sum]
      simp [population, hi]
    simp [hz]

theorem action_target_count (i : Fin (3*r)) (v : ℕ) :
    ((action r hr start i).edges.map Edge.dst).count v = population r hr start i v := by
  rw [Action.targetWord, action_output_count]

theorem actions_source_count (v : ℕ) :
    ((allEdges (rowActions r hr start)).map Edge.src).count v =
      ∑ i, if i.val+1=v then (action r hr start i).width else 0 := by
  have helper : ∀ (as : List (Action r)),
      ((allEdges as).map Edge.src).count v =
        (as.map (fun a => (a.edges.map Edge.src).count v)).sum := by
    intro as
    induction as with
    | nil => rfl
    | cons a as ih =>
      simp only [allEdges, List.flatMap_cons, List.map_append, List.count_append,
        List.map_cons, List.sum_cons]
      exact congrArg (fun z => _ + z) (show
        ((List.flatMap Action.edges as).map _).count v = _ from by
          simpa only [allEdges] using ih)
  rw [helper]
  simp [rowActions, List.map_ofFn, Fin.sum_ofFn, action_source_count]

theorem actions_target_count (v : ℕ) :
    ((allEdges (rowActions r hr start)).map Edge.dst).count v =
      ∑ i, population r hr start i v := by
  have helper : ∀ (as : List (Action r)),
      ((allEdges as).map Edge.dst).count v =
        (as.map (fun a => (a.edges.map Edge.dst).count v)).sum := by
    intro as
    induction as with
    | nil => rfl
    | cons a as ih =>
      simp only [allEdges, List.flatMap_cons, List.map_append, List.count_append,
        List.map_cons, List.sum_cons]
      exact congrArg (fun z => _ + z) (show
        ((List.flatMap Action.edges as).map _).count v = _ from by
          simpa only [allEdges] using ih)
  rw [helper]
  simp [rowActions, List.map_ofFn, Fin.sum_ofFn, action_target_count]

/-- Exact total mass of one grouped split. -/
theorem action_width_cast (i : Fin (3*r)) :
    ((action r hr start i).width : ℚ) =
      if i.val+1 < 3*r then (scale r hr start : ℚ) * occupation (rowWalk r hr) start i else 0 := by
  rw [action_width_eq_sum, Nat.cast_sum]
  by_cases hi : i.val+1 < 3*r
  · simp only [population_cast, dite_eq_left hi, dite_eq_left (Fin.isLt _), ite_eq_left hi]
    rw [← Finset.mul_sum, rowProbability_sum, mul_one]
  · simp [population, hi]

def resetIndex : Fin (3*r) := ⟨3*r-1, by omega⟩

def resetCount : ℕ := counts r hr start (resetIndex r hr) (rowOne r hr)

theorem resetIndex_val : (resetIndex r hr).val+1 = 3*r := by
  dsimp [resetIndex]; omega

theorem eq_resetIndex (i : Fin (3*r)) (hi : ¬ i.val+1 < 3*r) :
    i = resetIndex r hr := by
  apply Fin.ext
  have := i.isLt
  dsimp [resetIndex]
  omega

theorem resetCount_cast :
    (resetCount r hr start : ℚ) =
      (scale r hr start : ℚ) * occupation (rowWalk r hr) start (resetIndex r hr) := by
  rw [resetCount, counts_cast]
  simp [rowProbability, resetIndex_val]

/-- Restoring the omitted reset edge gives the full occupation outflow. -/
theorem source_mass (v : ℕ) :
    (((allEdges (rowActions r hr start)).map Edge.src).count v : ℚ) +
      (if 3*r=v then (resetCount r hr start : ℚ) else 0) =
      (scale r hr start : ℚ) *
        ∑ i : Fin (3*r), if i.val+1=v then occupation (rowWalk r hr) start i else 0 := by
  rw [actions_source_count, Nat.cast_sum, Finset.mul_sum]
  have hreset : (if 3*r=v then (resetCount r hr start : ℚ) else 0) =
      ∑ i : Fin (3*r), if i=resetIndex r hr then
        (if i.val+1=v then (resetCount r hr start : ℚ) else 0) else 0 := by
    simp [resetIndex_val]
  rw [hreset, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [Nat.cast_ite, Nat.cast_zero, action_width_cast]
  by_cases hi : i.val+1 < 3*r
  · have hn : i ≠ resetIndex r hr := by intro he; subst i; have := resetIndex_val r hr; omega
    simp [hi, hn]
  · have he := eq_resetIndex r hr i hi
    subst i
    simp [show ¬ (resetIndex r hr).val+1 < 3*r by rw [resetIndex_val]; omega,
      resetCount_cast]

/-- Restoring the omitted reset edge gives the full occupation inflow. -/
theorem target_mass (v : Fin (3*r+1)) :
    (((allEdges (rowActions r hr start)).map Edge.dst).count v.val : ℚ) +
      (if 1=v.val then (resetCount r hr start : ℚ) else 0) =
      (scale r hr start : ℚ) *
        ∑ i : Fin (3*r), occupation (rowWalk r hr) start i * rowProbability r hr i v := by
  rw [actions_target_count, Nat.cast_sum, Finset.mul_sum]
  have hreset : (if 1=v.val then (resetCount r hr start : ℚ) else 0) =
      ∑ i : Fin (3*r), if i=resetIndex r hr then
        (if 1=v.val then (resetCount r hr start : ℚ) else 0) else 0 := by simp
  rw [hreset, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [population_cast]
  by_cases hi : i.val+1 < 3*r
  · have hn : i ≠ resetIndex r hr := by intro he; subst i; have := resetIndex_val r hr; omega
    simp [hi, hn, v.isLt, mul_assoc]
  · have he := eq_resetIndex r hr i hi
    subst i
    have hv : v=rowOne r hr ↔ 1=v.val := by
      constructor
      · intro h; rw [h]; rfl
      · intro h; apply Fin.ext; exact h.symm
    simp [rowProbability, resetIndex_val, hv, resetCount_cast]

/-- The exact row boundary is proved from occupation conservation, including
both the natural reset count and the positive denominator-sized injection. -/
theorem row_balance :
    Balanced (List.replicate (scale r hr start) (start.val+1) ++
      List.replicate (resetCount r hr start) 1)
      (List.replicate (scale r hr start) 0 ++
      List.replicate (resetCount r hr start) (3*r))
      (allEdges (rowActions r hr start)) := by
  apply balanced_iff_counts.mpr
  intro v
  simp only [List.count_append, List.count_replicate, beq_iff_eq]
  by_cases hv : v < 3*r+1
  · let vf : Fin (3*r+1) := ⟨v,hv⟩
    have hs := source_mass r hr start v
    have ht := target_mass r hr start vf
    have hb := occupation_balance (rowWalk r hr) start vf
    simp only [divergence, mul_sub, mul_ite, mul_one, mul_zero,
      Finset.sum_sub_distrib, Fin.ext_iff, Fin.val_succ, Fin.val_zero] at hb
    have hscaled := congrArg (fun q : ℚ => (scale r hr start : ℚ)*q) hb
    simp only [rowWalk, mul_sub, mul_ite, mul_one, mul_zero] at hscaled
    have he :
        (if start.val+1=v then (scale r hr start : ℚ) else 0) +
        (if 1=v then (resetCount r hr start : ℚ) else 0) +
        (((allEdges (rowActions r hr start)).map Edge.dst).count v : ℚ) =
        (if 0=v then (scale r hr start : ℚ) else 0) +
        (if 3*r=v then (resetCount r hr start : ℚ) else 0) +
        (((allEdges (rowActions r hr start)).map Edge.src).count v : ℚ) := by
      dsimp [vf] at ht hscaled
      simp only [rowWalk] at hs ht
      linarith
    exact_mod_cast he
  · have hsource : ((allEdges (rowActions r hr start)).map Edge.src).count v=0 := by
      rw [actions_source_count]
      apply Finset.sum_eq_zero
      intro i _
      have := i.isLt
      simp [show i.val+1≠v by omega]
    have htarget : ((allEdges (rowActions r hr start)).map Edge.dst).count v=0 := by
      rw [actions_target_count]
      apply Finset.sum_eq_zero
      intro i _
      simp [population, hv]
    simp [hsource, htarget, show start.val+1≠v by have := start.isLt; omega,
      show 1≠v by omega, show 0≠v by omega, show 3*r≠v by omega]

/-- An actual row, with no desired row or balance premise. -/
def occupationRow : Row r (start.val+1) (scale r hr start) :=
  ⟨rowActions r hr start, resetCount r hr start, row_balance r hr start⟩

include hr in
theorem exists_row : ∃ K : ℕ, 0<K ∧ Nonempty (Row r (start.val+1) K) :=
  ⟨scale r hr start, scale_pos r hr start, ⟨occupationRow r hr start⟩⟩

/-- The exact profile-biased transition ratios survive denominator clearing,
including the zero-width action at the reset state. -/
theorem action_profile_proportional (i : Fin (3*r)) (y : ℕ)
    (hy : y ∈ (action r hr start i).children) :
    (action r hr start i).population y *
      (((action r hr start i).h+1) * profile r (action r hr start i).x) =
    (action r hr start i).width * profile r y := by
  by_cases hi : i.val+1 < 3*r
  · have hc := hy
    rw [children_eq r hr start i hi] at hc
    obtain ⟨t,ht,he⟩ := List.mem_map.mp hc
    have htf : t < rowWidth r (i.val+1)+1 := List.mem_range.mp ht
    let tf : Fin (rowWidth r (i.val+1)+1) := ⟨t,htf⟩
    have hey : (rowChild r i tf).val=y := he
    have hyv : y < 3*r+1 := by rw [← hey]; exact (rowChild r i tf).isLt
    have hprob := rowProbability_child r hr i (by omega) tf
    have hp := population_cast r hr start i y
    have hfin : (⟨y,hyv⟩ : Fin (3*r+1))=rowChild r i tf := by apply Fin.ext; exact hey.symm
    simp only [dite_eq_left hi, dite_eq_left hyv, hfin, hprob] at hp
    have hw := action_width_cast r hr start i
    rw [ite_eq_left hi] at hw
    have hden : ((rowWidth r (i.val+1)+1 : ℕ) : ℚ) * (profile r (i.val+1) : ℚ) ≠ 0 := by
      apply mul_ne_zero
      · positivity
      · exact_mod_cast (profile_pos r (i.val+1) hr).ne'
    have hq :
        (population r hr start i y : ℚ) *
          (((rowWidth r (i.val+1)+1 : ℕ) : ℚ) * (profile r (i.val+1) : ℚ)) =
        ((action r hr start i).width : ℚ) * (profile r y : ℚ) := by
      rw [hp, hw, hey]
      push_cast
      have hprof : (profile r (i.val+1) : ℚ) ≠ 0 := by
        exact_mod_cast (profile_pos r (i.val+1) hr).ne'
      field_simp
    have hn : population r hr start i y *
        ((rowWidth r (i.val+1)+1) * profile r (i.val+1)) =
        (action r hr start i).width * profile r y := by exact_mod_cast hq
    simpa only [action, site, dite_eq_left hi, IntegerRowConstruction.Site.action,
      IntegerRowConstruction.maximalSite, rowWidth] using hn
  · have hz : (action r hr start i).width=0 := by
      rw [action_width_eq_sum]
      simp [population, hi]
    simp [action_population, population, hi, hz]

include hr in
theorem exists_row_at (i : ℕ) (hi : 1 ≤ i) (hir : i < 3*r) :
    ∃ K : ℕ, 0<K ∧ Nonempty (Row r i K) := by
  let start : Fin (3*r) := ⟨i-1, by omega⟩
  have h := exists_row r hr start
  have he : start.val+1=i := by dsimp [start]; omega
  simpa only [he] using h

/-- For every row cutoff, a genuine all-row family exists at one positive
common injection scale. The row constructors use no family existence premise. -/
theorem exists_family (n : ℕ) : ∃ K : ℕ, 0<K ∧ Nonempty (Family n K) :=
  FamilySynchronizationBridge.exists_family
    (fun r hr i hi hir => exists_row_at r hr i hi hir) n

end
end MatrixDimensionAudit.OccupationFamilyBridge

#print axioms MatrixDimensionAudit.OccupationFamilyBridge.FlowEdge
#print axioms MatrixDimensionAudit.OccupationFamilyBridge.weight
#print axioms MatrixDimensionAudit.OccupationFamilyBridge.weight_nonnegative
#print axioms MatrixDimensionAudit.OccupationFamilyBridge.scale
#print axioms MatrixDimensionAudit.OccupationFamilyBridge.scale_pos
#print axioms MatrixDimensionAudit.OccupationFamilyBridge.counts
#print axioms MatrixDimensionAudit.OccupationFamilyBridge.counts_cast
#print axioms MatrixDimensionAudit.OccupationFamilyBridge.site
#print axioms MatrixDimensionAudit.OccupationFamilyBridge.population
#print axioms MatrixDimensionAudit.OccupationFamilyBridge.action
#print axioms MatrixDimensionAudit.OccupationFamilyBridge.rowActions
#print axioms MatrixDimensionAudit.OccupationFamilyBridge.population_cast
#print axioms MatrixDimensionAudit.OccupationFamilyBridge.action_population
#print axioms MatrixDimensionAudit.OccupationFamilyBridge.children_eq
#print axioms MatrixDimensionAudit.OccupationFamilyBridge.rowProbability_zero_off_children
#print axioms MatrixDimensionAudit.OccupationFamilyBridge.population_zero_off_children
#print axioms MatrixDimensionAudit.OccupationFamilyBridge.action_output_count
#print axioms MatrixDimensionAudit.OccupationFamilyBridge.action_width_eq_sum
#print axioms MatrixDimensionAudit.OccupationFamilyBridge.action_source_count
#print axioms MatrixDimensionAudit.OccupationFamilyBridge.action_target_count
#print axioms MatrixDimensionAudit.OccupationFamilyBridge.actions_source_count
#print axioms MatrixDimensionAudit.OccupationFamilyBridge.actions_target_count
#print axioms MatrixDimensionAudit.OccupationFamilyBridge.action_width_cast
#print axioms MatrixDimensionAudit.OccupationFamilyBridge.resetIndex
#print axioms MatrixDimensionAudit.OccupationFamilyBridge.resetCount
#print axioms MatrixDimensionAudit.OccupationFamilyBridge.resetIndex_val
#print axioms MatrixDimensionAudit.OccupationFamilyBridge.eq_resetIndex
#print axioms MatrixDimensionAudit.OccupationFamilyBridge.resetCount_cast
#print axioms MatrixDimensionAudit.OccupationFamilyBridge.source_mass
#print axioms MatrixDimensionAudit.OccupationFamilyBridge.target_mass
#print axioms MatrixDimensionAudit.OccupationFamilyBridge.row_balance
#print axioms MatrixDimensionAudit.OccupationFamilyBridge.occupationRow
#print axioms MatrixDimensionAudit.OccupationFamilyBridge.exists_row
#print axioms MatrixDimensionAudit.OccupationFamilyBridge.action_profile_proportional
#print axioms MatrixDimensionAudit.OccupationFamilyBridge.exists_row_at
#print axioms MatrixDimensionAudit.OccupationFamilyBridge.exists_family
