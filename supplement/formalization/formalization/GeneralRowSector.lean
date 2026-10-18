import formalization.RowTwoSectorProfile

namespace MatrixDimensionAudit
namespace GeneralRowSector

open WeightedSector GeneralFlow

/-- Integer scaling of the sharp affine profile for row r. -/
def profile (r x : Nat) : Nat := 3 * r - 3 + 2 * x

theorem profile_pos (r x : Nat) (hr : 2 ≤ r) : 0 < profile r x := by
  unfold profile
  omega

theorem profile_reset (r : Nat) (hr : 2 ≤ r) :
    profile r (3 * r) = 3 * profile r 1 := by
  unfold profile
  omega

private theorem sum_map_add (l : List Nat) (f g : Nat → Nat) :
    (l.map (fun t => f t + g t)).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => rfl
  | cons t tail ih => simp [ih, Nat.add_assoc, Nat.add_left_comm]

/-- Reflection t ↦ h-t permutes the complete child-index range. -/
theorem range_reflection (h : Nat) :
    ((List.range (h + 1)).map (fun t => h - t)) = (List.range (h + 1)).reverse := by
  have e := List.reverse_range' (s := 0) (n := h + 1)
  simpa [← List.range_eq_range'] using e.symm

/-- Pairing opposite children proves the identity for every width, with no
finite state or row certificate. -/
theorem profile_sum (r x h : Nat) (hh : h ≤ x) :
    ((List.range (h + 1)).map (fun t => profile r (x + h - 2 * t))).sum =
      (h + 1) * profile r x := by
  let f := fun t => profile r (x + h - 2 * t)
  have pair : ∀ t ∈ List.range (h + 1), f t + f (h - t) = 2 * profile r x := by
    intro t ht
    simp only [List.mem_range] at ht
    dsimp [f, profile]
    omega
  have reflection : ((List.range (h + 1)).map (fun t => f (h - t))).sum =
      ((List.range (h + 1)).map f).sum := by
    change ((List.range (h + 1)).map (f ∘ (fun t => h - t))).sum = _
    rw [← List.map_map, range_reflection, List.map_reverse, List.sum_reverse]
  have eq : ((List.range (h + 1)).map f).sum +
      ((List.range (h + 1)).map f).sum = (h + 1) * (2 * profile r x) := by
    have hm : ((List.range (h + 1)).map (fun t => f t + f (h - t))) =
        List.replicate (h + 1) (2 * profile r x) := by
      calc
        _ = (List.range (h + 1)).map (fun _ => 2 * profile r x) := List.map_congr_left pair
        _ = _ := by simp only [List.map_const', List.length_range]
    calc
      _ = ((List.range (h + 1)).map (fun t => f t + f (h - t))).sum := by
        rw [sum_map_add, reflection]
      _ = _ := by rw [hm, List.sum_replicate_nat]
  have rearrange : (h + 1) * (2 * profile r x) = 2 * ((h + 1) * profile r x) := by
    simp [Nat.mul_left_comm]
  rw [rearrange] at eq
  dsimp [f] at eq
  omega

/-- Every legal split width and arbitrary natural child populations. -/
structure Action (r : Nat) where
  x : Nat
  h : Nat
  x_lower : 1 ≤ x
  x_upper : x < 3 * r
  h_lower : 1 ≤ h
  h_upper : h ≤ min x (3 * r - x)
  population : Nat → Nat

variable {r : Nat}

def Action.children (a : Action r) : List Nat :=
  (List.range (a.h + 1)).map (fun t => a.x + a.h - 2 * t)

def Action.output (a : Action r) : List Nat := populationWord a.children a.population

def Action.width (a : Action r) : Nat := (a.children.map a.population).sum

def Action.input (a : Action r) : List Nat := List.replicate a.width a.x

def Action.count (a : Action r) : Nat := typeCount a.children a.output

def Action.dimension (a : Action r) : Nat := (a.h + 1) ^ a.width

def Action.edges (a : Action r) : List (Edge Nat) :=
  a.output.map (fun child => ⟨a.x, child⟩)

def allEdges (actions : List (Action r)) : List (Edge Nat) := actions.flatMap Action.edges

def totalCount (actions : List (Action r)) : Nat := (actions.map Action.count).prod

def totalDimension (actions : List (Action r)) : Nat := (actions.map Action.dimension).prod

theorem profile_word_pos (r : Nat) (hr : 2 ≤ r) (word : List Nat) :
    0 < wordWeight (profile r) word := by
  induction word with
  | nil => simp [wordWeight]
  | cons x tail ih => exact Nat.mul_pos (profile_pos r x hr) ih

theorem wordWeight_append (left right : List Nat) :
    wordWeight (profile r) (left ++ right) =
      wordWeight (profile r) left * wordWeight (profile r) right := by
  simp [wordWeight, List.map_append, List.prod_append]

theorem Action.profile_sum (a : Action r) :
    (a.children.map (profile r)).sum = (a.h + 1) * profile r a.x := by
  simpa [Action.children, List.map_map, Function.comp_def] using
    GeneralRowSector.profile_sum r a.x a.h (Nat.le_trans a.h_upper (Nat.min_le_left _ _))

theorem Action.children_nodup (a : Action r) : a.children.Nodup := by
  change List.Pairwise (fun x y => x ≠ y) ((List.range (a.h + 1)).map _)
  rw [List.pairwise_map]
  apply List.Pairwise.imp_of_mem (p := List.pairwise_lt_range)
  intro t u ht hu htu
  simp only [List.mem_range] at ht hu
  have hh := Nat.le_trans a.h_upper (Nat.min_le_left _ _)
  omega

/-- Every listed child remains in the row's state interval. -/
theorem Action.child_upper (a : Action r) (child : Nat) (hc : child ∈ a.children) :
    child ≤ 3 * r := by
  obtain ⟨t, ht, he⟩ := List.mem_map.mp hc
  have hh := Nat.le_trans a.h_upper (Nat.min_le_right _ _)
  have hx := a.x_upper
  omega

/-- The histogram family is a genuine finite set of words. -/
theorem Action.sector_nodup (a : Action r) : (typeSector a.children a.output).Nodup :=
  typeSector_nodup a.children a.output a.children_nodup

theorem Action.local_bound (a : Action r) :
    a.count * wordWeight (profile r) a.output ≤
      a.dimension * wordWeight (profile r) a.input := by
  have h := weighted_profile_bound (profile r) a.population a.children
    (a.h + 1) (profile r a.x) a.profile_sum
  rw [← populationWord_weight] at h
  simpa [Action.count, Action.output, Action.dimension, Action.width,
    Action.input, wordWeight_replicate] using h

theorem Action.sourceWord (a : Action r) :
    a.edges.map Edge.src = a.input := by
  simp [Action.edges, List.map_map, Function.comp_def, List.map_const',
    Action.input, Action.output, populationWord_length, Action.width]

theorem Action.targetWord (a : Action r) :
    a.edges.map Edge.dst = a.output := by
  simp [Action.edges, List.map_map, Function.comp_def]

theorem Action.coarse_bound (a : Action r) : a.count ≤ a.dimension := by
  have h := unweighted_type_bound a.children a.output
  simpa [Action.count, Action.output, Action.dimension, populationWord_length,
    Action.width, Action.children] using h

theorem product_coarse_bound (actions : List (Action r)) :
    totalCount actions ≤ totalDimension actions := by
  induction actions with
  | nil => exact Nat.le_refl _
  | cons a tail ih =>
    exact Nat.mul_le_mul a.coarse_bound ih

theorem product_sector_bound (actions : List (Action r)) :
    totalCount actions * wordWeight (profile r) ((allEdges actions).map Edge.dst) ≤
      totalDimension actions * wordWeight (profile r) ((allEdges actions).map Edge.src) := by
  induction actions with
  | nil => exact Nat.le_refl _
  | cons a tail ih =>
    have h := Nat.mul_le_mul a.local_bound ih
    simpa [totalCount, totalDimension, allEdges, List.flatMap_cons,
      List.map_append, wordWeight_append, a.sourceWord, a.targetWord,
      Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h

/-- Exact boundary telescope for any injected state i. -/
theorem boundary_sector_bound (actions : List (Action r)) (hr : 2 ≤ r) (i K Z : Nat)
    (balance : Balanced (List.replicate K i ++ List.replicate Z 1)
      (List.replicate K 0 ++ List.replicate Z (3 * r)) (allEdges actions)) :
    totalCount actions * (profile r 0 ^ K * profile r (3 * r) ^ Z) ≤
      totalDimension actions * (profile r i ^ K * profile r 1 ^ Z) := by
  have he := product_sector_bound actions
  have final :
      (totalCount actions * wordWeight (profile r)
        (List.replicate K 0 ++ List.replicate Z (3 * r))) *
          wordWeight (profile r) ((allEdges actions).map Edge.src) ≤
      (totalDimension actions * wordWeight (profile r)
        (List.replicate K i ++ List.replicate Z 1)) *
          wordWeight (profile r) ((allEdges actions).map Edge.src) := by
    calc
      _ = wordWeight (profile r) (List.replicate K i ++ List.replicate Z 1) *
          (totalCount actions * wordWeight (profile r) ((allEdges actions).map Edge.dst)) := by
        have hfull := multiplicative_balance balance (profile r)
        change wordWeight (profile r) (List.replicate K i ++ List.replicate Z 1) *
            wordWeight (profile r) ((allEdges actions).map Edge.dst) =
          wordWeight (profile r) (List.replicate K 0 ++ List.replicate Z (3 * r)) *
            wordWeight (profile r) ((allEdges actions).map Edge.src) at hfull
        rw [Nat.mul_assoc, ← hfull]
        simp [Nat.mul_left_comm]
      _ ≤ _ := by
        simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
          Nat.mul_le_mul_left
            (wordWeight (profile r) (List.replicate K i ++ List.replicate Z 1)) he
  have hc := Nat.le_of_mul_le_mul_right final
    (profile_word_pos r hr ((allEdges actions).map Edge.src))
  simpa [wordWeight_append, wordWeight_replicate] using hc

/-- Reset factors cancel because P_r(3r)=3P_r(1). -/
theorem sharp_split_count (actions : List (Action r)) (hr : 2 ≤ r) (i K Z : Nat)
    (balance : Balanced (List.replicate K i ++ List.replicate Z 1)
      (List.replicate K 0 ++ List.replicate Z (3 * r)) (allEdges actions)) :
    totalCount actions * (profile r 0 ^ K * 3 ^ Z) ≤
      totalDimension actions * profile r i ^ K := by
  have h := boundary_sector_bound actions hr i K Z balance
  rw [profile_reset r hr, Nat.mul_pow] at h
  have h' : (totalCount actions * (profile r 0 ^ K * 3 ^ Z)) * profile r 1 ^ Z ≤
      (totalDimension actions * profile r i ^ K) * profile r 1 ^ Z := by
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
  exact Nat.le_of_mul_le_mul_right h' (Nat.pow_pos (profile_pos r 1 hr))

abbrev triplingWords := RowTwoSectorProfile.triplingWords
abbrev triplingCount := RowTwoSectorProfile.triplingCount

def actualSectorCount (actions : List (Action r)) (Z : Nat) : Nat :=
  totalCount actions * triplingCount Z

/-- Actual fixed-histogram and ternary sectors; no gain inequality is assumed. -/
theorem sharp_actual_total_count (actions : List (Action r)) (hr : 2 ≤ r) (i K Z : Nat)
    (balance : Balanced (List.replicate K i ++ List.replicate Z 1)
      (List.replicate K 0 ++ List.replicate Z (3 * r)) (allEdges actions)) :
    actualSectorCount actions Z * (3 * r - 3) ^ K ≤
      totalDimension actions * (3 * r - 3 + 2 * i) ^ K := by
  have h := sharp_split_count actions hr i K Z balance
  have ht := Nat.mul_le_mul_left (totalCount actions * profile r 0 ^ K)
    (RowTwoSectorProfile.triplingCount_bound Z)
  have hc : actualSectorCount actions Z * profile r 0 ^ K ≤
      totalCount actions * (profile r 0 ^ K * 3 ^ Z) := by
    simpa [actualSectorCount, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using ht
  simpa [profile] using Nat.le_trans hc h

theorem coarse_actual_total_count (actions : List (Action r)) (Z : Nat) :
    actualSectorCount actions Z ≤ totalDimension actions * 3 ^ Z :=
  Nat.mul_le_mul (product_coarse_bound actions) (RowTwoSectorProfile.triplingCount_bound Z)

theorem top_actual_total_count (actions : List (Action r)) (hr : 2 ≤ r) (K Z : Nat)
    (balance : Balanced (List.replicate (K + Z) 1)
      (List.replicate K 0 ++ List.replicate Z (3 * r)) (allEdges actions)) :
    actualSectorCount actions Z * (3 * r - 3) ^ K ≤
      totalDimension actions * (3 * r - 1) ^ K := by
  have hi : 3 * r - 3 + 2 * 1 = 3 * r - 1 := by omega
  have hb : Balanced (List.replicate K 1 ++ List.replicate Z 1)
      (List.replicate K 0 ++ List.replicate Z (3 * r)) (allEdges actions) := by
    simpa only [List.replicate_append_replicate] using balance
  simpa only [hi] using sharp_actual_total_count actions hr 1 K Z hb

theorem lower_actual_total_count (actions : List (Action r)) (hr : 2 ≤ r) (K Z : Nat)
    (balance : Balanced (List.replicate K 2 ++ List.replicate Z 1)
      (List.replicate K 0 ++ List.replicate Z (3 * r)) (allEdges actions)) :
    actualSectorCount actions Z * (3 * r - 3) ^ K ≤
      totalDimension actions * (3 * r + 1) ^ K := by
  have hi : 3 * r - 3 + 2 * 2 = 3 * r + 1 := by omega
  simpa only [hi] using sharp_actual_total_count actions hr 2 K Z balance

end GeneralRowSector
end MatrixDimensionAudit

#print axioms MatrixDimensionAudit.GeneralRowSector.profile_sum
#print axioms MatrixDimensionAudit.GeneralRowSector.Action.children_nodup
#print axioms MatrixDimensionAudit.GeneralRowSector.boundary_sector_bound
#print axioms MatrixDimensionAudit.GeneralRowSector.sharp_actual_total_count
#print axioms MatrixDimensionAudit.GeneralRowSector.top_actual_total_count
#print axioms MatrixDimensionAudit.GeneralRowSector.lower_actual_total_count
#print axioms MatrixDimensionAudit.GeneralRowSector.coarse_actual_total_count
