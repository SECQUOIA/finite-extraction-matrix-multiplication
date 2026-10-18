import formalization.GeneralFlowCore
import formalization.WeightedSector
import formalization.RecipePowerBridge
import formalization.RowTwoCatalyst

namespace MatrixDimensionAudit
namespace RowTwoSectorProfile

open WeightedSector
open GeneralFlow

def profile (x : Nat) : Nat := 3 + 2 * x

structure Action where
  x : Fin 7
  h : Fin 7
  x_lower : 1 ≤ x.val
  x_upper : x.val < 6
  h_lower : 1 ≤ h.val
  h_upper : h.val ≤ min x.val (6 - x.val)
  population : Nat → Nat

def Action.children (a : Action) : List Nat :=
  (List.range (a.h.val + 1)).map (fun t => a.x.val + a.h.val - 2 * t)

def Action.output (a : Action) : List Nat := populationWord a.children a.population

def Action.width (a : Action) : Nat := (a.children.map a.population).sum

def Action.input (a : Action) : List Nat := List.replicate a.width a.x.val

def Action.count (a : Action) : Nat := typeCount a.children a.output

def Action.dimension (a : Action) : Nat := (a.h.val + 1) ^ a.width

def Action.edges (a : Action) : List (Edge Nat) :=
  a.output.map (fun child => ⟨a.x.val, child⟩)

def allEdges (actions : List Action) : List (Edge Nat) := actions.flatMap Action.edges

def totalCount (actions : List Action) : Nat := (actions.map Action.count).prod

def totalDimension (actions : List Action) : Nat := (actions.map Action.dimension).prod

theorem profile_pos (x : Nat) : 0 < profile x := by unfold profile; omega

theorem profile_word_pos (word : List Nat) : 0 < wordWeight profile word := by
  induction word with
  | nil => simp [wordWeight]
  | cons x tail ih => exact Nat.mul_pos (profile_pos x) ih

theorem wordWeight_append (left right : List Nat) :
    wordWeight profile (left ++ right) = wordWeight profile left * wordWeight profile right := by
  simp [wordWeight, List.map_append, List.prod_append]

/-- All legal widths, not just maximal-width splits. -/
theorem finite_profile_sum :
    ∀ x h : Fin 7, 1 ≤ x.val → x.val < 6 → 1 ≤ h.val →
      h.val ≤ min x.val (6 - x.val) →
      (((List.range (h.val + 1)).map
        (fun t => profile (x.val + h.val - 2 * t))).sum) =
        (h.val + 1) * profile x.val := by decide

theorem Action.profile_sum (a : Action) :
    (a.children.map profile).sum = (a.h.val + 1) * profile a.x.val := by
  simpa [Action.children, List.map_map, Function.comp_def] using
    finite_profile_sum a.x a.h a.x_lower a.x_upper a.h_lower a.h_upper

theorem finite_children_nodup :
    ∀ x h : Fin 7, 1 ≤ x.val → x.val < 6 → 1 ≤ h.val →
      h.val ≤ min x.val (6 - x.val) →
      (((List.range (h.val + 1)).map
        (fun t => x.val + h.val - 2 * t))).Nodup := by decide

theorem Action.children_nodup (a : Action) : a.children.Nodup :=
  finite_children_nodup a.x a.h a.x_lower a.x_upper a.h_lower a.h_upper

theorem Action.local_bound (a : Action) :
    a.count * wordWeight profile a.output ≤
      a.dimension * wordWeight profile a.input := by
  have h := weighted_profile_bound profile a.population a.children
    (a.h.val + 1) (profile a.x.val) a.profile_sum
  rw [← populationWord_weight] at h
  simpa [Action.count, Action.output, Action.dimension, Action.width,
    Action.input, wordWeight_replicate] using h

theorem Action.sourceWord (a : Action) :
    a.edges.map Edge.src = a.input := by
  simp [Action.edges, List.map_map, Function.comp_def, List.map_const',
    Action.input, Action.output, populationWord_length, Action.width]

theorem Action.targetWord (a : Action) :
    a.edges.map Edge.dst = a.output := by
  simp [Action.edges, List.map_map, Function.comp_def]

theorem Action.coarse_bound (a : Action) : a.count ≤ a.dimension := by
  have h := unweighted_type_bound a.children a.output
  simpa [Action.count, Action.output, Action.dimension, populationWord_length,
    Action.width, Action.children] using h

theorem product_coarse_bound (actions : List Action) :
    totalCount actions ≤ totalDimension actions := by
  induction actions with
  | nil => exact Nat.le_refl _
  | cons a tail ih =>
    exact Nat.mul_le_mul a.coarse_bound ih

theorem product_sector_bound (actions : List Action) :
    totalCount actions * wordWeight profile ((allEdges actions).map Edge.dst) ≤
      totalDimension actions * wordWeight profile ((allEdges actions).map Edge.src) := by
  induction actions with
  | nil => exact Nat.le_refl _
  | cons a tail ih =>
    have h := Nat.mul_le_mul a.local_bound ih
    simpa [totalCount, totalDimension, allEdges, List.flatMap_cons,
      List.map_append, wordWeight_append, a.sourceWord, a.targetWord,
      Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h

/-- A gain inequality derived from actual sector counts and graph conservation. -/
theorem boundary_sector_bound (actions : List Action) (K Z : Nat)
    (balance : Balanced (List.replicate (K + Z) 1)
      (List.replicate K 0 ++ List.replicate Z 6) (allEdges actions)) :
    totalCount actions * (3 ^ K * 15 ^ Z) ≤ totalDimension actions * 5 ^ (K + Z) := by
  have he := product_sector_bound actions
  have final :
      (totalCount actions * wordWeight profile
        (List.replicate K 0 ++ List.replicate Z 6)) *
          wordWeight profile ((allEdges actions).map Edge.src) ≤
      (totalDimension actions * wordWeight profile (List.replicate (K + Z) 1)) *
          wordWeight profile ((allEdges actions).map Edge.src) := by
    calc
      _ = wordWeight profile (List.replicate (K + Z) 1) *
          (totalCount actions * wordWeight profile ((allEdges actions).map Edge.dst)) := by
        have hfull := multiplicative_balance balance profile
        change wordWeight profile (List.replicate (K + Z) 1) *
            wordWeight profile ((allEdges actions).map Edge.dst) =
          wordWeight profile (List.replicate K 0 ++ List.replicate Z 6) *
            wordWeight profile ((allEdges actions).map Edge.src) at hfull
        rw [Nat.mul_assoc, ← hfull]
        simp [Nat.mul_left_comm]
      _ ≤ _ := by
        simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
          Nat.mul_le_mul_left (wordWeight profile (List.replicate (K + Z) 1)) he
  have hc := Nat.le_of_mul_le_mul_right final
    (profile_word_pos ((allEdges actions).map Edge.src))
  simpa [wordWeight_append, wordWeight_replicate, profile] using hc

/-- The reset profile ratio cancels exactly against the tripling type bound. -/
theorem sharp_split_count (actions : List Action) (K Z : Nat)
    (balance : Balanced (List.replicate (K + Z) 1)
      (List.replicate K 0 ++ List.replicate Z 6) (allEdges actions)) :
    totalCount actions * 3 ^ (K + Z) ≤ totalDimension actions * 5 ^ K := by
  have h := boundary_sector_bound actions K Z balance
  rw [show 15 = 3 * 5 by decide, Nat.mul_pow] at h
  have h' : (totalCount actions * 3 ^ (K + Z)) * 5 ^ Z ≤
      (totalDimension actions * 5 ^ K) * 5 ^ Z := by
    simpa [Nat.pow_add,
      Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
  exact Nat.le_of_mul_le_mul_right h' (Nat.pow_pos (by decide))

theorem sharp_total_count (actions : List Action) (K Z triplingCount : Nat)
    (balance : Balanced (List.replicate (K + Z) 1)
      (List.replicate K 0 ++ List.replicate Z 6) (allEdges actions))
    (tripling_bound : triplingCount ≤ 3 ^ Z) :
    (totalCount actions * triplingCount) * 3 ^ K ≤ totalDimension actions * 5 ^ K := by
  have h := sharp_split_count actions K Z balance
  have ht := Nat.mul_le_mul_left (totalCount actions * 3 ^ K) tripling_bound
  have hc : totalCount actions * triplingCount * 3 ^ K ≤
      totalCount actions * 3 ^ (K + Z) := by
    simpa [Nat.pow_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using ht
  exact Nat.le_trans hc h

theorem coarse_total_count (actions : List Action) (Z triplingCount : Nat)
    (tripling_bound : triplingCount ≤ 3 ^ Z) :
    totalCount actions * triplingCount ≤ totalDimension actions * 3 ^ Z :=
  Nat.mul_le_mul (product_coarse_bound actions) tripling_bound

/-- The actual tripling sector fixes the middle-letter population and allows
the other two letters freely. This is the choose-times-power count in word form. -/
def triplingWords (Z : Nat) : List (List Nat) :=
  (words [0, 1, 2] Z).filter (fun word => word.count 1 == (Z + 1) / 3)

def triplingCount (Z : Nat) : Nat := (triplingWords Z).length

theorem allWords_card (alphabet : List Nat) (n : Nat) :
    (words alphabet n).length = alphabet.length ^ n := by
  have hp : ∀ word : List Nat, wordWeight (fun _ => 1) word = 1 := by
    intro word
    induction word with
    | nil => rfl
    | cons x tail ih => simpa only [wordWeight_cons, Nat.one_mul] using ih
  have hc := totalWeight_constant (fun _ => 1) (words alphabet n) 1
    (by intro word _; exact hp word)
  have hs : (alphabet.map (fun _ => 1)).sum = alphabet.length := by
    clear hc
    induction alphabet with
    | nil => rfl
    | cons x tail ih => simp [ih, Nat.add_comm]
  rw [allWords_totalWeight, hs, Nat.mul_one] at hc
  exact hc.symm

theorem triplingCount_bound (Z : Nat) : triplingCount Z ≤ 3 ^ Z := by
  have h := List.length_filter_le (fun word : List Nat => word.count 1 == (Z + 1) / 3)
    (words [0, 1, 2] Z)
  simpa [triplingCount, triplingWords, allWords_card] using h

/-- Sharp row-two gain, with both split and tripling sectors defined by words. -/
theorem sharp_actual_total_count (actions : List Action) (K Z : Nat)
    (balance : Balanced (List.replicate (K + Z) 1)
      (List.replicate K 0 ++ List.replicate Z 6) (allEdges actions)) :
    (totalCount actions * triplingCount Z) * 3 ^ K ≤ totalDimension actions * 5 ^ K :=
  sharp_total_count actions K Z (triplingCount Z) balance (triplingCount_bound Z)

theorem coarse_actual_total_count (actions : List Action) (Z : Nat) :
    totalCount actions * triplingCount Z ≤ totalDimension actions * 3 ^ Z :=
  coarse_total_count actions Z (triplingCount Z) (triplingCount_bound Z)

theorem Action.output_mem_children (a : Action) (child : Nat)
    (hc : child ∈ a.output) : child ∈ a.children := by
  obtain ⟨symbol, hs, hc⟩ := List.mem_flatMap.mp hc
  have heq := List.eq_of_mem_replicate hc
  exact heq ▸ hs

theorem Action.child_witness (a : Action) (child : Nat) (hc : child ∈ a.output) :
    ∃ t, t ≤ a.h.val ∧ child = a.x.val + a.h.val - 2 * t := by
  obtain ⟨t, ht, heq⟩ := List.mem_map.mp (a.output_mem_children child hc)
  exact ⟨t, by simpa only [List.mem_range, Nat.lt_succ_iff] using ht, heq.symm⟩

/-- One legal selected-child split for each actual output occurrence. -/
noncomputable def Action.selectedSplit (a : Action) (child : {c // c ∈ a.output}) :
    RowTwoSplit := by
  let t := Classical.choose (a.child_witness child.val child.property)
  have ht := (Classical.choose_spec (a.child_witness child.val child.property)).1
  have hfin : t < 7 := by have hh := a.h.isLt; omega
  exact ⟨a.x, a.h, ⟨t, hfin⟩, a.x_lower, a.x_upper, a.h_lower, a.h_upper, ht⟩

theorem Action.selectedSplit_edge (a : Action) (child : {c // c ∈ a.output}) :
    (a.selectedSplit child).edge = (⟨a.x.val, child.val⟩ : Edge Nat) := by
  have hc := (Classical.choose_spec (a.child_witness child.val child.property)).2
  simp only [Action.selectedSplit, RowTwoSplit.edge]
  rw [← hc]

theorem Action.selectedSplit_dimension (a : Action) (child : {c // c ∈ a.output}) :
    (a.selectedSplit child).dimension = a.h.val + 1 := rfl

noncomputable def Action.expandedSplits (a : Action) : List RowTwoSplit :=
  a.output.attach.map a.selectedSplit

noncomputable def expandedSplits (actions : List Action) : List RowTwoSplit :=
  actions.flatMap Action.expandedSplits

theorem Action.expandedSplits_edges (a : Action) :
    a.expandedSplits.map RowTwoSplit.edge = a.edges := by
  simp only [Action.expandedSplits, List.map_map, Function.comp_def,
    a.selectedSplit_edge, List.attach_map_val, Action.edges]

theorem Action.expandedSplits_dimensions (a : Action) :
    (a.expandedSplits.map RowTwoSplit.dimension).prod = a.dimension := by
  simp only [Action.expandedSplits, List.map_map, Function.comp_def,
    a.selectedSplit_dimension, List.map_const', List.length_attach]
  rw [List.prod_replicate_nat]
  simp [Action.dimension, Action.output, populationWord_length, Action.width]

theorem expandedSplits_edges (actions : List Action) :
    (expandedSplits actions).map RowTwoSplit.edge = allEdges actions := by
  simp [expandedSplits, allEdges, List.map_flatMap, Action.expandedSplits_edges]

theorem expandedSplits_dimensions (actions : List Action) :
    ((expandedSplits actions).map RowTwoSplit.dimension).prod = totalDimension actions := by
  induction actions with
  | nil => rfl
  | cons a tail ih =>
    simpa only [expandedSplits, List.flatMap_cons, List.map_append,
      List.prod_append, a.expandedSplits_dimensions, totalDimension,
      List.map_cons, List.prod_cons] using congrArg (fun d => a.dimension * d) ih

theorem action_dimension_bound (actions : List Action) (K Z : Nat)
    (balance : Balanced (List.replicate (K + Z) 1)
      (List.replicate K 0 ++ List.replicate Z 6) (allEdges actions)) :
    2 ^ K * 16 ^ Z ≤ totalDimension actions := by
  have h := rowTwo_dimension_bound (expandedSplits actions) K Z
    (by simpa only [expandedSplits_edges] using balance)
  simpa only [expandedSplits_dimensions] using h

def actualSectorCount (actions : List Action) (Z : Nat) : Nat :=
  totalCount actions * triplingCount Z

/-- Any separator paying at least its sector count in each of three cyclic
orientations pays at least the cube of the total sector count. -/
theorem three_orientation_copies_paid (factors : List (Nat × Nat))
    (paid : ∀ p ∈ factors, p.fst ≤ p.snd) :
    ((factors.map Prod.fst).prod) ^ 3 ≤
      (factors.map (fun p => p.snd ^ 3)).prod := by
  induction factors with
  | nil => exact Nat.le_refl _
  | cons p tail ih =>
    have hp := paid p (by simp)
    have ht := ih (by intro q hq; exact paid q (by simp [hq]))
    have h := Nat.mul_le_mul (Nat.pow_le_pow_left hp 3) ht
    simpa only [List.map_cons, List.prod_cons, Nat.mul_pow] using h

/-- Only the remaining tensor-rank bookkeeping, not sector estimates or gain
inequalities. Populations and K,Z here are already expanded by any type scale. -/
structure RankData (actions : List Action) (K Z k j : Nat) where
  exactification : Nat
  copies : Nat
  exactification_pos : 0 < exactification
  copies_paid : actualSectorCount actions Z ^ 3 ≤ copies
  pooled_rank :
    (rowTwoActualCatalyst (allEdges actions) K Z ^ k * exactification ^ j * copies ^ (k * j) *
      27 ^ (K * k * j)) * (totalDimension actions ^ (k * j)) ^ 3 <
      actualSectorCount actions Z ^ (3 * k * j) *
        ((2 ^ K * actualSectorCount actions Z) ^ (k * j)) ^ 3

/-- Actual word sectors and conservation imply the numerical recipe premises. -/
def RankData.toPowerRecipe (actions : List Action) (K Z k j : Nat)
    (balance : Balanced (List.replicate (K + Z) 1)
      (List.replicate K 0 ++ List.replicate Z 6) (allEdges actions))
    (data : RankData actions K Z k j) :
    RowTwoPowerRecipe (totalDimension actions) K Z 1 k j where
  sectors := actualSectorCount actions Z
  catalyst := rowTwoActualCatalyst (allEdges actions) K Z
  exactification := data.exactification
  copies := data.copies
  exactification_pos := data.exactification_pos
  copies_paid := data.copies_paid
  coarse_count := by simpa [actualSectorCount] using coarse_actual_total_count actions Z
  profile_count := by
    apply rowTwo_profile_count_to_ratio
    simpa [actualSectorCount, Nat.mul_comm] using sharp_actual_total_count actions K Z balance
  catalyst_charge := by simpa using rowTwo_actualCatalyst_charge (allEdges actions) K Z balance
  pooled_rank := by simpa using data.pooled_rank

/-- No sector-gain, coarse-count, profile-count, reuse, or catalyst-charge
premise remains. Exact pooled-rank bookkeeping is explicit in RankData. -/
theorem actual_action_sourceSide_bound (actions : List Action) (K Z k j : Nat)
    (hK : 0 < K) (hk : 0 < k) (hj : 0 < j)
    (balance : Balanced (List.replicate (K + Z) 1)
      (List.replicate K 0 ++ List.replicate Z 6) (allEdges actions))
    (data : RankData actions K Z k j) :
    2 ^ 96 ≤ totalDimension actions ^ (k * j) := by
  have recipe := RankData.toPowerRecipe actions K Z k j balance data
  have bound := rowTwo_recipe_sourceSide_bound (expandedSplits actions) K Z 1 k j
    hK (by decide) hk hj (by simpa only [expandedSplits_edges] using balance)
    (by simpa only [expandedSplits_dimensions] using recipe)
  simpa only [expandedSplits_dimensions, Nat.one_mul] using bound

end RowTwoSectorProfile
end MatrixDimensionAudit

#print axioms MatrixDimensionAudit.RowTwoSectorProfile.finite_profile_sum
#print axioms MatrixDimensionAudit.RowTwoSectorProfile.sharp_split_count
#print axioms MatrixDimensionAudit.RowTwoSectorProfile.sharp_total_count
#print axioms MatrixDimensionAudit.RowTwoSectorProfile.coarse_total_count
#print axioms MatrixDimensionAudit.RowTwoSectorProfile.sharp_actual_total_count
#print axioms MatrixDimensionAudit.RowTwoSectorProfile.coarse_actual_total_count
#print axioms MatrixDimensionAudit.RowTwoSectorProfile.action_dimension_bound
#print axioms MatrixDimensionAudit.RowTwoSectorProfile.three_orientation_copies_paid
#print axioms MatrixDimensionAudit.RowTwoSectorProfile.actual_action_sourceSide_bound
