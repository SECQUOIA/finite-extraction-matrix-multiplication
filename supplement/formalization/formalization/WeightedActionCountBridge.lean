import formalization.MultinomialTypeBoundBridge
import formalization.FlowActionTensorBridge
import formalization.AllRowProfile
import formalization.FamilyScalingBridge

/-! Polynomial-loss lower bounds for actual grouped action sectors. -/
namespace MatrixDimensionAudit.WeightedActionCountBridge
open scoped BigOperators
open GeneralRowSector WeightedSector GeneralFlow AllRowProfile
open FlowActionTensorBridge DeterminantSplitRecipeBridge

/-- The existing finite-sector equivalence identifies the actual action count
with its multinomial coefficient; this is not a cardinality premise. -/
theorem action_count_eq_multinomial (a : Action r) :
    a.count = Nat.multinomial Finset.univ (actionCounts a) := by
  rw [action_sector_count, wordCount_multinomial, ite_eq_left (action_counts_sum a)]

/-- Extend the reviewed weighted bound to total zero. At zero all counts are
zero and both sides are one, regardless of the category weights. -/
theorem weighted_type_lower_bound_nat {α : Type*} [Fintype α] (n w : α → ℕ)
    (occupation : ∀ i, n i * (∑ j, w j) = (∑ j, n j) * w i) :
    (∑ i, w i) ^ (∑ i, n i) ≤
      ((∑ i, n i) + 1) ^ Fintype.card α * Nat.multinomial Finset.univ n *
        (∏ i, w i ^ n i) := by
  classical
  by_cases hN : ∑ i, n i = 0
  · have hn : n = fun _ => 0 := by
      funext i
      have hi : n i ≤ ∑ j, n j :=
        Finset.single_le_sum (fun j _ => Nat.zero_le (n j)) (Finset.mem_univ i)
      simpa [hN] using hi
    simp [hn, Nat.multinomial]
  · exact MultinomialTypeBoundBridge.weighted_type_lower_bound n w
      (Nat.pos_of_ne_zero hN) occupation

/-- The finite depth alphabet enumerates every legal child, in the original
state order. -/
theorem child_sum_nat (a : Action r) (P : ℕ → ℕ) :
    (∑ j, P (depthState a j)) = (a.children.map P).sum := by
  rw [children_ofFn, List.map_ofFn]
  exact (Fin.sum_ofFn (fun j => P (depthState a j))).symm

/-- The finite product is exactly the profile weight of the original expanded
output list. Arbitrary populations outside the legal children are irrelevant. -/
theorem child_product_nat (a : Action r) (P : ℕ → ℕ) :
    (∏ j, P (depthState a j) ^ actionCounts a j) = wordWeight P a.output := by
  rw [Action.output, populationWord_weight, children_ofFn, List.map_ofFn]
  simpa only [actionCounts, Function.comp_def] using (Fin.prod_ofFn
    (fun j => P (depthState a j) ^ a.population (depthState a j))).symm

/-- Exact per-child occupation ratios for arbitrary natural profile weights. -/
def ProportionalNat (a : Action r) (P : ℕ → ℕ) : Prop :=
  ∀ j, actionCounts a j * (∑ i, P (depthState a i)) = a.width * P (depthState a j)

/-- A derived lower bound on the actual retained sector count, including the
zero-width action. No desired type-mass bound is a premise. -/
theorem action_weighted_lower_bound_nat (a : Action r) (P : ℕ → ℕ)
    (occupation : ProportionalNat a P) :
    (∑ j, P (depthState a j)) ^ a.width ≤
      (a.width + 1) ^ (a.h + 1) * a.count *
        (∏ j, P (depthState a j) ^ actionCounts a j) := by
  have h := weighted_type_lower_bound_nat (actionCounts a) (fun j => P (depthState a j))
    (by intro j; simpa only [action_counts_sum] using occupation j)
  simpa only [action_counts_sum, Fintype.card_fin, ← action_count_eq_multinomial a] using h

/-- The same derived inequality with the determinant word-subtype cardinality
spelled out explicitly. -/
theorem action_word_count_lower_bound_nat (a : Action r) (P : ℕ → ℕ)
    (occupation : ProportionalNat a P) :
    (∑ j, P (depthState a j)) ^ a.width ≤
      (a.width + 1) ^ (a.h + 1) * wordCount a.h a.width (actionCounts a) *
        (∏ j, P (depthState a j) ^ actionCounts a j) := by
  simpa only [← action_sector_count a] using action_weighted_lower_bound_nat a P occupation

/-- A harmonic profile converts the total child weight to arity times parent
weight. This holds for any legal width satisfying the identity. -/
theorem action_harmonic_lower_bound_nat (a : Action r) (P : ℕ → ℕ)
    (harmonic : (a.children.map P).sum = (a.h + 1) * P a.x)
    (occupation : ProportionalNat a P) :
    a.dimension * wordWeight P a.input ≤
      (a.width + 1) ^ (a.h + 1) * a.count * wordWeight P a.output := by
  have h := action_weighted_lower_bound_nat a P occupation
  rw [child_sum_nat, harmonic, Nat.mul_pow, child_product_nat] at h
  simpa only [Action.dimension, Action.input, wordWeight_replicate] using h

/-- Exact occupations for the actual integer affine row profile. -/
def ProfileProportional (a : Action r) : Prop :=
  ∀ y ∈ a.children, a.population y * ((a.h + 1) * profile r a.x) =
    a.width * profile r y

theorem profile_proportional_nat (a : Action r) (occupation : ProfileProportional a) :
    ProportionalNat a (profile r) := by
  intro j
  rw [child_sum_nat, a.profile_sum]
  exact occupation _ (depthState_mem a j)

/-- The affine profile identity is proved for every legal split width, so no
maximal-width or harmonicity premise is needed in this specialization. -/
theorem action_profile_lower_bound (a : Action r) (occupation : ProfileProportional a) :
    a.dimension * wordWeight (profile r) a.input ≤
      (a.width + 1) ^ (a.h + 1) * a.count * wordWeight (profile r) a.output :=
  action_harmonic_lower_bound_nat a (profile r) a.profile_sum
    (profile_proportional_nat a occupation)

/-- Explicit polynomial loss, one factor for each actual grouped action. -/
def typeLoss (actions : List (Action r)) : ℕ :=
  (actions.map (fun a => (a.width + 1) ^ (a.h + 1))).prod

theorem typeLoss_pos (actions : List (Action r)) : 0 < typeLoss actions := by
  induction actions with
  | nil => exact Nat.zero_lt_one
  | cons a tail ih => exact Nat.mul_pos (Nat.pow_pos (Nat.succ_pos _)) ih

/-- Multiplying actual action estimates preserves their full histograms. -/
theorem product_profile_lower_bound (actions : List (Action r))
    (occupation : ∀ a ∈ actions, ProfileProportional a) :
    totalDimension actions * wordWeight (profile r) ((allEdges actions).map Edge.src) ≤
      typeLoss actions * totalCount actions *
        wordWeight (profile r) ((allEdges actions).map Edge.dst) := by
  induction actions with
  | nil => exact Nat.le_refl _
  | cons a tail ih =>
    have h := Nat.mul_le_mul (action_profile_lower_bound a (occupation a (by simp)))
      (ih (by intro b hb; exact occupation b (by simp [hb])))
    simpa [totalDimension, totalCount, typeLoss, allEdges, List.flatMap_cons,
      List.map_append, wordWeight, List.prod_append, a.sourceWord, a.targetWord,
      Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h

/-- Exact conservation telescopes the weighted lower bound to the row boundary.
Positivity is derived from the actual affine profile and r≥2. -/
theorem boundary_profile_count_lower_bound (actions : List (Action r)) (hr : 2 ≤ r)
    (i K Z : ℕ)
    (balance : Balanced (List.replicate K i ++ List.replicate Z 1)
      (List.replicate K 0 ++ List.replicate Z (3 * r)) (allEdges actions))
    (occupation : ∀ a ∈ actions, ProfileProportional a) :
    totalDimension actions * (profile r i ^ K * profile r 1 ^ Z) ≤
      typeLoss actions * totalCount actions *
        (profile r 0 ^ K * profile r (3 * r) ^ Z) := by
  have he := product_profile_lower_bound actions occupation
  have hb := multiplicative_balance balance (profile r)
  change wordWeight (profile r) (List.replicate K i ++ List.replicate Z 1) *
      wordWeight (profile r) ((allEdges actions).map Edge.dst) =
    wordWeight (profile r) (List.replicate K 0 ++ List.replicate Z (3*r)) *
      wordWeight (profile r) ((allEdges actions).map Edge.src) at hb
  have hm := Nat.mul_le_mul_left
    (wordWeight (profile r) (List.replicate K i ++ List.replicate Z 1)) he
  have final :
      (totalDimension actions *
        wordWeight (profile r) (List.replicate K i ++ List.replicate Z 1)) *
          wordWeight (profile r) ((allEdges actions).map Edge.src) ≤
      (typeLoss actions * totalCount actions *
        wordWeight (profile r) (List.replicate K 0 ++ List.replicate Z (3*r))) *
          wordWeight (profile r) ((allEdges actions).map Edge.src) := by
    calc
      _ ≤ typeLoss actions * totalCount actions *
          (wordWeight (profile r) (List.replicate K i ++ List.replicate Z 1) *
            wordWeight (profile r) ((allEdges actions).map Edge.dst)) := by
        simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hm
      _ = _ := by rw [hb]; ring
  have hc := Nat.le_of_mul_le_mul_right final
    (profile_word_pos r hr ((allEdges actions).map Edge.src))
  simpa [wordWeight, List.map_append, List.prod_append, wordWeight_replicate] using hc

/-- Reset weights cancel using P_r(3r)=3P_r(1). -/
theorem sharp_profile_count_lower_bound (actions : List (Action r)) (hr : 2 ≤ r)
    (i K Z : ℕ)
    (balance : Balanced (List.replicate K i ++ List.replicate Z 1)
      (List.replicate K 0 ++ List.replicate Z (3 * r)) (allEdges actions))
    (occupation : ∀ a ∈ actions, ProfileProportional a) :
    totalDimension actions * profile r i ^ K ≤
      typeLoss actions * totalCount actions * (profile r 0 ^ K * 3 ^ Z) := by
  have h := boundary_profile_count_lower_bound actions hr i K Z balance occupation
  rw [profile_reset r hr, Nat.mul_pow] at h
  have h' : (totalDimension actions * profile r i ^ K) * profile r 1 ^ Z ≤
      (typeLoss actions * totalCount actions * (profile r 0 ^ K * 3 ^ Z)) *
        profile r 1 ^ Z := by
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h
  exact Nat.le_of_mul_le_mul_right h' (Nat.pow_pos (profile_pos r 1 hr))

/-- The ternary mode estimate is about the actual retained reset words. -/
theorem actual_tripling_lower_bound (Z : ℕ) :
    3 ^ Z ≤ (Z + 1) * GeneralRowSector.triplingCount Z := by
  rw [row_tripling_count]
  exact TriplingSectorModeBridge.mode_average_bound Z

/-- Both the split histogram counts and the reset count are actual cardinalities.
The explicit finite loss is typeLoss*(Z+1). -/
theorem actual_row_count_lower_bound (row : Row r i K) (hr : 2 ≤ r)
    (occupation : ∀ a ∈ row.actions, ProfileProportional a) :
    row.dimension * profile r i ^ K ≤
      (typeLoss row.actions * (row.Z + 1)) * row.count * profile r 0 ^ K := by
  have h := sharp_profile_count_lower_bound row.actions hr i K row.Z row.balance occupation
  have ht := Nat.mul_le_mul_left
    (typeLoss row.actions * totalCount row.actions * profile r 0 ^ K)
    (actual_tripling_lower_bound row.Z)
  calc
    _ ≤ typeLoss row.actions * totalCount row.actions * (profile r 0 ^ K * 3 ^ row.Z) := h
    _ ≤ _ := by
      simpa [Row.count, actualSectorCount, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using ht

/-- The reviewed empirical integer bound also gives exact nonnegative real
weights, so rational profiles need no integrality premise. Zero total counts
are included. -/
theorem weighted_type_lower_bound_real {α : Type*} [Fintype α]
    (n : α → ℕ) (w : α → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (occupation : ∀ i, (n i : ℝ) * (∑ j, w j) = (∑ j, n j : ℕ) * w i) :
    (∑ i, w i) ^ (∑ i, n i) ≤
      (((∑ i, n i) + 1 : ℕ) : ℝ) ^ Fintype.card α *
        (Nat.multinomial Finset.univ n : ℝ) * (∏ i, w i ^ n i) := by
  classical
  by_cases hzero : ∑ i, n i = 0
  · have hn : n = fun _ => 0 := by
      funext i
      have hi : n i ≤ ∑ j, n j :=
        Finset.single_le_sum (fun j _ => Nat.zero_le (n j)) (Finset.mem_univ i)
      simpa [hzero] using hi
    simp [hn, Nat.multinomial]
  · have hN : 0 < ∑ i, n i := Nat.pos_of_ne_zero hzero
    let N := ∑ i, n i
    let S := ∑ i, w i
    let C : ℝ := ((N + 1 : ℕ) : ℝ) ^ Fintype.card α * Nat.multinomial Finset.univ n
    have identity : (∏ i, (n i : ℝ) ^ n i) * S ^ N =
        (N : ℝ) ^ N * (∏ i, w i ^ n i) := by
      calc
        _ = ∏ i, ((n i : ℝ) * S) ^ n i := by
          simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, N]
        _ = ∏ i, ((N : ℝ) * w i) ^ n i := by
          apply Finset.prod_congr rfl
          intro i _
          rw [occupation i]
        _ = _ := by
          simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, N]
    have empirical : (N : ℝ) ^ N ≤ C * (∏ i, (n i : ℝ) ^ n i) := by
      dsimp [N, C]
      exact_mod_cast MultinomialTypeBoundBridge.empirical_type_lower_bound n
    have h : (N : ℝ) ^ N * S ^ N ≤ (N : ℝ) ^ N * (C * ∏ i, w i ^ n i) := by
      calc
        _ ≤ (C * ∏ i, (n i : ℝ) ^ n i) * S ^ N :=
          mul_le_mul_of_nonneg_right empirical (pow_nonneg (Finset.sum_nonneg (fun i _ => hw i)) _)
        _ = C * ((∏ i, (n i : ℝ) ^ n i) * S ^ N) := by ring
        _ = _ := by rw [identity]; ring
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    change S ^ N ≤ C * ∏ i, w i ^ n i
    exact (mul_le_mul_iff_right₀ (pow_pos hNr N)).mp h

/-- A logarithmic version for positive real category weights. -/
theorem weighted_log_multinomial_lower_bound_real {α : Type*} [Fintype α]
    (n : α → ℕ) (w : α → ℝ)
    (hN : 0 < ∑ i, n i) (hw : ∀ i, 0 < w i)
    (occupation : ∀ i, (n i : ℝ) * (∑ j, w j) = (∑ j, n j : ℕ) * w i) :
    (∑ i, n i : ℕ) * Real.log (∑ i, w i) -
        (∑ i, (n i : ℝ) * Real.log (w i)) -
        (Fintype.card α : ℝ) * Real.log (((∑ i, n i) + 1 : ℕ) : ℝ) ≤
      Real.log (Nat.multinomial Finset.univ n : ℝ) := by
  classical
  let N := ∑ i, n i
  let S := ∑ i, w i
  let M := Nat.multinomial Finset.univ n
  have hex : ∃ i, n i ≠ 0 := by
    by_contra hn
    simp only [not_exists, not_not] at hn
    simp [hn] at hN
  obtain ⟨i, hi⟩ := hex
  have hS : 0 < S := (hw i).trans_le
    (Finset.single_le_sum (fun j _ => le_of_lt (hw j)) (Finset.mem_univ i))
  have hMr : (0 : ℝ) < M := by
    exact_mod_cast Nat.multinomial_pos Finset.univ n
  have hpow : ∀ i, (0 : ℝ) < w i ^ n i := fun i => pow_pos (hw i) _
  have hCr : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) ^ Fintype.card α := by positivity
  have hP : 0 < ∏ i, w i ^ n i := Finset.prod_pos (fun i _ => hpow i)
  have hbound : S ^ N ≤ ((N + 1 : ℕ) : ℝ) ^ Fintype.card α * M *
      (∏ i, w i ^ n i) :=
    weighted_type_lower_bound_real n w (fun i => le_of_lt (hw i)) occupation
  have hlog := Real.log_le_log (pow_pos hS N) hbound
  rw [Real.log_mul (ne_of_gt (mul_pos hCr hMr)) (ne_of_gt hP),
    Real.log_mul (ne_of_gt hCr) (ne_of_gt hMr), Real.log_pow, Real.log_pow,
    Real.log_prod (fun i _ => ne_of_gt (hpow i))] at hlog
  simp only [Real.log_pow] at hlog
  dsimp [N, S, M] at hlog
  linarith

/-- Exact real-valued occupation proportions on the complete legal alphabet. -/
def ProportionalReal (a : Action r) (P : ℕ → ℝ) : Prop :=
  ∀ j, (actionCounts a j : ℝ) * (∑ i, P (depthState a i)) =
    (a.width : ℝ) * P (depthState a j)

/-- The actual sector-cardinality lower bound with real or rational profile
weights. Rational weights enter through their exact coercion to the reals. -/
theorem action_weighted_lower_bound_real (a : Action r) (P : ℕ → ℝ)
    (nonnegative : ∀ j, 0 ≤ P (depthState a j))
    (occupation : ProportionalReal a P) :
    (∑ j, P (depthState a j)) ^ a.width ≤
      ((a.width + 1 : ℕ) : ℝ) ^ (a.h + 1) * (a.count : ℝ) *
        (∏ j, P (depthState a j) ^ actionCounts a j) := by
  have h := weighted_type_lower_bound_real (actionCounts a)
    (fun j => P (depthState a j)) nonnegative
    (by intro j; simpa only [action_counts_sum] using occupation j)
  simpa only [action_counts_sum, Fintype.card_fin, ← action_count_eq_multinomial a] using h

/-- A real-valued harmonic profile has child sum d*P(x), with d=h+1.
The conclusion keeps the actual action dimension and sector count. -/
theorem action_harmonic_lower_bound_real (a : Action r) (P : ℕ → ℝ)
    (nonnegative : ∀ j, 0 ≤ P (depthState a j))
    (harmonic : (∑ j, P (depthState a j)) = ((a.h + 1 : ℕ) : ℝ) * P a.x)
    (occupation : ProportionalReal a P) :
    (a.dimension : ℝ) * P a.x ^ a.width ≤
      ((a.width + 1 : ℕ) : ℝ) ^ (a.h + 1) * (a.count : ℝ) *
        (∏ j, P (depthState a j) ^ actionCounts a j) := by
  have h := action_weighted_lower_bound_real a P nonnegative occupation
  rw [harmonic, mul_pow] at h
  simpa only [Action.dimension, Nat.cast_pow] using h

/-- Taking logarithms at actual positive-weight action occupations derives the
local entropy lower bound; no logarithmic estimate is supplied by the caller. -/
theorem action_log_count_lower_bound_real (a : Action r) (P : ℕ → ℝ)
    (positive : ∀ j, 0 < P (depthState a j)) (width_pos : 0 < a.width)
    (occupation : ProportionalReal a P) :
    (a.width : ℝ) * Real.log (∑ j, P (depthState a j)) -
        (∑ j, (actionCounts a j : ℝ) * Real.log (P (depthState a j))) -
        ((a.h + 1 : ℕ) : ℝ) * Real.log ((a.width + 1 : ℕ) : ℝ) ≤
      Real.log (a.count : ℝ) := by
  have h := weighted_log_multinomial_lower_bound_real (actionCounts a)
    (fun j => P (depthState a j)) (by simpa only [action_counts_sum] using width_pos)
    positive (by intro j; simpa only [action_counts_sum] using occupation j)
  simpa only [action_counts_sum, Fintype.card_fin, ← action_count_eq_multinomial a] using h

/-- Exact integer scaling preserves the occupation ratios, including scale zero. -/
theorem scaleAction_profile_proportional (s : ℕ) (a : Action r)
    (occupation : ProfileProportional a) :
    ProfileProportional (FamilyScalingBridge.scaleAction s a) := by
  intro y hy
  have h := occupation y (by simpa only [FamilyScalingBridge.children_scale] using hy)
  change (s * a.population y) * ((a.h + 1) * profile r a.x) =
    (FamilyScalingBridge.scaleAction s a).width * profile r y
  rw [FamilyScalingBridge.width_scale]
  simpa only [Nat.mul_assoc] using congrArg (fun n => s * n) h

/-- The same property holds for all actions of an actual scaled row. -/
theorem scaleRow_profile_proportional (s : ℕ) (row : Row r i K)
    (occupation : ∀ a ∈ row.actions, ProfileProportional a) :
    ∀ a ∈ (FamilyScalingBridge.scaleRow s row).actions, ProfileProportional a := by
  intro a ha
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
  exact scaleAction_profile_proportional s b (occupation b hb)

/-- The degree of the explicit product bound for a fixed list of actions. -/
def lossDegree (actions : List (Action r)) : ℕ :=
  (actions.map (fun a => a.h + 1)).sum

/-- The scaled populations remain in one histogram at each original action. -/
theorem typeLoss_scale_eq (s : ℕ) (actions : List (Action r)) :
    typeLoss (FamilyScalingBridge.scaleActions s actions) =
      (actions.map (fun a => (s * a.width + 1) ^ (a.h + 1))).prod := by
  simp only [typeLoss, FamilyScalingBridge.scaleActions, List.map_map, Function.comp_def]
  apply congrArg List.prod
  apply List.map_congr_left
  intro a _
  rw [FamilyScalingBridge.width_scale]
  rfl

/-- For each fixed row the loss grows at most polynomially with its scale.
The degree and leading bound are explicit finite natural numbers. -/
theorem typeLoss_scale_le (s : ℕ) (actions : List (Action r)) :
    typeLoss (FamilyScalingBridge.scaleActions s actions) ≤
      (s + 1) ^ lossDegree actions * typeLoss actions := by
  rw [typeLoss_scale_eq]
  induction actions with
  | nil => simp [typeLoss, lossDegree]
  | cons a tail ih =>
    have base : s * a.width + 1 ≤ (s + 1) * (a.width + 1) := by nlinarith
    have hp := Nat.pow_le_pow_left base (a.h + 1)
    have h := Nat.mul_le_mul hp ih
    simpa [typeLoss, lossDegree, Nat.pow_add, Nat.mul_pow,
      Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h

/-- This includes the loss of the actual reset-word mode, with one additional
power of s+1. -/
theorem row_loss_scale_le (s : ℕ) (row : Row r i K) :
    typeLoss (FamilyScalingBridge.scaleRow s row).actions *
        ((FamilyScalingBridge.scaleRow s row).Z + 1) ≤
      (s + 1) ^ (lossDegree row.actions + 1) *
        (typeLoss row.actions * (row.Z + 1)) := by
  have hz : s * row.Z + 1 ≤ (s + 1) * (row.Z + 1) := by nlinarith
  have h := Nat.mul_le_mul (typeLoss_scale_le s row.actions) hz
  simpa [FamilyScalingBridge.scaleRow, Nat.pow_succ,
    Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h

/-- Every integer multiple of a seed row has an actual sector count lower
bound, with an explicit polynomial loss rather than a count premise. -/
theorem scaled_row_count_lower_bound (s : ℕ) (row : Row r i K) (hr : 2 ≤ r)
    (occupation : ∀ a ∈ row.actions, ProfileProportional a) :
    row.dimension ^ s * profile r i ^ (s * K) ≤
      ((s + 1) ^ (lossDegree row.actions + 1) *
        (typeLoss row.actions * (row.Z + 1))) *
          (FamilyScalingBridge.scaleRow s row).count * profile r 0 ^ (s * K) := by
  have h := actual_row_count_lower_bound (FamilyScalingBridge.scaleRow s row) hr
    (scaleRow_profile_proportional s row occupation)
  rw [FamilyScalingBridge.row_dimension_scale] at h
  exact h.trans (Nat.mul_le_mul_right _
    (Nat.mul_le_mul_right _ (row_loss_scale_le s row)))


#print axioms action_count_eq_multinomial
#print axioms weighted_type_lower_bound_nat
#print axioms child_sum_nat
#print axioms child_product_nat
#print axioms ProportionalNat
#print axioms action_weighted_lower_bound_nat
#print axioms action_word_count_lower_bound_nat
#print axioms action_harmonic_lower_bound_nat
#print axioms ProfileProportional
#print axioms profile_proportional_nat
#print axioms action_profile_lower_bound
#print axioms typeLoss
#print axioms typeLoss_pos
#print axioms product_profile_lower_bound
#print axioms boundary_profile_count_lower_bound
#print axioms sharp_profile_count_lower_bound
#print axioms actual_tripling_lower_bound
#print axioms actual_row_count_lower_bound
#print axioms weighted_type_lower_bound_real
#print axioms weighted_log_multinomial_lower_bound_real
#print axioms ProportionalReal
#print axioms action_weighted_lower_bound_real
#print axioms action_harmonic_lower_bound_real
#print axioms action_log_count_lower_bound_real
#print axioms scaleAction_profile_proportional
#print axioms scaleRow_profile_proportional
#print axioms lossDegree
#print axioms typeLoss_scale_eq
#print axioms typeLoss_scale_le
#print axioms row_loss_scale_le
#print axioms scaled_row_count_lower_bound

end MatrixDimensionAudit.WeightedActionCountBridge
