import formalization.ScaledFamilyGainLimitBridge
import formalization.SuppliedRelativeExponentLimitBridge

/-! Actual all-row families give the ordinary arithmetic exponent bound 9/4. -/
namespace MatrixDimensionAudit.FamilyRelativeExponentLimitBridge
open scoped BigOperators Topology
open Filter GeneralFlow GeneralRowSector AllRowProfile FamilyScalingBridge
open FlowActionTensorBridge LedgerRelationPackingBridge GlobalFamilySampleBridge
open FamilyTypeGainBridge ScaledFamilyGainLimitBridge SuppliedRelativeExponentLimitBridge
open OAI.MatrixMultiplication.Arithmetic
noncomputable section

theorem row_relations_length_scale (s : Nat) (negative : Bool) (r : Nat) (hr : 2 ≤ r)
    (actions : List (Action r)) (Z : Nat) :
    (rowRelations negative r hr (scaleActions s actions) (s * Z)).length =
      (rowRelations negative r hr actions Z).length := by
  simp [rowRelations, scaleActions]

theorem lower_relations_length_scale (s depth : Nat) (rows : LowerRows K n) :
    (lowerRelations depth (scaleLowerRows s rows)).length =
      (lowerRelations depth rows).length := by
  induction rows generalizing depth with
  | nil => rfl
  | cons row tail ih =>
    simp only [scaleLowerRows, lowerRelations, List.length_append]
    rw [ih]
    congr 1
    exact row_relations_length_scale s _ _ _ row.actions row.Z

theorem family_relations_length_scale (s : Nat) (family : Family n K) :
    (familyRelations (scaleFamily s family)).length =
      (familyRelations family).length := by
  simp only [familyRelations, scaleFamily, List.length_append]
  rw [lower_relations_length_scale]
  congr 1
  exact row_relations_length_scale s _ _ _ family.top.actions family.top.Z

theorem family_separators_length (family : Family n K) :
    (familySeparators family).length = (familyRelations family).length := by
  have h := congrArg List.length (family_block_list family)
  simpa only [List.length_map] using h.symm

theorem family_separators_length_scale (s : Nat) (family : Family n K) :
    (familySeparators (scaleFamily s family)).length =
      (familySeparators family).length := by
  rw [family_separators_length, family_separators_length, family_relations_length_scale]

theorem separator_product_doubled_upper (ss : List FreeAuxiliaryBridge.Separator) :
    (ss.map (fun s => s.blocks + s.blocks - 1)).prod ≤
      2 ^ ss.length * FreeAuxiliaryBridge.blockCount ss := by
  induction ss with
  | nil => simp [FreeAuxiliaryBridge.blockCount]
  | cons s ss ih =>
    change (s.blocks + s.blocks - 1) * _ ≤
      2 ^ (ss.length + 1) * (s.blocks * FreeAuxiliaryBridge.blockCount ss)
    calc
      _ ≤ (2 * s.blocks) * (2 ^ ss.length * FreeAuxiliaryBridge.blockCount ss) :=
        Nat.mul_le_mul (by omega) ih
      _ = _ := by rw [pow_succ]; ring

theorem family_copies_upper (family : Family n K) :
    familyCopies family ≤ 8 ^ (familyRelations family).length * family.count ^ 3 := by
  rw [family_copies_formula]
  have h := Nat.pow_le_pow_left (separator_product_doubled_upper (familySeparators family)) 3
  rw [Nat.mul_pow, ← Nat.pow_mul, Nat.mul_comm _ 3, Nat.pow_mul] at h
  norm_num at h
  rw [family_separators_length, family_separator_count] at h
  exact h

theorem family_copies_bounds (family : Family n K) :
    family.count ^ 3 ≤ familyCopies family ∧
      familyCopies family ≤ 8 ^ (familyRelations family).length * family.count ^ 3 :=
  ⟨SuppliedGlobalRestrictionBridge.copies_paid family, family_copies_upper family⟩
def copyOverhead (family : Family n K) : ℝ :=
  Real.log (familyCopies family : ℝ) - 3 * Real.log (family.count : ℝ)

theorem copyOverhead_bounds (family : Family n K) :
    0 ≤ copyOverhead family ∧
      copyOverhead family ≤ 3 * (familyRelations family).length * Real.log 2 := by
  have hM : 0 < (family.count : ℝ) := by
    exact_mod_cast SuppliedGlobalRestrictionBridge.count_pos family
  have hL : 0 < (familyCopies family : ℝ) := by
    exact_mod_cast SuppliedGlobalRestrictionBridge.copies_pos family
  have hlo : (family.count : ℝ)^3 ≤ (familyCopies family : ℝ) := by
    exact_mod_cast SuppliedGlobalRestrictionBridge.copies_paid family
  have hup : (familyCopies family : ℝ) ≤
      8 ^ (familyRelations family).length * (family.count : ℝ)^3 := by
    exact_mod_cast family_copies_upper family
  have hlolog := Real.log_le_log (pow_pos hM 3) hlo
  have huplog := Real.log_le_log hL hup
  rw [Real.log_pow] at hlolog
  rw [Real.log_mul (pow_ne_zero _ (by norm_num : (8 : ℝ) ≠ 0))
    (pow_ne_zero _ (ne_of_gt hM)), Real.log_pow, Real.log_pow] at huplog
  have h8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2^3 by norm_num, Real.log_pow]
    norm_num
  rw [h8] at huplog
  norm_num at hlolog huplog
  unfold copyOverhead
  constructor <;> nlinarith

theorem scaled_copyOverhead_tendsto (family : Family n K) (hK : 0 < K) :
    Tendsto (fun s : ℕ => copyOverhead (scaleFamily s family) / ((s : ℝ) * K))
      atTop (𝓝 0) := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hconstant : Tendsto
      (fun s : ℕ => (3 * (familyRelations family).length * Real.log 2) /
        ((s : ℝ) * K)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_mul_const hKr)
  apply squeeze_zero' _ _ hconstant
  · filter_upwards [] with s
    exact div_nonneg (copyOverhead_bounds (scaleFamily s family)).1 (by positivity)
  · filter_upwards [] with s
    have h := (copyOverhead_bounds (scaleFamily s family)).2
    rw [family_relations_length_scale] at h
    exact div_le_div_of_nonneg_right h (by positivity)


/-- The already proved actual normalized log gain is the supplied relative
constructor's gain divided by the same scaled injection count. -/
theorem normalizedLogGain_eq_gain_div (family : Family n K) (s : ℕ) :
    normalizedLogGain family s = gain (scaleFamily s family) / ((s*K : ℕ) : ℝ) := by
  have hH : (0 : ℝ) < ((2^(s*K) * (scaleFamily s family).count : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (Nat.pow_pos (by decide : 0 < 2))
      (SuppliedGlobalRestrictionBridge.count_pos (scaleFamily s family))
  have hD : (0 : ℝ) < (scaleFamily s family).dimension := by
    exact_mod_cast SuppliedGlobalRestrictionBridge.dimension_pos (scaleFamily s family)
  unfold normalizedLogGain gain
  rw [Real.log_div (ne_of_gt hH) (ne_of_gt hD), log_output_base]

/-- This gain limit concerns actual legal families, rather than a hypothesized
entropy value. The seed's proportions come from the occupation construction. -/
theorem scaled_gain_div_tendsto (family : Family n K)
    (occupation : familyProportional family) (hK : 0 < K) :
    Tendsto (fun s : ℕ => gain (scaleFamily s family) / ((s*K : ℕ) : ℝ)) atTop
      (𝓝 (Real.log (ScalarProfileGrowthBridge.profile (n+2) (n+2)))) := by
  exact (tendsto_congr' (Eventually.of_forall (normalizedLogGain_eq_gain_div family))).mp
    (normalizedLogGain_tendsto family occupation hK)

theorem scaled_gain_eventually_pos (family : Family n K)
    (occupation : familyProportional family) (hK : 0 < K) :
    ∀ᶠ s : ℕ in atTop, 0 < gain (scaleFamily s family) := by
  have hF : 0 < Real.log (ScalarProfileGrowthBridge.profile (n+2) (n+2)) :=
    ScalarProfileGrowthBridge.log_profile_pos _ (by omega)
  have hevent := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)).eventually_lt
    (scaled_gain_div_tendsto family occupation hK) hF
  filter_upwards [eventually_ge_atTop 1, hevent] with s hs hg
  have hN : (0 : ℝ) < ((s*K : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos (by omega : 0 < s) hK
  have h := mul_pos hg hN
  simpa only [div_mul_cancel₀ _ (ne_of_gt hN)] using h

/-- After division by the scaled injection count, the actual source-rank
charge has its literal constant limit; the local copy overhead vanishes. -/
theorem scaled_numerator_div_tendsto (family : Family n K) (hK : 0 < K) :
    Tendsto (fun s : ℕ =>
      (3 * ((s*K : ℕ) : ℝ) * Real.log ((2*(n+2)-1 : ℕ) : ℝ) +
        copyOverhead (scaleFamily s family)) / ((s*K : ℕ) : ℝ)) atTop
      (𝓝 (3 * Real.log ((2*(n+2)-1 : ℕ) : ℝ))) := by
  have hh := scaled_copyOverhead_tendsto family hK
  have h := (tendsto_const_nhds (x := 3 * Real.log ((2*(n+2)-1 : ℕ) : ℝ))).add hh
  simp only [add_zero] at h
  apply (tendsto_congr' ?_).mpr h
  filter_upwards [eventually_ge_atTop 1] with s hs
  have hN : ((s*K : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (Nat.mul_pos (by omega : 0<s) hK)
  push_cast
  push_cast at hN
  field_simp

/-- The supplied relative exponent of actual scaled families converges to the
manuscript's scalar exponent. All local copies remain charged at finite scale. -/
theorem scaled_limitingExponent_tendsto (family : Family n K)
    (occupation : familyProportional family) (hK : 0 < K) :
    Tendsto (fun s : ℕ => limitingExponent (scaleFamily s family)) atTop
      (𝓝 (ScalarProfileGrowthBridge.tau (n+2))) := by
  have hF : Real.log (ScalarProfileGrowthBridge.profile (n+2) (n+2)) ≠ 0 :=
    ne_of_gt (ScalarProfileGrowthBridge.log_profile_pos _ (by omega))
  have h := (scaled_numerator_div_tendsto family hK).div
    (scaled_gain_div_tendsto family occupation hK) hF
  have hU : (((2*(n+2)-1 : ℕ) : ℝ)) = 2*((n+2 : ℕ) : ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2*(n+2))]
    push_cast
    ring
  rw [hU] at h
  change Tendsto _ atTop (𝓝 (ScalarProfileGrowthBridge.tau (n+2))) at h
  apply (tendsto_congr' ?_).mpr h
  filter_upwards [eventually_ge_atTop 1] with s hs
  have hN : ((s*K : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (Nat.mul_pos (by omega : 0<s) hK)
  change limitingExponent (scaleFamily s family) =
    ((3 * ((s*K : ℕ) : ℝ) * Real.log (2*((n+2 : ℕ) : ℝ)-1) +
      copyOverhead (scaleFamily s family)) / ((s*K : ℕ) : ℝ)) /
      (gain (scaleFamily s family) / ((s*K : ℕ) : ℝ))
  rw [div_div_div_cancel_right₀ hN]
  unfold limitingExponent copyOverhead
  congr 1
  rw [← hU]
  ring

/-- Actual legal families, exactification, serial reuse, and pooled execution
bound the ordinary arithmetic exponent by each finite scalar profile exponent. -/
theorem omega_le_tau_cutoff (n : ℕ) :
    omega ℚ ≤ ScalarProfileGrowthBridge.tau (n+2) := by
  obtain ⟨K, hK, family, occupation⟩ := exists_proportional_family n
  apply ge_of_tendsto (scaled_limitingExponent_tendsto family occupation hK)
  filter_upwards [scaled_gain_eventually_pos family occupation hK] with s hs
  exact omega_le_limitingExponent (scaleFamily s family) hs

theorem omega_le_tau (a : ℕ) (ha : 2 ≤ a) :
    omega ℚ ≤ ScalarProfileGrowthBridge.tau a := by
  have h := omega_le_tau_cutoff (a-2)
  simpa only [Nat.sub_add_cancel ha] using h

/-- The ordinary rational arithmetic matrix multiplication exponent is at most
9/4. The scalar limit and the actual algorithm construction are both proved. -/
theorem omega_le_nine_fourths : omega ℚ ≤ (9/4 : ℝ) := by
  apply ge_of_tendsto ScalarProfileGrowthBridge.tau_tendsto
  filter_upwards [eventually_ge_atTop 2] with a ha
  exact omega_le_tau a ha

/-- Library admissibility includes arbitrarily small positive exponent slack;
this does not assert one finite algorithm attaining an exact n^(9/4) cost. -/
theorem nine_fourths_admissible : AdmissibleExponent ℚ (9/4 : ℝ) :=
  admissibleExponent_iff_omega_le.mpr omega_le_nine_fourths

/-- Explicit meaning of the endpoint: each positive slack has one constant
bounding correct division-free rational arithmetic programs at every size. -/
theorem algorithms_with_exponent_slack (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      ∃ P : MatrixAlgorithm ℚ m m m, P.Correct ∧
        (P.cost : ℝ) ≤ C * (m : ℝ)^((9/4 : ℝ)+ε) :=
  nine_fourths_admissible ε hε

#print axioms row_relations_length_scale
#print axioms lower_relations_length_scale
#print axioms family_relations_length_scale
#print axioms family_separators_length
#print axioms family_separators_length_scale
#print axioms separator_product_doubled_upper
#print axioms family_copies_upper
#print axioms family_copies_bounds
#print axioms copyOverhead
#print axioms copyOverhead_bounds
#print axioms scaled_copyOverhead_tendsto
#print axioms normalizedLogGain_eq_gain_div
#print axioms scaled_gain_div_tendsto
#print axioms scaled_gain_eventually_pos
#print axioms scaled_numerator_div_tendsto
#print axioms scaled_limitingExponent_tendsto
#print axioms omega_le_tau_cutoff
#print axioms omega_le_tau
#print axioms omega_le_nine_fourths
#print axioms nine_fourths_admissible
#print axioms algorithms_with_exponent_slack

end
end MatrixDimensionAudit.FamilyRelativeExponentLimitBridge
