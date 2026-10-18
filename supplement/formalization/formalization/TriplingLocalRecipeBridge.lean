import formalization.TriplingSectorAlignmentBridge

namespace MatrixDimensionAudit.TriplingLocalRecipeBridge
open OAI.MatrixMultiplication.Foundation
open TensorRankBridge TriplingRestrictionBridge PowerCoordinateBridge TriplingOrientationBridge
open TriplingSectorAlignmentBridge DependentSeparator SeparatorTensor
open scoped BigOperators

noncomputable section

local instance sectorYFinite (r b N m : Nat) (w : Word N m) : Fintype (sectorY r b N m w) := by
  unfold sectorY
  infer_instance

local instance sectorZFinite (r b N m : Nat) (w : Word N m) : Fintype (sectorZ r b N m w) := by
  unfold sectorZ
  infer_instance

abbrev Index (N m : Nat) := (Fin (Tripling.blockCount N m) × Fin (Tripling.blockCount N m)) ×
  Fin (Tripling.blockCount N m)

abbrev word₁ {N m : Nat} (h : Index N m) := Tripling.blockWord N m h.1.1
abbrev word₂ {N m : Nat} (h : Index N m) := Tripling.blockWord N m h.1.2
abbrev word₃ {N m : Nat} (h : Index N m) := Tripling.blockWord N m h.2

def child (r N : Nat) (hr : 0 < r) := (cyclicConvolution ℚ r r hr hr).power N

def blockX (r N m : Nat) (hr : 0 < r) (h : Index N m) :=
  (mixedX r r N m (word₁ h) (word₂ h) (word₃ h)).trans (commonFullX ℚ r N m hr (word₁ h))
def blockY (r N m : Nat) (hr : 0 < r) (h : Index N m) :=
  (mixedY r r N m (word₁ h) (word₂ h) (word₃ h)).trans (commonFullY ℚ r N m hr (word₁ h))
def blockZ (r N m : Nat) (hr : 0 < r) (h : Index N m) :=
  (mixedZ r r N m (word₁ h) (word₂ h) (word₃ h)).trans (commonFullZ ℚ r N m hr (word₁ h))

def normalizeWord {N m : Nat} (r : Nat) (w : Word N m) (x : Fin N → Fin r) :=
  fun i => normalizeFirst r (w.val i) (x i)

abbrev SepX (r N m : Nat) := Fin (Tripling.blockCount N m) × (Fin N → Fin r)
abbrev SepY (r N m aux : Nat) := Fin aux × Sigma (Tripling.blockY r r N m)
abbrev SepZ (r N m aux : Nat) := Fin aux × Sigma (Tripling.blockZ r r N m)

def separated (r N m aux : Nat) : Tensor ℚ (SepX r N m) (SepY r N m aux) (SepZ r N m aux) :=
  dependentTarget (n := aux) (Tripling.blocks r r N m)

/-- The complete auxiliary factor is the cubic matrix multiplication tensor. -/
def auxiliary (aux : Nat) : Tensor ℚ (Fin aux × Fin aux) (Fin aux × Fin aux) (Fin aux × Fin aux) :=
  Tensor.matrixCoefficients (Fin aux) (Fin aux) (Fin aux)

def outputBlock (r N aux : Nat) (hr : 0 < r) :=
  Tensor.product (child r N hr).tensor (auxiliary aux)

def output (r N m aux : Nat) (hr : 0 < r) :=
  Tensor.directSum (fun _ : Index N m => outputBlock r N aux hr)

/-- Maps from the uniform direct-sum coordinates to the full separator triple.
Every auxiliary index is retained; all three sector labels are independent. -/
def sourceX (r N m aux : Nat) (hr : 0 < r)
    (x : Index N m × ((child r N hr).X × (Fin aux × Fin aux))) :
    ((SepX r N m × SepY r N m aux) × SepZ r N m aux) :=
  let q := (blockX r N m hr x.1).symm x.2.1
  (((x.1.1.1, normalizeWord r (word₁ x.1) q.1.1), (x.2.2.2, ⟨x.1.1.2, q.1.2⟩)),
    (x.2.2.1, ⟨x.1.2, q.2⟩))

def sourceY (r N m aux : Nat) (hr : 0 < r)
    (y : Index N m × ((child r N hr).Y × (Fin aux × Fin aux))) :
    ((SepY r N m aux × SepZ r N m aux) × SepX r N m) :=
  let q := (blockY r N m hr y.1).symm y.2.1
  (((y.2.2.2, ⟨y.1.1.1, q.1.1⟩), (y.2.2.1, ⟨y.1.1.2, q.1.2⟩)),
    (y.1.2, normalizeWord r (word₃ y.1) q.2))

def sourceZ (r N m aux : Nat) (hr : 0 < r)
    (z : Index N m × ((child r N hr).Z × (Fin aux × Fin aux))) :
    ((SepZ r N m aux × SepX r N m) × SepY r N m aux) :=
  let q := (blockZ r N m hr z.1).symm z.2.1
  (((z.2.2.1, ⟨z.1.1.1, q.1.1⟩), (z.1.1.2, normalizeWord r (word₂ z.1) q.1.2)),
    (z.2.2.2, ⟨z.1.2, q.2⟩))

private theorem normalized_blocks (r N m : Nat) (h : Fin (Tripling.blockCount N m))
    (x : Fin N → Fin r) (y : Tripling.blockY r r N m h) (z : Tripling.blockZ r r N m h) :
    Tripling.blocks r r N m h (normalizeWord r (Tripling.blockWord N m h) x) y z =
      normalizedSector ℚ r r N m (Tripling.blockWord N m h) x y z := by
  exact Finset.prod_congr rfl (fun i _ => block_normalized ℚ r r _ _ _ _)

private theorem separated_normalized_same (r N m aux : Nat)
    (h : Fin (Tripling.blockCount N m)) (x : Fin N → Fin r)
    (y : Tripling.blockY r r N m h) (z : Tripling.blockZ r r N m h) (a b : Fin aux) :
    separated r N m aux (h, normalizeWord r (Tripling.blockWord N m h) x)
      (a, ⟨h, y⟩) (b, ⟨h, z⟩) =
      if a = b then normalizedSector ℚ r r N m (Tripling.blockWord N m h) x y z else 0 := by
  change dependentTarget _ _ _ _ = _
  rw [dependentTarget_same]
  by_cases hab : a = b
  · simp only [hab, ↓reduceIte]
    exact normalized_blocks r N m h x y z
  · simp only [hab, ↓reduceIte]

private theorem dot_cycle_factorization (aux : Nat) (a b c : ℚ)
    (x y z : Fin aux × Fin aux) :
    ((if y.2 = z.1 then a else 0) * (if x.2 = y.1 then b else 0)) *
      (if z.2 = x.1 then c else 0) = (a * b * c) * auxiliary aux x y z := by
  by_cases hx : x.2 = y.1 <;> by_cases hy : y.2 = z.1 <;> by_cases hz : z.2 = x.1 <;>
    simp [auxiliary, Tensor.matrixCoefficients, hx, hy, hz]

/-- All matching-index coefficients agree, with the full auxiliary matrix tensor. -/
theorem matching_coefficient (r N m aux : Nat) (hr : 0 < r) (h : Index N m)
    (x : (child r N hr).X) (y : (child r N hr).Y) (z : (child r N hr).Z)
    (ax ay az : Fin aux × Fin aux) :
    cyclicTriple ℚ (separated r N m aux) (sourceX r N m aux hr (h, (x, ax)))
      (sourceY r N m aux hr (h, (y, ay))) (sourceZ r N m aux hr (h, (z, az))) =
      outputBlock r N aux hr (x, ax) (y, ay) (z, az) := by
  let a := (blockX r N m hr h).symm x
  let b := (blockY r N m hr h).symm y
  let c := (blockZ r N m hr h).symm z
  have hm : mixedSector ℚ r r N m (word₁ h) (word₂ h) (word₃ h) a b c =
      (child r N hr).tensor x y z := by
    have he := congrFun (congrFun (congrFun
      (mixed_square_fullPower ℚ r N m hr (word₁ h) (word₂ h) (word₃ h)) a) b) c
    change mixedSector ℚ r r N m (word₁ h) (word₂ h) (word₃ h) a b c =
      (child r N hr).tensor ((blockX r N m hr h) a)
        ((blockY r N m hr h) b) ((blockZ r N m hr h) c) at he
    have hx : (blockX r N m hr h) a = x := (blockX r N m hr h).apply_symm_apply x
    have hy : (blockY r N m hr h) b = y := (blockY r N m hr h).apply_symm_apply y
    have hz : (blockZ r N m hr h) c = z := (blockZ r N m hr h).apply_symm_apply z
    rw [hx, hy, hz] at he
    exact he
  change (separated r N m aux
      (h.1.1, normalizeWord r (word₁ h) a.1.1) (ay.2, ⟨h.1.1, b.1.1⟩) (az.1, ⟨h.1.1, c.1.1⟩) *
    separated r N m aux
      (h.1.2, normalizeWord r (word₂ h) c.1.2) (ax.2, ⟨h.1.2, a.1.2⟩) (ay.1, ⟨h.1.2, b.1.2⟩)) *
    separated r N m aux
      (h.2, normalizeWord r (word₃ h) b.2) (az.2, ⟨h.2, c.2⟩) (ax.1, ⟨h.2, a.2⟩) =
      (child r N hr).tensor x y z * auxiliary aux ax ay az
  rw [separated_normalized_same, separated_normalized_same, separated_normalized_same]
  calc
    _ = mixedSector ℚ r r N m (word₁ h) (word₂ h) (word₃ h) a b c * auxiliary aux ax ay az :=
      dot_cycle_factorization aux _ _ _ ax ay az
    _ = _ := congrArg (fun t => t * auxiliary aux ax ay az) hm

private theorem separated_support (r N m aux : Nat) (x : SepX r N m)
    (y : SepY r N m aux) (z : SepZ r N m aux) (hn : separated r N m aux x y z ≠ 0) :
    x.1 = y.2.1 ∧ x.1 = z.2.1 := by
  by_cases h : x.1 = y.2.1 ∧ x.1 = z.2.1 ∧ y.1 = z.1
  · exact ⟨h.1, h.2.1⟩
  · simp [separated, dependentTarget, h] at hn

private theorem source_support (r N m aux : Nat) (hr : 0 < r)
    (x : Index N m × ((child r N hr).X × (Fin aux × Fin aux)))
    (y : Index N m × ((child r N hr).Y × (Fin aux × Fin aux)))
    (z : Index N m × ((child r N hr).Z × (Fin aux × Fin aux)))
    (hn : cyclicTriple ℚ (separated r N m aux) (sourceX r N m aux hr x)
      (sourceY r N m aux hr y) (sourceZ r N m aux hr z) ≠ 0) :
    x.1 = y.1 ∧ x.1 = z.1 := by
  have hs := mul_ne_zero_iff.mp hn
  have hs' := mul_ne_zero_iff.mp hs.1
  have h₁ := separated_support r N m aux _ _ _ hs'.1
  have h₂ := separated_support r N m aux _ _ _ hs'.2
  have h₃ := separated_support r N m aux _ _ _ hs.2
  change x.1.1.1 = y.1.1.1 ∧ x.1.1.1 = z.1.1.1 at h₁
  change z.1.1.2 = x.1.1.2 ∧ z.1.1.2 = y.1.1.2 at h₂
  change y.1.2 = z.1.2 ∧ y.1.2 = x.1.2 at h₃
  exact ⟨Prod.ext (Prod.ext h₁.1 (h₂.1.symm.trans h₂.2)) h₃.2.symm,
    Prod.ext (Prod.ext h₁.2 h₂.1.symm) (h₃.2.symm.trans h₃.1)⟩

/-- Simultaneous full direct-sum assembly: all M³ independent blocks survive,
and their complete cyclic auxiliary dot factors form the matrix tensor. -/
theorem full_constant_restriction (r N m aux : Nat) (hr : 0 < r) :
    Tensor.pullback (sourceX r N m aux hr) (sourceY r N m aux hr) (sourceZ r N m aux hr)
      (cyclicTriple ℚ (separated r N m aux)) = output r N m aux hr := by
  funext x y z
  by_cases h : x.1 = y.1 ∧ x.1 = z.1
  · rcases x with ⟨i, x⟩
    rcases y with ⟨j, y⟩
    rcases z with ⟨k, z⟩
    obtain ⟨rfl, rfl⟩ := h
    simpa only [Tensor.pullback, output, Tensor.directSum, true_and, ite_true, ↓reduceIte] using
      matching_coefficient r N m aux hr i x.1 y.1 z.1 x.2 y.2 z.2
  · change cyclicTriple ℚ (separated r N m aux) _ _ _ =
      if x.1 = y.1 ∧ x.1 = z.1 then _ else 0
    simp only [h, ↓reduceIte]
    by_contra hn
    exact h (source_support r N m aux hr x y z hn)

/-- Genuine decompositions transport through the complete constant tensor maps. -/
theorem output_rank (r N m aux R : Nat) (hr : 0 < r)
    (decomposition : Tensor.RankAtMost (cyclicTriple ℚ (separated r N m aux)) R) :
    Tensor.RankAtMost (output r N m aux hr) R := by
  rw [← full_constant_restriction r N m aux hr]
  exact decomposition.pullback _ _ _

def projectionMatrix {X X' : Type} (f : X' → X) : X' → X → ℚ := by
  classical
  exact fun x' x => if x = f x' then 1 else 0

private theorem projectionMatrix_restrict {X Y Z X' Y' Z' : Type}
    [Fintype X] [Fintype Y] [Fintype Z]
    (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z) (T : Tensor ℚ X Y Z) :
    Tensor.restrict (projectionMatrix fx) (projectionMatrix fy) (projectionMatrix fz) T =
      Tensor.pullback fx fy fz T := by
  classical
  exact (Tensor.pullback_eq_restrict fx fy fz T).symm

/-- The full sum identity is an ordinary linear restriction with three explicit
Kronecker delta matrices, rather than a numerical tensor-rank assertion. -/
theorem full_constant_linear_restriction (r N m aux : Nat) (hr : 0 < r) :
    Tensor.restrict (projectionMatrix (sourceX r N m aux hr))
      (projectionMatrix (sourceY r N m aux hr)) (projectionMatrix (sourceZ r N m aux hr))
      (cyclicTriple ℚ (separated r N m aux)) = output r N m aux hr := by
  rw [projectionMatrix_restrict]
  exact full_constant_restriction r N m aux hr

theorem index_card (N m : Nat) : Fintype.card (Index N m) = (N.choose m * 2 ^ (N - m)) ^ 3 := by
  have h : Tripling.blockCount N m = N.choose m * 2 ^ (N - m) := by
    unfold Tripling.blockCount
    exact TriplingSectorCountBridge.count_eq_choose N m
  simp only [Index, Fintype.card_prod, Fintype.card_fin, h]
  ring

theorem powered_index_card (N m k : Nat) :
    Fintype.card (Fin k → Index N m) = (N.choose m * 2 ^ (N - m)) ^ (3 * k) := by
  rw [Fintype.card_fun, Fintype.card_fin, index_card, ← pow_mul]

/-- Complete powers preserve the full word of independent sector triples. -/
theorem full_power_restriction (r N m aux k : Nat) (hr : 0 < r) :
    Tensor.pullback
      (fun x i => sourceX r N m aux hr (x i))
      (fun y i => sourceY r N m aux hr (y i))
      (fun z i => sourceZ r N m aux hr (z i))
      (Tensor.power (cyclicTriple ℚ (separated r N m aux)) k) =
      Tensor.power (output r N m aux hr) k := by
  funext x y z
  change (∏ i, cyclicTriple ℚ (separated r N m aux)
    (sourceX r N m aux hr (x i)) (sourceY r N m aux hr (y i)) (sourceZ r N m aux hr (z i))) =
      ∏ i, output r N m aux hr (x i) (y i) (z i)
  apply Finset.prod_congr rfl
  intro i _
  exact congrFun (congrFun (congrFun (full_constant_restriction r N m aux hr) (x i)) (y i)) (z i)

/-- An actual decomposition of the powered separated tensor gives the complete
direct sum of powered output blocks, with M^(3k) actual summand indices. -/
theorem powered_output_rank (r N m aux k R : Nat) (hr : 0 < r)
    (decomposition : Tensor.RankAtMost (Tensor.power (cyclicTriple ℚ (separated r N m aux)) k) R) :
    Tensor.RankAtMost (Tensor.directSum
      (fun _ : Fin k → Index N m => Tensor.power (outputBlock r N aux hr) k)) R := by
  have h := decomposition.pullback
    (fun (x : Fin k → Index N m × ((child r N hr).X × (Fin aux × Fin aux))) i => sourceX r N m aux hr (x i))
    (fun (y : Fin k → Index N m × ((child r N hr).Y × (Fin aux × Fin aux))) i => sourceY r N m aux hr (y i))
    (fun (z : Fin k → Index N m × ((child r N hr).Z × (Fin aux × Fin aux))) i => sourceZ r N m aux hr (z i))
  rw [full_power_restriction] at h
  exact h.directSum_const_of_power

/-- One polynomial parameter is shared by all three oriented separator factors. -/
def jointFamily (r N m aux : Nat) :=
  let P := dependentFamily (n := aux) (Tripling.blocks r r N m)
  Tensor.product (Tensor.product P (Tensor.cyclic P)) (Tensor.cyclic (Tensor.cyclic P))

def localDegree (N m aux : Nat) := min (Tripling.blockCount N m - 1) (aux - 1)

theorem jointFamily_degree (r N m aux : Nat) (x : (SepX r N m × SepY r N m aux) × SepZ r N m aux)
    (y : (SepY r N m aux × SepZ r N m aux) × SepX r N m)
    (z : (SepZ r N m aux × SepX r N m) × SepY r N m aux) :
    (jointFamily r N m aux x y z).natDegree ≤ 3 * localDegree N m aux := by
  let P := dependentFamily (n := aux) (Tripling.blocks r r N m)
  have hd : ∀ x y z, (P x y z).natDegree ≤ localDegree N m aux := dependent_degree _
  have hd' : ∀ x y z, (Tensor.cyclic P x y z).natDegree ≤ localDegree N m aux :=
    fun x y z => hd z x y
  have hd'' : ∀ x y z, (Tensor.cyclic (Tensor.cyclic P) x y z).natDegree ≤ localDegree N m aux :=
    fun x y z => hd y z x
  have h := tensor_product_degree (Tensor.product P (Tensor.cyclic P))
    (Tensor.cyclic (Tensor.cyclic P)) (localDegree N m aux + localDegree N m aux)
    (localDegree N m aux) (tensor_product_degree P (Tensor.cyclic P) _ _ hd hd') hd'' x y z
  exact h.trans (by omega)

theorem jointFamily_constant (r N m aux : Nat) :
    evaluate (jointFamily r N m aux) 0 = cyclicTriple ℚ (separated r N m aux) := by
  let P := dependentFamily (n := aux) (Tripling.blocks r r N m)
  have he : evaluate (jointFamily r N m aux) 0 = cyclicTriple ℚ (evaluate P 0) := by
    funext x y z
    simp only [evaluate, jointFamily, P, cyclicTriple, Tensor.product, Tensor.cyclic,
      Polynomial.eval_mul]
  rw [he]
  change cyclicTriple ℚ (evaluate (dependentFamily (n := aux) (Tripling.blocks r r N m)) 0) = _
  rw [dependent_constant]
  rfl

/-- Joint exactification uses E=3kd+1 evaluations. Its premise is an actual
decomposition of each joint evaluation; source-to-evaluation maps are separate. -/
theorem joint_exactification_rank (r N m aux k R : Nat) (hr : 0 < r)
    (samples : ∀ e : Fin (k * (3 * localDegree N m aux) + 1),
      Tensor.RankAtMost (evaluate (jointFamily r N m aux) (node e)) R) :
    Tensor.RankAtMost (Tensor.directSum
      (fun _ : Fin k → Index N m => Tensor.power (outputBlock r N aux hr) k))
      ((k * (3 * localDegree N m aux) + 1) * R ^ k) := by
  classical
  apply powered_output_rank r N m aux k _ hr
  rw [← jointFamily_constant r N m aux]
  exact tensor_power_exactification_rank (jointFamily r N m aux) k _ R
    (jointFamily_degree r N m aux) samples

end
end MatrixDimensionAudit.TriplingLocalRecipeBridge

#print axioms MatrixDimensionAudit.TriplingLocalRecipeBridge.matching_coefficient
#print axioms MatrixDimensionAudit.TriplingLocalRecipeBridge.full_constant_restriction
#print axioms MatrixDimensionAudit.TriplingLocalRecipeBridge.output_rank
#print axioms MatrixDimensionAudit.TriplingLocalRecipeBridge.full_constant_linear_restriction
#print axioms MatrixDimensionAudit.TriplingLocalRecipeBridge.index_card
#print axioms MatrixDimensionAudit.TriplingLocalRecipeBridge.powered_index_card
#print axioms MatrixDimensionAudit.TriplingLocalRecipeBridge.full_power_restriction
#print axioms MatrixDimensionAudit.TriplingLocalRecipeBridge.powered_output_rank
#print axioms MatrixDimensionAudit.TriplingLocalRecipeBridge.jointFamily_degree
#print axioms MatrixDimensionAudit.TriplingLocalRecipeBridge.jointFamily_constant
#print axioms MatrixDimensionAudit.TriplingLocalRecipeBridge.joint_exactification_rank
