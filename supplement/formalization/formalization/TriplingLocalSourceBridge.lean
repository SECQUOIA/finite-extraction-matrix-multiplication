import formalization.TriplingLocalRecipeBridge

namespace MatrixDimensionAudit.TriplingLocalSourceBridge
open OAI.MatrixMultiplication.Foundation
open TensorRankBridge TriplingRestrictionBridge TriplingLocalRecipeBridge
open DependentSeparator SeparatorTensor
open scoped BigOperators

noncomputable section

attribute [local instance] TriplingLocalRecipeBridge.sectorYFinite TriplingLocalRecipeBridge.sectorZFinite

def tripleMatrix {X Y Z X' Y' Z' : Type}
    (A : X' → X → ℚ) (B : Y' → Y → ℚ) (C : Z' → Z → ℚ) :
    ((X' × Y') × Z') → ((X × Y) × Z) → ℚ :=
  fun x u => (A x.1.1 u.1.1 * B x.1.2 u.1.2) * C x.2 u.2

theorem restrict_cyclic {X Y Z X' Y' Z' : Type} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor ℚ X Y Z) (A : X' → X → ℚ) (B : Y' → Y → ℚ) (C : Z' → Z → ℚ) :
    Tensor.restrict B C A (Tensor.cyclic T) = Tensor.cyclic (Tensor.restrict A B C T) := by
  funext y z x
  change (∑ b, ∑ c, ∑ a, B y b * C z c * A x a * T a b c) =
    ∑ a, ∑ b, ∑ c, A x a * B y b * C z c * T a b c
  calc
    _ = ∑ b, ∑ c, ∑ a, A x a * B y b * C z c * T a b c := by
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = ∑ b, ∑ a, ∑ c, A x a * B y b * C z c * T a b c := by
      apply Finset.sum_congr rfl
      intro b _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- Joint restriction matrices transport one cyclic-source decomposition,
without taking a cube of its rank. -/
theorem triple_restrict {X Y Z X' Y' Z' : Type} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor ℚ X Y Z) (A : X' → X → ℚ) (B : Y' → Y → ℚ) (C : Z' → Z → ℚ) :
    Tensor.restrict (tripleMatrix A B C) (tripleMatrix B C A) (tripleMatrix C A B)
      (cyclicTriple ℚ T) = cyclicTriple ℚ (Tensor.restrict A B C T) := by
  have h₁ := restrict_cyclic T A B C
  have h₂ := restrict_cyclic (Tensor.cyclic T) B C A
  unfold cyclicTriple
  rw [← h₁, ← h₂]
  have ho := Tensor.restrict_product
    (fun (x : X' × Y') (u : X × Y) => A x.1 u.1 * B x.2 u.2)
    (fun (y : Y' × Z') (v : Y × Z) => B y.1 v.1 * C y.2 v.2)
    (fun (z : Z' × X') (w : Z × X) => C z.1 w.1 * A z.2 w.2)
    C A B (Tensor.product T (Tensor.cyclic T)) (Tensor.cyclic (Tensor.cyclic T))
  exact ho.trans (congrArg (fun U => Tensor.product U
    (Tensor.restrict C A B (Tensor.cyclic (Tensor.cyclic T))))
    (Tensor.restrict_product A B C B C A T (Tensor.cyclic T)))

def collectCopies {L : Nat} {X Y Z : Type} :
    (((Fin L × X) × (Fin L × Y)) × (Fin L × Z)) →
      (((Fin L × Fin L) × Fin L) × ((X × Y) × Z)) :=
  fun x => (((x.1.1.1, x.1.2.1), x.2.1), ((x.1.1.2, x.1.2.2), x.2.2))

private theorem guarded_product (p q r : Prop) [Decidable p] [Decidable q] [Decidable r]
    (a b c : ℚ) :
    ((if p then a else 0) * (if q then b else 0)) * (if r then c else 0) =
      if p ∧ q ∧ r then (a * b) * c else 0 := by
  by_cases hp : p <;> by_cases hq : q <;> by_cases hr : r <;> simp [hp, hq, hr]

/-- The cyclic triple of ell source-copy sums is a coordinate pullback of
exactly ell³ copies of the original cyclic triple. -/
theorem cyclic_copy_sum {X Y Z : Type} (T : Tensor ℚ X Y Z) (L : Nat) :
    cyclicTriple ℚ (Tensor.directSum (fun _ : Fin L => T)) =
      Tensor.pullback collectCopies collectCopies collectCopies
        (Tensor.directSum (fun _ : (Fin L × Fin L) × Fin L => cyclicTriple ℚ T)) := by
  funext x y z
  have hg :
      ((((x.1.1.1, x.1.2.1), x.2.1) = ((y.1.1.1, y.1.2.1), y.2.1)) ∧
        (((x.1.1.1, x.1.2.1), x.2.1) = ((z.1.1.1, z.1.2.1), z.2.1))) ↔
      (x.1.1.1 = y.1.1.1 ∧ x.1.1.1 = z.1.1.1) ∧
      (z.1.2.1 = x.1.2.1 ∧ z.1.2.1 = y.1.2.1) ∧
      (y.2.1 = z.2.1 ∧ y.2.1 = x.2.1) := by
    simp only [Prod.mk.injEq]
    aesop
  simp only [cyclicTriple, Tensor.product, Tensor.cyclic, Tensor.directSum, Tensor.pullback,
    collectCopies]
  simp only [hg]
  exact guarded_product
    (x.1.1.1 = y.1.1.1 ∧ x.1.1.1 = z.1.1.1)
    (z.1.2.1 = x.1.2.1 ∧ z.1.2.1 = y.1.2.1)
    (y.2.1 = z.2.1 ∧ y.2.1 = x.2.1) _ _ _

theorem cyclic_copy_rank {X Y Z : Type} (T : Tensor ℚ X Y Z) (L R : Nat)
    (h : Tensor.RankAtMost (cyclicTriple ℚ T) R) :
    Tensor.RankAtMost (cyclicTriple ℚ (Tensor.directSum (fun _ : Fin L => T))) (L ^ 3 * R) := by
  have hc := directSum_rankAtMost (fun _ : (Fin L × Fin L) × Fin L => cyclicTriple ℚ T) R
    (fun _ => h)
  have hcard : Fintype.card ((Fin L × Fin L) × Fin L) = L ^ 3 := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    ring
  rw [hcard] at hc
  rw [cyclic_copy_sum]
  exact hc.pullback _ _ _

/-- The input rank certificate is for the actual original convolution source,
before keeping coordinates or applying any separator. -/
theorem matched_triple_rank (r N m R : Nat) (hr : 0 < r)
    (source_rank : Tensor.RankAtMost (cyclicTriple ℚ (Tensor.power (source ℚ r r) N)) R) :
    Tensor.RankAtMost (cyclicTriple ℚ (dependentMatched (Tripling.blocks r r N m))) R := by
  have he : dependentMatched (Tripling.blocks r r N m) = Tensor.pullback id
      (fun y => (Tripling.keptEmbeddingY r r N m hr hr y).val)
      (fun z => (Tripling.keptEmbeddingZ r r N m hr hr z).val)
      (Tensor.power (source ℚ r r) N) := by
    rw [Tripling.matched_from_kept r r N m hr hr]
    rfl
  rw [he, cyclicTriple_pullback]
  exact source_rank.pullback _ _ _

theorem jointFamily_evaluate (r N m aux : Nat) (ε : ℚ) :
    evaluate (jointFamily r N m aux) ε =
      cyclicTriple ℚ (evaluate (dependentFamily (n := aux) (Tripling.blocks r r N m)) ε) := by
  funext x y z
  simp only [evaluate, jointFamily, cyclicTriple, Tensor.product, Tensor.cyclic, Polynomial.eval_mul]

/-- Every nonzero joint sample is an actual restriction costing ell³ source
copies, applied to one cyclic source decomposition of rank R. -/
theorem joint_sample_rank (r N m aux R : Nat) (hr : 0 < r) (ε : ℚ) (hε : ε ≠ 0)
    (source_rank : Tensor.RankAtMost (cyclicTriple ℚ (Tensor.power (source ℚ r r) N)) R) :
    Tensor.RankAtMost (evaluate (jointFamily r N m aux) ε)
      (ell (Tripling.blockCount N m) aux ^ 3 * R) := by
  classical
  let T := dependentMatched (Tripling.blocks r r N m)
  let S := Tensor.directSum (fun _ : Fin (ell (Tripling.blockCount N m) aux) => T)
  let A := liftMatrix (firstCardinal (Tripling.blockCount N m) aux (X := Fin N → Fin r))
  let B := liftMatrix (dependentSecond (n := aux) (Y := Tripling.blockY r r N m) ε)
  let C := liftMatrix (dependentThird (n := aux) (Z := Tripling.blockZ r r N m) ε)
  have hc := cyclic_copy_rank T (ell (Tripling.blockCount N m) aux) R
    (matched_triple_rank r N m R hr source_rank)
  have hp := hc.restrict (tripleMatrix A B C) (tripleMatrix B C A) (tripleMatrix C A B)
  have he := triple_restrict S A B C
  rw [he] at hp
  have hs : Tensor.restrict A B C S =
      evaluate (dependentFamily (n := aux) (Tripling.blocks r r N m)) ε :=
    dependent_restriction _ ε hε
  rw [hs] at hp
  rw [jointFamily_evaluate]
  exact hp

/-- Complete local rank recipe: one source decomposition, all M^(3k) output
copies, ell^(3k) source-copy charge, and one E=3kd+1 joint exactification. -/
theorem actual_local_recipe (r N m aux k R : Nat) (hr : 0 < r)
    (source_rank : Tensor.RankAtMost (cyclicTriple ℚ (Tensor.power (source ℚ r r) N)) R) :
    Tensor.RankAtMost (Tensor.directSum
      (fun _ : Fin k → Index N m => Tensor.power (outputBlock r N aux hr) k))
      ((3 * k * localDegree N m aux + 1) *
        ell (Tripling.blockCount N m) aux ^ (3 * k) * R ^ k) := by
  have h := joint_exactification_rank r N m aux k
    (ell (Tripling.blockCount N m) aux ^ 3 * R) hr
    (fun e => joint_sample_rank r N m aux R hr (node e) (Separator.rationalNode_nonzero e.val) source_rank)
  convert h using 1
  simp only [mul_pow, ← pow_mul]
  ring

/-- Zipping the three words commutes with the cyclic tensor product and power. -/
theorem cyclic_power_reindex {X Y Z : Type} (T : Tensor ℚ X Y Z) (N : Nat) :
    cyclicTriple ℚ (Tensor.power T N) = Tensor.pullback
      (TriplingOrientationBridge.zipCoordinates (fun _ : Fin N => X) (fun _ => Y) (fun _ => Z))
      (TriplingOrientationBridge.zipCoordinates (fun _ : Fin N => Y) (fun _ => Z) (fun _ => X))
      (TriplingOrientationBridge.zipCoordinates (fun _ : Fin N => Z) (fun _ => X) (fun _ => Y))
      (Tensor.power (cyclicTriple ℚ T) N) := by
  funext x y z
  change (∏ i, T (x.1.1 i) (y.1.1 i) (z.1.1 i)) *
    (∏ i, T (z.1.2 i) (x.1.2 i) (y.1.2 i)) * (∏ i, T (y.2 i) (z.2 i) (x.2 i)) =
    ∏ i, (T (x.1.1 i) (y.1.1 i) (z.1.1 i) * T (z.1.2 i) (x.1.2 i) (y.1.2 i)) *
      T (y.2 i) (z.2 i) (x.2 i)
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]

def sourceFull (r : Nat) (hr : 0 < r) : FullTensor ℚ :=
  cyclicConvolution ℚ r (sourceWidth r r) hr (by unfold sourceWidth; omega)

def sourcePowerX (r N : Nat) (hr : 0 < r) :=
  (TriplingOrientationBridge.zipCoordinates (fun _ : Fin N => Fin r)
    (fun _ => Fin (sourceWidth r r)) (fun _ => Fin (r + sourceWidth r r - 1))).trans
    (PowerCoordinateBridge.xCoordinates ℚ (sourceFull r hr) N).symm

def sourcePowerY (r N : Nat) (hr : 0 < r) :=
  (TriplingOrientationBridge.zipCoordinates (fun _ : Fin N => Fin (sourceWidth r r))
    (fun _ => Fin (r + sourceWidth r r - 1)) (fun _ => Fin r)).trans
    (PowerCoordinateBridge.yCoordinates ℚ (sourceFull r hr) N).symm

def sourcePowerZ (r N : Nat) (hr : 0 < r) :=
  (TriplingOrientationBridge.zipCoordinates (fun _ : Fin N => Fin (r + sourceWidth r r - 1))
    (fun _ => Fin r) (fun _ => Fin (sourceWidth r r))).trans
    (PowerCoordinateBridge.zCoordinates ℚ (sourceFull r hr) N).symm

theorem source_power_reindex (r N : Nat) (hr : 0 < r) :
    cyclicTriple ℚ (Tensor.power (source ℚ r r) N) =
      Tensor.pullback (sourcePowerX r N hr) (sourcePowerY r N hr) (sourcePowerZ r N hr)
        ((sourceFull r hr).power N).tensor := by
  rw [cyclic_power_reindex]
  exact (PowerCoordinateBridge.pullback_from_fullPower ℚ (sourceFull r hr) N _ _ _).symm

theorem sourceFull_eq_reset (r : Nat) (hr : 2 ≤ r) :
    sourceFull r (by omega) = resetFactor ℚ false r hr := by
  have hw : sourceWidth r r = 4 * r - 1 := by unfold sourceWidth; omega
  unfold sourceFull resetFactor signedCyclicConvolution
  simp only [Bool.false_eq_true, ↓reduceIte, hw]

/-- The final source premise is the earlier rank bridge's genuine reset tensor
power decomposition. Every count, map, auxiliary factor, and local copy charge
in this endpoint is derived rather than supplied as a numerical assumption. -/
theorem actual_local_recipe_reset (r N m aux k R : Nat) (hr : 2 ≤ r)
    (source_rank : Tensor.RankAtMost ((resetFactor ℚ false r hr).power N).tensor R) :
    Tensor.RankAtMost (Tensor.directSum
      (fun _ : Fin k → Index N m => Tensor.power (outputBlock r N aux (by omega)) k))
      ((3 * k * localDegree N m aux + 1) *
        ell (Tripling.blockCount N m) aux ^ (3 * k) * R ^ k) := by
  have hf := source_rank
  rw [← sourceFull_eq_reset r hr] at hf
  apply actual_local_recipe r N m aux k R (by omega)
  rw [source_power_reindex r N (by omega)]
  exact hf.pullback _ _ _

def poweredBlockX (r N aux k : Nat) (hr : 0 < r) :=
  (Equiv.prodCongr (PowerCoordinateBridge.xCoordinates ℚ (child r N hr) k)
    (Equiv.refl (Fin k → Fin aux × Fin aux))).trans
    (Tensor.directSumPowerEquiv (child r N hr).X (Fin aux × Fin aux) k)
def poweredBlockY (r N aux k : Nat) (hr : 0 < r) :=
  (Equiv.prodCongr (PowerCoordinateBridge.yCoordinates ℚ (child r N hr) k)
    (Equiv.refl (Fin k → Fin aux × Fin aux))).trans
    (Tensor.directSumPowerEquiv (child r N hr).Y (Fin aux × Fin aux) k)
def poweredBlockZ (r N aux k : Nat) (hr : 0 < r) :=
  (Equiv.prodCongr (PowerCoordinateBridge.zCoordinates ℚ (child r N hr) k)
    (Equiv.refl (Fin k → Fin aux × Fin aux))).trans
    (Tensor.directSumPowerEquiv (child r N hr).Z (Fin aux × Fin aux) k)

theorem split_powered_block (r N aux k : Nat) (hr : 0 < r) :
    Tensor.pullback (poweredBlockX r N aux k hr) (poweredBlockY r N aux k hr)
      (poweredBlockZ r N aux k hr) (Tensor.power (outputBlock r N aux hr) k) =
      Tensor.product ((child r N hr).power k).tensor (Tensor.power (auxiliary aux) k) := by
  funext x y z
  change (∏ i, (child r N hr).tensor
    (PowerCoordinateBridge.xCoordinates ℚ (child r N hr) k x.1 i)
    (PowerCoordinateBridge.yCoordinates ℚ (child r N hr) k y.1 i)
    (PowerCoordinateBridge.zCoordinates ℚ (child r N hr) k z.1 i) * auxiliary aux (x.2 i) (y.2 i) (z.2 i)) =
      ((child r N hr).power k).tensor x.1 y.1 z.1 *
        ∏ i, auxiliary aux (x.2 i) (y.2 i) (z.2 i)
  rw [PowerCoordinateBridge.power_tensor_identity]
  exact Finset.prod_mul_distrib

/-- Final separated-factor form: M^(3k) copies of the child power tensored with
the complete auxiliary matrix-tensor power, paid by (3kd+1)ell^(3k)R^k. -/
theorem actual_local_recipe_reset_split (r N m aux k R : Nat) (hr : 2 ≤ r)
    (source_rank : Tensor.RankAtMost ((resetFactor ℚ false r hr).power N).tensor R) :
    Tensor.RankAtMost (Tensor.directSum
      (fun _ : Fin k → Index N m => Tensor.product
        ((child r N (by omega)).power k).tensor (Tensor.power (auxiliary aux) k)))
      ((3 * k * localDegree N m aux + 1) *
        ell (Tripling.blockCount N m) aux ^ (3 * k) * R ^ k) := by
  have h := (actual_local_recipe_reset r N m aux k R hr source_rank).directSum_pullback
    (poweredBlockX r N aux k (by omega)) (poweredBlockY r N aux k (by omega))
    (poweredBlockZ r N aux k (by omega))
  simpa only [split_powered_block] using h

end
end MatrixDimensionAudit.TriplingLocalSourceBridge

#print axioms MatrixDimensionAudit.TriplingLocalSourceBridge.restrict_cyclic
#print axioms MatrixDimensionAudit.TriplingLocalSourceBridge.triple_restrict
#print axioms MatrixDimensionAudit.TriplingLocalSourceBridge.cyclic_copy_sum
#print axioms MatrixDimensionAudit.TriplingLocalSourceBridge.cyclic_copy_rank
#print axioms MatrixDimensionAudit.TriplingLocalSourceBridge.matched_triple_rank
#print axioms MatrixDimensionAudit.TriplingLocalSourceBridge.joint_sample_rank
#print axioms MatrixDimensionAudit.TriplingLocalSourceBridge.actual_local_recipe
#print axioms MatrixDimensionAudit.TriplingLocalSourceBridge.cyclic_power_reindex
#print axioms MatrixDimensionAudit.TriplingLocalSourceBridge.source_power_reindex
#print axioms MatrixDimensionAudit.TriplingLocalSourceBridge.sourceFull_eq_reset
#print axioms MatrixDimensionAudit.TriplingLocalSourceBridge.actual_local_recipe_reset
#print axioms MatrixDimensionAudit.TriplingLocalSourceBridge.split_powered_block
#print axioms MatrixDimensionAudit.TriplingLocalSourceBridge.actual_local_recipe_reset_split
