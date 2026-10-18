import formalization.TensorResourcePoolingBridge

namespace MatrixDimensionAudit.FamilyPolynomialAssemblyBridge
open OAI.MatrixMultiplication.Foundation
open TensorResourcePoolingBridge SeparatorTensor
open scoped BigOperators

noncomputable section
variable {I : Type} [Fintype I] [DecidableEq I]

/-- Tensor product of an actual finite dependent family in function coordinates. -/
def tensorFamily {K : Type} [CommSemiring K] {X Y Z : I → Type}
    (T : ∀ i, Tensor K (X i) (Y i) (Z i)) : Tensor K (∀ i, X i) (∀ i, Y i) (∀ i, Z i) :=
  fun x y z => ∏ i, T i (x i) (y i) (z i)

def familyMatrix {X X' : I → Type} (A : ∀ i, X' i → X i → ℚ) :
    (∀ i, X' i) → (∀ i, X i) → ℚ := fun x u => ∏ i, A i (x i) (u i)

omit [DecidableEq I] in
theorem resourceFamily_tensor (A : I → TensorRankBridge.FullTensor ℚ) :
    (resourceFamily A).tensor = tensorFamily (fun i => (A i).tensor) := rfl

/-- The product of the local restriction matrices is an actual restriction
matrix for the complete family, not a product of local rank bounds. -/
theorem family_restriction {X Y Z X' Y' Z' : I → Type}
    [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] [∀ i, Fintype (Z i)]
    (T : ∀ i, Tensor ℚ (X i) (Y i) (Z i))
    (A : ∀ i, X' i → X i → ℚ) (B : ∀ i, Y' i → Y i → ℚ) (C : ∀ i, Z' i → Z i → ℚ) :
    Tensor.restrict (familyMatrix A) (familyMatrix B) (familyMatrix C) (tensorFamily T) =
      tensorFamily (fun i => Tensor.restrict (A i) (B i) (C i) (T i)) := by
  classical
  funext x y z
  change (∑ u : ∀ i, X i, ∑ v : ∀ i, Y i, ∑ w : ∀ i, Z i,
    (∏ i, A i (x i) (u i)) * (∏ i, B i (y i) (v i)) *
      (∏ i, C i (z i) (w i)) * ∏ i, T i (u i) (v i) (w i)) =
    ∏ i, ∑ u : X i, ∑ v : Y i, ∑ w : Z i, A i (x i) u * B i (y i) v * C i (z i) w * T i u v w
  simp_rw [← Finset.prod_mul_distrib]
  calc
    _ = ∑ p : ((∀ i, X i) × (∀ i, Y i)) × (∀ i, Z i),
        ∏ i, A i (x i) (p.1.1 i) * B i (y i) (p.1.2 i) *
          C i (z i) (p.2 i) * T i (p.1.1 i) (p.1.2 i) (p.2 i) := by
      simp only [Fintype.sum_prod_type]
    _ = ∑ p : ∀ i, (X i × Y i) × Z i,
        ∏ i, A i (x i) (p i).1.1 * B i (y i) (p i).1.2 *
          C i (z i) (p i).2 * T i (p i).1.1 (p i).1.2 (p i).2 :=
      (zipThree X Y Z).sum_comp (fun (p : ∀ i, (X i × Y i) × Z i) =>
        ∏ i, A i (x i) (p i).1.1 * B i (y i) (p i).1.2 *
          C i (z i) (p i).2 * T i (p i).1.1 (p i).1.2 (p i).2)
    _ = ∏ i, ∑ p : (X i × Y i) × Z i,
        A i (x i) p.1.1 * B i (y i) p.1.2 * C i (z i) p.2 * T i p.1.1 p.1.2 p.2 :=
      (Fintype.prod_sum (fun (i : I) (p : (X i × Y i) × Z i) =>
        A i (x i) p.1.1 * B i (y i) p.1.2 * C i (z i) p.2 * T i p.1.1 p.1.2 p.2)).symm
    _ = _ := by simp only [Fintype.sum_prod_type]

omit [DecidableEq I] in
/-- Regroup the local copy coordinates into one actual copy word. -/
theorem family_copies {X Y Z : I → Type} (L : I → Nat)
    (T : ∀ i, Tensor ℚ (X i) (Y i) (Z i)) :
    tensorFamily (fun i => Tensor.directSum (fun _ : Fin (L i) => T i)) =
      Tensor.pullback (splitPairs _ _) (splitPairs _ _) (splitPairs _ _)
        (Tensor.directSum (fun _ : ∀ i, Fin (L i) => tensorFamily T)) := by
  classical
  funext x y z
  simp only [tensorFamily, Tensor.directSum, Tensor.pullback, splitPairs, Equiv.coe_fn_mk]
  simp only [Fintype.prod_ite_zero, forall_and, ← funext_iff]
  rfl

/-- Reindex the finite source coordinates of a restriction by equivalences. -/
theorem restriction_reindex {X Y Z X₁ Y₁ Z₁ X' Y' Z' : Type}
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype X₁] [Fintype Y₁] [Fintype Z₁]
    (T : Tensor ℚ X₁ Y₁ Z₁) (ex : X ≃ X₁) (ey : Y ≃ Y₁) (ez : Z ≃ Z₁)
    (A : X' → X → ℚ) (B : Y' → Y → ℚ) (C : Z' → Z → ℚ) :
    Tensor.restrict A B C (Tensor.pullback ex ey ez T) =
      Tensor.restrict (fun x u => A x (ex.symm u)) (fun y v => B y (ey.symm v))
        (fun z w => C z (ez.symm w)) T := by
  funext x y z
  change (∑ u, ∑ v, ∑ w, A x u * B y v * C z w * T (ex u) (ey v) (ez w)) = _
  have hs := ex.sum_comp (fun u => ∑ v, ∑ w,
    A x (ex.symm u) * B y v * C z w * T u (ey v) (ez w))
  simp only [Equiv.symm_apply_apply] at hs
  rw [hs]
  apply Finset.sum_congr rfl
  intro u _
  have ht := ey.sum_comp (fun v => ∑ w,
    A x (ex.symm u) * B y (ey.symm v) * C z w * T u v (ez w))
  simp only [Equiv.symm_apply_apply] at ht
  rw [ht]
  apply Finset.sum_congr rfl
  intro v _
  have hw := ez.sum_comp (fun w =>
    A x (ex.symm u) * B y (ey.symm v) * C z (ez.symm w) * T u v w)
  simpa only [Equiv.symm_apply_apply] using hw

/-- The joint sample matrix acts on one copy word and one original source word. -/
def jointMatrix {X X' : I → Type} (L : I → Nat)
    (A : ∀ i, X' i → (Fin (L i) × X i) → ℚ) :
    (∀ i, X' i) → ((∀ i, Fin (L i)) × (∀ i, X i)) → ℚ :=
  fun x u => ∏ i, A i (x i) (u.1 i, u.2 i)

/-- Combine genuine local sample restriction identities into one actual
restriction of the complete source family. -/
theorem joint_sample_restriction {X Y Z X' Y' Z' : I → Type}
    [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] [∀ i, Fintype (Z i)]
    (L : I → Nat) (T : ∀ i, Tensor ℚ (X i) (Y i) (Z i))
    (P : ∀ i, Tensor (Polynomial ℚ) (X' i) (Y' i) (Z' i))
    (A : ∀ i, ℚ → X' i → (Fin (L i) × X i) → ℚ)
    (B : ∀ i, ℚ → Y' i → (Fin (L i) × Y i) → ℚ)
    (C : ∀ i, ℚ → Z' i → (Fin (L i) × Z i) → ℚ)
    (ε : ℚ)
    (local_maps : ∀ i, Tensor.restrict (A i ε) (B i ε) (C i ε)
      (Tensor.directSum (fun _ : Fin (L i) => T i)) = evaluate (P i) ε) :
    Tensor.restrict (jointMatrix L (fun i => A i ε)) (jointMatrix L (fun i => B i ε))
      (jointMatrix L (fun i => C i ε))
      (Tensor.directSum (fun _ : ∀ i, Fin (L i) => tensorFamily T)) =
      tensorFamily (fun i => evaluate (P i) ε) := by
  have hf := family_restriction
    (fun i => Tensor.directSum (fun _ : Fin (L i) => T i))
    (fun i => A i ε) (fun i => B i ε) (fun i => C i ε)
  rw [family_copies, restriction_reindex] at hf
  simp only [local_maps] at hf
  exact hf

/-- A concrete local polynomial restriction: all three matrices and their
coefficient identity are retained, with no local rank premise. -/
structure LocalRestrictions {X Y Z X' Y' Z' : I → Type}
    [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] [∀ i, Fintype (Z i)]
    (L : I → Nat) (T : ∀ i, Tensor ℚ (X i) (Y i) (Z i))
    (P : ∀ i, Tensor (Polynomial ℚ) (X' i) (Y' i) (Z' i)) where
  first : ∀ i, ℚ → X' i → (Fin (L i) × X i) → ℚ
  second : ∀ i, ℚ → Y' i → (Fin (L i) × Y i) → ℚ
  third : ∀ i, ℚ → Z' i → (Fin (L i) × Z i) → ℚ
  identity : ∀ ε, ε ≠ 0 → ∀ i,
    Tensor.restrict (first i ε) (second i ε) (third i ε)
      (Tensor.directSum (fun _ : Fin (L i) => T i)) = evaluate (P i) ε

/-- Apply output-coordinate maps to every polynomial coefficient before the
families are assembled. The original copy charge and sample witnesses remain. -/
def LocalRestrictions.pullback {X Y Z X' Y' Z' X'' Y'' Z'' : I → Type}
    [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] [∀ i, Fintype (Z i)]
    {L : I → Nat} {T : ∀ i, Tensor ℚ (X i) (Y i) (Z i)}
    {P : ∀ i, Tensor (Polynomial ℚ) (X' i) (Y' i) (Z' i)}
    (maps : LocalRestrictions L T P) (fx : ∀ i, X'' i → X' i)
    (fy : ∀ i, Y'' i → Y' i) (fz : ∀ i, Z'' i → Z' i) :
    LocalRestrictions L T (fun i => Tensor.pullback (fx i) (fy i) (fz i) (P i)) where
  first := fun i ε x => maps.first i ε (fx i x)
  second := fun i ε y => maps.second i ε (fy i y)
  third := fun i ε z => maps.third i ε (fz i z)
  identity := fun ε hε i => congrArg (Tensor.pullback (fx i) (fy i) (fz i)) (maps.identity ε hε i)

/-- The joint sample pays for the actual copy-word cardinality, using one
rank certificate for the complete original source family. -/
theorem joint_sample_rank {X Y Z X' Y' Z' : I → Type}
    [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] [∀ i, Fintype (Z i)]
    (L : I → Nat) (T : ∀ i, Tensor ℚ (X i) (Y i) (Z i))
    (P : ∀ i, Tensor (Polynomial ℚ) (X' i) (Y' i) (Z' i))
    (maps : LocalRestrictions L T P) (ε : ℚ) (hε : ε ≠ 0) (R : Nat)
    (source_rank : Tensor.RankAtMost (tensorFamily T) R) :
    Tensor.RankAtMost (tensorFamily (fun i => evaluate (P i) ε)) ((∏ i, L i) * R) := by
  classical
  have hc := directSum_rankAtMost
    (fun _ : ∀ i, Fin (L i) => tensorFamily T) R (fun _ => source_rank)
  have hcard : Fintype.card (∀ i, Fin (L i)) = ∏ i, L i := by
    simp only [Fintype.card_pi, Fintype.card_fin]
  rw [hcard] at hc
  have hp := hc.restrict (jointMatrix L (fun i => maps.first i ε))
    (jointMatrix L (fun i => maps.second i ε)) (jointMatrix L (fun i => maps.third i ε))
  rw [joint_sample_restriction L T P maps.first maps.second maps.third ε (maps.identity ε hε)] at hp
  exact hp

omit [DecidableEq I] in
theorem evaluate_family {X Y Z : I → Type}
    (P : ∀ i, Tensor (Polynomial ℚ) (X i) (Y i) (Z i)) (ε : ℚ) :
    evaluate (tensorFamily P) ε = tensorFamily (fun i => evaluate (P i) ε) := by
  funext x y z
  change (∏ i, P i (x i) (y i) (z i)).eval ε = ∏ i, (P i (x i) (y i) (z i)).eval ε
  exact Polynomial.eval_prod Finset.univ (fun i => P i (x i) (y i) (z i)) ε

omit [DecidableEq I] in
/-- The degree charge is the sum of the actual coefficient-degree bounds. -/
theorem family_degree {X Y Z : I → Type}
    (P : ∀ i, Tensor (Polynomial ℚ) (X i) (Y i) (Z i)) (d : I → Nat)
    (hd : ∀ i x y z, (P i x y z).natDegree ≤ d i)
    (x : ∀ i, X i) (y : ∀ i, Y i) (z : ∀ i, Z i) :
    (tensorFamily P x y z).natDegree ≤ ∑ i, d i := by
  apply (Polynomial.natDegree_prod_le Finset.univ (fun i => P i (x i) (y i) (z i))).trans
  exact Finset.sum_le_sum (fun i _ => hd i (x i) (y i) (z i))

theorem evaluate_power {X Y Z : Type} (P : Tensor (Polynomial ℚ) X Y Z) (k : Nat) (ε : ℚ) :
    evaluate (Tensor.power P k) ε = Tensor.power (evaluate P ε) k := by
  funext x y z
  exact Polynomial.eval_prod Finset.univ (fun i => P (x i) (y i) (z i)) ε

/-- The single exactification is also an explicit restriction identity. Its
samples are the complete assembled polynomial family at the same parameter. -/
theorem assembled_exactification {X Y Z : I → Type}
    [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] [∀ i, Fintype (Z i)]
    [∀ i, DecidableEq (X i)] [∀ i, DecidableEq (Y i)] [∀ i, DecidableEq (Z i)]
    (P : ∀ i, Tensor (Polynomial ℚ) (X i) (Y i) (Z i)) (d : I → Nat)
    (hd : ∀ i x y z, (P i x y z).natDegree ≤ d i) (k : Nat) :
    Tensor.restrict (foldMatrix (exactWeight (k * ∑ i, d i)))
      (foldMatrix (fun _ : Fin (k * (∑ i, d i) + 1) => 1))
      (foldMatrix (fun _ : Fin (k * (∑ i, d i) + 1) => 1))
      (Tensor.directSum (fun e : Fin (k * (∑ i, d i) + 1) =>
        Tensor.power (tensorFamily (fun i => evaluate (P i) (node e))) k)) =
      Tensor.power (tensorFamily (fun i => evaluate (P i) 0)) k := by
  classical
  have he := tensor_exactification (Tensor.power (tensorFamily P) k) (k * ∑ i, d i)
    (tensor_power_degree (tensorFamily P) k (∑ i, d i) (family_degree P d hd))
  simpa only [evaluate_power, evaluate_family] using he

/-- Assemble all local polynomial maps before exactifying. There is one shared
parameter and E=k*sum(d_i)+1, rather than a product of local E_i. -/
theorem joint_family_power_rank {X Y Z X' Y' Z' : I → Type}
    [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] [∀ i, Fintype (Z i)]
    [∀ i, Fintype (X' i)] [∀ i, Fintype (Y' i)] [∀ i, Fintype (Z' i)]
    (L : I → Nat) (T : ∀ i, Tensor ℚ (X i) (Y i) (Z i))
    (P : ∀ i, Tensor (Polynomial ℚ) (X' i) (Y' i) (Z' i))
    (maps : LocalRestrictions L T P) (d : I → Nat)
    (hd : ∀ i x y z, (P i x y z).natDegree ≤ d i) (k R : Nat)
    (source_rank : Tensor.RankAtMost (tensorFamily T) R) :
    Tensor.RankAtMost (Tensor.power (tensorFamily (fun i => evaluate (P i) 0)) k)
      ((k * (∑ i, d i) + 1) * (∏ i, L i) ^ k * R ^ k) := by
  classical
  have hp := tensor_power_exactification_rank (tensorFamily P) k (∑ i, d i) ((∏ i, L i) * R)
    (family_degree P d hd) (fun e => by
      rw [evaluate_family]
      exact joint_sample_rank L T P maps (node e) (Separator.rationalNode_nonzero e.val) R source_rank)
  rw [evaluate_family] at hp
  convert hp using 1
  rw [mul_pow]
  ring

omit [DecidableEq I] in
/-- Actual coefficient pullbacks can be applied to all local constant tensors
without decomposing any intermediate output. -/
theorem family_pullback {X Y Z X' Y' Z' : I → Type}
    (T : ∀ i, Tensor ℚ (X i) (Y i) (Z i))
    (fx : ∀ i, X' i → X i) (fy : ∀ i, Y' i → Y i) (fz : ∀ i, Z' i → Z i) :
    Tensor.pullback (fun x i => fx i (x i)) (fun y i => fy i (y i))
      (fun z i => fz i (z i)) (tensorFamily T) =
      tensorFamily (fun i => Tensor.pullback (fx i) (fy i) (fz i) (T i)) := rfl

/-- Concrete local witnesses for an arbitrary finite family of the checked
 dependent separators. Every polynomial map is supplied by its actual matrices. -/
def dependentSeparatorMaps {M : I → Nat} {X : I → Type}
    {Y Z : ∀ i, Fin (M i) → Type}
    [∀ i, Fintype (X i)] [∀ i h, Fintype (Y i h)] [∀ i h, Fintype (Z i h)]
    (aux : I → Nat) (T : ∀ i h, Tensor ℚ (X i) (Y i h) (Z i h)) :
    LocalRestrictions (fun i => ell (M i) (aux i))
      (fun i => DependentSeparator.dependentMatched (T i))
      (fun i => DependentSeparator.dependentFamily (n := aux i) (T i)) := by
  classical
  exact {
    first := fun i _ => liftMatrix (firstCardinal (M i) (aux i) (X := X i))
    second := fun i ε => liftMatrix (DependentSeparator.dependentSecond (n := aux i) (Y := Y i) ε)
    third := fun i ε => liftMatrix (DependentSeparator.dependentThird (n := aux i) (Z := Z i) ε)
    identity := fun ε hε i => DependentSeparator.dependent_restriction (T i) ε hε }

/-- A concrete finite family of actual separators uses one pooled input rank
and one interpolation at the sum of its local degrees. -/
theorem actual_dependent_separator_family_rank {M : I → Nat} {X : I → Type}
    {Y Z : ∀ i, Fin (M i) → Type}
    [∀ i, Fintype (X i)] [∀ i h, Fintype (Y i h)] [∀ i h, Fintype (Z i h)]
    (aux : I → Nat) (T : ∀ i h, Tensor ℚ (X i) (Y i h) (Z i h)) (k R : Nat)
    (source_rank : Tensor.RankAtMost
      (tensorFamily (fun i => DependentSeparator.dependentMatched (T i))) R) :
    Tensor.RankAtMost (Tensor.power
      (tensorFamily (fun i => DependentSeparator.dependentTarget (n := aux i) (T i))) k)
      ((k * (∑ i, min (M i - 1) (aux i - 1)) + 1) *
        (∏ i, ell (M i) (aux i)) ^ k * R ^ k) := by
  classical
  have hp := joint_family_power_rank (fun i => ell (M i) (aux i))
    (fun i => DependentSeparator.dependentMatched (T i))
    (fun i => DependentSeparator.dependentFamily (n := aux i) (T i))
    (dependentSeparatorMaps aux T) (fun i => min (M i - 1) (aux i - 1))
    (fun i => DependentSeparator.dependent_degree (T i)) k R source_rank
  simpa only [DependentSeparator.dependent_constant] using hp

end
end MatrixDimensionAudit.FamilyPolynomialAssemblyBridge

#print axioms MatrixDimensionAudit.FamilyPolynomialAssemblyBridge.tensorFamily
#print axioms MatrixDimensionAudit.FamilyPolynomialAssemblyBridge.familyMatrix
#print axioms MatrixDimensionAudit.FamilyPolynomialAssemblyBridge.resourceFamily_tensor
#print axioms MatrixDimensionAudit.FamilyPolynomialAssemblyBridge.family_restriction
#print axioms MatrixDimensionAudit.FamilyPolynomialAssemblyBridge.family_copies
#print axioms MatrixDimensionAudit.FamilyPolynomialAssemblyBridge.restriction_reindex
#print axioms MatrixDimensionAudit.FamilyPolynomialAssemblyBridge.jointMatrix
#print axioms MatrixDimensionAudit.FamilyPolynomialAssemblyBridge.joint_sample_restriction
#print axioms MatrixDimensionAudit.FamilyPolynomialAssemblyBridge.LocalRestrictions
#print axioms MatrixDimensionAudit.FamilyPolynomialAssemblyBridge.LocalRestrictions.pullback
#print axioms MatrixDimensionAudit.FamilyPolynomialAssemblyBridge.joint_sample_rank
#print axioms MatrixDimensionAudit.FamilyPolynomialAssemblyBridge.evaluate_family
#print axioms MatrixDimensionAudit.FamilyPolynomialAssemblyBridge.family_degree
#print axioms MatrixDimensionAudit.FamilyPolynomialAssemblyBridge.evaluate_power
#print axioms MatrixDimensionAudit.FamilyPolynomialAssemblyBridge.assembled_exactification
#print axioms MatrixDimensionAudit.FamilyPolynomialAssemblyBridge.joint_family_power_rank
#print axioms MatrixDimensionAudit.FamilyPolynomialAssemblyBridge.family_pullback
#print axioms MatrixDimensionAudit.FamilyPolynomialAssemblyBridge.dependentSeparatorMaps
#print axioms MatrixDimensionAudit.FamilyPolynomialAssemblyBridge.actual_dependent_separator_family_rank
#print axioms MatrixDimensionAudit.FamilyPolynomialAssemblyBridge.LocalRestrictions.mk
#print axioms MatrixDimensionAudit.FamilyPolynomialAssemblyBridge.LocalRestrictions.first
#print axioms MatrixDimensionAudit.FamilyPolynomialAssemblyBridge.LocalRestrictions.second
#print axioms MatrixDimensionAudit.FamilyPolynomialAssemblyBridge.LocalRestrictions.third
#print axioms MatrixDimensionAudit.FamilyPolynomialAssemblyBridge.LocalRestrictions.identity
