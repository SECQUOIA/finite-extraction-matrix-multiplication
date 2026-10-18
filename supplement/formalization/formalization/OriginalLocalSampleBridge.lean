import formalization.FamilyPolynomialAssemblyBridge
import formalization.FlowActionTensorBridge

namespace MatrixDimensionAudit.OriginalLocalSampleBridge
open OAI.MatrixMultiplication.Foundation
open TensorRankBridge TriplingRestrictionBridge TriplingLocalRecipeBridge TriplingLocalSourceBridge
open TensorResourcePoolingBridge FamilyPolynomialAssemblyBridge DependentSeparator SeparatorTensor
open scoped BigOperators

noncomputable section
attribute [local instance] TriplingLocalRecipeBridge.sectorYFinite TriplingLocalRecipeBridge.sectorZFinite

/-- One local sample witness uses the frozen finite-family interface at Unit. -/
abbrev SampleMaps {X Y Z X' Y' Z' : Type} [Fintype X] [Fintype Y] [Fintype Z]
    (L : Nat) (T : Tensor ℚ X Y Z) (P : Tensor (Polynomial ℚ) X' Y' Z') :=
  LocalRestrictions (I := Unit) (fun _ => L) (fun _ => T) (fun _ => P)

/-- Lift a local matrix along an actual equivalence of copy labels. -/
def copyMatrix {J K X X' : Type} [DecidableEq K] (e : J ≃ K) (A : X' → X → ℚ) :
    (J × X') → (K × X) → ℚ := fun x u => if u.1 = e x.1 then A x.2 u.2 else 0

theorem copy_restriction {J K X Y Z X' Y' Z' : Type}
    [Fintype J] [Fintype K] [DecidableEq J] [DecidableEq K]
    [Fintype X] [Fintype Y] [Fintype Z]
    (e : J ≃ K) (T : Tensor ℚ X Y Z)
    (A : X' → X → ℚ) (B : Y' → Y → ℚ) (C : Z' → Z → ℚ) :
    Tensor.restrict (copyMatrix e A) (copyMatrix e B) (copyMatrix e C)
      (Tensor.directSum (fun _ : K => T)) =
      Tensor.directSum (fun _ : J => Tensor.restrict A B C T) := by
  classical
  funext x y z
  simp only [Tensor.restrict, copyMatrix, Tensor.directSum, Fintype.sum_prod_type,
    mul_ite, ite_mul, ite_and, Finset.sum_ite_irrel]
  by_cases hxy : x.1 = y.1 <;> by_cases hxz : x.1 = z.1 <;>
    by_cases hyz : y.1 = z.1 <;> simp_all [eq_comm]

theorem projection_restriction {X Y Z X' Y' Z' : Type}
    [Fintype X] [Fintype Y] [Fintype Z]
    (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z) (T : Tensor ℚ X Y Z) :
    Tensor.restrict (projectionMatrix fx) (projectionMatrix fy) (projectionMatrix fz) T =
      Tensor.pullback fx fy fz T := by
  classical
  exact (Tensor.pullback_eq_restrict fx fy fz T).symm

/-- Three independent local copy labels are enumerated by Fin(L³). -/
def cubicCopies (L : Nat) : ((Fin L × Fin L) × Fin L) ≃ Fin (L ^ 3) :=
  (Fintype.equivFin _).trans (finCongr (by
    simp only [Fintype.card_prod, Fintype.card_fin]
    ring))

/-- Cyclic tensoring of an actual original-source restriction, followed by a
source-coordinate pullback, remains a single explicit restriction. -/
def matchedMatrix {X Y Z X' Y' Z' U : Type}
    [Fintype X] [Fintype Y] [Fintype Z]
    (A : X' → X → ℚ) (B : Y' → Y → ℚ) (C : Z' → Z → ℚ)
    (f : ((X × Y) × Z) → U) :=
  Tensor.composeRestrictionMatrix (tripleMatrix A B C) (projectionMatrix f)

set_option maxHeartbeats 1000000 in
/-- General cyclic separator pipeline with all original-source maps retained.
The source identification and matched restriction are coefficient identities. -/
def cyclicSeparatorMaps {M aux : Nat} {X Y Z X₀ Xr Yr Zr : Type}
    {BY BZ : Fin M → Type}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X₀]
    [Fintype Xr] [Fintype Yr] [Fintype Zr]
    [∀ j, Fintype (BY j)] [∀ j, Fintype (BZ j)]
    (T : Tensor ℚ X Y Z) (R : Tensor ℚ Xr Yr Zr)
    (blocks : ∀ j, Tensor ℚ X₀ (BY j) (BZ j))
    (A : X₀ → X → ℚ) (B : (Sigma BY) → Y → ℚ) (C : (Sigma BZ) → Z → ℚ)
    (fx : ((X × Y) × Z) → Xr) (fy : ((Y × Z) × X) → Yr) (fz : ((Z × X) × Y) → Zr)
    (source_eq : cyclicTriple ℚ T = Tensor.pullback fx fy fz R)
    (matched_eq : Tensor.restrict A B C T = dependentMatched blocks) :
    SampleMaps (ell M aux ^ 3) R
      (Tensor.product (Tensor.product (dependentFamily (n := aux) blocks)
        (Tensor.cyclic (dependentFamily (n := aux) blocks)))
        (Tensor.cyclic (Tensor.cyclic (dependentFamily (n := aux) blocks)))) := by
  classical
  let D := dependentMatched blocks
  let E := ell M aux
  let MA := matchedMatrix A B C fx
  let MB := matchedMatrix B C A fy
  let MC := matchedMatrix C A B fz
  have hm : Tensor.restrict MA MB MC R = cyclicTriple ℚ D := by
    have ht := triple_restrict T A B C
    rw [source_eq, Tensor.pullback_eq_restrict, Tensor.restrict_restrict] at ht
    rw [matched_eq] at ht
    exact ht
  let CA := copyMatrix (cubicCopies E) MA
  let CB := copyMatrix (cubicCopies E) MB
  let CC := copyMatrix (cubicCopies E) MC
  have hc : Tensor.restrict CA CB CC (Tensor.directSum (fun _ : Fin (E ^ 3) => R)) =
      Tensor.directSum (fun _ : (Fin E × Fin E) × Fin E => cyclicTriple ℚ D) := by
    rw [copy_restriction, hm]
  let PA := projectionMatrix (collectCopies (L := E) (X := X₀) (Y := Sigma BY) (Z := Sigma BZ))
  let PB := projectionMatrix (collectCopies (L := E) (X := Sigma BY) (Y := Sigma BZ) (Z := X₀))
  let PC := projectionMatrix (collectCopies (L := E) (X := Sigma BZ) (Y := X₀) (Z := Sigma BY))
  let QA := Tensor.composeRestrictionMatrix PA CA
  let QB := Tensor.composeRestrictionMatrix PB CB
  let QC := Tensor.composeRestrictionMatrix PC CC
  have hq : Tensor.restrict QA QB QC (Tensor.directSum (fun _ : Fin (E ^ 3) => R)) =
      cyclicTriple ℚ (Tensor.directSum (fun _ : Fin E => D)) := by
    rw [← Tensor.restrict_restrict, hc]
    change Tensor.restrict
      (projectionMatrix (collectCopies (L := E) (X := X₀) (Y := Sigma BY) (Z := Sigma BZ)))
      (projectionMatrix (collectCopies (L := E) (X := Sigma BY) (Y := Sigma BZ) (Z := X₀)))
      (projectionMatrix (collectCopies (L := E) (X := Sigma BZ) (Y := X₀) (Z := Sigma BY)))
      (Tensor.directSum (fun _ : (Fin E × Fin E) × Fin E => cyclicTriple ℚ D)) = _
    rw [projection_restriction]
    exact (cyclic_copy_sum D E).symm
  let SA := liftMatrix (firstCardinal M aux (X := X₀))
  let SB := fun ε => liftMatrix (dependentSecond (n := aux) (Y := BY) ε)
  let SC := fun ε => liftMatrix (dependentThird (n := aux) (Z := BZ) ε)
  exact {
    first := fun _ ε => Tensor.composeRestrictionMatrix (tripleMatrix SA (SB ε) (SC ε)) QA
    second := fun _ ε => Tensor.composeRestrictionMatrix (tripleMatrix (SB ε) (SC ε) SA) QB
    third := fun _ ε => Tensor.composeRestrictionMatrix (tripleMatrix (SC ε) SA (SB ε)) QC
    identity := fun ε hε _ => by
      rw [← Tensor.restrict_restrict, hq, triple_restrict, dependent_restriction blocks ε hε]
      funext x y z
      simp only [evaluate, Tensor.product, Tensor.cyclic, cyclicTriple, Polynomial.eval_mul] }

/-- The split input includes its entire determinant matrix factor. -/
def splitSource (r c h N : Nat) :=
  Tensor.product (Tensor.power (cyclicTriple ℚ (TensorRankBridge.convolution ℚ r c)) N)
    (Tensor.power (matrix (h + 1)) N)

def triplingSource (r N : Nat) :=
  Tensor.power (cyclicTriple ℚ (TriplingRestrictionBridge.source ℚ r r)) N

/-- Original positive split source, including T_(h+1)^N, to the full joint
separator polynomial. No rank statement is used to construct these matrices. -/
def positiveSplitMaps (r c h N aux : Nat) (hr : 0 < r) (hc : h + 1 ≤ c)
    (counts : Fin (h + 1) → Nat) :
    SampleMaps (ell (DeterminantSplitRecipeBridge.wordCount h N counts) aux ^ 3)
      (splitSource r c h N) (DeterminantCyclicRecipeBridge.jointFamily r c h N aux counts) := by
  classical
  exact cyclicSeparatorMaps (aux := aux)
    (Tensor.power (DeterminantTensorBridge.source ℚ r c h) N) (splitSource r c h N)
    (DeterminantSplitRecipeBridge.blocks r c h N counts)
    (DeterminantCyclicRecipeBridge.sourceA r N) (DeterminantCyclicRecipeBridge.sourceB r c h N counts)
    (DeterminantCyclicRecipeBridge.sourceC r c h N hr hc counts)
    (DeterminantCyclicRecipeBridge.sourceLegX r c h N)
    (DeterminantCyclicRecipeBridge.sourceLegY r c h N)
    (DeterminantCyclicRecipeBridge.sourceLegZ r c h N)
    (DeterminantCyclicRecipeBridge.source_identification r c h N)
    (DeterminantCyclicRecipeBridge.matched_restriction r c h N hr hc counts)

/-- Original positive tripling source to the complete joint separator family. -/
def positiveTriplingMaps (r N m aux : Nat) (hr : 0 < r) :
    SampleMaps (ell (Tripling.blockCount N m) aux ^ 3) (triplingSource r N)
      (TriplingLocalRecipeBridge.jointFamily r N m aux) := by
  classical
  let T := Tensor.power (TriplingRestrictionBridge.source ℚ r r) N
  let Y := fun y => (Tripling.keptEmbeddingY r r N m hr hr y).val
  let Z := fun z => (Tripling.keptEmbeddingZ r r N m hr hr z).val
  have hm : Tensor.restrict (projectionMatrix id) (projectionMatrix Y) (projectionMatrix Z) T =
      dependentMatched (Tripling.blocks r r N m) := by
    rw [projection_restriction]
    have he : dependentMatched (Tripling.blocks r r N m) = Tensor.pullback id Y Z T := by
      rw [Tripling.matched_from_kept r r N m hr hr]
      rfl
    exact he.symm
  exact cyclicSeparatorMaps (aux := aux) T (triplingSource r N) (Tripling.blocks r r N m)
    (projectionMatrix id) (projectionMatrix Y) (projectionMatrix Z)
    (TriplingOrientationBridge.zipCoordinates (fun _ : Fin N => Fin r)
      (fun _ => Fin (sourceWidth r r)) (fun _ => Fin (r + sourceWidth r r - 1)))
    (TriplingOrientationBridge.zipCoordinates (fun _ : Fin N => Fin (sourceWidth r r))
      (fun _ => Fin (r + sourceWidth r r - 1)) (fun _ => Fin r))
    (TriplingOrientationBridge.zipCoordinates (fun _ : Fin N => Fin (r + sourceWidth r r - 1))
      (fun _ => Fin r) (fun _ => Fin (sourceWidth r r)))
    (cyclic_power_reindex (TriplingRestrictionBridge.source ℚ r r) N) hm

theorem restrict_transpose {X Y Z X' Y' Z' : Type}
    [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor ℚ X Y Z) (A : X' → X → ℚ) (B : Y' → Y → ℚ) (C : Z' → Z → ℚ) :
    Tensor.restrict B A C (transposeInputs ℚ T) = transposeInputs ℚ (Tensor.restrict A B C T) := by
  funext y x z
  change (∑ v, ∑ u, ∑ w, B y v * A x u * C z w * T u v w) =
    ∑ u, ∑ v, ∑ w, A x u * B y v * C z w * T u v w
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro w _
  ring

/-- A negative local source produces the transposed polynomial output through
maps on fixed legs. Any outside spectator can therefore remain unchanged. -/
def transposeSourceMaps {X Y Z Xn Yn Zn X' Y' Z' : Type}
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype Xn] [Fintype Yn] [Fintype Zn]
    {L : Nat} {T : Tensor ℚ X Y Z} {P : Tensor (Polynomial ℚ) X' Y' Z'}
    (maps : SampleMaps L T P) (S : Tensor ℚ Xn Yn Zn)
    (ex : Xn ≃ Y) (ey : Yn ≃ X) (ez : Zn ≃ Z)
    (source_eq : S = Tensor.pullback ex ey ez (transposeInputs ℚ T)) :
    SampleMaps L S (fun y x z => P x y z) := by
  classical
  let cx := Equiv.prodCongr (Equiv.refl (Fin L)) ex
  let cy := Equiv.prodCongr (Equiv.refl (Fin L)) ey
  let cz := Equiv.prodCongr (Equiv.refl (Fin L)) ez
  have hc : Tensor.directSum (fun _ : Fin L => S) =
      Tensor.pullback cx cy cz (transposeInputs ℚ (Tensor.directSum (fun _ : Fin L => T))) := by
    rw [source_eq, ← Tensor.directSum_pullback, TriplingContextBridge.transpose_directSum]
    rfl
  have hi : transposeInputs ℚ (Tensor.directSum (fun _ : Fin L => T)) =
      Tensor.pullback cx.symm cy.symm cz.symm (Tensor.directSum (fun _ : Fin L => S)) := by
    rw [hc]
    funext x y z
    simp only [Tensor.pullback, Equiv.apply_symm_apply]
  exact {
    first := fun _ ε x u => maps.second () ε x (u.1, ex u.2)
    second := fun _ ε y v => maps.first () ε y (v.1, ey v.2)
    third := fun _ ε z w => maps.third () ε z (w.1, ez w.2)
    identity := fun ε hε _ => by
      have hp := congrArg (transposeInputs ℚ) (maps.identity ε hε ())
      rw [← restrict_transpose, hi, FamilyPolynomialAssemblyBridge.restriction_reindex] at hp
      exact hp }

def negativePowerX (r c N : Nat) (hr : 0 < r) (hc : 0 < c) :=
  Equiv.piCongrRight (fun _ : Fin N => TriplingOddSourceBridge.oddX r c hr hc)
def negativePowerY (r c N : Nat) (hr : 0 < r) (hc : 0 < c) :=
  Equiv.piCongrRight (fun _ : Fin N => TriplingOddSourceBridge.oddY r c hr hc)
def negativePowerZ (r c N : Nat) (hr : 0 < r) (hc : 0 < c) :=
  Equiv.piCongrRight (fun _ : Fin N => TriplingOddSourceBridge.oddZ r c hr hc)

theorem negative_power_source (r c N : Nat) (hr : 0 < r) (hc : 0 < c) :
    Tensor.power (cyclicTriple ℚ (convolution ℚ c r)) N =
      Tensor.pullback (negativePowerX r c N hr hc) (negativePowerY r c N hr hc)
        (negativePowerZ r c N hr hc)
        (transposeInputs ℚ (Tensor.power (cyclicTriple ℚ (convolution ℚ r c)) N)) := by
  funext x y z
  apply Finset.prod_congr rfl
  intro i _
  exact congrFun (congrFun (congrFun (TriplingOddSourceBridge.odd_tensor_identity r c hr hc)
    (x i)) (y i)) (z i)

def reverseEntries (a N : Nat) : (Fin N → Fin a × Fin a) ≃ (Fin N → Fin a × Fin a) :=
  Equiv.piCongrRight (fun _ => Equiv.prodComm _ _)

theorem reverse_matrix_power (a N : Nat) :
    Tensor.power (matrix a) N = Tensor.pullback (reverseEntries a N) (reverseEntries a N)
      (reverseEntries a N) (transposeInputs ℚ (Tensor.power (matrix a) N)) := by
  funext x y z
  apply Finset.prod_congr rfl
  intro i _
  change matrix a (x i) (y i) (z i) =
    transposeInputs ℚ (matrix a) ((x i).swap) ((y i).swap) ((z i).swap)
  have he := congrFun (congrFun (congrFun (matrix_transpose a) ((x i).swap)) ((y i).swap)) ((z i).swap)
  simpa only [Tensor.pullback, Equiv.prodComm_apply, Prod.swap_swap] using he.symm

def negativeSplitX (r c h N : Nat) (hr : 0 < r) (hc : 0 < c) :=
  Equiv.prodCongr (negativePowerX r c N hr hc) (reverseEntries (h + 1) N)
def negativeSplitY (r c h N : Nat) (hr : 0 < r) (hc : 0 < c) :=
  Equiv.prodCongr (negativePowerY r c N hr hc) (reverseEntries (h + 1) N)
def negativeSplitZ (r c h N : Nat) (hr : 0 < r) (hc : 0 < c) :=
  Equiv.prodCongr (negativePowerZ r c N hr hc) (reverseEntries (h + 1) N)

theorem negative_split_source (r c h N : Nat) (hr : 0 < r) (hc : 0 < c) :
    splitSource c r h N = Tensor.pullback (negativeSplitX r c h N hr hc)
      (negativeSplitY r c h N hr hc) (negativeSplitZ r c h N hr hc)
      (transposeInputs ℚ (splitSource r c h N)) := by
  unfold splitSource
  conv_lhs => rw [negative_power_source r c N hr hc, reverse_matrix_power (h + 1) N]
  rfl

/-- Original odd split source retains the full input auxiliary power; its
polynomial output retains the required opposite orientation. -/
def negativeSplitMaps (r c h N aux : Nat) (hr : 0 < r) (hc : h + 1 ≤ c)
    (counts : Fin (h + 1) → Nat) :
    SampleMaps (ell (DeterminantSplitRecipeBridge.wordCount h N counts) aux ^ 3)
      (splitSource c r h N) (fun y x z => DeterminantCyclicRecipeBridge.jointFamily r c h N aux counts x y z) :=
  transposeSourceMaps (positiveSplitMaps r c h N aux hr hc counts) (splitSource c r h N)
    (negativeSplitX r c h N hr (by omega)) (negativeSplitY r c h N hr (by omega))
    (negativeSplitZ r c h N hr (by omega)) (negative_split_source r c h N hr (by omega))

def negativeTriplingMaps (r N m aux : Nat) (hr : 0 < r) :
    SampleMaps (ell (Tripling.blockCount N m) aux ^ 3)
      (Tensor.power (cyclicTriple ℚ (convolution ℚ (sourceWidth r r) r)) N)
      (fun y x z => TriplingLocalRecipeBridge.jointFamily r N m aux x y z) :=
  transposeSourceMaps (positiveTriplingMaps r N m aux hr) _
    (negativePowerX r (sourceWidth r r) N hr (by unfold sourceWidth; omega))
    (negativePowerY r (sourceWidth r r) N hr (by unfold sourceWidth; omega))
    (negativePowerZ r (sourceWidth r r) N hr (by unfold sourceWidth; omega))
    (negative_power_source r (sourceWidth r r) N hr (by unfold sourceWidth; omega))

def splitOutputPolynomial (r c h N aux : Nat) (counts : Fin (h + 1) → Nat) :=
  Tensor.pullback (DeterminantCyclicRecipeBridge.outputX r c h N aux counts)
    (DeterminantCyclicRecipeBridge.outputY r c h N aux counts)
    (DeterminantCyclicRecipeBridge.outputZ r c h N aux counts)
    (DeterminantCyclicRecipeBridge.jointFamily r c h N aux counts)

def triplingOutputPolynomial (r N m aux : Nat) (hr : 0 < r) :=
  Tensor.pullback (TriplingLocalRecipeBridge.sourceX r N m aux hr)
    (TriplingLocalRecipeBridge.sourceY r N m aux hr) (TriplingLocalRecipeBridge.sourceZ r N m aux hr)
    (TriplingLocalRecipeBridge.jointFamily r N m aux)

def positiveSplitOutputMaps (r c h N aux : Nat) (hr : 0 < r) (hc : h + 1 ≤ c)
    (counts : Fin (h + 1) → Nat) :
    SampleMaps (ell (DeterminantSplitRecipeBridge.wordCount h N counts) aux ^ 3)
      (splitSource r c h N) (splitOutputPolynomial r c h N aux counts) :=
  (positiveSplitMaps r c h N aux hr hc counts).pullback
    (fun _ => DeterminantCyclicRecipeBridge.outputX r c h N aux counts)
    (fun _ => DeterminantCyclicRecipeBridge.outputY r c h N aux counts)
    (fun _ => DeterminantCyclicRecipeBridge.outputZ r c h N aux counts)

def negativeSplitOutputMaps (r c h N aux : Nat) (hr : 0 < r) (hc : h + 1 ≤ c)
    (counts : Fin (h + 1) → Nat) :
    SampleMaps (ell (DeterminantSplitRecipeBridge.wordCount h N counts) aux ^ 3)
      (splitSource c r h N) (fun y x z => splitOutputPolynomial r c h N aux counts x y z) :=
  transposeSourceMaps (positiveSplitOutputMaps r c h N aux hr hc counts) _
    (negativeSplitX r c h N hr (by omega)) (negativeSplitY r c h N hr (by omega))
    (negativeSplitZ r c h N hr (by omega)) (negative_split_source r c h N hr (by omega))

def positiveTriplingOutputMaps (r N m aux : Nat) (hr : 0 < r) :
    SampleMaps (ell (Tripling.blockCount N m) aux ^ 3) (triplingSource r N)
      (triplingOutputPolynomial r N m aux hr) :=
  (positiveTriplingMaps r N m aux hr).pullback
    (fun _ => TriplingLocalRecipeBridge.sourceX r N m aux hr)
    (fun _ => TriplingLocalRecipeBridge.sourceY r N m aux hr)
    (fun _ => TriplingLocalRecipeBridge.sourceZ r N m aux hr)

def negativeTriplingOutputMaps (r N m aux : Nat) (hr : 0 < r) :
    SampleMaps (ell (Tripling.blockCount N m) aux ^ 3)
      (Tensor.power (cyclicTriple ℚ (convolution ℚ (sourceWidth r r) r)) N)
      (fun y x z => triplingOutputPolynomial r N m aux hr x y z) :=
  transposeSourceMaps (positiveTriplingOutputMaps r N m aux hr) _
    (negativePowerX r (sourceWidth r r) N hr (by unfold sourceWidth; omega))
    (negativePowerY r (sourceWidth r r) N hr (by unfold sourceWidth; omega))
    (negativePowerZ r (sourceWidth r r) N hr (by unfold sourceWidth; omega))
    (negative_power_source r (sourceWidth r r) N hr (by unfold sourceWidth; omega))

theorem split_output_constant (r c h N aux : Nat) (counts : Fin (h + 1) → Nat) :
    evaluate (splitOutputPolynomial r c h N aux counts) 0 =
      DeterminantCyclicRecipeBridge.output r c h N aux counts := by
  change Tensor.pullback _ _ _ (evaluate (DeterminantCyclicRecipeBridge.jointFamily r c h N aux counts) 0) = _
  rw [DeterminantCyclicRecipeBridge.jointFamily_constant, DeterminantCyclicRecipeBridge.full_constant_restriction]

theorem tripling_output_constant (r N m aux : Nat) (hr : 0 < r) :
    evaluate (triplingOutputPolynomial r N m aux hr) 0 = TriplingLocalRecipeBridge.output r N m aux hr := by
  change Tensor.pullback _ _ _ (evaluate (TriplingLocalRecipeBridge.jointFamily r N m aux) 0) = _
  rw [TriplingLocalRecipeBridge.jointFamily_constant, TriplingLocalRecipeBridge.full_constant_restriction]

theorem split_output_degree (r c h N aux : Nat) (counts : Fin (h + 1) → Nat) :
    ∀ x y z, (splitOutputPolynomial r c h N aux counts x y z).natDegree ≤
      3 * DeterminantCyclicRecipeBridge.localDegree h N aux counts :=
  fun x y z => DeterminantCyclicRecipeBridge.jointFamily_degree r c h N aux counts
    (DeterminantCyclicRecipeBridge.outputX r c h N aux counts x)
    (DeterminantCyclicRecipeBridge.outputY r c h N aux counts y)
    (DeterminantCyclicRecipeBridge.outputZ r c h N aux counts z)

theorem tripling_output_degree (r N m aux : Nat) (hr : 0 < r) :
    ∀ x y z, (triplingOutputPolynomial r N m aux hr x y z).natDegree ≤
      3 * TriplingLocalRecipeBridge.localDegree N m aux :=
  fun x y z => TriplingLocalRecipeBridge.jointFamily_degree r N m aux
    (TriplingLocalRecipeBridge.sourceX r N m aux hr x) (TriplingLocalRecipeBridge.sourceY r N m aux hr y)
    (TriplingLocalRecipeBridge.sourceZ r N m aux hr z)

/-- Actual population-expanded flow actions instantiate the original-source
sample maps, before any local interpolation or rank bound. -/
def positiveActionMaps {r : Nat} (a : GeneralRowSector.Action r) (hr : 2 ≤ r) (aux : Nat) :=
  positiveSplitOutputMaps r (FlowActionTensorBridge.actionColumn a) a.h a.width aux (by omega)
    (FlowActionTensorBridge.action_column_legal a hr) (FlowActionTensorBridge.actionCounts a)

def negativeActionMaps {r : Nat} (a : GeneralRowSector.Action r) (hr : 2 ≤ r) (aux : Nat) :=
  negativeSplitOutputMaps r (FlowActionTensorBridge.actionColumn a) a.h a.width aux (by omega)
    (FlowActionTensorBridge.action_column_legal a hr) (FlowActionTensorBridge.actionCounts a)

theorem action_copy_count {r : Nat} (a : GeneralRowSector.Action r) (aux : Nat) :
    ell (DeterminantSplitRecipeBridge.wordCount a.h a.width (FlowActionTensorBridge.actionCounts a)) aux ^ 3 =
      ell a.count aux ^ 3 := by
  rw [← FlowActionTensorBridge.action_sector_count]

def positiveResetMaps (r Z aux : Nat) (hr : 2 ≤ r) :=
  positiveTriplingOutputMaps r Z (TriplingSectorModeBridge.mode Z) aux (by omega)
def negativeResetMaps (r Z aux : Nat) (hr : 2 ≤ r) :=
  negativeTriplingOutputMaps r Z (TriplingSectorModeBridge.mode Z) aux (by omega)

theorem reset_copy_count (Z aux : Nat) :
    ell (Tripling.blockCount Z (TriplingSectorModeBridge.mode Z)) aux ^ 3 =
      ell (GeneralRowSector.triplingCount Z) aux ^ 3 := by
  change ell (TriplingSectorCountBridge.count Z (TriplingSectorModeBridge.mode Z)) aux ^ 3 = _
  rw [← FlowActionTensorBridge.row_tripling_count]

theorem positive_split_source_named (r c h N : Nat) (hr : 0 < r) (hc : 0 < c) :
    splitSource r c h N = Tensor.product
      (Tensor.power (signedCyclicConvolution ℚ false r c hr hc).tensor N)
      (Tensor.power (matrix (h + 1)) N) := rfl

theorem negative_split_source_named (r c h N : Nat) (hr : 0 < r) (hc : 0 < c) :
    splitSource c r h N = Tensor.product
      (Tensor.power (signedCyclicConvolution ℚ true r c hr hc).tensor N)
      (Tensor.power (matrix (h + 1)) N) := rfl

theorem negative_split_output_constant (r c h N aux : Nat) (counts : Fin (h + 1) → Nat) :
    evaluate (fun y x z => splitOutputPolynomial r c h N aux counts x y z) 0 =
      transposeInputs ℚ (DeterminantCyclicRecipeBridge.output r c h N aux counts) :=
  congrArg (transposeInputs ℚ) (split_output_constant r c h N aux counts)

theorem negative_tripling_output_constant (r N m aux : Nat) (hr : 0 < r) :
    evaluate (fun y x z => triplingOutputPolynomial r N m aux hr x y z) 0 =
      transposeInputs ℚ (TriplingLocalRecipeBridge.output r N m aux hr) :=
  congrArg (transposeInputs ℚ) (tripling_output_constant r N m aux hr)

theorem tripling_reset_named (negative : Bool) (r : Nat) (hr : 2 ≤ r) :
    signedCyclicConvolution ℚ negative r (sourceWidth r r) (by omega)
      (by unfold sourceWidth; omega) = resetFactor ℚ negative r hr := by
  have hw : sourceWidth r r = 4 * r - 1 := by unfold sourceWidth; omega
  unfold resetFactor
  simp only [hw]

theorem action_polynomial_degree {r : Nat} (a : GeneralRowSector.Action r) (aux : Nat) :
    ∀ x y z, (splitOutputPolynomial r (FlowActionTensorBridge.actionColumn a) a.h a.width aux
      (FlowActionTensorBridge.actionCounts a) x y z).natDegree ≤ 3 * min (a.count - 1) (aux - 1) := by
  simpa only [DeterminantCyclicRecipeBridge.localDegree, ← FlowActionTensorBridge.action_sector_count a]
    using split_output_degree r (FlowActionTensorBridge.actionColumn a) a.h a.width aux
      (FlowActionTensorBridge.actionCounts a)

theorem reset_polynomial_degree (r Z aux : Nat) (hr : 0 < r) :
    ∀ x y z, (triplingOutputPolynomial r Z (TriplingSectorModeBridge.mode Z) aux hr x y z).natDegree ≤
      3 * min (GeneralRowSector.triplingCount Z - 1) (aux - 1) := by
  have hc : Tripling.blockCount Z (TriplingSectorModeBridge.mode Z) = GeneralRowSector.triplingCount Z := by
    change TriplingSectorCountBridge.count Z (TriplingSectorModeBridge.mode Z) = _
    exact (FlowActionTensorBridge.row_tripling_count Z).symm
  simpa only [TriplingLocalRecipeBridge.localDegree, hc]
    using tripling_output_degree r Z (TriplingSectorModeBridge.mode Z) aux hr

/-- Assemble heterogeneous original-source witnesses without adding local
rank certificates or local exactifications. -/
def sampleMapsFamily {I : Type} [Fintype I] [DecidableEq I]
    {X Y Z X' Y' Z' : I → Type}
    [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] [∀ i, Fintype (Z i)]
    {L : I → Nat} {T : ∀ i, Tensor ℚ (X i) (Y i) (Z i)}
    {P : ∀ i, Tensor (Polynomial ℚ) (X' i) (Y' i) (Z' i)}
    (maps : ∀ i, SampleMaps (L i) (T i) (P i)) : LocalRestrictions L T P where
  first := fun i => (maps i).first ()
  second := fun i => (maps i).second ()
  third := fun i => (maps i).third ()
  identity := fun ε hε i => (maps i).identity ε hε ()

end
end MatrixDimensionAudit.OriginalLocalSampleBridge

#print axioms MatrixDimensionAudit.OriginalLocalSampleBridge.SampleMaps
#print axioms MatrixDimensionAudit.OriginalLocalSampleBridge.copyMatrix
#print axioms MatrixDimensionAudit.OriginalLocalSampleBridge.copy_restriction
#print axioms MatrixDimensionAudit.OriginalLocalSampleBridge.projection_restriction
#print axioms MatrixDimensionAudit.OriginalLocalSampleBridge.cubicCopies
#print axioms MatrixDimensionAudit.OriginalLocalSampleBridge.matchedMatrix
#print axioms MatrixDimensionAudit.OriginalLocalSampleBridge.cyclicSeparatorMaps
#print axioms MatrixDimensionAudit.OriginalLocalSampleBridge.splitSource
#print axioms MatrixDimensionAudit.OriginalLocalSampleBridge.triplingSource
#print axioms MatrixDimensionAudit.OriginalLocalSampleBridge.positiveSplitMaps
#print axioms MatrixDimensionAudit.OriginalLocalSampleBridge.positiveTriplingMaps
#print axioms MatrixDimensionAudit.OriginalLocalSampleBridge.restrict_transpose
#print axioms MatrixDimensionAudit.OriginalLocalSampleBridge.transposeSourceMaps
#print axioms MatrixDimensionAudit.OriginalLocalSampleBridge.negativePowerX
#print axioms MatrixDimensionAudit.OriginalLocalSampleBridge.negativePowerY
#print axioms MatrixDimensionAudit.OriginalLocalSampleBridge.negativePowerZ
#print axioms MatrixDimensionAudit.OriginalLocalSampleBridge.negative_power_source
#print axioms MatrixDimensionAudit.OriginalLocalSampleBridge.reverseEntries
#print axioms MatrixDimensionAudit.OriginalLocalSampleBridge.reverse_matrix_power
#print axioms MatrixDimensionAudit.OriginalLocalSampleBridge.negativeSplitX
#print axioms MatrixDimensionAudit.OriginalLocalSampleBridge.negativeSplitY
#print axioms MatrixDimensionAudit.OriginalLocalSampleBridge.negativeSplitZ
#print axioms MatrixDimensionAudit.OriginalLocalSampleBridge.negative_split_source
#print axioms MatrixDimensionAudit.OriginalLocalSampleBridge.negativeSplitMaps
#print axioms MatrixDimensionAudit.OriginalLocalSampleBridge.negativeTriplingMaps
#print axioms MatrixDimensionAudit.OriginalLocalSampleBridge.splitOutputPolynomial
#print axioms MatrixDimensionAudit.OriginalLocalSampleBridge.triplingOutputPolynomial
#print axioms MatrixDimensionAudit.OriginalLocalSampleBridge.positiveSplitOutputMaps
#print axioms MatrixDimensionAudit.OriginalLocalSampleBridge.negativeSplitOutputMaps
#print axioms MatrixDimensionAudit.OriginalLocalSampleBridge.positiveTriplingOutputMaps
#print axioms MatrixDimensionAudit.OriginalLocalSampleBridge.negativeTriplingOutputMaps
#print axioms MatrixDimensionAudit.OriginalLocalSampleBridge.split_output_constant
#print axioms MatrixDimensionAudit.OriginalLocalSampleBridge.tripling_output_constant
#print axioms MatrixDimensionAudit.OriginalLocalSampleBridge.split_output_degree
#print axioms MatrixDimensionAudit.OriginalLocalSampleBridge.tripling_output_degree
#print axioms MatrixDimensionAudit.OriginalLocalSampleBridge.positiveActionMaps
#print axioms MatrixDimensionAudit.OriginalLocalSampleBridge.negativeActionMaps
#print axioms MatrixDimensionAudit.OriginalLocalSampleBridge.action_copy_count
#print axioms MatrixDimensionAudit.OriginalLocalSampleBridge.positiveResetMaps
#print axioms MatrixDimensionAudit.OriginalLocalSampleBridge.negativeResetMaps
#print axioms MatrixDimensionAudit.OriginalLocalSampleBridge.reset_copy_count
#print axioms MatrixDimensionAudit.OriginalLocalSampleBridge.positive_split_source_named
#print axioms MatrixDimensionAudit.OriginalLocalSampleBridge.negative_split_source_named
#print axioms MatrixDimensionAudit.OriginalLocalSampleBridge.negative_split_output_constant
#print axioms MatrixDimensionAudit.OriginalLocalSampleBridge.negative_tripling_output_constant
#print axioms MatrixDimensionAudit.OriginalLocalSampleBridge.tripling_reset_named
#print axioms MatrixDimensionAudit.OriginalLocalSampleBridge.action_polynomial_degree
#print axioms MatrixDimensionAudit.OriginalLocalSampleBridge.reset_polynomial_degree
#print axioms MatrixDimensionAudit.OriginalLocalSampleBridge.sampleMapsFamily
