import formalization.GlobalFamilySampleBridge

/-! Exact serial restriction maps retain one catalyst. -/
namespace MatrixDimensionAudit.CatalystReuseBridge
open OAI.MatrixMultiplication.Foundation
open TensorRankBridge SignedCatalystLedgerBridge TensorResourcePoolingBridge
open scoped BigOperators
noncomputable section
attribute [local instance] GlobalFamilySampleBridge.productFiniteX GlobalFamilySampleBridge.productFiniteY
local instance nestedFiniteX (A : FullTensor ℚ) [Fintype A.X] : (n : ℕ) → Fintype (A.power n).X
  | 0 => inferInstanceAs (Fintype Unit)
  | n+1 => @GlobalFamilySampleBridge.productFiniteX A (A.power n) inferInstance (nestedFiniteX A n)
local instance nestedFiniteY (A : FullTensor ℚ) [Fintype A.Y] : (n : ℕ) → Fintype (A.power n).Y
  | 0 => inferInstanceAs (Fintype Unit)
  | n+1 => @GlobalFamilySampleBridge.productFiniteY A (A.power n) inferInstance (nestedFiniteY A n)



/-- Three actual restriction matrices and their complete coefficient identity. -/
structure Maps (A B : FullTensor ℚ) [Fintype A.X] [Fintype A.Y] where
  first : B.X → A.X → ℚ
  second : B.Y → A.Y → ℚ
  third : B.Z → A.Z → ℚ
  identity : Tensor.restrict first second third A.tensor = B.tensor

namespace Maps

def ofIso {A B : FullTensor ℚ} [Fintype A.X] [Fintype A.Y] (p : Iso A B) : Maps A B := by
  classical
  exact {
    first := TriplingLocalRecipeBridge.projectionMatrix p.x.symm
    second := TriplingLocalRecipeBridge.projectionMatrix p.y.symm
    third := TriplingLocalRecipeBridge.projectionMatrix p.z.symm
    identity := (OriginalLocalSampleBridge.projection_restriction p.x.symm p.y.symm p.z.symm A.tensor).trans p.symm.tensor_eq.symm }

def refl (A : FullTensor ℚ) [Fintype A.X] [Fintype A.Y] : Maps A A := ofIso (Iso.refl A)

def trans {A B C : FullTensor ℚ} [Fintype A.X] [Fintype A.Y] [Fintype B.X] [Fintype B.Y]
    (p : Maps A B) (q : Maps B C) : Maps A C where
  first := Tensor.composeRestrictionMatrix q.first p.first
  second := Tensor.composeRestrictionMatrix q.second p.second
  third := Tensor.composeRestrictionMatrix q.third p.third
  identity := by rw [← Tensor.restrict_restrict, p.identity, q.identity]

def product {A B C D : FullTensor ℚ} [Fintype A.X] [Fintype A.Y] [Fintype C.X] [Fintype C.Y]
    (p : Maps A B) (q : Maps C D) : Maps (A.product C) (B.product D) where
  first := fun x u => p.first x.1 u.1 * q.first x.2 u.2
  second := fun y v => p.second y.1 v.1 * q.second y.2 v.2
  third := fun z w => p.third z.1 w.1 * q.third z.2 w.2
  identity := by
    exact (Tensor.restrict_product p.first p.second p.third q.first q.second q.third A.tensor C.tensor).trans
      (congrArg₂ Tensor.product p.identity q.identity)

theorem rank {A B : FullTensor ℚ} [Fintype A.X] [Fintype A.Y]
    (p : Maps A B) {R : ℕ} (h : Tensor.RankAtMost A.tensor R) : Tensor.RankAtMost B.tensor R := by
  rw [← p.identity]
  exact h.restrict _ _ _

end Maps

/-- Move the first pass's resources together; leave all second-pass resources intact. -/
def splitInputs (D E C A B : FullTensor ℚ) :
    Iso ((D.product E).product (C.product (A.product B)))
      ((D.product (C.product A)).product (E.product B)) where
  x := {
    toFun := fun x => ((x.1.1, (x.2.1, x.2.2.1)), (x.1.2, x.2.2.2))
    invFun := fun x => ((x.1.1, x.2.1), (x.1.2.1, (x.1.2.2, x.2.2)))
    left_inv _ := rfl
    right_inv _ := rfl }
  y := {
    toFun := fun x => ((x.1.1, (x.2.1, x.2.2.1)), (x.1.2, x.2.2.2))
    invFun := fun x => ((x.1.1, x.2.1), (x.1.2.1, (x.1.2.2, x.2.2)))
    left_inv _ := rfl
    right_inv _ := rfl }
  z := {
    toFun := fun x => ((x.1.1, (x.2.1, x.2.2.1)), (x.1.2, x.2.2.2))
    invFun := fun x => ((x.1.1, x.2.1), (x.1.2.1, (x.1.2.2, x.2.2)))
    left_inv _ := rfl
    right_inv _ := rfl }
  coeff := by
    intro x y z
    change (D.X × E.X) × (C.X × (A.X × B.X)) at x
    change (D.Y × E.Y) × (C.Y × (A.Y × B.Y)) at y
    change (D.Z × E.Z) × (C.Z × (A.Z × B.Z)) at z
    change (D.tensor x.1.1 y.1.1 z.1.1 * E.tensor x.1.2 y.1.2 z.1.2) *
      (C.tensor x.2.1 y.2.1 z.2.1 * (A.tensor x.2.2.1 y.2.2.1 z.2.2.1 * B.tensor x.2.2.2 y.2.2.2 z.2.2.2)) =
      (D.tensor x.1.1 y.1.1 z.1.1 * (C.tensor x.2.1 y.2.1 z.2.1 * A.tensor x.2.2.1 y.2.2.1 z.2.2.1)) *
      (E.tensor x.1.2 y.1.2 z.1.2 * B.tensor x.2.2.2 y.2.2.2 z.2.2.2)
    ring

/-- Hand the same catalyst to the second pass, with the first output as spectator. -/
def handoff (C B D A : FullTensor ℚ) :
    Iso ((C.product B).product (D.product A)) ((D.product (C.product A)).product B) where
  x := {
    toFun := fun x => ((x.2.1, (x.1.1, x.2.2)), x.1.2)
    invFun := fun x => ((x.1.2.1, x.2), (x.1.1, x.1.2.2))
    left_inv _ := rfl
    right_inv _ := rfl }
  y := {
    toFun := fun x => ((x.2.1, (x.1.1, x.2.2)), x.1.2)
    invFun := fun x => ((x.1.2.1, x.2), (x.1.1, x.1.2.2))
    left_inv _ := rfl
    right_inv _ := rfl }
  z := {
    toFun := fun x => ((x.2.1, (x.1.1, x.2.2)), x.1.2)
    invFun := fun x => ((x.1.2.1, x.2), (x.1.1, x.1.2.2))
    left_inv _ := rfl
    right_inv _ := rfl }
  coeff := by
    intro x y z
    change (C.X × B.X) × (D.X × A.X) at x
    change (C.Y × B.Y) × (D.Y × A.Y) at y
    change (C.Z × B.Z) × (D.Z × A.Z) at z
    change (C.tensor x.1.1 y.1.1 z.1.1 * B.tensor x.1.2 y.1.2 z.1.2) *
      (D.tensor x.2.1 y.2.1 z.2.1 * A.tensor x.2.2 y.2.2 z.2.2) =
      (D.tensor x.2.1 y.2.1 z.2.1 * (C.tensor x.1.1 y.1.1 z.1.1 * A.tensor x.2.2 y.2.2 z.2.2)) *
      B.tensor x.1.2 y.1.2 z.1.2
    ring

/-- Genuine two-pass composition: one catalyst occurs in both source and target. -/
def twoPass (D E C A B U V : FullTensor ℚ)
    [Fintype D.X] [Fintype D.Y] [Fintype E.X] [Fintype E.Y]
    [Fintype C.X] [Fintype C.Y] [Fintype A.X] [Fintype A.Y]
    [Fintype B.X] [Fintype B.Y] [Fintype U.X] [Fintype U.Y] [Fintype V.X] [Fintype V.Y]
    (p : Maps (D.product (C.product A)) (C.product U))
    (q : Maps (E.product (C.product B)) (C.product V)) :
    Maps ((D.product E).product (C.product (A.product B))) (C.product (U.product V)) :=
  (Maps.ofIso (splitInputs D E C A B)).trans
    ((p.product (Maps.refl (E.product B))).trans
      ((Maps.ofIso (handoff C U E B)).trans
        ((q.product (Maps.refl U)).trans
          (Maps.ofIso ((Iso.assoc C V U).trans ((Iso.refl C).product (Iso.comm V U)))))))


/-- Repeat an exact pass; the catalyst is never tensored with another catalyst. -/
def serial (D C A B : FullTensor ℚ)
    [Fintype D.X] [Fintype D.Y] [Fintype C.X] [Fintype C.Y]
    [Fintype A.X] [Fintype A.Y] [Fintype B.X] [Fintype B.Y]
    (p : Maps (D.product (C.product A)) (C.product B)) :
    (j : ℕ) → Maps ((D.power j).product (C.product (A.power j))) (C.product (B.power j))
  | 0 => Maps.ofIso (Iso.unitLeft _)
  | j+1 => twoPass D (D.power j) C A (A.power j) B (B.power j) p (serial D C A B p j)

/-- The repeated maps satisfy the actual coefficient equation, for every reuse count. -/
theorem serial_identity (D C A B : FullTensor ℚ)
    [Fintype D.X] [Fintype D.Y] [Fintype C.X] [Fintype C.Y]
    [Fintype A.X] [Fintype A.Y] [Fintype B.X] [Fintype B.Y]
    (p : Maps (D.product (C.product A)) (C.product B)) (j : ℕ) :
    Tensor.restrict (serial D C A B p j).first (serial D C A B p j).second
      (serial D C A B p j).third ((D.power j).product (C.product (A.power j))).tensor =
        (C.product (B.power j)).tensor := (serial D C A B p j).identity

/-- Reuse preserves one pooled source rank certificate, with one catalyst. -/
theorem serial_rank (D C A B : FullTensor ℚ)
    [Fintype D.X] [Fintype D.Y] [Fintype C.X] [Fintype C.Y]
    [Fintype A.X] [Fintype A.Y] [Fintype B.X] [Fintype B.Y]
    (p : Maps (D.product (C.product A)) (C.product B)) (j R : ℕ)
    (h : Tensor.RankAtMost ((D.power j).product (C.product (A.power j))).tensor R) :
    Tensor.RankAtMost (C.product (B.power j)).tensor R := (serial D C A B p j).rank h

/-- Separate powers of two actual tensor resources. -/
def shuffleProduct (A B C D : FullTensor ℚ) :
    Iso ((A.product B).product (C.product D)) ((A.product C).product (B.product D)) where
  x := shufflePairs _ _ _ _
  y := shufflePairs _ _ _ _
  z := shufflePairs _ _ _ _
  coeff := by
    intro x y z
    change (A.X × B.X) × (C.X × D.X) at x
    change (A.Y × B.Y) × (C.Y × D.Y) at y
    change (A.Z × B.Z) × (C.Z × D.Z) at z
    change (A.tensor x.1.1 y.1.1 z.1.1 * B.tensor x.1.2 y.1.2 z.1.2) *
      (C.tensor x.2.1 y.2.1 z.2.1 * D.tensor x.2.2 y.2.2 z.2.2) =
      (A.tensor x.1.1 y.1.1 z.1.1 * C.tensor x.2.1 y.2.1 z.2.1) *
      (B.tensor x.1.2 y.1.2 z.1.2 * D.tensor x.2.2 y.2.2 z.2.2)
    ring

def powerProductIso (A B : FullTensor ℚ) : (j : ℕ) →
    Iso ((A.product B).power j) ((A.power j).product (B.power j))
  | 0 => (Iso.unitLeft _).symm
  | j+1 => ((Iso.refl (A.product B)).product (powerProductIso A B j)).trans
      (shuffleProduct A B (A.power j) (B.power j))

/-- A finite direct-sum label as a full coefficient tensor. -/
def diagonalFull (n : ℕ) : FullTensor ℚ where
  X := Fin n
  Y := Fin n
  Z := Fin n
  finiteZ := inferInstance
  equalZ := inferInstance
  tensor := fun x y z => if x=y ∧ y=z then 1 else 0
  left := id
  right := id
  identity := by intro i j; simp

local instance diagonalFiniteX (n : ℕ) : Fintype (diagonalFull n).X := inferInstanceAs (Fintype (Fin n))
local instance diagonalFiniteY (n : ℕ) : Fintype (diagonalFull n).Y := inferInstanceAs (Fintype (Fin n))

local instance diagonalDecX (n : ℕ) : DecidableEq (diagonalFull n).X := inferInstanceAs (DecidableEq (Fin n))
local instance diagonalDecY (n : ℕ) : DecidableEq (diagonalFull n).Y := inferInstanceAs (DecidableEq (Fin n))

/-- No copy label is discarded when a diagonal factor is read as a direct sum. -/
theorem diagonal_product (n : ℕ) (A : FullTensor ℚ) :
    ((diagonalFull n).product A).tensor = Tensor.directSum (fun _ : Fin n => A.tensor) := by
  classical
  funext x y z
  simp only [FullTensor.product, diagonalFull, Tensor.product, Tensor.directSum]
  split_ifs <;> simp_all
  aesop

/-- Copy multiplicities multiply by an explicit finite-pair equivalence. -/
def diagonalProductIso (a b : ℕ) :
    Iso ((diagonalFull a).product (diagonalFull b)) (diagonalFull (a*b)) where
  x := finProdFinEquiv
  y := finProdFinEquiv
  z := finProdFinEquiv
  coeff := by
    intro x y z
    change Fin a × Fin b at x y z
    change (if x.1=y.1 ∧ y.1=z.1 then (1:ℚ) else 0) *
      (if x.2=y.2 ∧ y.2=z.2 then 1 else 0) =
      if finProdFinEquiv x = finProdFinEquiv y ∧ finProdFinEquiv y = finProdFinEquiv z then 1 else 0
    simp only [Equiv.apply_eq_iff_eq, Prod.ext_iff]
    split_ifs <;> simp_all


def diagonalUnitIso : Iso (diagonalFull 1) (FullTensor.unit (F := ℚ)) where
  x := Equiv.ofUnique (Fin 1) Unit
  y := Equiv.ofUnique (Fin 1) Unit
  z := Equiv.ofUnique (Fin 1) Unit
  coeff := by intro x y z; change Fin 1 at x y z; have hx : x=y := Subsingleton.elim _ _; have hy : y=z := Subsingleton.elim _ _; simp [diagonalFull, hx, hy, FullTensor.unit]

/-- Every nested copy word is enumerated by Fin(L^j), including j=0 and L=0. -/
def diagonalPowerIso (L : ℕ) : (j : ℕ) → Iso ((diagonalFull L).power j) (diagonalFull (L^j))
  | 0 => diagonalUnitIso.symm
  | j+1 => ((Iso.refl _).product (diagonalPowerIso L j)).trans
      ((diagonalProductIso L (L^j)).trans (Iso.ofEq (congrArg diagonalFull (pow_succ' L j).symm)))

/-- Move the copy factor to the right of a catalyst, by full coordinate maps. -/
def swapHead (A B C : FullTensor ℚ) : Iso (A.product (B.product C)) (B.product (A.product C)) :=
  (Iso.assoc A B C).symm.trans (((Iso.comm A B).product (Iso.refl C)).trans (Iso.assoc B A C))

def resourceFrame (D S C A : FullTensor ℚ) :
    Iso (D.product ((S.product C).product A)) ((D.product S).product (C.product A)) :=
  ((Iso.refl D).product (Iso.assoc S C A)).trans (Iso.assoc D S (C.product A)).symm

/-- Actual copied one-pass maps become the serial interface without any tensor equality premise. -/
def framePass (L M : ℕ) (S C A B : FullTensor ℚ)
    [Fintype S.X] [Fintype S.Y] [Fintype C.X] [Fintype C.Y]
    [Fintype A.X] [Fintype A.Y] [Fintype B.X] [Fintype B.Y]
    (p : Maps ((diagonalFull L).product ((S.product C).product A))
      ((diagonalFull M).product (C.product B))) :
    Maps (((diagonalFull L).product S).product (C.product A))
      (C.product ((diagonalFull M).product B)) :=
  (Maps.ofIso (resourceFrame (diagonalFull L) S C A).symm).trans
    (p.trans (Maps.ofIso (swapHead (diagonalFull M) C B)))

/-- Source resources for repeated exact restrictions, with the full copy count exposed. -/
def serialSourceIso (L : ℕ) (S C A : FullTensor ℚ) (j : ℕ) :
    Iso ((diagonalFull (L^j)).product (((S.power j).product C).product (A.power j)))
      ((((diagonalFull L).product S).power j).product (C.product (A.power j))) :=
  (((diagonalPowerIso L j).symm).product (Iso.refl _)).trans
    ((resourceFrame ((diagonalFull L).power j) (S.power j) C (A.power j)).trans
      ((powerProductIso (diagonalFull L) S j).symm.product (Iso.refl _)))

/-- Output copy words expose M^j summands, all retaining the same catalyst. -/
def serialTargetIso (M : ℕ) (C B : FullTensor ℚ) (j : ℕ) :
    Iso (C.product (((diagonalFull M).product B).power j))
      ((diagonalFull (M^j)).product (C.product (B.power j))) :=
  ((Iso.refl C).product (powerProductIso (diagonalFull M) B j)).trans
    ((swapHead C ((diagonalFull M).power j) (B.power j)).trans
      ((diagonalPowerIso M j).product (Iso.refl _)))

/-- Repeat an actual copied restriction j times using one catalyst, not C^j. -/
def copiedSerial (L M : ℕ) (S C A B : FullTensor ℚ)
    [Fintype S.X] [Fintype S.Y] [Fintype C.X] [Fintype C.Y]
    [Fintype A.X] [Fintype A.Y] [Fintype B.X] [Fintype B.Y]
    (p : Maps ((diagonalFull L).product ((S.product C).product A))
      ((diagonalFull M).product (C.product B))) (j : ℕ) :
    Maps ((diagonalFull (L^j)).product (((S.power j).product C).product (A.power j)))
      ((diagonalFull (M^j)).product (C.product (B.power j))) :=
  (Maps.ofIso (serialSourceIso L S C A j)).trans
    ((serial _ C A _ (framePass L M S C A B p) j).trans (Maps.ofIso (serialTargetIso M C B j)))

/-- Complete coefficient identity for the repeated actual direct-sum restriction. -/
theorem copiedSerial_identity (L M : ℕ) (S C A B : FullTensor ℚ)
    [Fintype S.X] [Fintype S.Y] [Fintype C.X] [Fintype C.Y]
    [Fintype A.X] [Fintype A.Y] [Fintype B.X] [Fintype B.Y]
    (p : Maps ((diagonalFull L).product ((S.product C).product A))
      ((diagonalFull M).product (C.product B))) (j : ℕ) :
    Tensor.restrict (copiedSerial L M S C A B p j).first (copiedSerial L M S C A B p j).second
      (copiedSerial L M S C A B p j).third
      (Tensor.directSum (fun _ : Fin (L^j) => (((S.power j).product C).product (A.power j)).tensor)) =
      Tensor.directSum (fun _ : Fin (M^j) => (C.product (B.power j)).tensor) := by
  classical
  have h := (copiedSerial L M S C A B p j).identity
  rw [diagonal_product, diagonal_product] at h
  exact h


/-- Pool a repeated full matrix tensor by actual entry-index equivalences. -/
def matrixPowerIso (a j : ℕ) : Iso ((matrixFull a).power j) (matrixFull (a^j)) where
  x := matrixNestedX a j
  y := matrixNestedY a j
  z := matrixNestedZ a j
  coeff := fun x y z => congrFun (congrFun (congrFun (matrix_nested_power a j) x) y) z

attribute [local instance] GlobalFamilySampleBridge.matrixFiniteX GlobalFamilySampleBridge.matrixFiniteY

/-- Complete matrix-input reuse maps, with all input/output powers pooled. -/
def copiedMatrixSerial (L M a b : ℕ) (S C : FullTensor ℚ)
    [Fintype S.X] [Fintype S.Y] [Fintype C.X] [Fintype C.Y]
    (p : Maps ((diagonalFull L).product ((S.product C).product (matrixFull a)))
      ((diagonalFull M).product (C.product (matrixFull b)))) (j : ℕ) :
    Maps ((diagonalFull (L^j)).product (((S.power j).product C).product (matrixFull (a^j))))
      ((diagonalFull (M^j)).product (C.product (matrixFull (b^j)))) :=
  (Maps.ofIso ((Iso.refl _).product ((Iso.refl _).product (matrixPowerIso a j).symm))).trans
    ((copiedSerial L M S C (matrixFull a) (matrixFull b) p j).trans
      (Maps.ofIso ((Iso.refl _).product ((Iso.refl C).product (matrixPowerIso b j)))))

/-- The exact interpolation charge is raised to j, as in exactify-then-reuse. -/
theorem exactified_copy_count (L k d j : ℕ) :
    (((k*d+1) * L^k)^j) = (k*d+1)^j * L^(k*j) := by
  rw [mul_pow, pow_mul]

/-- Output sector multiplicities are likewise the actual repeated direct-sum count. -/
theorem repeated_sector_count (M k j : ℕ) : (M^(3*k))^j = M^(3*k*j) :=
  (pow_mul M (3*k) j).symm


/-- The complete repeated restriction keeps the full matrix input as a resource. -/
theorem copiedMatrixSerial_identity (L M a b : ℕ) (S C : FullTensor ℚ)
    [Fintype S.X] [Fintype S.Y] [Fintype C.X] [Fintype C.Y]
    (p : Maps ((diagonalFull L).product ((S.product C).product (matrixFull a)))
      ((diagonalFull M).product (C.product (matrixFull b)))) (j : ℕ) :
    Tensor.restrict (copiedMatrixSerial L M a b S C p j).first
      (copiedMatrixSerial L M a b S C p j).second (copiedMatrixSerial L M a b S C p j).third
      (Tensor.directSum (fun _ : Fin (L^j) => (((S.power j).product C).product (matrixFull (a^j))).tensor)) =
      Tensor.directSum (fun _ : Fin (M^j) => (C.product (matrixFull (b^j))).tensor) := by
  have h := (copiedMatrixSerial L M a b S C p j).identity
  rw [diagonal_product, diagonal_product] at h
  exact h

/-- A Laurent sample map can amplify a perturbation outside the constant catalyst. -/
def poleMap (ε : ℚ) (i j : Fin 2) : ℚ :=
  if i=0 then (if j=0 then 1 else 0) else (if j=0 then ε else ε⁻¹)

def poleSeed (i : Fin 2) : ℚ := if i=0 then 1 else 0

def poleOnce (i : Fin 2) : Polynomial ℚ := if i=0 then 1 else Polynomial.X

def poleTwice (i : Fin 2) : Polynomial ℚ := if i=0 then 1 else Polynomial.X + 1

/-- A degree-one first output has exactly the intended seed as constant term. -/
theorem pole_once (ε : ℚ) (i : Fin 2) :
    (∑ j : Fin 2, poleMap ε i j * poleSeed j) = (poleOnce i).eval ε := by
  fin_cases i <;> simp [poleMap, poleSeed, poleOnce]

/-- Reusing the same Laurent map changes the constant term. -/
theorem pole_twice (ε : ℚ) (hε : ε ≠ 0) (i : Fin 2) :
    (∑ j : Fin 2, poleMap ε i j * (poleOnce j).eval ε) = (poleTwice i).eval ε := by
  fin_cases i <;> simp [Fin.sum_univ_two, poleMap, poleOnce, poleTwice, hε]

theorem pole_constant_changed : (poleOnce 1).eval 0 = (0:ℚ) ∧ (poleTwice 1).eval 0 = 1 := by
  simp [poleOnce, poleTwice]


/-- Exact catalytic reuse after source supply: alpha^j inputs, beta^j outputs,
with one catalyst throughout and the complete matrix powers retained. -/
def catalyticSerial (α β a b : ℕ) (C : FullTensor ℚ) [Fintype C.X] [Fintype C.Y]
    (p : Maps ((diagonalFull α).product (C.product (matrixFull a)))
      ((diagonalFull β).product (C.product (matrixFull b)))) (j : ℕ) :
    Maps ((diagonalFull (α^j)).product (C.product (matrixFull (a^j))))
      ((diagonalFull (β^j)).product (C.product (matrixFull (b^j)))) :=
  (Maps.ofIso (((diagonalPowerIso α j).symm).product
    ((Iso.refl C).product (matrixPowerIso a j).symm))).trans
      ((serial (diagonalFull α) C (matrixFull a) ((diagonalFull β).product (matrixFull b))
        (p.trans (Maps.ofIso (swapHead (diagonalFull β) C (matrixFull b)))) j).trans
          (Maps.ofIso ((serialTargetIso β C (matrixFull b) j).trans
            ((Iso.refl _).product ((Iso.refl C).product (matrixPowerIso b j))))))

/-- Actual serial restriction identity in the exactified one-step interface. -/
theorem catalyticSerial_identity (α β a b : ℕ) (C : FullTensor ℚ) [Fintype C.X] [Fintype C.Y]
    (p : Maps ((diagonalFull α).product (C.product (matrixFull a)))
      ((diagonalFull β).product (C.product (matrixFull b)))) (j : ℕ) :
    Tensor.restrict (catalyticSerial α β a b C p j).first
      (catalyticSerial α β a b C p j).second (catalyticSerial α β a b C p j).third
      (Tensor.directSum (fun _ : Fin (α^j) => (C.product (matrixFull (a^j))).tensor)) =
      Tensor.directSum (fun _ : Fin (β^j) => (C.product (matrixFull (b^j))).tensor) := by
  have h := (catalyticSerial α β a b C p j).identity
  rw [diagonal_product, diagonal_product] at h
  exact h

end
end MatrixDimensionAudit.CatalystReuseBridge
