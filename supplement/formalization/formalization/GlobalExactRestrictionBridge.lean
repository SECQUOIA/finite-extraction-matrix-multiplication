import formalization.CatalystReuseBridge
import formalization.RankSupplyRestrictionBridge

/-! Compose the complete original sample matrices, exactify once, and then reuse one exact catalyst. -/

namespace MatrixDimensionAudit.GlobalExactRestrictionBridge
open OAI.MatrixMultiplication.Foundation
open TensorRankBridge TensorResourcePoolingBridge SignedCatalystLedgerBridge
open GlobalFamilySampleBridge OriginalLocalSampleBridge FamilyPolynomialAssemblyBridge SeparatorTensor
open CatalystReuseBridge AllRowProfile
open scoped BigOperators
noncomputable section
attribute [local instance] GlobalFamilySampleBridge.productFiniteX GlobalFamilySampleBridge.productFiniteY
  CatalystReuseBridge.nestedFiniteX CatalystReuseBridge.nestedFiniteY
  GlobalFamilySampleBridge.matrixFiniteX GlobalFamilySampleBridge.matrixFiniteY
  GlobalFamilySampleBridge.familySourceFiniteX GlobalFamilySampleBridge.familySourceFiniteY
  GlobalFamilySampleBridge.familyTargetFiniteX GlobalFamilySampleBridge.familyTargetFiniteY
  CatalystReuseBridge.diagonalFiniteX CatalystReuseBridge.diagonalFiniteY
  CatalystReuseBridge.diagonalDecX CatalystReuseBridge.diagonalDecY

/-- Lift every node's three actual matrices without mixing node labels. -/
def blockMatrix {E X U : Type} [DecidableEq E] (A : E → U → X → ℚ) :
    (E × U) → (E × X) → ℚ := fun x u => if x.1 = u.1 then A x.1 x.2 u.2 else 0

theorem block_entry {E X Y Z U V W : Type} [DecidableEq E]
    (T : E → Tensor ℚ X Y Z) (A : E → U → X → ℚ)
    (B : E → V → Y → ℚ) (C : E → W → Z → ℚ)
    (x : E × U) (y : E × V) (z : E × W) (u : E × X) (v : E × Y) (w : E × Z) :
    blockMatrix A x u * blockMatrix B y v * blockMatrix C z w * Tensor.directSum T u v w =
    if u.1=x.1 ∧ v.1=y.1 ∧ w.1=z.1 then
      A x.1 x.2 u.2 * B y.1 y.2 v.2 * C z.1 z.2 w.2 *
        Tensor.directSum T (x.1,u.2) (y.1,v.2) (z.1,w.2) else 0 := by
  by_cases hx : u.1=x.1 <;> by_cases hy : v.1=y.1 <;> by_cases hz : w.1=z.1
  all_goals simp_all [blockMatrix, eq_comm]

theorem block_restriction {E X Y Z U V W : Type} [Fintype E] [DecidableEq E]
    [Fintype X] [Fintype Y] [Fintype Z]
    (T : E → Tensor ℚ X Y Z) (A : E → U → X → ℚ)
    (B : E → V → Y → ℚ) (C : E → W → Z → ℚ) :
    Tensor.restrict (blockMatrix A) (blockMatrix B) (blockMatrix C) (Tensor.directSum T) =
      Tensor.directSum (fun e => Tensor.restrict (A e) (B e) (C e) (T e)) := by
  classical
  funext x y z
  unfold Tensor.restrict
  simp_rw [block_entry]
  simp only [Fintype.sum_prod_type, ite_and, Finset.sum_ite_irrel]
  by_cases hxy : x.1=y.1 <;> by_cases hxz : x.1=z.1
  all_goals simp_all [Tensor.directSum]

def powerCopyX (A : FullTensor ℚ) (L k : Nat) :=
  Equiv.prodCongr (wordIndex L k) (PowerCoordinateBridge.xCoordinates ℚ A k).symm
def powerCopyY (A : FullTensor ℚ) (L k : Nat) :=
  Equiv.prodCongr (wordIndex L k) (PowerCoordinateBridge.yCoordinates ℚ A k).symm
def powerCopyZ (A : FullTensor ℚ) (L k : Nat) :=
  Equiv.prodCongr (wordIndex L k) (PowerCoordinateBridge.zCoordinates ℚ A k).symm

theorem source_power_copies (A : FullTensor ℚ) (L k : Nat) :
    Tensor.directSum (fun _ : Fin k → Fin L => Tensor.power A.tensor k) =
      Tensor.pullback (powerCopyX A L k) (powerCopyY A L k) (powerCopyZ A L k)
        (Tensor.directSum (fun _ : Fin (L^k) => (A.power k).tensor)) :=
  directSum_reindex _ _ (wordIndex L k) _ _ _ (PowerCoordinateBridge.tensorPower_eq_pullback ℚ A k)

def samplePowerX (A B : FullTensor ℚ) [Fintype A.X] [Fintype A.Y]
    {M L d : Nat} (p : NormalizedSample A B M L d) (k : Nat) (ε : ℚ) :=
  fun (x : Fin k → Fin (M^3) × B.X) (u : Fin (L^k) × (A.power k).X) =>
    jointMatrix (fun _ : Fin k => L) (fun _ => p.maps.first () ε) x ((powerCopyX A L k).symm u)
def samplePowerY (A B : FullTensor ℚ) [Fintype A.X] [Fintype A.Y]
    {M L d : Nat} (p : NormalizedSample A B M L d) (k : Nat) (ε : ℚ) :=
  fun (y : Fin k → Fin (M^3) × B.Y) (v : Fin (L^k) × (A.power k).Y) =>
    jointMatrix (fun _ : Fin k => L) (fun _ => p.maps.second () ε) y ((powerCopyY A L k).symm v)
def samplePowerZ (A B : FullTensor ℚ) [Fintype A.X] [Fintype A.Y]
    {M L d : Nat} (p : NormalizedSample A B M L d) (k : Nat) (ε : ℚ) :=
  fun (z : Fin k → Fin (M^3) × B.Z) (w : Fin (L^k) × (A.power k).Z) =>
    jointMatrix (fun _ : Fin k => L) (fun _ => p.maps.third () ε) z ((powerCopyZ A L k).symm w)

theorem sample_power_restriction (A B : FullTensor ℚ) [Fintype A.X] [Fintype A.Y]
    {M L d : Nat} (p : NormalizedSample A B M L d) (k : Nat) (ε : ℚ) (hε : ε ≠ 0) :
    Tensor.restrict (samplePowerX A B p k ε) (samplePowerY A B p k ε) (samplePowerZ A B p k ε)
      (Tensor.directSum (fun _ : Fin (L^k) => (A.power k).tensor)) =
      evaluate (Tensor.power p.polynomial k) ε := by
  classical
  have h := joint_sample_restriction (fun _ : Fin k => L) (fun _ => A.tensor)
    (fun _ => p.polynomial) (fun _ => p.maps.first ()) (fun _ => p.maps.second ())
    (fun _ => p.maps.third ()) ε (fun _ => p.maps.identity ε hε ())
  change Tensor.restrict _ _ _ (Tensor.directSum (fun _ : Fin k → Fin L => Tensor.power A.tensor k)) =
    Tensor.power (evaluate p.polynomial ε) k at h
  rw [source_power_copies, FamilyPolynomialAssemblyBridge.restriction_reindex] at h
  exact h.trans (FamilyPolynomialAssemblyBridge.evaluate_power p.polynomial k ε).symm

def nodeCopies (E L : Nat) (X : Type) : (Fin E × (Fin L × X)) ≃ (Fin (E*L) × X) :=
  (Equiv.prodAssoc _ _ _).symm.trans (Equiv.prodCongr finProdFinEquiv (Equiv.refl X))

theorem nested_copies (A : FullTensor ℚ) (E L : Nat) :
    Tensor.directSum (fun _ : Fin E => Tensor.directSum (fun _ : Fin L => A.tensor)) =
      Tensor.pullback (nodeCopies E L A.X) (nodeCopies E L A.Y) (nodeCopies E L A.Z)
        (Tensor.directSum (fun _ : Fin (E*L) => A.tensor)) := by
  classical
  funext x y z
  change (if x.1=y.1 ∧ x.1=z.1 then
      (if x.2.1=y.2.1 ∧ x.2.1=z.2.1 then A.tensor x.2.2 y.2.2 z.2.2 else 0) else 0) =
    if finProdFinEquiv (x.1,x.2.1)=finProdFinEquiv (y.1,y.2.1) ∧
      finProdFinEquiv (x.1,x.2.1)=finProdFinEquiv (z.1,z.2.1) then A.tensor x.2.2 y.2.2 z.2.2 else 0
  simp only [Equiv.apply_eq_iff_eq, Prod.mk.injEq]
  split_ifs <;> simp_all <;> grind

def outputPowerX (B : FullTensor ℚ) (M k : Nat) :
    (Fin k → Fin (M^3) × B.X) ≃ (Fin (M^(3*k)) × (B.power k).X) :=
  (splitPairs _ _).trans (Equiv.prodCongr
    ((wordIndex (M^3) k).trans (finCongr (pow_mul M 3 k).symm))
    (PowerCoordinateBridge.xCoordinates ℚ B k).symm)
def outputPowerY (B : FullTensor ℚ) (M k : Nat) :
    (Fin k → Fin (M^3) × B.Y) ≃ (Fin (M^(3*k)) × (B.power k).Y) :=
  (splitPairs _ _).trans (Equiv.prodCongr
    ((wordIndex (M^3) k).trans (finCongr (pow_mul M 3 k).symm))
    (PowerCoordinateBridge.yCoordinates ℚ B k).symm)
def outputPowerZ (B : FullTensor ℚ) (M k : Nat) :
    (Fin k → Fin (M^3) × B.Z) ≃ (Fin (M^(3*k)) × (B.power k).Z) :=
  (splitPairs _ _).trans (Equiv.prodCongr
    ((wordIndex (M^3) k).trans (finCongr (pow_mul M 3 k).symm))
    (PowerCoordinateBridge.zCoordinates ℚ B k).symm)

theorem output_power_copies (B : FullTensor ℚ) (M k : Nat) :
    Tensor.power (Tensor.directSum (fun _ : Fin (M^3) => B.tensor)) k =
      Tensor.pullback (outputPowerX B M k) (outputPowerY B M k) (outputPowerZ B M k)
        (Tensor.directSum (fun _ : Fin (M^(3*k)) => (B.power k).tensor)) := by
  classical
  have h := family_copies (fun _ : Fin k => M^3) (fun _ => B.tensor)
  change Tensor.power (Tensor.directSum (fun _ : Fin (M^3) => B.tensor)) k =
    Tensor.pullback (splitPairs _ _) (splitPairs _ _) (splitPairs _ _)
      (Tensor.directSum (fun _ : Fin k → Fin (M^3) => Tensor.power B.tensor k)) at h
  rw [directSum_reindex _ (B.power k).tensor
    ((wordIndex (M^3) k).trans (finCongr (pow_mul M 3 k).symm)) _ _ _
    (PowerCoordinateBridge.tensorPower_eq_pullback ℚ B k)] at h
  exact h

set_option maxHeartbeats 1000000 in
/-- Compose every powered original sample restriction with the single node fold. -/
def exactSample (A B : FullTensor ℚ) [Fintype A.X] [Fintype A.Y]
    [Fintype B.X] [Fintype B.Y] {M L d : Nat}
    (p : NormalizedSample A B M L d) (k : Nat) :
    Maps ((diagonalFull ((k*d+1)*L^k)).product (A.power k))
      ((diagonalFull (M^(3*k))).product (B.power k)) := by
  classical
  let ax := blockMatrix (fun e : Fin (k*d+1) => samplePowerX A B p k (node e))
  let ay := blockMatrix (fun e : Fin (k*d+1) => samplePowerY A B p k (node e))
  let az := blockMatrix (fun e : Fin (k*d+1) => samplePowerZ A B p k (node e))
  let fx := Tensor.composeRestrictionMatrix (foldMatrix (exactWeight (k*d))) ax
  let fy := Tensor.composeRestrictionMatrix (foldMatrix (fun _ : Fin (k*d+1) => (1:ℚ))) ay
  let fz := Tensor.composeRestrictionMatrix (foldMatrix (fun _ : Fin (k*d+1) => (1:ℚ))) az
  have hnodes : Tensor.restrict ax ay az
      (Tensor.directSum (fun _ : Fin (k*d+1) =>
        Tensor.directSum (fun _ : Fin (L^k) => (A.power k).tensor))) =
      Tensor.directSum (fun e : Fin (k*d+1) => evaluate (Tensor.power p.polynomial k) (node e)) := by
    dsimp only [ax, ay, az]
    rw [block_restriction]
    congr 1
    funext e
    exact sample_power_restriction A B p k (node e) (Separator.rationalNode_nonzero e.val)
  have h : Tensor.restrict fx fy fz
      (Tensor.directSum (fun _ : Fin (k*d+1) =>
        Tensor.directSum (fun _ : Fin (L^k) => (A.power k).tensor))) =
      evaluate (Tensor.power p.polynomial k) 0 := by
    change Tensor.restrict (Tensor.composeRestrictionMatrix _ ax)
      (Tensor.composeRestrictionMatrix _ ay) (Tensor.composeRestrictionMatrix _ az) _ = _
    rw [← Tensor.restrict_restrict, hnodes]
    exact tensor_exactification _ (k*d) (tensor_power_degree _ k d p.bound)
  rw [nested_copies, FamilyPolynomialAssemblyBridge.restriction_reindex] at h
  rw [FamilyPolynomialAssemblyBridge.evaluate_power, p.constant, output_power_copies] at h
  let ex := outputPowerX B M k
  let ey := outputPowerY B M k
  let ez := outputPowerZ B M k
  exact {
    first := fun x u => fx (ex.symm x) ((nodeCopies (k*d+1) (L^k) (A.power k).X).symm u)
    second := fun y v => fy (ey.symm y) ((nodeCopies (k*d+1) (L^k) (A.power k).Y).symm v)
    third := fun z w => fz (ez.symm z) ((nodeCopies (k*d+1) (L^k) (A.power k).Z).symm w)
    identity := by
      rw [diagonal_product, diagonal_product]
      funext x y z
      change Fin (M^(3*k)) × (B.power k).X at x
      change Fin (M^(3*k)) × (B.power k).Y at y
      change Fin (M^(3*k)) × (B.power k).Z at z
      have hh := congrFun (congrFun (congrFun h (ex.symm x)) (ey.symm y)) (ez.symm z)
      change _ = Tensor.directSum (fun _ : Fin (M^(3*k)) => (B.power k).tensor)
        (ex (ex.symm x)) (ey (ey.symm y)) (ez (ez.symm z)) at hh
      rw [ex.apply_symm_apply, ey.apply_symm_apply, ez.apply_symm_apply] at hh
      exact hh }

attribute [local instance] GlobalFamilySampleBridge.splitFiniteX GlobalFamilySampleBridge.splitFiniteY
  GlobalFamilySampleBridge.resetFiniteX GlobalFamilySampleBridge.resetFiniteY
  GlobalFamilySampleBridge.sourceFiniteX GlobalFamilySampleBridge.sourceFiniteY
local instance splitListFiniteX (negative : Bool) (r : Nat) (hr : 2 ≤ r) :
    (xs : List Nat) → Fintype (splitFactors ℚ negative r hr xs).X
  | [] => inferInstanceAs (Fintype Unit)
  | x :: xs => by
    change Fintype ((splitFactor ℚ negative r hr x).X × (splitFactors ℚ negative r hr xs).X)
    letI := splitListFiniteX negative r hr xs
    infer_instance
local instance splitListFiniteY (negative : Bool) (r : Nat) (hr : 2 ≤ r) :
    (xs : List Nat) → Fintype (splitFactors ℚ negative r hr xs).Y
  | [] => inferInstanceAs (Fintype Unit)
  | x :: xs => by
    change Fintype ((splitFactor ℚ negative r hr x).Y × (splitFactors ℚ negative r hr xs).Y)
    letI := splitListFiniteY negative r hr xs
    infer_instance
local instance topFiniteX (row : Row r 1 K) (hr : 2 ≤ r) : Fintype (topConsumed ℚ row hr).X := by
  unfold topConsumed; infer_instance
local instance topFiniteY (row : Row r 1 K) (hr : 2 ≤ r) : Fintype (topConsumed ℚ row hr).Y := by
  unfold topConsumed; infer_instance
local instance lowerFiniteX (negative : Bool) (row : Row r 2 K) (hr : 2 ≤ r) : Fintype (lowerConsumed ℚ negative row hr).X := by
  unfold lowerConsumed; infer_instance
local instance lowerFiniteY (negative : Bool) (row : Row r 2 K) (hr : 2 ≤ r) : Fintype (lowerConsumed ℚ negative row hr).Y := by
  unfold lowerConsumed; infer_instance
local instance lowerRowsFiniteX (depth : Nat) : {n : Nat} → (rows : LowerRows K n) → Fintype (lowerRowsConsumed ℚ depth rows).X
  | _, .nil => inferInstanceAs (Fintype Unit)
  | _, .cons row tail => by unfold lowerRowsConsumed; letI := lowerRowsFiniteX (depth+1) tail; infer_instance
local instance lowerRowsFiniteY (depth : Nat) : {n : Nat} → (rows : LowerRows K n) → Fintype (lowerRowsConsumed ℚ depth rows).Y
  | _, .nil => inferInstanceAs (Fintype Unit)
  | _, .cons row tail => by unfold lowerRowsConsumed; letI := lowerRowsFiniteY (depth+1) tail; infer_instance
local instance catalystFiniteX (family : Family n K) : Fintype (familyConsumed ℚ family).X := by
  unfold familyConsumed; infer_instance
local instance catalystFiniteY (family : Family n K) : Fintype (familyConsumed ℚ family).Y := by
  unfold familyConsumed; infer_instance

/-- Split nested powers by actual coordinate equivalences. -/
def powerAddIso (A : FullTensor ℚ) : (a b : Nat) → Iso (A.power (a+b)) ((A.power a).product (A.power b))
  | 0, b => by simpa only [Nat.zero_add, FullTensor.power] using (Iso.unitLeft (A.power b)).symm
  | a+1, b => by
    simpa only [Nat.succ_add, FullTensor.power] using
      ((Iso.refl A).product (powerAddIso A a b)).trans (Iso.assoc A (A.power a) (A.power b)).symm

def powerMulIso (A : FullTensor ℚ) (a : Nat) : (b : Nat) → Iso ((A.power a).power b) (A.power (a*b))
  | 0 => Iso.refl _
  | b+1 => ((Iso.refl (A.power a)).product (powerMulIso A a b)).trans
      ((powerAddIso A a (a*b)).symm.trans
        (Iso.ofEq (congrArg A.power (by rw [Nat.mul_succ]; omega))))

def inputPowerIso (family : Family n K) (k : Nat) :
    Iso ((familySource family).power k)
      (((((sourceFactor ℚ (n+2) (by omega)).power K).power k).product
        ((familyConsumed ℚ family).power k)).product (matrixFull (family.dimension^k))) :=
  (powerProductIso _ _ k).trans ((powerProductIso _ _ k).product (matrixPowerIso _ k))

def outputPowerIso (family : Family n K) (k : Nat) :
    Iso ((familyTarget family).power k)
      (((familyConsumed ℚ family).power k).product (matrixFull ((2^K*family.count)^k))) :=
  (powerProductIso _ _ k).trans ((Iso.refl _).product (matrixPowerIso _ k))

def exactCopies (family : Family n K) (k : Nat) := (k*familyDegree family+1)*familyCopies family^k

/-- Exact one-pass maps on the full grouped source, catalyst, and matrix resources. -/
def familyExact (family : Family n K) (k : Nat) :
    Maps ((diagonalFull (exactCopies family k)).product
      (((((sourceFactor ℚ (n+2) (by omega)).power K).power k).product
        ((familyConsumed ℚ family).power k)).product (matrixFull (family.dimension^k))))
      ((diagonalFull (family.count^(3*k))).product
        (((familyConsumed ℚ family).power k).product (matrixFull ((2^K*family.count)^k)))) :=
  (Maps.ofIso ((Iso.refl _).product (inputPowerIso family k).symm)).trans
    ((exactSample _ _ (familySample family) k).trans
      (Maps.ofIso ((Iso.refl _).product (outputPowerIso family k))))

/-- Flatten only the external source powers; the catalyst occurs exactly once. -/
def repeatedInputIso (family : Family n K) (k j : Nat) :
    Iso (((((((sourceFactor ℚ (n+2) (by omega)).power K).power k).power j).product
        ((familyConsumed ℚ family).power k)).product (matrixFull ((family.dimension^k)^j))))
      ((jointSource ℚ family k j).product (matrixFull (family.dimension^(k*j)))) :=
  ((((powerMulIso _ K k).power j).trans (powerMulIso _ (K*k) j)).product (Iso.refl _)).product
    (Iso.ofEq (congrArg matrixFull (pow_mul family.dimension k j).symm))

local instance jointFiniteX (family : Family n K) (k j : Nat) : Fintype (jointSource ℚ family k j).X := by
  unfold jointSource; infer_instance
local instance jointFiniteY (family : Family n K) (k j : Nat) : Fintype (jointSource ℚ family k j).Y := by
  unfold jointSource; infer_instance

/-- Serial reuse of the exact powered relation, with E_k^j and one catalyst C^k. -/
def familySerial (family : Family n K) (k j : Nat) :
    Maps ((diagonalFull (exactCopies family k ^ j)).product
      ((jointSource ℚ family k j).product (matrixFull (family.dimension^(k*j)))))
      ((diagonalFull (family.count^(3*k*j))).product
        (((familyConsumed ℚ family).power k).product (matrixFull ((2^K*family.count)^(k*j))))) := by
  let h := copiedMatrixSerial (exactCopies family k) (family.count^(3*k))
    (family.dimension^k) ((2^K*family.count)^k)
    (((sourceFactor ℚ (n+2) (by omega)).power K).power k)
    ((familyConsumed ℚ family).power k) (familyExact family k) j
  let a := Maps.ofIso ((Iso.refl (diagonalFull (exactCopies family k ^ j))).product (repeatedInputIso family k j).symm)
  let b := Maps.ofIso ((Iso.ofEq (congrArg diagonalFull (pow_mul family.count (3*k) j).symm)).product
    ((Iso.refl ((familyConsumed ℚ family).power k)).product (Iso.ofEq (congrArg matrixFull (pow_mul (2^K*family.count) k j).symm))))
  exact a.trans (h.trans b)

theorem family_serial_identity (family : Family n K) (k j : Nat) :
    Tensor.restrict (familySerial family k j).first (familySerial family k j).second
      (familySerial family k j).third
      (Tensor.directSum (fun _ : Fin (exactCopies family k ^ j) =>
        ((jointSource ℚ family k j).product (matrixFull (family.dimension^(k*j)))).tensor)) =
      Tensor.directSum (fun _ : Fin (family.count^(3*k*j)) =>
        (((familyConsumed ℚ family).power k).product (matrixFull ((2^K*family.count)^(k*j)))).tensor) := by
  have h := (familySerial family k j).identity
  rw [diagonal_product, diagonal_product] at h
  exact h

theorem exact_source_copy_count (family : Family n K) (k j : Nat) :
    exactCopies family k ^ j = (k*familyDegree family+1)^j * familyCopies family^(k*j) :=
  exactified_copy_count _ _ _ _

/-- Supply the complete pooled source while retaining the matrix input. -/
def supplyMaps (S : FullTensor ℚ) (D R : Nat)
    (hs : Tensor.RankAtMost S.tensor R) :
    Maps ((diagonalFull R).product (matrixFull D)) (S.product (matrixFull D)) := by
  classical
  choose a b c h using RankSupplyRestrictionBridge.full_matrix_restriction S D R hs
  exact { first := a, second := b, third := c, identity := by rw [diagonal_product]; exact h }

/-- An actual copied supply restriction pays one certificate for the entire joint source. -/
def copiedSupply (S : FullTensor ℚ) [Fintype S.X] [Fintype S.Y] (D R N : Nat)
    (hs : Tensor.RankAtMost S.tensor R) :
    Maps ((diagonalFull (R*N)).product (matrixFull D))
      ((diagonalFull N).product (S.product (matrixFull D))) :=
  (Maps.ofIso (((Iso.assoc (diagonalFull N) (diagonalFull R) (matrixFull D)).symm.trans
    (((diagonalProductIso N R).trans (Iso.ofEq (congrArg diagonalFull (Nat.mul_comm N R)))).product
      (Iso.refl (matrixFull D)))).symm)).trans
    ((Maps.refl (diagonalFull N)).product (supplyMaps S D R hs))

/-- Complete relative restriction to all output blocks, retaining the exact catalyst. -/
def familyRelativeWithCatalyst (family : Family n K) (k j R : Nat)
    (hs : Tensor.RankAtMost (jointSource ℚ family k j).tensor R) :
    Maps ((diagonalFull (R * exactCopies family k ^ j)).product (matrixFull (family.dimension^(k*j))))
      ((diagonalFull (family.count^(3*k*j))).product
        (((familyConsumed ℚ family).power k).product (matrixFull ((2^K*family.count)^(k*j))))) :=
  (copiedSupply (jointSource ℚ family k j) _ R _ hs).trans (familySerial family k j)

/-- The actual common catalyst has a nonempty identity minor. -/
theorem catalyst_dimension_pos (family : Family n K) : 0 < (familyConsumed ℚ family).dimension := by
  have hp : ∀ n, 0 < GeneralRowCatalyst.lowerSourceProduct n := by
    intro n
    induction n with
    | zero => exact Nat.zero_lt_one
    | succ n ih =>
      change 0 < GeneralRowCatalyst.sourceLeg (n+2) * GeneralRowCatalyst.lowerSourceProduct n
      apply Nat.mul_pos _ ih
      unfold GeneralRowCatalyst.sourceLeg
      have h : 0 < 2*(n+2)-1 := by omega
      positivity
  rw [familyConsumed_dimension]
  exact lt_of_lt_of_le (Nat.mul_pos (pow_pos (hp n) K) (by positivity))
    (GeneralRowCatalyst.family_charge_floor family)

local instance unitFiniteX : Fintype (FullTensor.unit (F := ℚ)).X := inferInstanceAs (Fintype Unit)
local instance unitFiniteY : Fintype (FullTensor.unit (F := ℚ)).Y := inferInstanceAs (Fintype Unit)

/-- Extract the scalar identity minor using three actual coordinate projections. -/
def unitMaps (A : FullTensor ℚ) [Fintype A.X] [Fintype A.Y] (hA : 0 < A.dimension) :
    Maps A (FullTensor.unit (F := ℚ)) := by
  classical
  let z : A.Z := Classical.choice (Fintype.card_pos_iff.mp hA)
  exact {
    first := TriplingLocalRecipeBridge.projectionMatrix (fun _ : Unit => A.left z)
    second := TriplingLocalRecipeBridge.projectionMatrix (fun _ : Unit => A.right z)
    third := TriplingLocalRecipeBridge.projectionMatrix (fun _ : Unit => z)
    identity := by
      change Tensor.restrict (TriplingLocalRecipeBridge.projectionMatrix (fun _ : Unit => A.left z))
        (TriplingLocalRecipeBridge.projectionMatrix (fun _ : Unit => A.right z))
        (TriplingLocalRecipeBridge.projectionMatrix (fun _ : Unit => z)) A.tensor = (fun _ _ _ : Unit => 1)
      rw [OriginalLocalSampleBridge.projection_restriction]
      funext x y w
      change A.tensor (A.left z) (A.right z) z = 1
      simp only [A.identity, ite_true] }

/-- Discard only the output catalyst after all exact restrictions are composed. -/
def eraseCatalyst (N : Nat) (C B : FullTensor ℚ) [Fintype C.X] [Fintype C.Y]
    [Fintype B.X] [Fintype B.Y] (hC : 0 < C.dimension) :
    Maps ((diagonalFull N).product (C.product B)) ((diagonalFull N).product B) :=
  (Maps.refl (diagonalFull N)).product
    (((unitMaps C hC).product (Maps.refl B)).trans (Maps.ofIso (Iso.unitLeft B)))

def relativeCopies (family : Family n K) (k j R : Nat) : Nat :=
  R * (k*familyDegree family+1)^j * familyCopies family^(k*j)

/-- An actual relative matrix algorithm: supply the complete joint source once,
reuse one powered catalyst through exact restrictions, then extract its scalar minor. -/
def familyRelative (family : Family n K) (k j R : Nat)
    (hs : Tensor.RankAtMost (jointSource ℚ family k j).tensor R) :
    Maps ((diagonalFull (relativeCopies family k j R)).product (matrixFull (family.dimension^(k*j))))
      ((diagonalFull (family.count^(3*k*j))).product (matrixFull ((2^K*family.count)^(k*j)))) := by
  have hc : relativeCopies family k j R = R * exactCopies family k ^ j := by
    rw [exact_source_copy_count]
    exact (mul_assoc _ _ _)
  let a := Maps.ofIso ((Iso.ofEq (congrArg diagonalFull hc)).product
    (Iso.refl (matrixFull (family.dimension^(k*j)))))
  let b := eraseCatalyst (family.count^(3*k*j)) ((familyConsumed ℚ family).power k)
    (matrixFull ((2^K*family.count)^(k*j)))
    (by rw [FullTensor.dimension_power]; exact pow_pos (catalyst_dimension_pos family) k)
  exact a.trans ((familyRelativeWithCatalyst family k j R hs).trans b)

/-- All four relative-algorithm parameters occur in the checked coefficient identity. -/
theorem family_relative_identity (family : Family n K) (k j R : Nat)
    (hs : Tensor.RankAtMost (jointSource ℚ family k j).tensor R) :
    Tensor.restrict (familyRelative family k j R hs).first (familyRelative family k j R hs).second
      (familyRelative family k j R hs).third
      (Tensor.directSum (fun _ : Fin (relativeCopies family k j R) =>
        (matrixFull (family.dimension^(k*j))).tensor)) =
      Tensor.directSum (fun _ : Fin (family.count^(3*k*j)) =>
        (matrixFull ((2^K*family.count)^(k*j))).tensor) := by
  have h := (familyRelative family k j R hs).identity
  rw [diagonal_product, diagonal_product] at h
  exact h

end
end MatrixDimensionAudit.GlobalExactRestrictionBridge
