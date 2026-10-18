import formalization.SuppliedGlobalRestrictionBridge
import formalization.RealExponentBridge
import OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.RecursiveBlockPrograms

/-! Actual matrix tensor restrictions give finite arithmetic batch programs. -/
namespace MatrixDimensionAudit.RelativeAlgorithmBridge
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.Arithmetic
open TensorRankBridge TensorResourcePoolingBridge SignedCatalystLedgerBridge CatalystReuseBridge
open scoped BigOperators
noncomputable section
attribute [local instance] GlobalFamilySampleBridge.productFiniteX GlobalFamilySampleBridge.productFiniteY
attribute [local instance] GlobalFamilySampleBridge.matrixFiniteX GlobalFamilySampleBridge.matrixFiniteY
attribute [local instance] CatalystReuseBridge.diagonalFiniteX CatalystReuseBridge.diagonalFiniteY
attribute [local instance] CatalystReuseBridge.diagonalDecX CatalystReuseBridge.diagonalDecY

/-- Actual three-map restriction from q source products to m target products. -/
abbrev MatrixTensorMaps (q A m B : ℕ) :=
  Maps ((diagonalFull q).product (matrixFull A)) ((diagonalFull m).product (matrixFull B))

/-- Bilinear evaluation of a restriction is linear preprocessing, source
contraction, and linear recombination. -/
theorem contract_restrict {X Y Z X' Y' Z' : Type}
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype X'] [Fintype Y']
    (T : Tensor ℚ X Y Z) (a : X' → X → ℚ) (b : Y' → Y → ℚ) (c : Z' → Z → ℚ)
    (left : X' → ℚ) (right : Y' → ℚ) (z' : Z') :
    Tensor.contract (Tensor.restrict a b c T) left right z' =
      ∑ z, c z' z * Tensor.contract T (fun x => ∑ x', a x' x * left x')
        (fun y => ∑ y', b y' y * right y') z := by
  let e : (X' × (Y' × (X × (Y × Z)))) ≃ (Z × (X × (Y × (X' × Y')))) := {
    toFun := fun p => (p.2.2.2.2, (p.2.2.1, (p.2.2.2.1, (p.1, p.2.1))))
    invFun := fun p => (p.2.2.2.1, (p.2.2.2.2, (p.2.1, (p.2.2.1, p.1))))
    left_inv _ := rfl
    right_inv _ := rfl }
  have he := e.sum_comp (fun p => c z' p.1 *
    (T p.2.1 p.2.2.1 p.1 * (a p.2.2.2.1 p.2.1 * left p.2.2.2.1) *
      (b p.2.2.2.2 p.2.2.1 * right p.2.2.2.2)))
  simp only [Fintype.sum_prod_type, e, Equiv.coe_fn_mk] at he
  simp only [Tensor.contract, Tensor.restrict, Finset.sum_mul, Finset.mul_sum]
  calc
    _ = ∑ x', ∑ y', ∑ x, ∑ y, ∑ z,
        c z' z * (T x y z * (a x' x * left x') * (b y' y * right y')) := by
      repeat' (apply Finset.sum_congr rfl; intro _ _)
      ring
    _ = _ := by
      rw [he]
      apply Finset.sum_congr rfl
      intro z _
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      exact Finset.sum_comm

/-- Contracting an actual direct sum computes every independent matrix product. -/
theorem contract_matrix_copies (m B : ℕ)
    (left right : Fin m × (Fin B × Fin B) → ℚ) (g : Fin m) (i k : Fin B) :
    Tensor.contract (Tensor.directSum (fun _ : Fin m => matrix B)) left right (g,(k,i)) =
      ∑ j, left (g,(i,j)) * right (g,(j,k)) := by
  simp [Tensor.contract, Tensor.directSum, matrix, Tensor.matrixCoefficients,
    Fintype.sum_prod_type, ite_and, ite_mul]

theorem contract_matrix_copies_at (m B : ℕ)
    (left right : Fin m × (Fin B × Fin B) → ℚ) (z : Fin m × (Fin B × Fin B)) :
    Tensor.contract (Tensor.directSum (fun _ : Fin m => matrix B)) left right z =
      ∑ j, left (z.1,(z.2.2,j)) * right (z.1,(j,z.2.1)) := by
  rcases z with ⟨g,k,i⟩
  exact contract_matrix_copies m B left right g i k

/-- Source matrices formed by the restriction's first leg. -/
def encodedLeft {q A m B : ℕ} (p : MatrixTensorMaps q A m B)
    (inputs : Fin m × MatrixInput B B B → ℚ) (s : Fin q) (u v : Fin A) : ℚ :=
  ∑ x : Fin m × (Fin B × Fin B), p.first x (s,(u,v)) * inputs (x.1,.inl x.2)

def encodedRight {q A m B : ℕ} (p : MatrixTensorMaps q A m B)
    (inputs : Fin m × MatrixInput B B B → ℚ) (s : Fin q) (u v : Fin A) : ℚ :=
  ∑ y : Fin m × (Fin B × Fin B), p.second y (s,(u,v)) * inputs (y.1,.inr y.2)

/-- The output map decodes q genuine source matrix products. -/
theorem coefficient_batch_correct {q A m B : ℕ} (p : MatrixTensorMaps q A m B)
    (inputs : Fin m × MatrixInput B B B → ℚ) (g : Fin m) (i k : Fin B) :
    (∑ z : Fin q × (Fin A × Fin A), p.third (g,(k,i)) (z.1,(z.2.2,z.2.1)) *
      ∑ j, encodedLeft p inputs z.1 z.2.1 j * encodedRight p inputs z.1 j z.2.2) =
      ∑ j, inputs (g,.inl (i,j)) * inputs (g,.inr (j,k)) := by
  have h := p.identity
  rw [diagonal_product, diagonal_product] at h
  change Tensor.restrict p.first p.second p.third (Tensor.directSum (fun _ : Fin q => matrix A)) =
    Tensor.directSum (fun _ : Fin m => matrix B) at h
  let aa : (Fin m × (Fin B × Fin B)) → (Fin q × (Fin A × Fin A)) → ℚ := p.first
  let bb : (Fin m × (Fin B × Fin B)) → (Fin q × (Fin A × Fin A)) → ℚ := p.second
  let cc : (Fin m × (Fin B × Fin B)) → (Fin q × (Fin A × Fin A)) → ℚ := p.third
  have hh : Tensor.restrict aa bb cc (Tensor.directSum (fun _ : Fin q => matrix A)) =
      Tensor.directSum (fun _ : Fin m => matrix B) := h
  have hc := contract_restrict (Tensor.directSum (fun _ : Fin q => matrix A))
    aa bb cc (fun x => inputs (x.1,.inl x.2))
    (fun y => inputs (y.1,.inr y.2)) (g,(k,i))
  rw [hh, contract_matrix_copies] at hc
  simp_rw [contract_matrix_copies_at] at hc
  dsimp only [aa, bb, cc] at hc
  rw [Fintype.sum_prod_type] at hc ⊢
  have hs : ∀ s : Fin q,
      (∑ z : Fin A × Fin A, p.third (g,(k,i)) (s,z) *
        ∑ j, encodedLeft p inputs s z.2 j * encodedRight p inputs s j z.1) =
      ∑ z : Fin A × Fin A, p.third (g,(k,i)) (s,(z.2,z.1)) *
        ∑ j, encodedLeft p inputs s z.1 j * encodedRight p inputs s j z.2 := by
    intro s
    exact ((Equiv.prodComm (Fin A) (Fin A)).sum_comp _).symm
  calc
    _ = ∑ s : Fin q, ∑ z : Fin A × Fin A, p.third (g,(k,i)) (s,z) *
        ∑ j, encodedLeft p inputs s z.2 j * encodedRight p inputs s j z.1 := by
      apply Finset.sum_congr rfl
      intro s _
      exact (hs s).symm
    _ = _ := hc.symm


open RecursiveBlock

/-- Compile each source input entry as its prescribed linear combination. -/
def inputExpressions {q A m B : ℕ} (p : MatrixTensorMaps q A m B) :
    (Fin q × MatrixInput A A A) → Expression ℚ (Fin m × MatrixInput B B B)
  | (s,.inl uv) => LinearExpression.linear (fun x : Fin m × (Fin B × Fin B) => p.first x (s,uv))
      (fun x => (x.1,.inl x.2))
  | (s,.inr uv) => LinearExpression.linear (fun y : Fin m × (Fin B × Fin B) => p.second y (s,uv))
      (fun y => (y.1,.inr y.2))

def inputProgram {q A m B : ℕ} (p : MatrixTensorMaps q A m B) := Family.expressions (inputExpressions p)

/-- Compile the third-leg linear recombination, with output-pair order restored. -/
def outputExpressions {q A m B : ℕ} (p : MatrixTensorMaps q A m B)
    (o : Fin m × (Fin B × Fin B)) : Expression ℚ (Fin q × (Fin A × Fin A)) :=
  LinearExpression.linear (fun z : Fin q × (Fin A × Fin A) =>
    p.third (o.1,(o.2.2,o.2.1)) (z.1,(z.2.2,z.2.1))) id

def outputProgram {q A m B : ℕ} (p : MatrixTensorMaps q A m B) := Family.expressions (outputExpressions p)

/-- A genuine finite arithmetic program computing every target product. -/
def batchProgram {q A m B : ℕ} (p : MatrixTensorMaps q A m B) (alg : MatrixAlgorithm ℚ A A A) :
    Family ℚ (Fin m × MatrixInput B B B) (Fin m × (Fin B × Fin B)) :=
  (inputProgram p).compose ((Family.copies q (Family.ofMatrix alg)).compose (outputProgram p))

theorem inputProgram_left {q A m B : ℕ} (p : MatrixTensorMaps q A m B)
    (inputs : Fin m × MatrixInput B B B → ℚ) (s : Fin q) (u v : Fin A) :
    (inputProgram p).eval inputs (s,.inl (u,v)) = encodedLeft p inputs s u v := by
  simp only [inputProgram, Family.eval_expressions, inputExpressions, LinearExpression.eval_linear, encodedLeft]

theorem inputProgram_right {q A m B : ℕ} (p : MatrixTensorMaps q A m B)
    (inputs : Fin m × MatrixInput B B B → ℚ) (s : Fin q) (u v : Fin A) :
    (inputProgram p).eval inputs (s,.inr (u,v)) = encodedRight p inputs s u v := by
  simp only [inputProgram, Family.eval_expressions, inputExpressions, LinearExpression.eval_linear, encodedRight]

/-- All m products are correct, using exactly q source matrix-program calls. -/
theorem batchProgram_correct {q A m B : ℕ} (p : MatrixTensorMaps q A m B)
    (alg : MatrixAlgorithm ℚ A A A) (halg : alg.Correct)
    (inputs : Fin m × MatrixInput B B B → ℚ) (g : Fin m) (i k : Fin B) :
    (batchProgram p alg).eval inputs (g,(i,k)) =
      ∑ j, inputs (g,.inl (i,j)) * inputs (g,.inr (j,k)) := by
  simp only [batchProgram, Family.eval_compose, outputProgram, Family.eval_expressions,
    outputExpressions, LinearExpression.eval_linear, id_eq, Family.eval_copies, Family.eval_ofMatrix alg halg]
  simp only [inputProgram_left, inputProgram_right]
  exact coefficient_batch_correct p inputs g i k

theorem inputProgram_cost {q A m B : ℕ} (p : MatrixTensorMaps q A m B) :
    (inputProgram p).cost = 4*q*m*A^2*B^2 := by
  simp only [inputProgram, Family.cost_expressions, Fintype.sum_prod_type, Fintype.sum_sum_type,
    inputExpressions, LinearExpression.cost_linear, Fintype.card_prod, Fintype.card_fin]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
  ring

theorem outputProgram_cost {q A m B : ℕ} (p : MatrixTensorMaps q A m B) :
    (outputProgram p).cost = 2*q*m*A^2*B^2 := by
  simp only [outputProgram, Family.cost_expressions, outputExpressions, LinearExpression.cost_linear,
    Fintype.card_prod, Fintype.card_fin]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
  ring

/-- The finite linear work is explicit; source matrix multiplication is charged q times. -/
theorem batchProgram_cost {q A m B : ℕ} (p : MatrixTensorMaps q A m B)
    (alg : MatrixAlgorithm ℚ A A A) :
    (batchProgram p alg).cost = q*alg.cost + 6*q*m*A^2*B^2 := by
  rw [batchProgram, Family.cost_compose, Family.cost_compose, Family.cost_copies,
    Family.cost_ofMatrix, inputProgram_cost, outputProgram_cost]
  ring


/-- A restriction factors through the original output-coordinate space. -/
theorem restrict_contract {X Y Z X' Y' Z' : Type}
    [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor ℚ X Y Z) (a : X' → X → ℚ) (b : Y' → Y → ℚ) (c : Z' → Z → ℚ)
    (x' : X') (y' : Y') (z' : Z') :
    Tensor.restrict a b c T x' y' z' =
      ∑ z, Tensor.contract T (a x') (b y') z * c z' z := by
  simp only [Tensor.restrict, Tensor.contract, Finset.sum_mul]
  calc
    _ = ∑ xy : X × Y, ∑ z, T xy.1 xy.2 z * a x' xy.1 * b y' xy.2 * c z' z := by
      simp only [Fintype.sum_prod_type]
      repeat' (apply Finset.sum_congr rfl; intro _ _)
      ring
    _ = ∑ z, ∑ xy : X × Y, T xy.1 xy.2 z * a x' xy.1 * b y' xy.2 * c z' z := Finset.sum_comm
    _ = _ := by simp only [Fintype.sum_prod_type]

/-- Actual restriction matrices cannot enlarge the full output flattening. -/
theorem maps_dimension_le {S T : FullTensor ℚ} [Fintype S.X] [Fintype S.Y]
    (p : Maps S T) : T.dimension ≤ S.dimension := by
  classical
  let L : Matrix T.Z S.Z ℚ := fun i w => Tensor.contract S.tensor (p.first (T.left i)) (p.second (T.right i)) w
  let R : Matrix S.Z T.Z ℚ := fun w j => p.third j w
  have hm : L * R = 1 := by
    funext i j
    change (∑ w, Tensor.contract S.tensor (p.first (T.left i)) (p.second (T.right i)) w * p.third j w) =
      if i=j then 1 else 0
    rw [← restrict_contract]
    exact (congrFun (congrFun (congrFun p.identity (T.left i)) (T.right i)) j).trans (T.identity i j)
  have h := (Matrix.rank_mul_le_left L R).trans (Matrix.rank_le_card_width L)
  rw [hm, Matrix.rank_one] at h
  exact h

/-- The source pays for every target matrix-entry direction, retaining m. -/
theorem relative_entry_floor {q A m B : ℕ} (p : MatrixTensorMaps q A m B) : m*B^2 ≤ q*A^2 := by
  have h := maps_dimension_le p
  change Fintype.card (Fin m × (Fin B × Fin B)) ≤ Fintype.card (Fin q × (Fin A × Fin A)) at h
  simpa only [Fintype.card_prod, Fintype.card_fin, pow_two] using h

/-- Tensor with the identity matrix block and retain all complete matrix coordinates. -/
def scaleMatrixMaps {q A m B : ℕ} (p : MatrixTensorMaps q A m B) (t : ℕ) :
    MatrixTensorMaps q (A*t) m (B*t) :=
  (Maps.ofIso (((Iso.refl _).product (LedgerRelationPackingBridge.matrixProductIso A t).symm).trans
    (Iso.assoc _ _ _).symm)).trans
      ((p.product (Maps.refl (matrixFull t))).trans
        (Maps.ofIso ((Iso.assoc _ _ _).trans
          ((Iso.refl _).product (LedgerRelationPackingBridge.matrixProductIso B t)))))


/-- The logarithmic resource ratio of an actual positive-gain relative restriction. -/
def pooledExponent (q A m B : ℕ) : ℝ :=
  (Real.log (q:ℝ) - Real.log (m:ℝ)) / (Real.log (B:ℝ) - Real.log (A:ℝ))

theorem pooledExponent_ge_two {q A m B : ℕ} (p : MatrixTensorMaps q A m B)
    (hA : 0 < A) (hB : 0 < B) (hq : 0 < q) (hm : 0 < m) (hAB : A < B) :
    2 ≤ pooledExponent q A m B := by
  have hAr : (0:ℝ) < A := by exact_mod_cast hA
  have hBr : (0:ℝ) < B := by exact_mod_cast hB
  have hqr : (0:ℝ) < q := by exact_mod_cast hq
  have hmr : (0:ℝ) < m := by exact_mod_cast hm
  have hABr : (A:ℝ) < B := by exact_mod_cast hAB
  have hd : 0 < Real.log (B:ℝ)-Real.log (A:ℝ) := sub_pos.mpr (Real.log_lt_log hAr hABr)
  have hf : (m:ℝ)*(B:ℝ)^2 ≤ (q:ℝ)*(A:ℝ)^2 := by exact_mod_cast relative_entry_floor p
  have hl := Real.log_le_log (mul_pos hmr (pow_pos hBr 2)) hf
  rw [Real.log_mul (ne_of_gt hmr) (ne_of_gt (pow_pos hBr 2)),
    Real.log_mul (ne_of_gt hqr) (ne_of_gt (pow_pos hAr 2)), Real.log_pow, Real.log_pow] at hl
  apply (le_div_iff₀ hd).mpr
  norm_num at hl
  linarith

theorem source_copies_gt_target {q A m B : ℕ} (p : MatrixTensorMaps q A m B)
    (hm : 0 < m) (hAB : A < B) : m < q := by
  have h := relative_entry_floor p
  have hs : A^2 < B^2 := by nlinarith
  have ht := Nat.mul_lt_mul_of_pos_left hs hm
  by_contra hn
  have hq : q ≤ m := by omega
  have hc := Nat.mul_le_mul_right (A^2) hq
  omega

/-- The frozen global relative restriction directly supplies a finite batch program. -/
def familyBatchProgram (family : AllRowProfile.Family n K) (k j R : ℕ)
    (hs : Tensor.RankAtMost (jointSource ℚ family k j).tensor R)
    (alg : MatrixAlgorithm ℚ (family.dimension^(k*j)) (family.dimension^(k*j)) (family.dimension^(k*j))) :=
  batchProgram (GlobalExactRestrictionBridge.familyRelative family k j R hs) alg

/-- Concrete family output programs compute every named independent target product. -/
theorem familyBatchProgram_correct (family : AllRowProfile.Family n K) (k j R : ℕ)
    (hs : Tensor.RankAtMost (jointSource ℚ family k j).tensor R)
    (alg : MatrixAlgorithm ℚ (family.dimension^(k*j)) (family.dimension^(k*j)) (family.dimension^(k*j)))
    (halg : alg.Correct)
    (inputs : Fin (family.count^(3*k*j)) × MatrixInput
      ((2^K*family.count)^(k*j)) ((2^K*family.count)^(k*j)) ((2^K*family.count)^(k*j)) → ℚ)
    (g : Fin (family.count^(3*k*j))) (i t : Fin ((2^K*family.count)^(k*j))) :
    (familyBatchProgram family k j R hs alg).eval inputs (g,(i,t)) =
      ∑ s, inputs (g,.inl (i,s)) * inputs (g,.inr (s,t)) :=
  batchProgram_correct _ alg halg inputs g i t


/-- The fully supplied global restriction gives a program without a rank premise. -/
def suppliedBatchProgram (family : AllRowProfile.Family n K) (k j : ℕ)
    (alg : MatrixAlgorithm ℚ (SuppliedGlobalRestrictionBridge.inputWidth family k j)
      (SuppliedGlobalRestrictionBridge.inputWidth family k j) (SuppliedGlobalRestrictionBridge.inputWidth family k j)) :=
  batchProgram (SuppliedGlobalRestrictionBridge.suppliedMaps family k j) alg

/-- Every output of the closed supplied-family batch program is correct. -/
theorem suppliedBatchProgram_correct (family : AllRowProfile.Family n K) (k j : ℕ)
    (alg : MatrixAlgorithm ℚ (SuppliedGlobalRestrictionBridge.inputWidth family k j)
      (SuppliedGlobalRestrictionBridge.inputWidth family k j) (SuppliedGlobalRestrictionBridge.inputWidth family k j))
    (halg : alg.Correct)
    (inputs : Fin (SuppliedGlobalRestrictionBridge.outputCopies family k j) × MatrixInput
      (SuppliedGlobalRestrictionBridge.outputWidth family k j) (SuppliedGlobalRestrictionBridge.outputWidth family k j)
      (SuppliedGlobalRestrictionBridge.outputWidth family k j) → ℚ)
    (g : Fin (SuppliedGlobalRestrictionBridge.outputCopies family k j))
    (i t : Fin (SuppliedGlobalRestrictionBridge.outputWidth family k j)) :
    (suppliedBatchProgram family k j alg).eval inputs (g,(i,t)) =
      ∑ s, inputs (g,.inl (i,s)) * inputs (g,.inr (s,t)) :=
  batchProgram_correct _ alg halg inputs g i t

/-- The concrete family's finite arithmetic cost uses all q source calls and all m outputs. -/
theorem suppliedBatchProgram_cost (family : AllRowProfile.Family n K) (k j : ℕ)
    (alg : MatrixAlgorithm ℚ (SuppliedGlobalRestrictionBridge.inputWidth family k j)
      (SuppliedGlobalRestrictionBridge.inputWidth family k j) (SuppliedGlobalRestrictionBridge.inputWidth family k j)) :
    (suppliedBatchProgram family k j alg).cost =
      SuppliedGlobalRestrictionBridge.inputCopies family k j * alg.cost +
      6 * SuppliedGlobalRestrictionBridge.inputCopies family k j * SuppliedGlobalRestrictionBridge.outputCopies family k j *
        (SuppliedGlobalRestrictionBridge.inputWidth family k j)^2 * (SuppliedGlobalRestrictionBridge.outputWidth family k j)^2 :=
  batchProgram_cost _ alg

end
end MatrixDimensionAudit.RelativeAlgorithmBridge
