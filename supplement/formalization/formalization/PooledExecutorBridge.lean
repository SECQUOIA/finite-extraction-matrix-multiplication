import formalization.BlockRelativeAlgorithmBridge
import formalization.PooledBatchRecurrence
import OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.Padding
import OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.NaiveAlgorithm

/-! A pooled arithmetic executor, retaining sharing across all current batches. -/
namespace MatrixDimensionAudit.PooledExecutorBridge
open OAI.MatrixMultiplication.Arithmetic
open OAI.MatrixMultiplication.Arithmetic.RecursiveBlock
open RelativeAlgorithmBridge
open scoped BigOperators
noncomputable section

/-- A finite arithmetic program computing all T independent n-square products. -/
structure MultiMatrixAlgorithm (T n : ℕ) where
  family : Family ℚ (Fin T × MatrixInput n n n) (Fin T × (Fin n × Fin n))
  correct : ∀ inputs g i k, family.eval inputs (g,(i,k)) =
    ∑ j, inputs (g,.inl (i,j)) * inputs (g,.inr (j,k))

def MultiMatrixAlgorithm.cost {T n : ℕ} (P : MultiMatrixAlgorithm T n) : ℕ := P.family.cost

/-- The classical leaf computes all tasks in parallel, including empty tasks/sides. -/
def classicalMulti (T n : ℕ) : MultiMatrixAlgorithm T n where
  family := Family.copies T (Family.ofMatrix (naiveAlgorithm n n n))
  correct := by
    intro inputs g i k
    rw [Family.eval_copies, Family.eval_ofMatrix _ (naiveAlgorithm_correct n n n)]

theorem classical_cost (T n : ℕ) : (classicalMulti T n).cost = 2*T*n^3 := by
  simp only [MultiMatrixAlgorithm.cost, classicalMulti, Family.cost_copies, Family.cost_ofMatrix, naiveAlgorithm_cost]
  ring

/-- Enumerate every next-level task across all parent batches in one common pool. -/
def poolIndex (q c : ℕ) : Fin c × Fin q ≃ Fin (q*c) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm c q))

/-- This is one recursive multi-product program, with input/output labels regrouped. -/
def pooledMiddle (c q n : ℕ) (P : MultiMatrixAlgorithm (q*c) n) :
    Family ℚ (Fin c × (Fin q × MatrixInput n n n)) (Fin c × (Fin q × (Fin n × Fin n))) where
  registers := P.family.registers
  program := P.family.program.mapInput (fun x =>
    (((poolIndex q c).symm x.1).1, (((poolIndex q c).symm x.1).2, x.2)))
  output := fun o => P.family.output (poolIndex q c (o.1,o.2.1), o.2.2)

theorem pooledMiddle_correct (c q n : ℕ) (P : MultiMatrixAlgorithm (q*c) n)
    (inputs : Fin c × (Fin q × MatrixInput n n n) → ℚ)
    (h : Fin c) (s : Fin q) (i k : Fin n) :
    (pooledMiddle c q n P).eval inputs (h,(s,(i,k))) =
      ∑ j, inputs (h,(s,.inl (i,j))) * inputs (h,(s,.inr (j,k))) := by
  change (P.family.program.mapInput _).eval inputs
    (P.family.output (poolIndex q c (h,s),(i,k))) = _
  rw [Program.eval_mapInput]
  change P.family.eval _ (poolIndex q c (h,s),(i,k)) = _
  rw [P.correct]
  simp only [Function.comp_apply, Equiv.symm_apply_apply]

theorem pooledMiddle_cost (c q n : ℕ) (P : MultiMatrixAlgorithm (q*c) n) :
    (pooledMiddle c q n P).cost = P.cost :=
  Program.cost_mapInput _ _

/-- Sparse pre/post stages surround one pooled recursive program. -/
def pooledBody {q A m B : ℕ} (p : MatrixTensorMaps q A m B) (c t : ℕ)
    (P : MultiMatrixAlgorithm (q*c) (A*t)) :
    Family ℚ (Fin c × (Fin m × MatrixInput (B*t) (B*t) (B*t)))
      (Fin c × (Fin m × (Fin (B*t) × Fin (B*t)))) :=
  (Family.copies c (BlockRelativeAlgorithmBridge.inputProgram p t)).compose
    ((pooledMiddle c q (A*t) P).compose
      (Family.copies c (BlockRelativeAlgorithmBridge.outputProgram p t)))

theorem pooledBody_correct {q A m B : ℕ} (p : MatrixTensorMaps q A m B) (c t : ℕ)
    (P : MultiMatrixAlgorithm (q*c) (A*t))
    (inputs : Fin c × (Fin m × MatrixInput (B*t) (B*t) (B*t)) → ℚ)
    (h : Fin c) (g : Fin m) (u v : Fin (B*t)) :
    (pooledBody p c t P).eval inputs (h,(g,(u,v))) =
      ∑ j, inputs (h,(g,.inl (u,j))) * inputs (h,(g,.inr (j,v))) := by
  have hu := (BlockRelativeAlgorithmBridge.split B t).symm_apply_apply u
  have hv := (BlockRelativeAlgorithmBridge.split B t).symm_apply_apply v
  change RecursiveBlock.join (BlockRelativeAlgorithmBridge.split B t u).1
    (BlockRelativeAlgorithmBridge.split B t u).2 = u at hu
  change RecursiveBlock.join (BlockRelativeAlgorithmBridge.split B t v).1
    (BlockRelativeAlgorithmBridge.split B t v).2 = v at hv
  simp only [pooledBody, Family.eval_compose, Family.eval_copies,
    BlockRelativeAlgorithmBridge.outputProgram, Family.eval_expressions,
    BlockRelativeAlgorithmBridge.outputExpressions, LinearExpression.eval_linear, pooledMiddle_correct]
  simp only [BlockRelativeAlgorithmBridge.inputProgram_left,
    BlockRelativeAlgorithmBridge.inputProgram_right]
  have hh := BlockRelativeAlgorithmBridge.block_coefficient_correct p (fun x => inputs (h,x)) g
    (BlockRelativeAlgorithmBridge.split B t u).1 (BlockRelativeAlgorithmBridge.split B t v).1
    (BlockRelativeAlgorithmBridge.split B t u).2 (BlockRelativeAlgorithmBridge.split B t v).2
  rw [hu,hv] at hh
  exact hh

theorem pooledBody_cost {q A m B : ℕ} (p : MatrixTensorMaps q A m B) (c t : ℕ)
    (P : MultiMatrixAlgorithm (q*c) (A*t)) :
    (pooledBody p c t P).cost = P.cost + c*(6*q*m*A^2*B^2*t^2) := by
  rw [pooledBody, Family.cost_compose, Family.cost_compose, Family.cost_copies,
    Family.cost_copies, pooledMiddle_cost, BlockRelativeAlgorithmBridge.inputProgram_cost,
    BlockRelativeAlgorithmBridge.outputProgram_cost]
  ring


/-- Padding is input/constant rewiring, so it introduces no arithmetic gates. -/
def paddingSource (T n c m N : ℕ) :
    (Fin c × (Fin m × MatrixInput N N N)) → (Fin T × MatrixInput n n n) ⊕ ℚ :=
  fun o => if h : (finProdFinEquiv (o.1,o.2.1)).val < T then
    Sum.map (fun e => (⟨(finProdFinEquiv (o.1,o.2.1)).val,h⟩,e)) id
      (padSource (F := ℚ) (a := n) (b := n) (c := n) o.2.2)
    else .inr 0

def selectedCopy {T c m : ℕ} (hc : T ≤ c*m) (g : Fin T) : Fin c × Fin m :=
  finProdFinEquiv.symm (Fin.castLE hc g)

theorem paddingSource_selected {T n c m N : ℕ} (hc : T ≤ c*m)
    (inputs : Fin T × MatrixInput n n n → ℚ) (g : Fin T) (e : MatrixInput N N N) :
    Sum.elim inputs id (paddingSource T n c m N
      ((selectedCopy hc g).1,((selectedCopy hc g).2,e))) =
      matrixInputs
        (zeroPadMatrix N N (fun i j => inputs (g,.inl (i,j))))
        (zeroPadMatrix N N (fun j k => inputs (g,.inr (j,k)))) e := by
  simp only [paddingSource, selectedCopy, Prod.mk.eta, Equiv.apply_symm_apply, Fin.val_castLE, g.isLt, dite_true]
  have he := congrFun (padSource_eval (A := N) (B := N) (C := N)
    (fun i j : Fin n => inputs (g,.inl (i,j))) (fun j k : Fin n => inputs (g,.inr (j,k)))) e
  rw [← he]
  cases padSource (F := ℚ) (a := n) (b := n) (c := n) e with
  | inl e => cases e <;> rfl
  | inr z => rfl

/-- Select precisely the original copies and matrix coordinates after decoding. -/
def outputSelection {T n c m N : ℕ} (hc : T ≤ c*m) (hn : n ≤ N)
    (o : Fin T × (Fin n × Fin n)) : Fin c × (Fin m × (Fin N × Fin N)) :=
  ((selectedCopy hc o.1).1,((selectedCopy hc o.1).2,(Fin.castLE hn o.2.1,Fin.castLE hn o.2.2)))

/-- Zero-copy padding, zero-entry padding, and output truncation of an actual program. -/
def padProgram {T n c m N : ℕ} (hc : T ≤ c*m) (hn : n ≤ N)
    (P : Family ℚ (Fin c × (Fin m × MatrixInput N N N)) (Fin c × (Fin m × (Fin N × Fin N)))) :
    Family ℚ (Fin T × MatrixInput n n n) (Fin T × (Fin n × Fin n)) where
  registers := P.registers
  program := P.program.mapSource (paddingSource T n c m N)
  output := fun o => P.output (outputSelection hc hn o)

theorem padProgram_eval {T n c m N : ℕ} (hc : T ≤ c*m) (hn : n ≤ N)
    (P : Family ℚ (Fin c × (Fin m × MatrixInput N N N)) (Fin c × (Fin m × (Fin N × Fin N))))
    (inputs : Fin T × MatrixInput n n n → ℚ) (o : Fin T × (Fin n × Fin n)) :
    (padProgram hc hn P).eval inputs o =
      P.eval (fun x => Sum.elim inputs id (paddingSource T n c m N x)) (outputSelection hc hn o) :=
  Program.eval_mapSource _ _ _ _

theorem padProgram_cost {T n c m N : ℕ} (hc : T ≤ c*m) (hn : n ≤ N)
    (P : Family ℚ (Fin c × (Fin m × MatrixInput N N N)) (Fin c × (Fin m × (Fin N × Fin N)))) :
    (padProgram hc hn P).cost = P.cost := Program.cost_mapSource _ _

/-- One actual pooled level consumes one program for all q*c next-level tasks. -/
def oneLevel {q A m B T n : ℕ} (p : MatrixTensorMaps q A m B) (c t : ℕ)
    (hc : T ≤ c*m) (hn : n ≤ B*t) (P : MultiMatrixAlgorithm (q*c) (A*t)) : MultiMatrixAlgorithm T n where
  family := padProgram hc hn (pooledBody p c t P)
  correct := by
    intro inputs g i k
    rw [padProgram_eval]
    change (pooledBody p c t P).eval _
      ((selectedCopy hc g).1,((selectedCopy hc g).2,(Fin.castLE hn i,Fin.castLE hn k))) = _
    rw [pooledBody_correct]
    simp_rw [paddingSource_selected]
    change (zeroPadMatrix (B*t) (B*t) (fun i j => inputs (g,.inl (i,j))) *
      zeroPadMatrix (B*t) (B*t) (fun j k => inputs (g,.inr (j,k))))
        (Fin.castLE hn i) (Fin.castLE hn k) = _
    exact zeroPadMatrix_mul hn hn hn _ _ i k

theorem oneLevel_cost {q A m B T n : ℕ} (p : MatrixTensorMaps q A m B) (c t : ℕ)
    (hc : T ≤ c*m) (hn : n ≤ B*t) (P : MultiMatrixAlgorithm (q*c) (A*t)) :
    (oneLevel p c t hc hn P).cost = P.cost + c*(6*q*m*A^2*B^2*t^2) := by
  exact (padProgram_cost hc hn _).trans (pooledBody_cost p c t P)


/-- The precise rounded population and side required by one pooled recursion level. -/
def ceilLevel {q A m B : ℕ} (p : MatrixTensorMaps q A m B) (hm : 0 < m) (hB : 0 < B)
    (T n : ℕ) (P : MultiMatrixAlgorithm (q*(T ⌈/⌉ m)) (A*(n ⌈/⌉ B))) : MultiMatrixAlgorithm T n :=
  oneLevel p (T ⌈/⌉ m) (n ⌈/⌉ B)
    (by simpa only [Nat.mul_comm] using PooledBatchRecurrence.ceil_lower T m hm)
    (PooledBatchRecurrence.ceil_lower n B hB) P

theorem ceilLevel_cost {q A m B : ℕ} (p : MatrixTensorMaps q A m B) (hm : 0 < m) (hB : 0 < B)
    (T n : ℕ) (P : MultiMatrixAlgorithm (q*(T ⌈/⌉ m)) (A*(n ⌈/⌉ B))) :
    (ceilLevel p hm hB T n P).cost = P.cost + (T ⌈/⌉ m)*(6*q*m*A^2*B^2*(n ⌈/⌉ B)^2) :=
  oneLevel_cost p _ _ _ _ P

/-- A bounded downward/upward executor, ending with classical products at its leaves. -/
def bounded {q A m B : ℕ} (p : MatrixTensorMaps q A m B) (hm : 0 < m) (hB : 0 < B) :
    (depth T n : ℕ) → MultiMatrixAlgorithm T n
  | 0,T,n => classicalMulti T n
  | depth+1,T,n => ceilLevel p hm hB T n
      (bounded p hm hB depth (q*(T ⌈/⌉ m)) (A*(n ⌈/⌉ B)))

/-- Exact arithmetic work recurrence of the bounded pooled executor. -/
def work (q A m B : ℕ) : (depth T n : ℕ) → ℕ
  | 0,T,n => 2*T*n^3
  | depth+1,T,n => work q A m B depth (q*(T ⌈/⌉ m)) (A*(n ⌈/⌉ B)) +
      (T ⌈/⌉ m)*(6*q*m*A^2*B^2*(n ⌈/⌉ B)^2)

theorem bounded_cost {q A m B : ℕ} (p : MatrixTensorMaps q A m B) (hm : 0 < m) (hB : 0 < B)
    (depth T n : ℕ) : (bounded p hm hB depth T n).cost = work q A m B depth T n := by
  induction depth generalizing T n with
  | zero => exact classical_cost T n
  | succ depth ih =>
      rw [bounded, ceilLevel_cost, ih]
      rfl

theorem bounded_correct {q A m B : ℕ} (p : MatrixTensorMaps q A m B) (hm : 0 < m) (hB : 0 < B)
    (depth T n : ℕ) (inputs : Fin T × MatrixInput n n n → ℚ) (g : Fin T) (i k : Fin n) :
    (bounded p hm hB depth T n).family.eval inputs (g,(i,k)) =
      ∑ j, inputs (g,.inl (i,j)) * inputs (g,.inr (j,k)) :=
  (bounded p hm hB depth T n).correct inputs g i k

/-- One output task is an ordinary exact matrix algorithm, with no extra operations. -/
def squareAlgorithm {n : ℕ} (P : MultiMatrixAlgorithm 1 n) : MatrixAlgorithm ℚ n n n where
  registers := P.family.registers
  program := P.family.program.mapInput Prod.snd
  output := fun i k => P.family.output (0,(i,k))

theorem squareAlgorithm_correct {n : ℕ} (P : MultiMatrixAlgorithm 1 n) : (squareAlgorithm P).Correct := by
  apply (MatrixAlgorithm.correct_iff_entries _).mpr
  intro L R i k
  change (P.family.program.mapInput Prod.snd).eval (matrixInputs L R) (P.family.output (0,(i,k))) = _
  rw [Program.eval_mapInput]
  exact P.correct (fun x => matrixInputs L R x.2) 0 i k

theorem squareAlgorithm_cost {n : ℕ} (P : MultiMatrixAlgorithm 1 n) :
    (squareAlgorithm P).cost = P.cost := Program.cost_mapInput _ _


/-- The actual population/side state advanced by the executor at one level. -/
def nextState (q A m B : ℕ) (v : ℕ × ℕ) : ℕ × ℕ :=
  (q*(v.1 ⌈/⌉ m), A*(v.2 ⌈/⌉ B))

def stateAfter (q A m B depth T n : ℕ) : ℕ × ℕ := (nextState q A m B)^[depth] (T,n)

theorem stateAfter_zero (q A m B T n : ℕ) : stateAfter q A m B 0 T n = (T,n) := rfl

theorem stateAfter_shift (q A m B depth T n : ℕ) :
    stateAfter q A m B (depth+1) T n =
      stateAfter q A m B depth (q*(T ⌈/⌉ m)) (A*(n ⌈/⌉ B)) :=
  Function.iterate_succ_apply _ _ _

theorem stateAfter_succ (q A m B depth T n : ℕ) :
    stateAfter q A m B (depth+1) T n = nextState q A m B (stateAfter q A m B depth T n) :=
  Function.iterate_succ_apply' _ _ _

/-- Starting from one product, the executor follows exactly the frozen numerical recurrences. -/
theorem stateAfter_initial (q A m B depth n : ℕ) :
    stateAfter q A m B depth 1 n =
      (PooledBatchRecurrence.tasks q m depth, PooledBatchRecurrence.side A B n depth) := by
  induction depth with
  | zero => rfl
  | succ depth ih => rw [stateAfter_succ, ih]; rfl

/-- Sum of the actual work at every level, with classical leaf work shown explicitly. -/
theorem work_profile (q A m B depth T n : ℕ) :
    work q A m B depth T n =
      2*(stateAfter q A m B depth T n).1*(stateAfter q A m B depth T n).2^3 +
      (6*q*m*A^2*B^2) * ∑ l ∈ Finset.range depth,
        ((stateAfter q A m B l T n).1 ⌈/⌉ m)*((stateAfter q A m B l T n).2 ⌈/⌉ B)^2 := by
  induction depth generalizing T n with
  | zero => simp [work, stateAfter]
  | succ depth ih =>
      rw [work, ih, Finset.sum_range_succ']
      simp only [stateAfter_shift, stateAfter_zero]
      ring

/-- The real program's cost is tied to the task/side recurrences at every depth. -/
theorem bounded_cost_profile {q A m B : ℕ} (p : MatrixTensorMaps q A m B)
    (hm : 0 < m) (hB : 0 < B) (depth n : ℕ) :
    (bounded p hm hB depth 1 n).cost =
      2*PooledBatchRecurrence.tasks q m depth*PooledBatchRecurrence.side A B n depth^3 +
      (6*q*m*A^2*B^2) * ∑ l ∈ Finset.range depth,
        (PooledBatchRecurrence.tasks q m l ⌈/⌉ m)*(PooledBatchRecurrence.side A B n l ⌈/⌉ B)^2 := by
  rw [bounded_cost, work_profile]
  simp only [stateAfter_initial]

/-- The numerical stopping proof now selects an actual correct arithmetic algorithm. -/
theorem exists_stopped_algorithm {q A m B : ℕ} (p : MatrixTensorMaps q A m B)
    (hm : 0 < m) (hA : 0 < A) (hAB : A < B) (n : ℕ) :
    ∃ depth : ℕ, PooledBatchRecurrence.side A B n depth ≤ PooledBatchRecurrence.sideConstant A B ∧
      ∃ alg : MatrixAlgorithm ℚ n n n, alg.Correct ∧ alg.cost = work q A m B depth 1 n := by
  have hB : 0 < B := hA.trans hAB
  obtain ⟨depth,hcover⟩ := PooledBatchRecurrence.exists_cover A B n hA hAB
  refine ⟨depth,PooledBatchRecurrence.side_bounded_at_cover A B n depth hA hAB hcover,
    squareAlgorithm (bounded p hm hB depth 1 n),squareAlgorithm_correct _,?_⟩
  exact (squareAlgorithm_cost _).trans (bounded_cost p hm hB depth 1 n)


/-- The first ideal cover selects a finite leaf depth without an execution schedule premise. -/
def coverDepth (A B n : ℕ) (hA : 0 < A) (hAB : A < B) : ℕ :=
  Nat.find (PooledBatchRecurrence.exists_cover A B n hA hAB)

theorem coverDepth_cover (A B n : ℕ) (hA : 0 < A) (hAB : A < B) :
    A^(coverDepth A B n hA hAB)*n ≤ B^(coverDepth A B n hA hAB) :=
  Nat.find_spec (PooledBatchRecurrence.exists_cover A B n hA hAB)

theorem coverDepth_previous (A B n : ℕ) (hA : 0 < A) (hAB : A < B)
    (i : ℕ) (hi : i < coverDepth A B n hA hAB) : B^i < A^i*n :=
  Nat.lt_of_not_ge (Nat.find_min (PooledBatchRecurrence.exists_cover A B n hA hAB) hi)

/-- A named finite matrix algorithm at every side, using pooled recursion to the fixed leaf range. -/
def stoppedAlgorithm {q A m B : ℕ} (p : MatrixTensorMaps q A m B)
    (hm : 0 < m) (hA : 0 < A) (hAB : A < B) (n : ℕ) : MatrixAlgorithm ℚ n n n :=
  squareAlgorithm (bounded p hm (hA.trans hAB) (coverDepth A B n hA hAB) 1 n)

theorem stoppedAlgorithm_correct {q A m B : ℕ} (p : MatrixTensorMaps q A m B)
    (hm : 0 < m) (hA : 0 < A) (hAB : A < B) (n : ℕ) :
    (stoppedAlgorithm p hm hA hAB n).Correct := squareAlgorithm_correct _

theorem stoppedAlgorithm_leaf_side {q A m B : ℕ} (_p : MatrixTensorMaps q A m B)
    (hA : 0 < A) (hAB : A < B) (n : ℕ) :
    PooledBatchRecurrence.side A B n (coverDepth A B n hA hAB) ≤ PooledBatchRecurrence.sideConstant A B :=
  PooledBatchRecurrence.side_bounded_at_cover A B n _ hA hAB (coverDepth_cover A B n hA hAB)

theorem stoppedAlgorithm_cost {q A m B : ℕ} (p : MatrixTensorMaps q A m B)
    (hm : 0 < m) (hA : 0 < A) (hAB : A < B) (n : ℕ) :
    (stoppedAlgorithm p hm hA hAB n).cost = work q A m B (coverDepth A B n hA hAB) 1 n :=
  (squareAlgorithm_cost _).trans (bounded_cost p hm (hA.trans hAB) _ 1 n)

/-- The numerical power envelope applies at this actual executor's chosen leaf depth. -/
theorem stoppedAlgorithm_leaf_population {q A m B : ℕ} (p : MatrixTensorMaps q A m B)
    (hm : 0 < m) (hA : 0 < A) (hAB : A < B) (n r s : ℕ) (hn : 0 < n)
    (hrate : q^s*A^r ≤ m^s*B^r) :
    A^r*PooledBatchRecurrence.tasks q m (coverDepth A B n hA hAB)^s ≤
      PooledBatchRecurrence.taskConstant q m^s*B^r*n^r :=
  PooledBatchRecurrence.tasks_at_minimal_cover q m A B n r s _ hm
    (source_copies_gt_target p hm hAB) hA hAB hn hrate (coverDepth_previous A B n hA hAB)

/-- A closed concrete flow family now supplies a finite ordinary matrix algorithm. -/
def suppliedAlgorithm (family : AllRowProfile.Family n K) (k j : ℕ)
    (hgain : SuppliedGlobalRestrictionBridge.inputWidth family k j <
      SuppliedGlobalRestrictionBridge.outputWidth family k j) (t : ℕ) : MatrixAlgorithm ℚ t t t :=
  stoppedAlgorithm (SuppliedGlobalRestrictionBridge.suppliedMaps family k j)
    (SuppliedGlobalRestrictionBridge.output_copies_pos family k j)
    (SuppliedGlobalRestrictionBridge.input_width_pos family k j) hgain t

theorem suppliedAlgorithm_correct (family : AllRowProfile.Family n K) (k j : ℕ)
    (hgain : SuppliedGlobalRestrictionBridge.inputWidth family k j <
      SuppliedGlobalRestrictionBridge.outputWidth family k j) (t : ℕ) :
    (suppliedAlgorithm family k j hgain t).Correct := stoppedAlgorithm_correct _ _ _ _ _

end
end MatrixDimensionAudit.PooledExecutorBridge
