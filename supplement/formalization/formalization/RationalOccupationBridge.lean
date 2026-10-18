import formalization.GeneralRowSector
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.BigOperators.Field
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Lean.Elab.Tactic.Omega

/-! Finite rational absorbing walks with a positive descending escape edge. -/
namespace MatrixDimensionAudit.RationalOccupationBridge
open scoped BigOperators
noncomputable section

/-- State zero is the absorbing boundary; every transient row has a positive
transition to a smaller state. No occupation vector is part of this data. -/
structure Walk (n : Nat) where
  probability : Fin n → Fin (n+1) → ℚ
  nonnegative : ∀ i j, 0 ≤ probability i j
  row_sum : ∀ i, ∑ j, probability i j = 1
  escape : ∀ i, ∃ j, j.val < i.val+1 ∧ 0 < probability i j

/-- A rational superharmonic function with zero boundary is nonnegative. -/
theorem maximum_principle (P : Walk n) (f : Fin (n+1) → ℚ) (hzero : f 0 = 0)
    (hsuper : ∀ i, (∑ j, P.probability i j * f j) ≤ f i.succ) :
    ∀ j, 0 ≤ f j := by
  classical
  let values := Finset.univ.image f
  have hv : values.Nonempty := ⟨f 0, Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩⟩
  let m := values.min' hv
  have hmin : ∀ j, m ≤ f j := fun j => Finset.min'_le values (f j)
    (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
  obtain ⟨jmin, _, hjmin⟩ := Finset.mem_image.mp (Finset.min'_mem values hv)
  by_contra hn
  push Not at hn
  obtain ⟨bad,hbad⟩ := hn
  have hm : m < 0 := lt_of_le_of_lt (hmin bad) hbad
  have strict : ∀ a, ∀ j : Fin (n+1), j.val=a → m < f j := by
    intro a
    induction a using Nat.strong_induction_on with
    | h a ih =>
      intro j hj
      cases j using Fin.cases with
      | zero => simpa only [hzero] using hm
      | succ i =>
        obtain ⟨child, hchild, hpositive⟩ := P.escape i
        have hvalue := ih child.val (by simpa only [← hj, Fin.val_succ] using hchild) child rfl
        have hsum : m < ∑ k, P.probability i k * f k := by
          calc
            m = (∑ k, P.probability i k) * m := by rw [P.row_sum, one_mul]
            _ = ∑ k, P.probability i k * m := Finset.sum_mul ..
            _ < ∑ k, P.probability i k * f k := by
              apply Finset.sum_lt_sum
              · intro k _
                exact mul_le_mul_of_nonneg_left (hmin k) (P.nonnegative i k)
              · exact ⟨child, Finset.mem_univ _, mul_lt_mul_of_pos_left hvalue hpositive⟩
        exact lt_of_lt_of_le hsum (hsuper i)
  have hc := strict jmin.val jmin rfl
  rw [hjmin] at hc
  exact (lt_irrefl m) hc

/-- Extend a transient vector by its exact zero boundary coordinate. -/
def extend (f : Fin n → ℚ) : Fin (n+1) → ℚ := Fin.cases 0 f

/-- The rational forward operator I-P on transient coordinates. -/
def operator (P : Walk n) : (Fin n → ℚ) →ₗ[ℚ] (Fin n → ℚ) where
  toFun := fun f i => f i - ∑ j, P.probability i j * extend f j
  map_add' := by
    intro f g
    funext i
    have he : extend (f+g) = extend f + extend g := by
      funext j; cases j using Fin.cases <;> simp [extend]
    simp only [he, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    ring
  map_smul' := by
    intro c f
    funext i
    have he : extend (c • f) = c • extend f := by
      funext j; cases j using Fin.cases <;> simp [extend]
    simp only [he, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    simp_rw [← mul_assoc, mul_comm (P.probability i _ ) c, mul_assoc, ← Finset.mul_sum]
    ring

theorem operator_solution_nonnegative (P : Walk n) (f b : Fin n → ℚ)
    (hb : ∀ i, 0 ≤ b i) (he : operator P f = b) : ∀ i, 0 ≤ f i := by
  have h := maximum_principle P (extend f) rfl (by
    intro i
    have hi := congrFun he i
    change f i - ∑ j, P.probability i j * extend f j = b i at hi
    change (∑ j, P.probability i j * extend f j) ≤ f i
    linarith [hb i])
  exact fun i => h i.succ

theorem operator_injective (P : Walk n) : Function.Injective (operator P) := by
  intro f g he
  have hd : operator P (f-g) = 0 := by rw [map_sub, he, sub_self]
  have hp := operator_solution_nonnegative P (f-g) 0 (by simp) hd
  have hn := operator_solution_nonnegative P (-(f-g)) 0 (by simp) (by rw [map_neg, hd, neg_zero])
  funext i
  have hpi := hp i
  have hni := hn i
  simp only [Pi.sub_apply, Pi.neg_apply] at hpi hni
  linarith

/-- Nonsingularity is derived from the escape condition, not supplied as a premise. -/
def forwardEquiv (P : Walk n) : (Fin n → ℚ) ≃ₗ[ℚ] (Fin n → ℚ) :=
  LinearEquiv.ofInjectiveEndo (operator P) (operator_injective P)

def fundamental (P : Walk n) : Matrix (Fin n) (Fin n) ℚ :=
  LinearMap.toMatrix' (forwardEquiv P).symm.toLinearMap

theorem fundamental_nonnegative (P : Walk n) (i j : Fin n) : 0 ≤ fundamental P i j := by
  change 0 ≤ (forwardEquiv P).symm (Pi.single j 1) i
  apply operator_solution_nonnegative P _ (Pi.single j 1) (by intro k; simp only [Pi.single_apply]; split_ifs <;> norm_num)
  exact (forwardEquiv P).apply_symm_apply _

theorem fundamental_forward (P : Walk n) :
    fundamental P * LinearMap.toMatrix' (operator P) = 1 := by
  rw [fundamental, ← LinearMap.toMatrix'_comp]
  have h : (forwardEquiv P).symm.toLinearMap.comp (operator P) = LinearMap.id := by
    apply LinearMap.ext
    intro f
    funext i
    exact congrFun ((forwardEquiv P).symm_apply_apply f) i
  rw [h, LinearMap.toMatrix'_id]

theorem operator_matrix_entry (P : Walk n) (i j : Fin n) :
    LinearMap.toMatrix' (operator P) i j = (if i=j then 1 else 0) - P.probability i j.succ := by
  simp [LinearMap.toMatrix'_apply, operator, extend, Fin.sum_univ_succ, Pi.single_apply]

/-- The expected-visit coefficients are explicitly rational matrix entries. -/
def occupation (P : Walk n) (start : Fin n) : Fin n → ℚ := fundamental P start

def divergence (P : Walk n) (f : Fin n → ℚ) (y : Fin (n+1)) : ℚ :=
  ∑ i, f i * ((if i.succ=y then 1 else 0) - P.probability i y)

theorem occupation_transient_balance (P : Walk n) (start k : Fin n) :
    divergence P (occupation P start) k.succ = if start=k then 1 else 0 := by
  have h := congrFun (congrFun (fundamental_forward P) start) k
  change (∑ i, fundamental P start i * LinearMap.toMatrix' (operator P) i k) =
    if start=k then 1 else 0 at h
  simpa only [divergence, occupation, operator_matrix_entry, Fin.succ_inj] using h

theorem divergence_sum (P : Walk n) (f : Fin n → ℚ) :
    ∑ y, divergence P f y = 0 := by
  unfold divergence
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, Finset.sum_sub_distrib]
  simp [P.row_sum]

/-- Full supported unit flow, including the absorbing boundary coordinate. -/
theorem occupation_balance (P : Walk n) (start : Fin n) (y : Fin (n+1)) :
    divergence P (occupation P start) y =
      (if start.succ=y then 1 else 0) - (if (0 : Fin (n+1))=y then 1 else 0) := by
  cases y using Fin.cases with
  | zero =>
    have h := divergence_sum P (occupation P start)
    rw [Fin.sum_univ_succ] at h
    simp_rw [occupation_transient_balance] at h
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true] at h
    simp only [Fin.succ_ne_zero, ite_false, ite_true, zero_sub]
    linarith
  | succ k =>
    have hzero : (0 : Fin (n+1)) ≠ k.succ := (Fin.succ_ne_zero k).symm
    simpa only [Fin.succ_inj, hzero, ite_false, sub_zero] using occupation_transient_balance P start k

theorem occupation_nonnegative (P : Walk n) (start i : Fin n) :
    0 ≤ occupation P start i := fundamental_nonnegative P start i

/-- A nonnegative rational unit occupation flow is constructed for every start.
No real occupation vector or target row-balance equality is assumed. -/
theorem exists_occupation (P : Walk n) (start : Fin n) :
    ∃ f : Fin n → ℚ, (∀ i, 0 ≤ f i) ∧ ∀ y,
      divergence P f y = (if start.succ=y then 1 else 0) - (if (0 : Fin (n+1))=y then 1 else 0) :=
  ⟨occupation P start, occupation_nonnegative P start, occupation_balance P start⟩

theorem occupation_unique (P : Walk n) (start : Fin n) (f : Fin n → ℚ)
    (hf : ∀ y, divergence P f y =
      (if start.succ=y then 1 else 0) - (if (0 : Fin (n+1))=y then 1 else 0)) :
    f = occupation P start := by
  have he : Matrix.vecMul f (LinearMap.toMatrix' (operator P)) =
      Matrix.vecMul (occupation P start) (LinearMap.toMatrix' (operator P)) := by
    funext k
    change (∑ i, f i * _) = ∑ i, occupation P start i * _
    simp_rw [operator_matrix_entry]
    have h := hf k.succ
    have hzero : (0 : Fin (n+1)) ≠ k.succ := (Fin.succ_ne_zero k).symm
    simp only [Fin.succ_inj, hzero, ite_false, sub_zero] at h
    simpa only [divergence, Fin.succ_inj] using h.trans (occupation_transient_balance P start k).symm
  have hinv : LinearMap.toMatrix' (operator P) * fundamental P = 1 := by
    rw [fundamental, ← LinearMap.toMatrix'_comp]
    have h : (operator P).comp (forwardEquiv P).symm.toLinearMap = LinearMap.id := by
      apply LinearMap.ext
      intro f
      exact (forwardEquiv P).apply_symm_apply f
    rw [h, LinearMap.toMatrix'_id]
  have h := congrArg (fun v => Matrix.vecMul v (fundamental P)) he
  simpa only [Matrix.vecMul_vecMul, hinv, Matrix.vecMul_one] using h

/-- Every transition retains precisely the support of the given walk. -/
def transitionFlow (P : Walk n) (start i : Fin n) (y : Fin (n+1)) : ℚ :=
  occupation P start i * P.probability i y

theorem transition_nonnegative (P : Walk n) (start i : Fin n) (y : Fin (n+1)) :
    0 ≤ transitionFlow P start i y :=
  mul_nonneg (occupation_nonnegative P start i) (P.nonnegative i y)

theorem transition_zero (P : Walk n) (start i : Fin n) (y : Fin (n+1))
    (h : P.probability i y = 0) : transitionFlow P start i y = 0 := by
  simp only [transitionFlow, h, mul_zero]

/-- The actual maximal-width row used in the manuscript. -/
def rowWidth (r x : Nat) : Nat := min x (3*r-x)

def rowChild (r : Nat) (i : Fin (3*r)) (t : Fin (rowWidth r (i.val+1)+1)) : Fin (3*r+1) :=
  ⟨i.val+1+rowWidth r (i.val+1)-2*t.val, by
    have h := Nat.min_le_right (i.val+1) (3*r-(i.val+1))
    have hi := i.isLt
    dsimp [rowWidth] at *
    omega⟩

theorem rowChild_injective (r : Nat) (i : Fin (3*r)) : Function.Injective (rowChild r i) := by
  intro t u he
  apply Fin.ext
  have ht := t.isLt
  have hu := u.isLt
  have hw := Nat.min_le_left (i.val+1) (3*r-(i.val+1))
  have hv := congrArg Fin.val he
  dsimp [rowChild,rowWidth] at hv
  dsimp [rowWidth] at ht hu
  omega

def rowOne (r : Nat) (hr : 2 ≤ r) : Fin (3*r+1) := ⟨1, by omega⟩

def rowProbability (r : Nat) (hr : 2 ≤ r) (i : Fin (3*r)) (y : Fin (3*r+1)) : ℚ :=
  if i.val+1=3*r then (if y=rowOne r hr then 1 else 0) else
    ∑ t : Fin (rowWidth r (i.val+1)+1), if y=rowChild r i t then
      (GeneralRowSector.profile r (rowChild r i t).val : ℚ) /
        ((rowWidth r (i.val+1)+1) * (GeneralRowSector.profile r (i.val+1) : ℚ)) else 0

/-- Each legal child has exactly the manuscript's profile-biased probability. -/
theorem rowProbability_child (r : Nat) (hr : 2 ≤ r) (i : Fin (3*r))
    (hi : i.val+1 ≠ 3*r) (t : Fin (rowWidth r (i.val+1)+1)) :
    rowProbability r hr i (rowChild r i t) =
      (GeneralRowSector.profile r (rowChild r i t).val : ℚ) /
        ((rowWidth r (i.val+1)+1) * (GeneralRowSector.profile r (i.val+1) : ℚ)) := by
  simp only [rowProbability, hi, ite_false, (rowChild_injective r i).eq_iff,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]

theorem rowProbability_off_children (r : Nat) (hr : 2 ≤ r) (i : Fin (3*r))
    (hi : i.val+1 ≠ 3*r) (y : Fin (3*r+1))
    (hy : ∀ t, y ≠ rowChild r i t) : rowProbability r hr i y = 0 := by
  simp only [rowProbability, hi, ite_false]
  apply Finset.sum_eq_zero
  intro t _
  exact ite_eq_right (hy t)

theorem child_profile_sum (r : Nat) (i : Fin (3*r)) :
    (∑ t : Fin (rowWidth r (i.val+1)+1), GeneralRowSector.profile r (rowChild r i t).val) =
      (rowWidth r (i.val+1)+1) * GeneralRowSector.profile r (i.val+1) := by
  let h := rowWidth r (i.val+1)
  change (∑ t : Fin (h+1), GeneralRowSector.profile r (i.val+1+h-2*t.val)) = _
  rw [Fin.sum_univ_eq_sum_range (fun t => GeneralRowSector.profile r (i.val+1+h-2*t)) (h+1)]
  have he := List.sum_toFinset (fun t => GeneralRowSector.profile r (i.val+1+h-2*t))
    (List.nodup_range : (List.range (h+1)).Nodup)
  simp only [List.toFinset_range] at he
  rw [he]
  exact GeneralRowSector.profile_sum r (i.val+1) h (Nat.min_le_left _ _)

theorem rowProbability_nonnegative (r : Nat) (hr : 2 ≤ r) (i : Fin (3*r)) (y : Fin (3*r+1)) :
    0 ≤ rowProbability r hr i y := by
  unfold rowProbability
  split_ifs
  all_goals try norm_num
  apply Finset.sum_nonneg
  intro t _
  split_ifs <;> positivity

theorem rowProbability_sum (r : Nat) (hr : 2 ≤ r) (i : Fin (3*r)) :
    ∑ y, rowProbability r hr i y = 1 := by
  unfold rowProbability
  by_cases hi : i.val+1=3*r
  · simp [hi]
  · simp only [hi, ite_false]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [← Finset.sum_div]
    have he : (∑ t : Fin (rowWidth r (i.val+1)+1),
        (GeneralRowSector.profile r (rowChild r i t).val : ℚ)) =
        (rowWidth r (i.val+1)+1) * (GeneralRowSector.profile r (i.val+1) : ℚ) := by
      exact_mod_cast child_profile_sum r i
    rw [he]
    have hp : (0 : ℚ) < GeneralRowSector.profile r (i.val+1) := by
      exact_mod_cast GeneralRowSector.profile_pos r (i.val+1) hr
    exact div_self (ne_of_gt (mul_pos (by positivity) hp))

theorem rowProbability_escape (r : Nat) (hr : 2 ≤ r) (i : Fin (3*r)) :
    ∃ y, y.val < i.val+1 ∧ 0 < rowProbability r hr i y := by
  by_cases hi : i.val+1=3*r
  · refine ⟨rowOne r hr, by dsimp [rowOne]; omega, ?_⟩
    simp only [rowProbability, hi, ite_true]
    norm_num
  · let w := rowWidth r (i.val+1)
    let last : Fin (w+1) := ⟨w, by omega⟩
    let y := rowChild r i last
    have hw : 0 < w := by dsimp [w,rowWidth]; have := i.isLt; omega
    have hwu : w ≤ i.val+1 := Nat.min_le_left _ _
    refine ⟨y, by dsimp [y,rowChild,last]; omega, ?_⟩
    simp only [rowProbability, hi, ite_false]
    apply Finset.sum_pos'
    · intro t _
      split_ifs <;> positivity
    · refine ⟨last, Finset.mem_univ _, ?_⟩
      rw [ite_eq_left rfl]
      apply div_pos
      · exact_mod_cast GeneralRowSector.profile_pos r y.val hr
      · have hp : (0 : ℚ) < GeneralRowSector.profile r (i.val+1) := by
          exact_mod_cast GeneralRowSector.profile_pos r (i.val+1) hr
        exact mul_pos (by positivity) hp

/-- A genuine rational absorbing walk is constructed at every legal row. -/
def rowWalk (r : Nat) (hr : 2 ≤ r) : Walk (3*r) :=
  ⟨rowProbability r hr, rowProbability_nonnegative r hr, rowProbability_sum r hr, rowProbability_escape r hr⟩

theorem row_exists_occupation (r : Nat) (hr : 2 ≤ r) (start : Fin (3*r)) :
    ∃ f : Fin (3*r) → ℚ, (∀ i, 0 ≤ f i) ∧ ∀ y,
      divergence (rowWalk r hr) f y =
        (if start.succ=y then 1 else 0) - (if (0 : Fin (3*r+1))=y then 1 else 0) :=
  exists_occupation (rowWalk r hr) start

end
end MatrixDimensionAudit.RationalOccupationBridge
