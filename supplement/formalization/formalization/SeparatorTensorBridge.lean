import formalization.SeparatorInterpolationBridge
import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensorRestrictionComposition

/-!
Actual coefficient matrices for the polynomial separator on a matched block
sum with a common first leg, and tensor exactification by nonzero evaluations.
The interpolation identity comes from SeparatorInterpolationBridge; the full
three-map restriction and its diagonal constant tensor are proved here.
The maps are those of H. Lü, arXiv:2610.18914, Proposition 2.1, over ℚ.
-/

namespace MatrixDimensionAudit.SeparatorTensor

open OAI.MatrixMultiplication.Foundation
open MatrixDimensionAudit.Separator Polynomial
open scoped BigOperators

noncomputable section

/-- The coefficient matrix of a linear map, with its finite coordinate action. -/
def coordinateMap {I J : Type*} [Fintype I] (A : I → J → ℚ) :
    (I → ℚ) →ₗ[ℚ] (J → ℚ) where
  toFun x j := ∑ i, A i j * x i
  map_add' x y := by funext j; simp [mul_add, Finset.sum_add_distrib]
  map_smul' c x := by funext j; simp [Finset.mul_sum, mul_left_comm]

/-- Lift copy coefficients while preserving the original tensor coordinate. -/
def liftMatrix {I X : Type*} [DecidableEq X] {L : ℕ}
    (A : I → X → Fin L → ℚ) : (I × X) → (Fin L × X) → ℚ :=
  fun ix bx => if bx.2 = ix.2 then A ix.1 ix.2 bx.1 else 0

/-- Three explicit maps on a direct sum of copies retain all original
coordinates; only their copy-coordinate coefficients are contracted. -/
theorem restrict_copies {I J K X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (L : ℕ) (T : Tensor ℚ X Y Z)
    (A : I → X → Fin L → ℚ) (B : J → Y → Fin L → ℚ)
    (C : K → Z → Fin L → ℚ) (ix : I × X) (jy : J × Y) (kz : K × Z) :
    Tensor.restrict (liftMatrix A) (liftMatrix B) (liftMatrix C)
      (Tensor.directSum (fun _ : Fin L => T)) ix jy kz =
      (∑ b, A ix.1 ix.2 b * B jy.1 jy.2 b * C kz.1 kz.2 b) *
        T ix.2 jy.2 kz.2 := by
  simp [Tensor.restrict, Tensor.directSum, liftMatrix, Fintype.sum_prod_type,
    mul_ite, ite_mul, Finset.sum_mul, ite_and, Finset.sum_ite_irrel]

/-- A matched block sum shares exactly its first input coordinate. -/
def matchedTensor {X Y Z : Type*} {M : ℕ}
    (T : Fin M → Tensor ℚ X Y Z) : Tensor ℚ X (Fin M × Y) (Fin M × Z) :=
  fun x hy hz => if hy.1 = hz.1 then T hy.1 x hy.2 hz.2 else 0

abbrev ell (M n : ℕ) := M + n - 1

def node {N : ℕ} (b : Fin N) : ℚ := rationalNode b.val

def firstMonomial (M n : ℕ) {X : Type*} : Fin M → X → Fin (ell M n) → ℚ :=
  fun p _ b => node b ^ p.val

def secondLaurent (M n : ℕ) {Y : Type*} (ε : ℚ) :
    Fin n → (Fin M × Y) → Fin (ell M n) → ℚ :=
  fun j hy b => (node b - node hy.1) ^ j.val * ε ^ (-(j.val : ℤ))

def thirdTaylor (M n : ℕ) {Z : Type*} (ε : ℚ) :
    Fin n → (Fin M × Z) → Fin (ell M n) → ℚ :=
  fun r hz b =>
    (taylor (node hz.1)
      (Lagrange.basis (Finset.range (ell M n)) rationalNode b.val)).coeff r.val *
      ε ^ r.val

/-- Each coefficient of the monomial-coordinate tensor family is a polynomial. -/
def monomialFamily {X Y Z : Type*} {M n : ℕ}
    (T : Fin M → Tensor ℚ X Y Z) :
    Tensor ℚ[X] (Fin M × X) (Fin n × (Fin M × Y)) (Fin n × (Fin M × Z)) :=
  fun px jhy rhz => if jhy.2.1 = rhz.2.1 then
    Polynomial.C (T jhy.2.1 px.2 jhy.2.2 rhz.2.2 *
      sourceCoefficient (Finset.range (ell M n)) rationalNode
        (node jhy.2.1) px.1.val jhy.1.val rhz.1.val) *
      Polynomial.X ^ (rhz.1.val - jhy.1.val) else 0

/-- Evaluate a polynomial coefficient tensor. -/
def evaluate {X Y Z : Type*} (P : Tensor ℚ[X] X Y Z) (ε : ℚ) : Tensor ℚ X Y Z :=
  fun x y z => (P x y z).eval ε

private theorem scalar_maps (M n : ℕ) (a ε : ℚ) (p : Fin M) (j r : Fin n)
    (hε : ε ≠ 0) :
    (∑ b : Fin (ell M n), node b ^ p.val *
      ((node b - a) ^ j.val * ε ^ (-(j.val : ℤ))) *
      ((taylor a (Lagrange.basis (Finset.range (ell M n)) rationalNode b.val)).coeff
        r.val * ε ^ r.val)) =
      sourceCoefficient (Finset.range (ell M n)) rationalNode a p.val j.val r.val *
        ε ^ (r.val - j.val) := by
  have hdeg : p.val + j.val < (Finset.range (ell M n)).card := by
    simp only [Finset.card_range]; dsimp [ell]; have := p.isLt; have := j.isLt; omega
  have rearrange : ∀ b : Fin (ell M n), node b ^ p.val *
      ((node b - a) ^ j.val * ε ^ (-(j.val : ℤ))) *
      ((taylor a (Lagrange.basis (Finset.range (ell M n)) rationalNode b.val)).coeff
        r.val * ε ^ r.val) =
      (node b ^ p.val * (node b - a) ^ j.val *
        (taylor a (Lagrange.basis (Finset.range (ell M n)) rationalNode b.val)).coeff
          r.val) * ε ^ ((r.val : ℤ) - (j.val : ℤ)) := by
    intro b
    rw [zpow_sub₀ hε]
    simp only [zpow_natCast, zpow_neg, div_eq_mul_inv]
    ring
  simp_rw [rearrange]
  rw [← Finset.sum_mul]
  have hsum : (∑ b : Fin (ell M n), node b ^ p.val * (node b - a) ^ j.val *
      (taylor a (Lagrange.basis (Finset.range (ell M n)) rationalNode b.val)).coeff r.val) =
      sourceCoefficient (Finset.range (ell M n)) rationalNode a p.val j.val r.val := by
    unfold sourceCoefficient node
    exact Fin.sum_univ_eq_sum_range
      (fun b => rationalNode b ^ p.val * (rationalNode b - a) ^ j.val *
        (taylor a (Lagrange.basis (Finset.range (ell M n)) rationalNode b)).coeff r.val) _
  rw [hsum]
  by_cases hle : j.val ≤ r.val
  · rw [← Int.natCast_sub hle, zpow_natCast]
  · rw [sourceCoefficient_negative _ _ rationalNode_injective.injOn _ _ _ _
      hdeg (by omega)]
    simp

/-- The actual three source matrices produce the polynomial tensor at every
nonzero parameter. No desired restriction identity is assumed. -/
theorem monomial_restriction {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    {M n : ℕ} (T : Fin M → Tensor ℚ X Y Z) (ε : ℚ) (hε : ε ≠ 0) :
    Tensor.restrict (liftMatrix (firstMonomial M n))
      (liftMatrix (secondLaurent M n ε)) (liftMatrix (thirdTaylor M n ε))
      (Tensor.directSum (fun _ : Fin (ell M n) => matchedTensor T)) =
      evaluate (monomialFamily (n := n) T) ε := by
  funext px jhy rhz
  rw [restrict_copies]
  by_cases h : jhy.2.1 = rhz.2.1
  · simp only [matchedTensor, h, ite_true, evaluate, monomialFamily,
      eval_mul, eval_C, eval_pow, eval_X]
    dsimp [firstMonomial, secondLaurent, thirdTaylor]
    rw [← h, scalar_maps M n _ ε px.1 jhy.1 rhz.1 hε]
    ring
  · simp [matchedTensor, h, evaluate, monomialFamily]

/-- Cardinal coordinates on the shared first leg. -/
def cardinal (M : ℕ) (g : Fin M) : ℚ[X] :=
  Lagrange.basis (Finset.range M) rationalNode g.val

private theorem cardinal_degree (M : ℕ) (g : Fin M) : (cardinal M g).natDegree < M := by
  have hd := Lagrange.natDegree_basis rationalNode_injective.injOn
    (Finset.mem_range.mpr g.isLt)
  dsimp [cardinal]
  rw [hd, Finset.card_range]
  have := g.isLt
  omega

def firstCardinal (M n : ℕ) {X : Type*} : Fin M → X → Fin (ell M n) → ℚ :=
  fun g _ b => ∑ p : Fin M, (cardinal M g).coeff p.val * node b ^ p.val

/-- The first source map is exactly evaluation of the cardinal polynomial. -/
theorem firstCardinal_eq_eval (M n : ℕ) {X : Type*}
    (g : Fin M) (x : X) (b : Fin (ell M n)) :
    firstCardinal M n g x b = (cardinal M g).eval (node b) := by
  unfold firstCardinal
  rw [Polynomial.eval_eq_sum_range' (cardinal_degree M g) (node b)]
  exact Fin.sum_univ_eq_sum_range
    (fun p => (cardinal M g).coeff p * node b ^ p) M

/-- The tensor polynomial in independent evaluation coordinates on the first leg. -/
def separatorFamily {X Y Z : Type*} {M n : ℕ}
    (T : Fin M → Tensor ℚ X Y Z) :
    Tensor ℚ[X] (Fin M × X) (Fin n × (Fin M × Y)) (Fin n × (Fin M × Z)) :=
  fun gx jy rz => ∑ p : Fin M,
    Polynomial.C ((cardinal M gx.1).coeff p.val) *
      monomialFamily (n := n) T (p, gx.2) jy rz

/-- Actual source maps for the separator in independent first-leg coordinates. -/
theorem separator_restriction {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    {M n : ℕ} (T : Fin M → Tensor ℚ X Y Z) (ε : ℚ) (hε : ε ≠ 0) :
    Tensor.restrict (liftMatrix (firstCardinal M n))
      (liftMatrix (secondLaurent M n ε)) (liftMatrix (thirdTaylor M n ε))
      (Tensor.directSum (fun _ : Fin (ell M n) => matchedTensor T)) =
      evaluate (separatorFamily (n := n) T) ε := by
  funext gx jy rz
  have hm' : ∀ p : Fin M,
      evaluate (monomialFamily (n := n) T) ε (p, gx.2) jy rz =
        (∑ b, firstMonomial M n p gx.2 b * secondLaurent M n ε jy.1 jy.2 b *
          thirdTaylor M n ε rz.1 rz.2 b) * matchedTensor T gx.2 jy.2 rz.2 := by
    intro p
    rw [← monomial_restriction T ε hε, restrict_copies]
  simp only [evaluate, separatorFamily, eval_finsetSum, eval_mul, eval_C]
  change _ = ∑ p : Fin M, (cardinal M gx.1).coeff p.val *
    evaluate (monomialFamily (n := n) T) ε (p, gx.2) jy rz
  simp_rw [hm']
  rw [restrict_copies]
  dsimp [firstCardinal, firstMonomial]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro b hb
  ring

/-- The exact full direct sum, with an n-dimensional dot product on the
second and third legs of each block. The first leg is shared in the source. -/
def separatedTarget {X Y Z : Type*} {M n : ℕ}
    (T : Fin M → Tensor ℚ X Y Z) :
    Tensor ℚ (Fin M × X) (Fin n × (Fin M × Y)) (Fin n × (Fin M × Z)) :=
  fun gx jhy rhz => if gx.1 = jhy.2.1 ∧ gx.1 = rhz.2.1 ∧ jhy.1 = rhz.1 then
    T gx.1 gx.2 jhy.2.2 rhz.2.2 else 0

private theorem monomial_constant {X Y Z : Type*} {M n : ℕ}
    (T : Fin M → Tensor ℚ X Y Z) (px : Fin M × X)
    (jhy : Fin n × (Fin M × Y)) (rhz : Fin n × (Fin M × Z)) :
    evaluate (monomialFamily (n := n) T) 0 px jhy rhz =
      if jhy.2.1 = rhz.2.1 ∧ jhy.1 = rhz.1 then
        T jhy.2.1 px.2 jhy.2.2 rhz.2.2 * node jhy.2.1 ^ px.1.val else 0 := by
  have hd : px.1.val + jhy.1.val < (Finset.range (ell M n)).card := by
    simp only [Finset.card_range]; dsimp [ell]
    have := px.1.isLt; have := jhy.1.isLt; omega
  by_cases hh : jhy.2.1 = rhz.2.1
  · by_cases hjr : jhy.1 = rhz.1
    · have hc := sourceCoefficient_constant (Finset.range (ell M n)) rationalNode
        rationalNode_injective.injOn (node jhy.2.1) px.1.val jhy.1.val hd
      simp only [evaluate, monomialFamily, ite_eq_left hh, eval_mul, eval_C, eval_pow, eval_X]
      rw [← hjr, hc]
      simp [hh, hjr]
    · by_cases hlt : rhz.1.val < jhy.1.val
      · simp [evaluate, monomialFamily, hh, hjr,
          sourceCoefficient_negative _ _ rationalNode_injective.injOn _ _ _ _ hd hlt]
      · have hpos : 0 < rhz.1.val - jhy.1.val := by
          have : rhz.1.val ≠ jhy.1.val := by intro h; exact hjr (Fin.ext h.symm)
          omega
        simp [evaluate, monomialFamily, hh, hjr, zero_pow (Nat.ne_of_gt hpos)]
  · simp [evaluate, monomialFamily, hh]

/-- The constant coefficient is the complete direct-sum tensor, including
all zero cross-block and unequal auxiliary-index entries. -/
theorem separator_constant {X Y Z : Type*} {M n : ℕ}
    (T : Fin M → Tensor ℚ X Y Z) :
    evaluate (separatorFamily (n := n) T) 0 = separatedTarget (n := n) T := by
  funext gx jhy rhz
  simp only [evaluate, separatorFamily, eval_finsetSum, eval_mul, eval_C]
  change (∑ p : Fin M, (cardinal M gx.1).coeff p.val *
    evaluate (monomialFamily (n := n) T) 0 (p, gx.2) jhy rhz) = _
  simp_rw [monomial_constant]
  by_cases hh : jhy.2.1 = rhz.2.1 ∧ jhy.1 = rhz.1
  · simp_rw [ite_eq_left hh]
    have heval : (∑ p : Fin M, (cardinal M gx.1).coeff p.val *
        (T jhy.2.1 gx.2 jhy.2.2 rhz.2.2 * node jhy.2.1 ^ p.val)) =
        T jhy.2.1 gx.2 jhy.2.2 rhz.2.2 * (cardinal M gx.1).eval (node jhy.2.1) := by
      rw [Polynomial.eval_eq_sum_range' (cardinal_degree M gx.1) (node jhy.2.1)]
      rw [← Fin.sum_univ_eq_sum_range (fun p =>
        (cardinal M gx.1).coeff p * node jhy.2.1 ^ p) M]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    rw [heval]
    by_cases hg : gx.1 = jhy.2.1
    · have hself : (cardinal M gx.1).eval (node jhy.2.1) = 1 := by
        rw [hg]
        exact Lagrange.eval_basis_self rationalNode_injective.injOn
          (Finset.mem_range.mpr jhy.2.1.isLt)
      rw [hself]
      simp [separatedTarget, hg, hh.1, hh.2]
    · have hval : (cardinal M gx.1).eval (node jhy.2.1) = 0 := by
        exact Lagrange.eval_basis_of_ne (by intro h; exact hg (Fin.ext h))
          (Finset.mem_range.mpr jhy.2.1.isLt)
      simp [hval, separatedTarget, hg]
  · simp_rw [ite_eq_right hh, mul_zero]
    rw [Finset.sum_const_zero]
    simp only [separatedTarget]
    split_ifs with h
    · exact False.elim (hh ⟨h.1.symm.trans h.2.1, h.2.2⟩)
    · rfl

/-- Every actual polynomial tensor coefficient has the improved local degree bound. -/
theorem monomial_degree {X Y Z : Type*} {M n : ℕ}
    (T : Fin M → Tensor ℚ X Y Z) (px : Fin M × X)
    (jhy : Fin n × (Fin M × Y)) (rhz : Fin n × (Fin M × Z)) :
    (monomialFamily (n := n) T px jhy rhz).natDegree ≤ min (M - 1) (n - 1) := by
  unfold monomialFamily
  split_ifs
  · have hd : px.1.val + jhy.1.val < (Finset.range (ell M n)).card := by
      simp only [Finset.card_range]; dsimp [ell]
      have := px.1.isLt; have := jhy.1.isLt; omega
    by_cases hb : px.1.val < rhz.1.val - jhy.1.val
    · simp [sourceCoefficient_above _ _ rationalNode_injective.injOn _ _ _ _ hd hb]
    · apply (natDegree_C_mul_X_pow_le _ _).trans
      have := px.1.isLt; have := rhz.1.isLt; omega
  · simp

theorem separator_degree {X Y Z : Type*} {M n : ℕ}
    (T : Fin M → Tensor ℚ X Y Z) (gx : Fin M × X)
    (jhy : Fin n × (Fin M × Y)) (rhz : Fin n × (Fin M × Z)) :
    (separatorFamily (n := n) T gx jhy rhz).natDegree ≤ min (M - 1) (n - 1) := by
  apply natDegree_sum_le_of_forall_le
  intro p hp
  exact (natDegree_C_mul_le _ _).trans (monomial_degree T (p, gx.2) jhy rhz)

/-- Fold evaluation copies onto a common coordinate space, charging the
interpolation weight on the first leg. -/
def foldMatrix {E X : Type*} [DecidableEq X] (w : E → ℚ) : X → (E × X) → ℚ :=
  fun x ex => if ex.2 = x then w ex.1 else 0

theorem restrict_fold {E X Y Z : Type*}
    [Fintype E] [DecidableEq E] [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (T : E → Tensor ℚ X Y Z) (w : E → ℚ) :
    Tensor.restrict (foldMatrix w) (foldMatrix (fun _ : E => 1))
      (foldMatrix (fun _ : E => 1)) (Tensor.directSum T) =
      fun x y z => ∑ e, w e * T e x y z := by
  funext x y z
  simp [Tensor.restrict, Tensor.directSum, foldMatrix, Fintype.sum_prod_type,
    mul_ite, ite_mul, ite_and, Finset.sum_ite_irrel]

/-- A genuine decomposition of every summand yields a decomposition of the
direct sum, with the full number of summands charged. -/
theorem directSum_rankAtMost {E X Y Z : Type*} [Fintype E] [DecidableEq E]
    (T : E → Tensor ℚ X Y Z) (R : ℕ) (h : ∀ e, Tensor.RankAtMost (T e) R) :
    Tensor.RankAtMost (Tensor.directSum T) (Fintype.card E * R) := by
  choose a b c heq using h
  let aa : E × Fin R → E × X → ℚ := fun ei ex =>
    if ex.1 = ei.1 then a ei.1 ei.2 ex.2 else 0
  let bb : E × Fin R → E × Y → ℚ := fun ei ey =>
    if ey.1 = ei.1 then b ei.1 ei.2 ey.2 else 0
  let cc : E × Fin R → E × Z → ℚ := fun ei ez =>
    if ez.1 = ei.1 then c ei.1 ei.2 ez.2 else 0
  have ht : Tensor.directSum T = fun x y z =>
      ∑ ei : E × Fin R, Tensor.rankOne (aa ei) (bb ei) (cc ei) x y z := by
    funext x y z
    by_cases hxy : x.1 = y.1 <;> by_cases hxz : x.1 = z.1 <;>
      by_cases hyz : y.1 = z.1 <;>
      simp_all [Tensor.directSum, Tensor.rankOne, aa, bb, cc, Fintype.sum_prod_type,
        mul_ite, ite_mul, Finset.sum_ite_irrel]
  rw [ht]
  simpa using Tensor.rankAtMost_sum_rankOne aa bb cc

/-- Cardinal weights for exact tensor interpolation at zero. -/
def exactWeight (d : ℕ) (e : Fin (d + 1)) : ℚ :=
  (Lagrange.basis (Finset.range (d + 1)) rationalNode e.val).eval 0

/-- Every polynomial coefficient tensor of degree at most d is an exact
restriction of d+1 nonzero evaluation copies, with all three maps explicit. -/
theorem tensor_exactification {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (P : Tensor ℚ[X] X Y Z) (d : ℕ)
    (hd : ∀ x y z, (P x y z).natDegree ≤ d) :
    Tensor.restrict (foldMatrix (exactWeight d))
      (foldMatrix (fun _ : Fin (d + 1) => 1))
      (foldMatrix (fun _ : Fin (d + 1) => 1))
      (Tensor.directSum (fun e : Fin (d + 1) => evaluate P (node e))) =
        evaluate P 0 := by
  rw [restrict_fold]
  funext x y z
  have hs := exactification (P x y z) 1 d (by simpa using hd x y z)
  simp only [Nat.one_mul] at hs
  dsimp [exactWeight, evaluate, node]
  rw [Fin.sum_univ_eq_sum_range (fun e =>
    (Lagrange.basis (Finset.range (d + 1)) rationalNode e).eval 0 *
      (P x y z).eval (rationalNode e)) (d + 1)]
  exact hs.symm

theorem tensor_exactification_rank {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (P : Tensor ℚ[X] X Y Z) (d R : ℕ)
    (hd : ∀ x y z, (P x y z).natDegree ≤ d)
    (hr : ∀ e : Fin (d + 1), Tensor.RankAtMost (evaluate P (node e)) R) :
    Tensor.RankAtMost (evaluate P 0) ((d + 1) * R) := by
  have h := directSum_rankAtMost (fun e : Fin (d + 1) => evaluate P (node e)) R hr
  have ht := h.restrict (foldMatrix (exactWeight d))
    (foldMatrix (fun _ : Fin (d + 1) => 1)) (foldMatrix (fun _ : Fin (d + 1) => 1))
  simpa only [tensor_exactification P d hd, Fintype.card_fin] using ht

/-- A source rank certificate survives each nonzero separator evaluation,
with exactly ell copies of the matched tensor charged. -/
theorem separator_sample_rank {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    {M n R : ℕ} (T : Fin M → Tensor ℚ X Y Z)
    (hr : Tensor.RankAtMost (matchedTensor T) R) (ε : ℚ) (hε : ε ≠ 0) :
    Tensor.RankAtMost (evaluate (separatorFamily (n := n) T) ε) (ell M n * R) := by
  have h := directSum_rankAtMost (fun _ : Fin (ell M n) => matchedTensor T) R (fun _ => hr)
  have ht := h.restrict (liftMatrix (firstCardinal M n))
    (liftMatrix (secondLaurent M n ε)) (liftMatrix (thirdTaylor M n ε))
  simpa only [separator_restriction T ε hε, Fintype.card_fin] using ht

/-- The complete diagonal separator has a proved exact rank bound, obtained
from actual maps and interpolation, with every evaluation and copy charged. -/
theorem separated_rank {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    {M n R : ℕ} (T : Fin M → Tensor ℚ X Y Z)
    (hr : Tensor.RankAtMost (matchedTensor T) R) :
    Tensor.RankAtMost (separatedTarget (n := n) T)
      ((min (M - 1) (n - 1) + 1) * (ell M n * R)) := by
  rw [← separator_constant T]
  apply tensor_exactification_rank _ _ _ (separator_degree T)
  intro e
  exact separator_sample_rank T hr (node e) (rationalNode_nonzero e.val)

/-- Products in a tensor power have degree at most k times the coordinate degree. -/
theorem tensor_power_degree {X Y Z : Type*} (P : Tensor ℚ[X] X Y Z)
    (k d : ℕ) (hd : ∀ x y z, (P x y z).natDegree ≤ d)
    (x : Fin k → X) (y : Fin k → Y) (z : Fin k → Z) :
    (Tensor.power P k x y z).natDegree ≤ k * d := by
  apply (natDegree_prod_le Finset.univ (fun i => P (x i) (y i) (z i))).trans
  exact (Finset.sum_le_sum (fun i _ => hd (x i) (y i) (z i))).trans (by simp)

/-- General tensor-power exactification with E=kD+1, using the actual
coefficient tensor power and genuine evaluation rank decompositions. -/
theorem tensor_power_exactification_rank {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (P : Tensor ℚ[X] X Y Z) (k d R : ℕ)
    (hd : ∀ x y z, (P x y z).natDegree ≤ d)
    (hr : ∀ e : Fin (k * d + 1), Tensor.RankAtMost (evaluate P (node e)) R) :
    Tensor.RankAtMost (Tensor.power (evaluate P 0) k) ((k * d + 1) * R ^ k) := by
  have heval : ∀ ε, evaluate (Tensor.power P k) ε = Tensor.power (evaluate P ε) k := by
    intro ε
    funext x y z
    simp [evaluate, Tensor.power, eval_prod]
  rw [← heval 0]
  apply tensor_exactification_rank _ _ _ (tensor_power_degree P k d hd)
  intro e
  rw [heval]
  exact (hr e).power k

/-- The auxiliary dot product has no new shared-first-leg coordinate. -/
def dotTensor (n : ℕ) : Tensor ℚ Unit (Fin n) (Fin n) :=
  fun _ j r => if j = r then 1 else 0

/-- The displayed target is literally a coordinate relabeling of the direct
sum of each original block tensored with the auxiliary dot product. -/
theorem separatedTarget_directSum {X Y Z : Type*} {M n : ℕ}
    (T : Fin M → Tensor ℚ X Y Z) :
    separatedTarget (n := n) T = Tensor.pullback
      (fun gx : Fin M × X => (gx.1, (gx.2, ())))
      (fun jy : Fin n × (Fin M × Y) => (jy.2.1, (jy.2.2, jy.1)))
      (fun rz : Fin n × (Fin M × Z) => (rz.2.1, (rz.2.2, rz.1)))
      (Tensor.directSum (fun h => Tensor.product (T h) (dotTensor n))) := by
  funext gx jy rz
  simp only [separatedTarget, Tensor.pullback, Tensor.directSum, Tensor.product, dotTensor]
  split_ifs <;> simp_all <;> grind

/-- Bundled first input linear map for the actual separator restriction. -/
def firstMap {X : Type*} [Fintype X] [DecidableEq X] (M n : ℕ) :=
  coordinateMap (liftMatrix (firstCardinal M n (X := X)))

/-- Bundled second input linear map, evaluated only at nonzero parameters. -/
def secondMap {Y : Type*} [Fintype Y] [DecidableEq Y] (M n : ℕ) (ε : ℚ) :=
  coordinateMap (liftMatrix (secondLaurent M n (Y := Y) ε))

/-- Bundled third input linear map for the Taylor-functional pullback. -/
def thirdMap {Z : Type*} [Fintype Z] [DecidableEq Z] (M n : ℕ) (ε : ℚ) :=
  coordinateMap (liftMatrix (thirdTaylor M n (Z := Z) ε))

/-- Generic product degree accounting for actual polynomial coefficient tensors. -/
theorem tensor_product_degree {X Y Z U V W : Type*}
    (P : Tensor ℚ[X] X Y Z) (Q : Tensor ℚ[X] U V W) (d e : ℕ)
    (hd : ∀ x y z, (P x y z).natDegree ≤ d)
    (he : ∀ u v w, (Q u v w).natDegree ≤ e)
    (x : X × U) (y : Y × V) (z : Z × W) :
    (Tensor.product P Q x y z).natDegree ≤ d + e :=
  natDegree_mul_le.trans (add_le_add (hd x.1 y.1 z.1) (he x.2 y.2 z.2))

/-- Exactification of separator powers uses E=kd+1 nonzero evaluation tensors,
where d=min(M-1,n-1), and ell^k source copies per evaluation. -/
theorem separated_power_rank {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    {M n R : ℕ} (T : Fin M → Tensor ℚ X Y Z) (k : ℕ)
    (hr : Tensor.RankAtMost (matchedTensor T) R) :
    Tensor.RankAtMost (Tensor.power (separatedTarget (n := n) T) k)
      ((k * min (M - 1) (n - 1) + 1) * (ell M n * R) ^ k) := by
  rw [← separator_constant T]
  apply tensor_power_exactification_rank _ _ _ _ (separator_degree T)
  intro e
  exact separator_sample_rank T hr (node e) (rationalNode_nonzero e.val)

#print axioms monomial_restriction
#print axioms separator_restriction
#print axioms separator_constant
#print axioms separator_degree
#print axioms separatedTarget_directSum
#print axioms tensor_exactification
#print axioms tensor_exactification_rank
#print axioms tensor_power_exactification_rank
#print axioms separated_power_rank

end
end MatrixDimensionAudit.SeparatorTensor
