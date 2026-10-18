import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Tactic

/-!
The coefficientwise core of the polynomial shared-leg separator, together
with exact reconstruction of polynomial families from nonzero evaluations.
No Laurent-map coefficient identity is assumed.

The separator is the polynomial separator of H. Lü, "Polynomial Separation
of a Shared Tensor Leg and Matrix Multiplication in Arbitrary Characteristic",
arXiv:2610.18914, Proposition 2.1, specialized to ℚ.
-/

namespace MatrixDimensionAudit.Separator

open Polynomial
open scoped BigOperators

variable {F ι : Type*} [Field F] [DecidableEq ι]

/-- The coefficient supplied by the actual evaluation/interpolation source maps.
The exponent of the parameter attached to this coefficient is `r - j` in ℤ. -/
noncomputable def sourceCoefficient (s : Finset ι) (v : ι → F)
    (a : F) (p j r : ℕ) : F :=
  ∑ b ∈ s, v b ^ p * (v b - a) ^ j *
    (taylor a (Lagrange.basis s v b)).coeff r

/-- Interpolation followed by Taylor shift computes every source-map coefficient. -/
theorem sourceCoefficient_eq_taylor (s : Finset ι) (v : ι → F)
    (hv : Set.InjOn v s) (a : F) (p j r : ℕ) (hdeg : p + j < s.card) :
    sourceCoefficient s v a p j r =
      (taylor a ((X : F[X]) ^ p * (X - C a) ^ j)).coeff r := by
  have hd : (((X : F[X]) ^ p * (X - C a) ^ j)).degree < (s.card : WithBot ℕ) := by
    apply lt_of_le_of_lt degree_le_natDegree
    exact_mod_cast (lt_of_le_of_lt
      (natDegree_mul_le.trans (add_le_add (natDegree_X_pow_le p)
        (by simp))) hdeg)
  have hi := Lagrange.eq_interpolate (f := (X : F[X]) ^ p * (X - C a) ^ j) hv hd
  rw [hi, Lagrange.interpolate_apply]
  simp only [map_sum, taylor_mul, taylor_C, finsetSum_coeff, coeff_C_mul,
    eval_mul, eval_pow, eval_X, eval_sub, eval_C, sourceCoefficient]

/-- The explicit binomial formula, valid for arbitrary distinct interpolation nodes. -/
theorem sourceCoefficient_eq (s : Finset ι) (v : ι → F)
    (hv : Set.InjOn v s) (a : F) (p j r : ℕ) (hdeg : p + j < s.card) :
    sourceCoefficient s v a p j r =
      if j ≤ r then (p.choose (r - j) : F) * a ^ (p - (r - j)) else 0 := by
  rw [sourceCoefficient_eq_taylor s v hv a p j r hdeg]
  have ht : taylor a (X - C a : F[X]) = X := by
    simp [taylor_apply]
  simp only [taylor_mul, taylor_pow, ht, taylor_X]
  rw [coeff_mul_X_pow']
  simp only [coeff_X_add_C_pow]
  split_ifs <;> simp_all [mul_comm]

/-- Equation (4), including its explicit zero case outside the binomial range. -/
theorem sourceCoefficient_piecewise (s : Finset ι) (v : ι → F)
    (hv : Set.InjOn v s) (a : F) (p j r : ℕ) (hdeg : p + j < s.card) :
    sourceCoefficient s v a p j r =
      if j ≤ r ∧ r - j ≤ p then
        (p.choose (r - j) : F) * a ^ (p - (r - j)) else 0 := by
  rw [sourceCoefficient_eq s v hv a p j r hdeg]
  by_cases hj : j ≤ r
  · by_cases hp : r - j ≤ p
    · simp [hj, hp]
    · simp [hj, hp, Nat.choose_eq_zero_of_lt (by omega : p < r - j)]
  · simp [hj]

/-- Every would-be negative Laurent power has zero coefficient. -/
theorem sourceCoefficient_negative (s : Finset ι) (v : ι → F)
    (hv : Set.InjOn v s) (a : F) (p j r : ℕ)
    (hdeg : p + j < s.card) (hnegative : r < j) :
    sourceCoefficient s v a p j r = 0 := by
  rw [sourceCoefficient_eq s v hv a p j r hdeg, ite_eq_right (by omega)]

/-- No parameter exponent above the degree of the first input survives. -/
theorem sourceCoefficient_above (s : Finset ι) (v : ι → F)
    (hv : Set.InjOn v s) (a : F) (p j r : ℕ)
    (hdeg : p + j < s.card) (habove : p < r - j) :
    sourceCoefficient s v a p j r = 0 := by
  rw [sourceCoefficient_eq s v hv a p j r hdeg]
  simp [Nat.choose_eq_zero_of_lt habove]

/-- The constant parameter coefficient reads the first input at the block node. -/
theorem sourceCoefficient_constant (s : Finset ι) (v : ι → F)
    (hv : Set.InjOn v s) (a : F) (p j : ℕ) (hdeg : p + j < s.card) :
    sourceCoefficient s v a p j j = a ^ p := by
  simp [sourceCoefficient_eq s v hv a p j j hdeg]

/-- The scalar parameter polynomial after cancellation. Terms with `r < j`
vanish by `sourceCoefficient_negative`, so natural subtraction loses no terms. -/
noncomputable def parameterPolynomial (s : Finset ι) (v : ι → F)
    (a : F) (p j n : ℕ) : F[X] :=
  ∑ r ∈ Finset.range n, C (sourceCoefficient s v a p j r) * X ^ (r - j)

/-- On every nonzero parameter, the Laurent expression from the source maps
is exactly the polynomial obtained by cancellation. -/
theorem parameterPolynomial_eval (s : Finset ι) (v : ι → F)
    (hv : Set.InjOn v s) (a ε : F) (p j n : ℕ)
    (hdeg : p + j < s.card) (hε : ε ≠ 0) :
    (parameterPolynomial s v a p j n).eval ε =
      ∑ r ∈ Finset.range n, sourceCoefficient s v a p j r *
        ε ^ ((r : ℤ) - (j : ℤ)) := by
  unfold parameterPolynomial
  rw [eval_finsetSum]
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hle : j ≤ r
  · rw [eval_mul, eval_C, eval_pow, eval_X,
      zpow_natCast_sub_natCast₀ hε, div_eq_mul_inv, pow_sub₀ ε hε hle]
  · simp [sourceCoefficient_negative s v hv a p j r hdeg (by omega)]

/-- The universal separator degree bound for arbitrary input dimensions. -/
theorem parameterPolynomial_degree (s : Finset ι) (v : ι → F)
    (hv : Set.InjOn v s) (a : F) (M n p j : ℕ)
    (hcard : s.card = M + n - 1) (hp : p < M) (hj : j < n) :
    (parameterPolynomial s v a p j n).natDegree ≤ min (M - 1) (n - 1) := by
  have hdeg : p + j < s.card := by omega
  apply natDegree_sum_le_of_forall_le
  intro r hr
  have hrn : r < n := Finset.mem_range.mp hr
  by_cases hzero : p < r - j
  · simp [sourceCoefficient_above s v hv a p j r hdeg hzero]
  · exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)

/-- At parameter zero the scalar family evaluates the first polynomial at
its block node; the auxiliary monomial is preserved. -/
theorem parameterPolynomial_constant (s : Finset ι) (v : ι → F)
    (hv : Set.InjOn v s) (a : F) (p j n : ℕ)
    (hdeg : p + j < s.card) (hj : j < n) :
    (parameterPolynomial s v a p j n).eval 0 = a ^ p := by
  unfold parameterPolynomial
  rw [eval_finsetSum]
  rw [Finset.sum_eq_single j]
  · simp [sourceCoefficient_constant s v hv a p j hdeg]
  · intro r hr hrj
    by_cases hrlt : r < j
    · simp [sourceCoefficient_negative s v hv a p j r hdeg hrlt]
    · have hpos : 0 < r - j := by omega
      simp [zero_pow (Nat.ne_of_gt hpos)]
  · simp [Finset.mem_range.mpr hj]

/-- General constant-term reconstruction with the actual Lagrange weights. -/
theorem reconstruct_at_zero (s : Finset ι) (v : ι → F)
    (hv : Set.InjOn v s) (f : F[X]) (hdeg : f.natDegree < s.card) :
    f.eval 0 = ∑ b ∈ s, (Lagrange.basis s v b).eval 0 * f.eval (v b) := by
  have hd : f.degree < (s.card : WithBot ℕ) :=
    lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast hdeg)
  conv_lhs => rw [Lagrange.eq_interpolate hv hd]
  simp [Lagrange.interpolate_apply, eval_finsetSum, mul_comm]

/-- The exactification node `b + 1`, hence all nodes lie in `1,...,E`. -/
def rationalNode (b : ℕ) : ℚ := (b + 1 : ℕ)

theorem rationalNode_injective : Function.Injective rationalNode := by
  intro b c h
  unfold rationalNode at h
  have : b + 1 = c + 1 := by exact_mod_cast h
  omega

theorem rationalNode_nonzero (b : ℕ) : rationalNode b ≠ 0 := by
  unfold rationalNode
  exact_mod_cast (by omega : b + 1 ≠ 0)

/-- Every degree-`≤ kD` polynomial is recovered from `kD + 1` nonzero
rational evaluations, with explicit cardinal-polynomial weights. -/
theorem exactification (f : ℚ[X]) (k D : ℕ) (hdeg : f.natDegree ≤ k * D) :
    f.eval 0 = ∑ b ∈ Finset.range (k * D + 1),
      (Lagrange.basis (Finset.range (k * D + 1)) rationalNode b).eval 0 *
        f.eval (rationalNode b) := by
  apply reconstruct_at_zero _ _ (rationalNode_injective.injOn) f
  simpa using Nat.lt_succ_of_le hdeg

/-- Raising a degree-`≤ D` scalar polynomial to the `k`th power needs only
`kD + 1` nonzero evaluations. -/
theorem exactification_power (f : ℚ[X]) (k D : ℕ) (hdeg : f.natDegree ≤ D) :
    (f.eval 0) ^ k = ∑ b ∈ Finset.range (k * D + 1),
      (Lagrange.basis (Finset.range (k * D + 1)) rationalNode b).eval 0 *
        (f.eval (rationalNode b)) ^ k := by
  simpa only [eval_pow] using exactification (f ^ k) k D
    (natDegree_pow_le_of_le k hdeg)

/-- The manuscript's node set and every admissible basis input are covered
for all positive dimensions, including unequal dimensions. -/
theorem rational_sourceCoefficient (M n p j r : ℕ) (a : ℚ)
    (hp : p < M) (hj : j < n) :
    sourceCoefficient (Finset.range (M + n - 1)) rationalNode a p j r =
      if j ≤ r then (p.choose (r - j) : ℚ) * a ^ (p - (r - j)) else 0 := by
  apply sourceCoefficient_eq _ _ rationalNode_injective.injOn
  simp only [Finset.card_range]
  omega

#print axioms sourceCoefficient_eq
#print axioms sourceCoefficient_negative
#print axioms parameterPolynomial_eval
#print axioms parameterPolynomial_degree
#print axioms parameterPolynomial_constant
#print axioms exactification_power

end MatrixDimensionAudit.Separator
