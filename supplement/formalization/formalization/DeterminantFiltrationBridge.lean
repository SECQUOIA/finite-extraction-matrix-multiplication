import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Ring
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Span
import Lean.Elab.Tactic.Omega

/-! Constructive integer normal forms for the determinant filtration in
`manuscript/maps.tex`. No tensor rank or dimension inequality is assumed. -/
namespace MatrixDimensionAudit.DeterminantFiltrationBridge

noncomputable section

abbrev Poly := MvPolynomial (Fin 4) ℤ
abbrev Binary := MvPolynomial (Fin 2) ℤ

def u : Poly := MvPolynomial.X 0
def v : Poly := MvPolynomial.X 1
def up : Poly := MvPolynomial.X 2
def vp : Poly := MvPolynomial.X 3

def delta : Poly := u * vp - v * up

def monomial (a b p q : ℕ) : Poly := u ^ a * v ^ b * up ^ p * vp ^ q

/-- The manuscript's monomial lift, indexed by dimension `c` and primed degree `h`. -/
def lift (c h i : ℕ) : Poly :=
  if i ≤ c - 1 then monomial (c - 1 - i) i h 0
  else monomial 0 (c - 1) (c + h - 1 - i) (i - c + 1)

/-- The proposed basis vectors, defined without assuming that they form a basis. -/
def basisVector (c h j i : ℕ) : Poly := delta ^ j * lift (c - j) (h - j) i

/-- Removing `t` copies of `uv'` leaves the complementary powers unchanged. -/
theorem factor_monomial (a b p q t : ℕ) (ha : t ≤ a) (hq : t ≤ q) :
    monomial a b p q =
      monomial (a - t) b p (q - t) * (u * vp) ^ t := by
  unfold monomial
  have hua : u ^ a = u ^ (a - t) * u ^ t := by
    rw [← pow_add, Nat.sub_add_cancel ha]
  have hvq : vp ^ q = vp ^ (q - t) * vp ^ t := by
    rw [← pow_add, Nat.sub_add_cancel hq]
  rw [hua, hvq, mul_pow]
  ring

/-- A normal monomial in each binomial summand is exactly a manuscript lift. -/
theorem normal_monomial_eq_lift (a b p q j : ℕ)
    (hj : j ≤ min a q) :
    monomial (a - min a q) (b + (min a q - j))
      (p + (min a q - j)) (q - min a q) =
      lift (a + b + 1 - j) (p + q - j) (b + q - j) := by
  have hja : j ≤ a := le_trans hj (Nat.min_le_left _ _)
  have hjq : j ≤ q := le_trans hj (Nat.min_le_right _ _)
  by_cases haq : a ≤ q
  · rw [Nat.min_eq_left haq]
    by_cases hqa : q ≤ a
    · have heq : q = a := by omega
      subst q
      rw [lift, ite_eq_left (by omega)]
      congr 1 <;> omega
    · rw [lift, ite_eq_right (by omega)]
      congr 1 <;> omega
  · have hqa : q ≤ a := by omega
    rw [Nat.min_eq_right hqa, lift, ite_eq_left (by omega)]
    congr 1 <;> omega

/-- An explicit integral expansion of every monomial in determinant lifts.
The depth is bounded by `min a q`, so this works for arbitrary degrees. -/
theorem monomial_determinant_expansion (a b p q : ℕ) :
    monomial a b p q =
      ∑ j ∈ Finset.range (min a q + 1),
        (Nat.choose (min a q) j : Poly) *
          basisVector (a + b + 1) (p + q) j (b + q - j) := by
  let t := min a q
  rw [factor_monomial a b p q t (Nat.min_le_left _ _) (Nat.min_le_right _ _)]
  have huv : u * vp = delta + v * up := by unfold delta; ring
  rw [huv, add_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjt : j ≤ t := by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hn := normal_monomial_eq_lift a b p q j hjt
  unfold basisVector
  rw [← hn]
  unfold monomial
  rw [mul_pow]
  simp only [pow_add]
  ring

/-- Every summand has a valid filtration index and a valid quotient monomial index. -/
theorem expansion_indices (a b p q j : ℕ) (hj : j < min a q + 1) :
    j ≤ p + q ∧ j < a + b + 1 ∧
      b + q - j < (a + b + 1) + (p + q) - 2 * j := by
  have hja := Nat.min_le_left a q
  have hjq := Nat.min_le_right a q
  omega

/-- The integral span of all bihomogeneous monomials of bidegree `(c-1,h)`. -/
def monomialSpace (c h : ℕ) : Submodule ℤ Poly :=
  Submodule.span ℤ {x | ∃ a b p q : ℕ,
    a + b + 1 = c ∧ p + q = h ∧ monomial a b p q = x}

/-- The integral span of precisely the index range in the manuscript. -/
def determinantSpan (c h : ℕ) : Submodule ℤ Poly :=
  Submodule.span ℤ {x | ∃ j i : ℕ,
    j ≤ h ∧ j < c ∧ i < c + h - 2 * j ∧ basisVector c h j i = x}

theorem monomial_mem_determinantSpan (a b p q : ℕ) :
    monomial a b p q ∈ determinantSpan (a + b + 1) (p + q) := by
  rw [monomial_determinant_expansion]
  apply Submodule.sum_mem
  intro j hj
  obtain ⟨hjh, hjc, hji⟩ := expansion_indices a b p q j (Finset.mem_range.mp hj)
  have hb : basisVector (a + b + 1) (p + q) j (b + q - j) ∈
      determinantSpan (a + b + 1) (p + q) :=
    Submodule.subset_span ⟨j, b + q - j, hjh, hjc, hji, rfl⟩
  simpa [Algebra.smul_def] using
    (determinantSpan (a + b + 1) (p + q)).smul_mem
      (Nat.choose (min a q) j : ℤ) hb

/-- Constructive integer spanning, with no basis or dimension hypothesis. -/
theorem monomialSpace_le_determinantSpan (c h : ℕ) :
    monomialSpace c h ≤ determinantSpan c h := by
  apply Submodule.span_le.mpr
  rintro x ⟨a, b, p, q, hc, hh, rfl⟩
  subst c
  subst h
  exact monomial_mem_determinantSpan a b p q

/-- Substitute `(u',v')=(u,v)` into the four-variable polynomial ring. -/
def diagonal : Poly →+* Binary :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun i => if i = 0 ∨ i = 2 then MvPolynomial.X 0 else MvPolynomial.X 1)

@[simp] theorem diagonal_u : diagonal u = MvPolynomial.X 0 := by
  simp [diagonal, u]
@[simp] theorem diagonal_v : diagonal v = MvPolynomial.X 1 := by
  simp [diagonal, v]
@[simp] theorem diagonal_up : diagonal up = MvPolynomial.X 0 := by
  simp [diagonal, up]
@[simp] theorem diagonal_vp : diagonal vp = MvPolynomial.X 1 := by
  simp [diagonal, vp]
@[simp] theorem diagonal_delta : diagonal delta = 0 := by
  simp [delta, mul_comm]

theorem diagonal_monomial (a b p q : ℕ) :
    diagonal (monomial a b p q) =
      (MvPolynomial.X 0 : Binary) ^ (a + p) * MvPolynomial.X 1 ^ (b + q) := by
  simp only [monomial, map_mul, map_pow, diagonal_u, diagonal_v,
    diagonal_up, diagonal_vp, pow_add]
  ring

/-- The lift really is a section of diagonal specialization on binary monomials. -/
theorem diagonal_lift (c h i : ℕ) (hc : 0 < c) (hi : i < c + h) :
    diagonal (lift c h i) =
      (MvPolynomial.X 0 : Binary) ^ (c + h - 1 - i) * MvPolynomial.X 1 ^ i := by
  unfold lift
  split_ifs with hic
  · rw [diagonal_monomial]
    congr 2; omega
  · rw [diagonal_monomial]
    congr 2 <;> omega

/-- Multiplication preserves determinant divisibility for every filtration depth. -/
theorem multiplication_preserves_filtration (f rho : Poly) (j : ℕ) :
    f * (delta ^ j * rho) = delta ^ j * (f * rho) := by ring

/-- On divided representatives, diagonal specialization intertwines multiplication. -/
theorem diagonal_multiplication (f rho : Poly) :
    diagonal (f * rho) = diagonal f * diagonal rho := map_mul diagonal f rho

/-- Every strictly higher filtration layer is killed by diagonal specialization
after dividing out the current determinant power. -/
theorem diagonal_higher_layer (rho : Poly) (k : ℕ) :
    diagonal (delta ^ (k + 1) * rho) = 0 := by simp

private theorem power_difference (x y : Poly) (n : ℕ) :
    ∃ rho : Poly, x ^ n = y ^ n + (x - y) * rho := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨rho, hrho⟩ := ih
    refine ⟨y ^ n + rho * x, ?_⟩
    rw [pow_succ, pow_succ, hrho]
    ring

/-- The first normal-form step, as an exact divisibility statement over `ℤ`. -/
theorem delta_dvd_monomial_sub_lift (a b p q : ℕ) :
    delta ∣ monomial a b p q - lift (a + b + 1) (p + q) (b + q) := by
  let t := min a q
  let rest := monomial (a - t) b p (q - t)
  obtain ⟨rho, hrho⟩ := power_difference (u * vp) (v * up) t
  have hlift : lift (a + b + 1) (p + q) (b + q) = rest * (v * up) ^ t := by
    have hn := normal_monomial_eq_lift a b p q 0 (by omega)
    simp only [Nat.sub_zero] at hn
    rw [← hn]
    dsimp [rest, t]
    unfold monomial
    simp only [mul_pow, pow_add]
    ring
  refine ⟨rest * rho, ?_⟩
  rw [factor_monomial a b p q t (Nat.min_le_left _ _) (Nat.min_le_right _ _),
    hlift, hrho]
  change rest * ((v * up) ^ t + delta * rho) - rest * (v * up) ^ t =
    delta * (rest * rho)
  ring

/-- The ambient determinant quotient, used only for polynomial identities. -/
abbrev DeterminantQuotient := Poly ⧸ Ideal.span ({delta} : Set Poly)

def quotientMap : Poly →+* DeterminantQuotient := Ideal.Quotient.mk _

/-- Every bihomogeneous monomial has the prescribed lift as its residue modulo `Δ`. -/
theorem monomial_quotient (a b p q : ℕ) :
    quotientMap (monomial a b p q) =
      quotientMap (lift (a + b + 1) (p + q) (b + q)) := by
  apply Ideal.Quotient.eq.mpr
  exact Ideal.mem_span_singleton.mpr (delta_dvd_monomial_sub_lift a b p q)

private theorem first_monomial_mul (s t a b p q : ℕ) :
    (u ^ s * v ^ t) * monomial a b p q = monomial (a + s) (b + t) p q := by
  unfold monomial
  simp only [pow_add]
  ring

/-- Multiplication in the determinant quotient is ordinary convolution:
the quotient monomial index increases by the `v` exponent `t`.
This holds for unbounded input and multiplier degrees. -/
theorem quotient_convolution (c h i s t : ℕ) (hc : 0 < c) (hi : i < c + h) :
    quotientMap ((u ^ s * v ^ t) * lift c h i) =
      quotientMap (lift (c + s + t) h (i + t)) := by
  by_cases hic : i ≤ c - 1
  · have hout : i + t ≤ c + s + t - 1 := by omega
    rw [lift, ite_eq_left hic, lift, ite_eq_left hout]
    congr 1
    unfold monomial
    have ha : c + s + t - 1 - (i + t) = (c - 1 - i) + s := by omega
    rw [ha]
    simp only [pow_add]
    ring
  · rw [lift, ite_eq_right hic, first_monomial_mul]
    have heq := monomial_quotient (0 + s) (c - 1 + t) (c + h - 1 - i) (i - c + 1)
    have hc' : 0 + s + (c - 1 + t) + 1 = c + s + t := by omega
    have hh' : c + h - 1 - i + (i - c + 1) = h := by omega
    have hi' : c - 1 + t + (i - c + 1) = i + t := by omega
    simpa only [hc', hh', hi'] using heq

/-- At every determinant depth, the error from convolution is in the next
determinant layer. This is an actual polynomial divisibility statement. -/
theorem filtration_convolution (c h j i s t : ℕ)
    (hjc : j < c) (hjh : j ≤ h) (hi : i < (c - j) + (h - j)) :
    delta ^ (j + 1) ∣
      (u ^ s * v ^ t) * basisVector c h j i -
        basisVector (c + s + t) h j (i + t) := by
  have hquot := quotient_convolution (c - j) (h - j) i s t (by omega) hi
  have hdim : c - j + s + t = c + s + t - j := by omega
  rw [hdim] at hquot
  have hdiv : delta ∣
      (u ^ s * v ^ t) * lift (c - j) (h - j) i -
        lift (c + s + t - j) (h - j) (i + t) :=
    Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp hquot)
  obtain ⟨rho, hrho⟩ := hdiv
  refine ⟨rho, ?_⟩
  unfold basisVector
  calc
    _ = delta ^ j * ((u ^ s * v ^ t) * lift (c - j) (h - j) i -
          lift (c + s + t - j) (h - j) (i + t)) := by ring
    _ = delta ^ (j + 1) * rho := by rw [hrho, pow_succ]; ring

end
end MatrixDimensionAudit.DeterminantFiltrationBridge
