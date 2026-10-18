import formalization.DeterminantFiltrationBridge
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Integral determinant bases and unimodular coordinate changes. The proof
uses a two-sided integer inverse, without a rational dimension argument. -/
namespace MatrixDimensionAudit.DeterminantBasisBridge

open DeterminantFiltrationBridge
noncomputable section
open scoped Matrix

/-- Standard monomials are indexed by the exponents of v and vp. -/
abbrev MonomialIndex (c h : ℕ) := Fin c × Fin (h + 1)
/-- The manuscript filtration and quotient-monomial index ranges. -/
abbrev DeterminantIndex (c h : ℕ) := (j : Fin (h + 1)) × Fin (c + h - 2 * j.val)

/-- The four-variable exponent vector of a standard bihomogeneous monomial. -/
def indexExponent (c h : ℕ) (m : MonomialIndex c h) : Fin 4 →₀ ℕ :=
  Finsupp.single 0 (c - 1 - m.1.val) + Finsupp.single 1 m.1.val +
    Finsupp.single 2 (h - m.2.val) + Finsupp.single 3 m.2.val

/-- The standard monomial with the prescribed two degrees. -/
def standardMonomial (c h : ℕ) (m : MonomialIndex c h) : Poly :=
  monomial (c - 1 - m.1.val) m.1.val (h - m.2.val) m.2.val

/-- The actual determinant polynomial with its finite valid index. -/
def indexedBasisVector (c h : ℕ) (d : DeterminantIndex c h) : Poly :=
  basisVector c h d.1.val d.2.val

theorem indexExponent_injective (c h : ℕ) : Function.Injective (indexExponent c h) := by
  intro x y hxy
  have h1 := congrArg (fun e => e 1) hxy
  have h3 := congrArg (fun e => e 3) hxy
  simp [indexExponent] at h1 h3
  exact Prod.ext (Fin.ext h1) (Fin.ext h3)

theorem standardMonomial_eq (c h : ℕ) (m : MonomialIndex c h) :
    standardMonomial c h m = MvPolynomial.monomial (indexExponent c h m) 1 := by
  simp [standardMonomial, monomial, u, v, up, vp,
    MvPolynomial.X_pow_eq_monomial, indexExponent]

theorem standardMonomial_coeff (c h : ℕ) (m n : MonomialIndex c h) :
    (standardMonomial c h n).coeff (indexExponent c h m) =
      if m = n then 1 else 0 := by
  rw [standardMonomial_eq, MvPolynomial.coeff_monomial]
  simp [(indexExponent_injective c h).eq_iff, eq_comm]

private theorem count_lengths (h c : ℕ) (hc : h + 1 ≤ c) :
    ∑ j ∈ Finset.range (h + 1), (c + h - 2 * j) = c * (h + 1) := by
  induction h generalizing c with
  | zero => simp
  | succ h ih =>
    rw [Finset.sum_range_succ']
    have hc' : h + 1 ≤ c - 1 := by omega
    have heq : (∑ j ∈ Finset.range (h + 1), (c + (h + 1) - 2 * (j + 1))) =
        ∑ j ∈ Finset.range (h + 1), (c - 1 + h - 2 * j) := by
      apply Finset.sum_congr rfl
      intro j hj
      omega
    rw [heq, ih (c - 1) hc']
    simp only [Nat.mul_zero, Nat.sub_zero]
    have hc1 : c = (c - 1) + 1 := by omega
    calc
      (c - 1) * (h + 1) + (c + (h + 1)) =
          (c - 1) * (h + 1) + ((c - 1) + 1 + (h + 1)) := by rw [← hc1]
      _ = ((c - 1) + 1) * (h + 1 + 1) := by ring
      _ = c * (h + 1 + 1) := by rw [← hc1]

theorem index_cardinality (c h : ℕ) (hc : h + 1 ≤ c) :
    Fintype.card (MonomialIndex c h) = Fintype.card (DeterminantIndex c h) := by
  simp only [MonomialIndex, Fintype.card_prod, Fintype.card_fin, DeterminantIndex,
    Fintype.card_sigma]
  exact (count_lengths h c hc).symm.trans
    (Fin.sum_univ_eq_sum_range (fun j => c + h - 2 * j) (h + 1)).symm

theorem determinantSpan_eq_range (c h : ℕ) (hc : h + 1 ≤ c) :
    determinantSpan c h = Submodule.span ℤ (Set.range (indexedBasisVector c h)) := by
  unfold determinantSpan
  congr 1
  ext x
  constructor
  · rintro ⟨j, i, hjh, hjc, hi, rfl⟩
    exact ⟨⟨⟨j, by omega⟩, ⟨i, hi⟩⟩, rfl⟩
  · rintro ⟨⟨j, i⟩, rfl⟩
    exact ⟨j.val, i.val, by omega, by omega, i.isLt, rfl⟩

theorem standardMonomial_in_span (c h : ℕ) (hc : h + 1 ≤ c) (m : MonomialIndex c h) :
    standardMonomial c h m ∈ Submodule.span ℤ (Set.range (indexedBasisVector c h)) := by
  rw [← determinantSpan_eq_range c h hc]
  have heq1 : (c - 1 - m.1.val) + m.1.val + 1 = c := by have := m.1.isLt; omega
  have heq2 : (h - m.2.val) + m.2.val = h := by have := m.2.isLt; omega
  have hm := monomial_mem_determinantSpan (c - 1 - m.1.val) m.1.val (h - m.2.val) m.2.val
  simpa only [heq1, heq2, standardMonomial] using hm


/-- Integer coefficients chosen from the proved constructive spanning theorem. -/
def expansionMatrix (c h : ℕ) (hc : h + 1 ≤ c) :
    Matrix (DeterminantIndex c h) (MonomialIndex c h) ℤ :=
  fun d m => Classical.choose ((Submodule.mem_span_range_iff_exists_fun ℤ).mp
    (standardMonomial_in_span c h hc m)) d

theorem expansionMatrix_spec (c h : ℕ) (hc : h + 1 ≤ c) (m : MonomialIndex c h) :
    ∑ d, expansionMatrix c h hc d m • indexedBasisVector c h d =
      standardMonomial c h m :=
  Classical.choose_spec ((Submodule.mem_span_range_iff_exists_fun ℤ).mp
    (standardMonomial_in_span c h hc m))

/-- Actual monomial coefficients of every determinant polynomial. -/
def coordinateMatrix (c h : ℕ) : Matrix (MonomialIndex c h) (DeterminantIndex c h) ℤ :=
  fun m d => (indexedBasisVector c h d).coeff (indexExponent c h m)

theorem coordinateMatrix_mul_expansionMatrix (c h : ℕ) (hc : h + 1 ≤ c) :
    coordinateMatrix c h * expansionMatrix c h hc = 1 := by
  ext m n
  have hs := congrArg (fun p : Poly => p.coeff (indexExponent c h m))
    (expansionMatrix_spec c h hc n)
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, standardMonomial_coeff] at hs
  simpa [Matrix.mul_apply, Matrix.one_apply, coordinateMatrix, smul_eq_mul, mul_comm] using hs

theorem expansionMatrix_mul_coordinateMatrix (c h : ℕ) (hc : h + 1 ≤ c) :
    expansionMatrix c h hc * coordinateMatrix c h = 1 :=
  (Matrix.mul_eq_one_comm_of_card_eq _ _ ℤ (index_cardinality c h hc)).mp
    (coordinateMatrix_mul_expansionMatrix c h hc)

theorem determinant_linearIndependent (c h : ℕ) (hc : h + 1 ≤ c) :
    LinearIndependent ℤ (indexedBasisVector c h) := by
  apply Fintype.linearIndependent_iff.mpr
  intro g hg d
  have hcoord : coordinateMatrix c h *ᵥ g = 0 := by
    funext m
    have hs := congrArg (fun p : Poly => p.coeff (indexExponent c h m)) hg
    simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, AddMonoidAlgebra.coeff_zero] at hs
    simpa [Matrix.mulVec, dotProduct, coordinateMatrix, smul_eq_mul, mul_comm] using hs
  have hgzero : g = 0 := by
    calc
      g = 1 *ᵥ g := by simp
      _ = (expansionMatrix c h hc * coordinateMatrix c h) *ᵥ g := by
        rw [expansionMatrix_mul_coordinateMatrix c h hc]
      _ = expansionMatrix c h hc *ᵥ (coordinateMatrix c h *ᵥ g) := by
        rw [Matrix.mulVec_mulVec]
      _ = 0 := by rw [hcoord]; simp
  exact congrFun hgzero d


theorem determinantVector_expansion (c h : ℕ) (hc : h + 1 ≤ c)
    (d : DeterminantIndex c h) :
    (∑ m, coordinateMatrix c h m d • standardMonomial c h m) = indexedBasisVector c h d := by
  calc
    _ = ∑ m, coordinateMatrix c h m d •
        (∑ n, expansionMatrix c h hc n m • indexedBasisVector c h n) := by
      simp only [expansionMatrix_spec]
    _ = ∑ n, (∑ m, expansionMatrix c h hc n m * coordinateMatrix c h m d) •
        indexedBasisVector c h n := by
      simp only [Finset.smul_sum, Finset.sum_smul, smul_smul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro m hm
      rw [mul_comm]
    _ = ∑ n, (expansionMatrix c h hc * coordinateMatrix c h) n d •
        indexedBasisVector c h n := rfl
    _ = indexedBasisVector c h d := by
      rw [expansionMatrix_mul_coordinateMatrix c h hc]
      simp [Matrix.one_apply, ite_smul]

theorem standardMonomial_mem_monomialSpace (c h : ℕ) (m : MonomialIndex c h) :
    standardMonomial c h m ∈ monomialSpace c h := by
  apply Submodule.subset_span
  refine ⟨c - 1 - m.1.val, m.1.val, h - m.2.val, m.2.val, ?_, ?_, rfl⟩
  · have := m.1.isLt; omega
  · have := m.2.isLt; omega

theorem determinantSpan_eq_monomialSpace (c h : ℕ) (hc : h + 1 ≤ c) :
    determinantSpan c h = monomialSpace c h := by
  apply le_antisymm _ (monomialSpace_le_determinantSpan c h)
  rw [determinantSpan_eq_range c h hc]
  apply Submodule.span_le.mpr
  rintro _ ⟨d, rfl⟩
  rw [← determinantVector_expansion c h hc d]
  apply Submodule.sum_mem
  intro m hm
  exact (monomialSpace c h).smul_mem _ (standardMonomial_mem_monomialSpace c h m)


/-- The manuscript determinant basis as an actual basis over the integers. -/
def determinantBasis (c h : ℕ) (hc : h + 1 ≤ c) :
    Module.Basis (DeterminantIndex c h) ℤ (monomialSpace c h) :=
  (Module.Basis.span (determinant_linearIndependent c h hc)).map
    (LinearEquiv.ofEq _ _ (by
      rw [← determinantSpan_eq_range c h hc, determinantSpan_eq_monomialSpace c h hc]))

@[simp] theorem determinantBasis_coe (c h : ℕ) (hc : h + 1 ≤ c)
    (d : DeterminantIndex c h) :
    (determinantBasis c h hc d : Poly) = basisVector c h d.1.val d.2.val := by
  simp [determinantBasis, Module.Basis.span_apply, indexedBasisVector]


/-- Reindex the equally large coordinate sets to make the matrix square. -/
def indexEquiv (c h : ℕ) (hc : h + 1 ≤ c) :
    MonomialIndex c h ≃ DeterminantIndex c h :=
  (Fintype.card_eq.mp (index_cardinality c h hc)).some

def squareCoordinateMatrix (c h : ℕ) (hc : h + 1 ≤ c) :
    Matrix (MonomialIndex c h) (MonomialIndex c h) ℤ :=
  (coordinateMatrix c h).submatrix id (indexEquiv c h hc)

def squareExpansionMatrix (c h : ℕ) (hc : h + 1 ≤ c) :
    Matrix (MonomialIndex c h) (MonomialIndex c h) ℤ :=
  (expansionMatrix c h hc).submatrix (indexEquiv c h hc) id

theorem squareCoordinateMatrix_mul_squareExpansionMatrix (c h : ℕ) (hc : h + 1 ≤ c) :
    squareCoordinateMatrix c h hc * squareExpansionMatrix c h hc = 1 := by
  unfold squareCoordinateMatrix squareExpansionMatrix
  rw [Matrix.submatrix_mul_equiv, coordinateMatrix_mul_expansionMatrix c h hc]
  simp

/-- The basis change is literally unimodular: its integer determinant is ±1. -/
theorem determinant_unimodular (c h : ℕ) (hc : h + 1 ≤ c) :
    (squareCoordinateMatrix c h hc).det = 1 ∨
      (squareCoordinateMatrix c h hc).det = -1 := by
  apply Int.isUnit_iff.mp
  apply IsUnit.of_mul_eq_one (squareExpansionMatrix c h hc).det
  rw [← Matrix.det_mul, squareCoordinateMatrix_mul_squareExpansionMatrix c h hc, Matrix.det_one]

end
end MatrixDimensionAudit.DeterminantBasisBridge
