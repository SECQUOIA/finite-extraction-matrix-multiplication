import formalization.DeterminantBasisBridge

/-! Finite binary-form quotients of the determinant filtration over the integers. -/
namespace MatrixDimensionAudit.DeterminantQuotientBridge
open DeterminantFiltrationBridge DeterminantBasisBridge
noncomputable section

/-- The actual degree `n-1` binary monomial. -/
def binaryMonomial (n : ℕ) (i : Fin n) : Binary :=
  MvPolynomial.X 0 ^ (n - 1 - i.val) * MvPolynomial.X 1 ^ i.val

/-- The finite integral module of binary forms indexed by dimension. -/
def binarySpace (n : ℕ) : Submodule ℤ Binary :=
  Submodule.span ℤ (Set.range (binaryMonomial n))

def binaryVector (n : ℕ) (i : Fin n) : binarySpace n :=
  ⟨binaryMonomial n i, Submodule.subset_span ⟨i, rfl⟩⟩

def binaryExponent (n : ℕ) (i : Fin n) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 (n - 1 - i.val) + Finsupp.single 1 i.val

theorem binaryMonomial_coeff (n : ℕ) (i k : Fin n) :
    (binaryMonomial n k).coeff (binaryExponent n i) = if i = k then 1 else 0 := by
  have hinj : Function.Injective (binaryExponent n) := by
    intro a b hab
    have h := congrArg (fun e => e 1) hab
    simp [binaryExponent] at h
    exact Fin.ext h
  have hm : binaryMonomial n k = MvPolynomial.monomial (binaryExponent n k) 1 := by
    simp [binaryMonomial, MvPolynomial.X_pow_eq_monomial, binaryExponent]
  rw [hm, MvPolynomial.coeff_monomial]
  simp [hinj.eq_iff, eq_comm]

def diagonalLinear : Poly →ₗ[ℤ] Binary := diagonal.toAddMonoidHom.toIntLinearMap

@[simp] theorem diagonalLinear_apply (p : Poly) : diagonalLinear p = diagonal p := rfl

theorem diagonal_mem_binarySpace (c h : ℕ) {p : Poly} (hp : p ∈ monomialSpace c h) :
    diagonalLinear p ∈ binarySpace (c + h) := by
  unfold monomialSpace at hp
  induction hp using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, b, p, q, hc, hh, rfl⟩ := hx
    have hi : b + q < c + h := by omega
    have hexp : c + h - 1 - (b + q) = a + p := by omega
    rw [diagonalLinear_apply, diagonal_monomial]
    apply Submodule.subset_span
    refine ⟨⟨b + q, hi⟩, ?_⟩
    simp [binaryMonomial, hexp]
  | zero => simp
  | add x y hx hy ihx ihy =>
    rw [map_add]
    exact (binarySpace (c + h)).add_mem ihx ihy
  | smul a x hx ih =>
    rw [map_smul]
    exact (binarySpace (c + h)).smul_mem a ih

/-- Actual diagonal substitution restricted to the two finite polynomial modules. -/
def quotientMap (c h : ℕ) : monomialSpace c h →ₗ[ℤ] binarySpace (c + h) :=
  (diagonalLinear.domRestrict (monomialSpace c h)).codRestrict _
    (fun p => diagonal_mem_binarySpace c h p.property)

@[simp] theorem quotientMap_coe (c h : ℕ) (p : monomialSpace c h) :
    (quotientMap c h p : Binary) = diagonal (p : Poly) := rfl

def zeroIndex (c h : ℕ) (i : Fin (c + h)) : DeterminantIndex c h :=
  ⟨⟨0, by omega⟩, ⟨i.val, i.isLt⟩⟩

theorem quotientMap_basis_zero (c h : ℕ) (hc : h + 1 ≤ c) (i : Fin (c + h)) :
    quotientMap c h (determinantBasis c h hc (zeroIndex c h i)) = binaryVector (c + h) i := by
  apply Subtype.ext
  rw [quotientMap_coe, determinantBasis_coe]
  simp only [basisVector, zeroIndex, Nat.sub_zero, pow_zero, one_mul]
  exact diagonal_lift c h i.val (by omega) i.isLt

theorem quotientMap_basis_positive (c h : ℕ) (hc : h + 1 ≤ c)
    (d : DeterminantIndex c h) (hd : 0 < d.1.val) :
    quotientMap c h (determinantBasis c h hc d) = 0 := by
  apply Subtype.ext
  rw [quotientMap_coe, determinantBasis_coe]
  simp [basisVector, zero_pow (Nat.ne_of_gt hd)]

/-- The next-layer submodule, using actual positive-depth determinant polynomials. -/
def positiveSpan (c h : ℕ) (hc : h + 1 ≤ c) : Submodule ℤ (monomialSpace c h) :=
  Submodule.span ℤ (Set.range (fun d : {d : DeterminantIndex c h // 0 < d.1.val} =>
    determinantBasis c h hc d.val))

theorem depth_zero_index (c h : ℕ) (d : DeterminantIndex c h) (hd : d.1.val = 0) :
    ∃ i : Fin (c + h), d = zeroIndex c h i := by
  rcases d with ⟨⟨j, hj⟩, ⟨i, hi⟩⟩
  dsimp at hd
  subst j
  exact ⟨⟨i, by simpa using hi⟩, rfl⟩

theorem zeroIndex_injective (c h : ℕ) : Function.Injective (zeroIndex c h) := by
  intro i k hik
  exact Fin.ext (congrArg (fun d => d.2.val) hik)

/-- The zero-depth basis coordinate is exactly an actual specialized coefficient. -/
theorem quotientMap_coefficient (c h : ℕ) (hc : h + 1 ≤ c)
    (p : monomialSpace c h) (i : Fin (c + h)) :
    (quotientMap c h p : Binary).coeff (binaryExponent (c + h) i) =
      (determinantBasis c h hc).repr p (zeroIndex c h i) := by
  have hl : (MvPolynomial.lcoeff ℤ (binaryExponent (c + h) i)).comp
      ((binarySpace (c + h)).subtype.comp (quotientMap c h)) =
      (determinantBasis c h hc).coord (zeroIndex c h i) := by
    apply (determinantBasis c h hc).ext
    intro d
    by_cases hd : d.1.val = 0
    · obtain ⟨k, rfl⟩ := depth_zero_index c h d hd
      simp only [LinearMap.comp_apply, Submodule.subtype_apply, quotientMap_basis_zero,
        Module.Basis.coord_apply, Module.Basis.repr_self]
      change (binaryMonomial (c + h) k).coeff (binaryExponent (c + h) i) = _
      rw [binaryMonomial_coeff]
      simp [Finsupp.single_apply, (zeroIndex_injective c h).eq_iff, eq_comm]
    · have hpos : 0 < d.1.val := by omega
      simp only [LinearMap.comp_apply, quotientMap_basis_positive c h hc d hpos,
        map_zero, Module.Basis.coord_apply, Module.Basis.repr_self]
      have hne : d ≠ zeroIndex c h i := by
        intro he
        exact hd (congrArg (fun d => d.1.val) he)
      simp [hne]
  exact congrArg (fun f => f p) hl

theorem quotientMap_surjective (c h : ℕ) (hc : h + 1 ≤ c) :
    Function.Surjective (quotientMap c h) := by
  intro p
  obtain ⟨v, hv⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp p.property
  refine ⟨∑ i, v i • determinantBasis c h hc (zeroIndex c h i), ?_⟩
  simp only [map_sum, map_smul, quotientMap_basis_zero]
  apply Subtype.ext
  simpa only [Submodule.coe_sum, Submodule.coe_smul, binaryVector] using hv

theorem quotientMap_kernel (c h : ℕ) (hc : h + 1 ≤ c) :
    (quotientMap c h).ker = positiveSpan c h hc := by
  apply le_antisymm
  · intro p hp
    rw [← (determinantBasis c h hc).sum_repr p]
    apply Submodule.sum_mem
    intro d hd
    by_cases hpos : 0 < d.1.val
    · exact (positiveSpan c h hc).smul_mem _
        (Submodule.subset_span ⟨⟨d, hpos⟩, rfl⟩)
    · obtain ⟨i, rfl⟩ := depth_zero_index c h d (by omega)
      have hz : (determinantBasis c h hc).repr p (zeroIndex c h i) = 0 := by
        rw [← quotientMap_coefficient]
        have hzero : quotientMap c h p = 0 := hp
        rw [hzero]
        rfl
      rw [hz, zero_smul]
      exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨d, hd⟩, rfl⟩
    exact quotientMap_basis_positive c h hc d hd

/-- The genuine finite quotient by the positive determinant layers is the
module of actual binary forms of dimension `c+h`. -/
def finiteQuotientEquiv (c h : ℕ) (hc : h + 1 ≤ c) :
    ((monomialSpace c h) ⧸ positiveSpan c h hc) ≃ₗ[ℤ] binarySpace (c + h) :=
  (Submodule.quotEquivOfEq _ _ (quotientMap_kernel c h hc).symm).trans
    ((quotientMap c h).quotKerEquivOfSurjective (quotientMap_surjective c h hc))

/-- Multiplication by the actual determinant power on the reduced finite space. -/
def layerLift (c h j : ℕ) : monomialSpace (c - j) (h - j) →ₗ[ℤ] Poly :=
  (LinearMap.mulLeft ℤ (delta ^ j)).domRestrict _

/-- The terminal layer is zero; the other layers have precisely the manuscript degrees. -/
def finiteLayer (c h j : ℕ) : Submodule ℤ Poly :=
  if j ≤ h then (layerLift c h j).range else ⊥

def higherSpan (c h j : ℕ) : Submodule ℤ Poly :=
  Submodule.span ℤ {x | ∃ k i : ℕ, j ≤ k ∧ k ≤ h ∧ k < c ∧
    i < c + h - 2 * k ∧ basisVector c h k i = x}

theorem determinant_shift (c h j k i : ℕ) :
    delta ^ j * basisVector (c - j) (h - j) k i = basisVector c h (j + k) i := by
  simp only [basisVector, Nat.sub_sub, pow_add]
  ring

theorem layerLift_range (c h j : ℕ) :
    (layerLift c h j).range =
      (monomialSpace (c - j) (h - j)).map (LinearMap.mulLeft ℤ (delta ^ j)) := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨p, p.property, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨⟨p, hp⟩, rfl⟩

/-- The finite determinant layer is exactly the span of the adapted basis tail. -/
theorem finiteLayer_eq_higherSpan (c h j : ℕ) (hc : h + 1 ≤ c) :
    finiteLayer c h j = higherSpan c h j := by
  by_cases hj : j ≤ h
  · have hc' : (h - j) + 1 ≤ c - j := by omega
    rw [finiteLayer, ite_eq_left hj, layerLift_range,
      ← determinantSpan_eq_monomialSpace (c - j) (h - j) hc']
    unfold determinantSpan higherSpan
    rw [Submodule.map_span]
    congr 1
    ext x
    constructor
    · rintro ⟨p, ⟨k, i, hkh, hkc, hki, rfl⟩, rfl⟩
      refine ⟨j + k, i, by omega, by omega, by omega, ?_, ?_⟩
      · omega
      · exact (determinant_shift c h j k i).symm
    · rintro ⟨k, i, hjk, hkh, hkc, hki, rfl⟩
      refine ⟨basisVector (c - j) (h - j) (k - j) i,
        ⟨k - j, i, by omega, by omega, by omega, rfl⟩, ?_⟩
      change delta ^ j * basisVector (c - j) (h - j) (k - j) i = _
      rw [determinant_shift, Nat.add_sub_of_le hjk]
  · rw [finiteLayer, ite_eq_right hj]
    unfold higherSpan
    have he : {x : Poly | ∃ k i : ℕ, j ≤ k ∧ k ≤ h ∧ k < c ∧
        i < c + h - 2 * k ∧ basisVector c h k i = x} = ∅ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨k, i, hjk, hkh, _⟩
      omega
    rw [he, Submodule.span_empty]

theorem positiveSpan_ambient (c h : ℕ) (hc : h + 1 ≤ c) :
    (positiveSpan c h hc).map (monomialSpace c h).subtype = finiteLayer c h 1 := by
  rw [finiteLayer_eq_higherSpan c h 1 hc]
  unfold positiveSpan higherSpan
  rw [Submodule.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨p, ⟨⟨d, hd⟩, rfl⟩, rfl⟩
    exact ⟨d.1.val, d.2.val, hd, by have := d.1.isLt; omega,
      by have := d.1.isLt; omega, d.2.isLt, (determinantBasis_coe c h hc d).symm⟩
  · rintro ⟨k, i, hk, hkh, hkc, hki, rfl⟩
    let d : DeterminantIndex c h := ⟨⟨k, by omega⟩, ⟨i, hki⟩⟩
    refine ⟨determinantBasis c h hc d, ⟨⟨d, hk⟩, rfl⟩, ?_⟩
    exact determinantBasis_coe c h hc d

theorem delta_ne_zero : delta ≠ 0 := by
  let ev : Poly →+* ℤ := MvPolynomial.eval (fun i => if i = 0 ∨ i = 3 then 1 else 0)
  have he : ev delta = 1 := by simp [ev, delta, u, v, up, vp]
  intro hz
  rw [hz, map_zero] at he
  exact Int.zero_ne_one he

theorem layerLift_injective (c h j : ℕ) : Function.Injective (layerLift c h j) := by
  intro p q hpq
  apply Subtype.ext
  exact mul_left_cancel₀ (pow_ne_zero j delta_ne_zero) hpq

/-- Dividing a finite determinant layer by its determinant power is well defined. -/
def layerEquiv (c h j : ℕ) (hj : j ≤ h) :
    monomialSpace (c - j) (h - j) ≃ₗ[ℤ] finiteLayer c h j :=
  (LinearEquiv.ofInjective (layerLift c h j) (layerLift_injective c h j)).trans
    (LinearEquiv.ofEq _ _ (by simp only [finiteLayer, ite_eq_left hj]))

@[simp] theorem layerEquiv_coe (c h j : ℕ) (hj : j ≤ h)
    (p : monomialSpace (c - j) (h - j)) :
    (layerEquiv c h j hj p : Poly) = delta ^ j * (p : Poly) := rfl

theorem shifted_positiveSpan (c h j : ℕ) (hc : h + 1 ≤ c) (hj : j ≤ h) :
    (positiveSpan (c - j) (h - j) (by omega)).map (layerLift c h j) =
      finiteLayer c h (j + 1) := by
  rw [finiteLayer_eq_higherSpan c h (j + 1) hc]
  unfold positiveSpan higherSpan
  rw [Submodule.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨p, ⟨⟨d, hd⟩, rfl⟩, rfl⟩
    refine ⟨j + d.1.val, d.2.val, by omega, ?_, ?_, ?_, ?_⟩
    · have := d.1.isLt; omega
    · have := d.1.isLt; omega
    · have := d.1.isLt; have := d.2.isLt; omega
    · change basisVector c h (j + d.1.val) d.2.val =
        delta ^ j * (determinantBasis (c - j) (h - j) (by omega) d : Poly)
      rw [determinantBasis_coe, determinant_shift]
  · rintro ⟨k, i, hjk, hkh, hkc, hki, rfl⟩
    let d : DeterminantIndex (c - j) (h - j) :=
      ⟨⟨k - j, by omega⟩, ⟨i, by change i < (c - j) + (h - j) - 2 * (k - j); omega⟩⟩
    have hd : 0 < d.1.val := by dsimp [d]; omega
    refine ⟨determinantBasis (c - j) (h - j) (by omega) d, ⟨⟨d, hd⟩, rfl⟩, ?_⟩
    change delta ^ j * (determinantBasis (c - j) (h - j) (by omega) d : Poly) = _
    rw [determinantBasis_coe, determinant_shift]
    change basisVector c h (j + (k - j)) i = _
    rw [Nat.add_sub_of_le (by omega : j ≤ k)]

/-- The next actual finite layer, regarded as a submodule of the current one. -/
def nextInLayer (c h j : ℕ) : Submodule ℤ (finiteLayer c h j) :=
  (finiteLayer c h (j + 1)).comap (finiteLayer c h j).subtype

theorem nextInLayer_membership (c h j : ℕ) (hc : h + 1 ≤ c) (hj : j ≤ h)
    (p : finiteLayer c h j) :
    p ∈ nextInLayer c h j ↔
      (layerEquiv c h j hj).symm p ∈ positiveSpan (c - j) (h - j) (by omega) := by
  change (p : Poly) ∈ finiteLayer c h (j + 1) ↔ _
  rw [← shifted_positiveSpan c h j hc hj]
  constructor
  · rintro ⟨q, hq, heq⟩
    have hqp : layerEquiv c h j hj q = p := Subtype.ext heq
    rw [← hqp]
    simpa using hq
  · intro hp
    refine ⟨(layerEquiv c h j hj).symm p, hp, ?_⟩
    change (layerEquiv c h j hj ((layerEquiv c h j hj).symm p) : Poly) = p
    rw [LinearEquiv.apply_symm_apply]

/-- Divide by `Δ^j`, then perform actual diagonal substitution. -/
def layerQuotientMap (c h j : ℕ) (hj : j ≤ h) :
    finiteLayer c h j →ₗ[ℤ] binarySpace ((c - j) + (h - j)) :=
  (quotientMap (c - j) (h - j)).comp (layerEquiv c h j hj).symm.toLinearMap

theorem layerQuotientMap_kernel (c h j : ℕ) (hc : h + 1 ≤ c) (hj : j ≤ h) :
    (layerQuotientMap c h j hj).ker = nextInLayer c h j := by
  ext p
  change quotientMap (c - j) (h - j) ((layerEquiv c h j hj).symm p) = 0 ↔ _
  rw [← LinearMap.mem_ker, quotientMap_kernel (c - j) (h - j) (by omega)]
  exact (nextInLayer_membership c h j hc hj p).symm

theorem layerQuotientMap_surjective (c h j : ℕ) (hc : h + 1 ≤ c) (hj : j ≤ h) :
    Function.Surjective (layerQuotientMap c h j hj) :=
  (quotientMap_surjective (c - j) (h - j) (by omega)).comp
    (layerEquiv c h j hj).symm.surjective

/-- The actual finite `j`-th filtration quotient is the indicated binary-form module. -/
def filtrationQuotientEquiv (c h j : ℕ) (hc : h + 1 ≤ c) (hj : j ≤ h) :
    ((finiteLayer c h j) ⧸ nextInLayer c h j) ≃ₗ[ℤ] binarySpace (c + h - 2 * j) :=
  ((Submodule.quotEquivOfEq _ _ (layerQuotientMap_kernel c h j hc hj).symm).trans
    ((layerQuotientMap c h j hj).quotKerEquivOfSurjective
      (layerQuotientMap_surjective c h j hc hj))).trans
    (LinearEquiv.ofEq _ _ (by congr 1; omega))

private theorem first_monomial_product (a b p q s t : ℕ) :
    (u ^ s * v ^ t) * monomial a b p q = monomial (a + s) (b + t) p q := by
  unfold monomial
  simp only [pow_add]
  ring

theorem first_monomial_mem (c h s t : ℕ) {p : Poly} (hp : p ∈ monomialSpace c h) :
    (u ^ s * v ^ t) * p ∈ monomialSpace (c + s + t) h := by
  unfold monomialSpace at hp
  let f := LinearMap.mulLeft ℤ (u ^ s * v ^ t)
  change f p ∈ monomialSpace (c + s + t) h
  induction hp using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, b, p, q, hc, hh, rfl⟩ := hx
    change (u ^ s * v ^ t) * monomial a b p q ∈ _
    rw [first_monomial_product]
    exact Submodule.subset_span ⟨a + s, b + t, p, q, by omega, hh, rfl⟩
  | zero => simp
  | add x y hx hy ihx ihy =>
    rw [map_add]
    exact Submodule.add_mem _ ihx ihy
  | smul a x hx ih =>
    rw [map_smul]
    exact Submodule.smul_mem _ a ih

def reducedMul (c h j s t : ℕ) (hjc : j < c) :
    monomialSpace (c - j) (h - j) →ₗ[ℤ] monomialSpace (c + s + t - j) (h - j) :=
  ((LinearMap.mulLeft ℤ (u ^ s * v ^ t)).domRestrict _).codRestrict _ (by
    intro p
    change (u ^ s * v ^ t) * (p : Poly) ∈ _
    have hm := first_monomial_mem (c - j) (h - j) s t p.property
    have he : c - j + s + t = c + s + t - j := by omega
    simpa only [he] using hm)

/-- Multiplication on the actual finite layers, defined through the proved division maps. -/
def layerMul (c h j s t : ℕ) (hc : h + 1 ≤ c) (hj : j ≤ h) :
    finiteLayer c h j →ₗ[ℤ] finiteLayer (c + s + t) h j :=
  (layerEquiv (c + s + t) h j hj).toLinearMap.comp
    ((reducedMul c h j s t (by omega)).comp (layerEquiv c h j hj).symm.toLinearMap)

theorem divide_layer_coe (c h j : ℕ) (hj : j ≤ h) (p : finiteLayer c h j) :
    delta ^ j * ((layerEquiv c h j hj).symm p : Poly) = (p : Poly) := by
  change (layerEquiv c h j hj ((layerEquiv c h j hj).symm p) : Poly) = p
  rw [LinearEquiv.apply_symm_apply]

/-- The finite-layer map really multiplies the ambient polynomial by `u^s v^t`. -/
theorem layerMul_coe (c h j s t : ℕ) (hc : h + 1 ≤ c) (hj : j ≤ h)
    (p : finiteLayer c h j) :
    (layerMul c h j s t hc hj p : Poly) = (u ^ s * v ^ t) * (p : Poly) := by
  change delta ^ j * ((u ^ s * v ^ t) * ((layerEquiv c h j hj).symm p : Poly)) = _
  calc
    _ = (u ^ s * v ^ t) *
      (delta ^ j * ((layerEquiv c h j hj).symm p : Poly)) := by ring
    _ = _ := by rw [divide_layer_coe]

/-- Multiplication on divided finite representatives induces polynomial multiplication. -/
theorem layerMul_diagonal (c h j s t : ℕ) (hc : h + 1 ≤ c) (hj : j ≤ h)
    (p : finiteLayer c h j) :
    (layerQuotientMap (c + s + t) h j hj (layerMul c h j s t hc hj p) : Binary) =
      diagonal (u ^ s * v ^ t) * (layerQuotientMap c h j hj p : Binary) := by
  simp only [layerMul, layerQuotientMap, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  change diagonal ((u ^ s * v ^ t) * ((layerEquiv c h j hj).symm p : Poly)) = _
  exact map_mul diagonal _ _

/-- The actual depth-`j` basis polynomial as an element of its finite layer. -/
def layerVector (c h j : ℕ) (hc : h + 1 ≤ c) (hj : j ≤ h)
    (i : Fin ((c - j) + (h - j))) : finiteLayer c h j :=
  layerEquiv c h j hj
    (determinantBasis (c - j) (h - j) (by omega) (zeroIndex (c - j) (h - j) i))

@[simp] theorem layerVector_coe (c h j : ℕ) (hc : h + 1 ≤ c) (hj : j ≤ h)
    (i : Fin ((c - j) + (h - j))) :
    (layerVector c h j hc hj i : Poly) = basisVector c h j i.val := by
  rw [layerVector, layerEquiv_coe, determinantBasis_coe]
  simp [basisVector, zeroIndex]

theorem layerQuotientMap_vector (c h j : ℕ) (hc : h + 1 ≤ c) (hj : j ≤ h)
    (i : Fin ((c - j) + (h - j))) :
    layerQuotientMap c h j hj (layerVector c h j hc hj i) =
      binaryVector ((c - j) + (h - j)) i := by
  simp [layerQuotientMap, layerVector, quotientMap_basis_zero]

def outputIndex (c h j s t : ℕ) (hc : h + 1 ≤ c) (hj : j ≤ h)
    (i : Fin ((c - j) + (h - j))) : Fin ((c + s + t - j) + (h - j)) :=
  ⟨i.val + t, by have := i.isLt; omega⟩

/-- On every finite quotient, the monomial index shifts by the multiplier's `v` exponent. -/
theorem finite_convolution (c h j s t : ℕ) (hc : h + 1 ≤ c) (hj : j ≤ h)
    (i : Fin ((c - j) + (h - j))) :
    layerQuotientMap (c + s + t) h j hj
      (layerMul c h j s t hc hj (layerVector c h j hc hj i)) =
      binaryVector ((c + s + t - j) + (h - j)) (outputIndex c h j s t hc hj i) := by
  apply Subtype.ext
  rw [layerMul_diagonal, layerQuotientMap_vector]
  change diagonal (u ^ s * v ^ t) * binaryMonomial ((c - j) + (h - j)) i = _
  simp only [map_mul, map_pow, diagonal_u, diagonal_v, binaryVector, binaryMonomial, outputIndex]
  have he : (c + s + t - j + (h - j)) - 1 - (i.val + t) =
      s + ((c - j + (h - j)) - 1 - i.val) := by have := i.isLt; omega
  rw [he]
  simp only [pow_add]
  ring

/-- The convolution remainder belongs to the actual next finite bidegree layer. -/
theorem finite_convolution_remainder (c h j s t : ℕ) (hc : h + 1 ≤ c) (hj : j ≤ h)
    (i : Fin ((c - j) + (h - j))) :
    (u ^ s * v ^ t) * basisVector c h j i.val -
      basisVector (c + s + t) h j (i.val + t) ∈ finiteLayer (c + s + t) h (j + 1) := by
  have hout : h + 1 ≤ c + s + t := by omega
  let q := layerMul c h j s t hc hj (layerVector c h j hc hj i) -
    layerVector (c + s + t) h j hout hj (outputIndex c h j s t hc hj i)
  have hq : q ∈ (layerQuotientMap (c + s + t) h j hj).ker := by
    change layerQuotientMap (c + s + t) h j hj q = 0
    simp only [q, map_sub, finite_convolution, layerQuotientMap_vector, sub_self]
  rw [layerQuotientMap_kernel (c + s + t) h j hout hj] at hq
  change (q : Poly) ∈ finiteLayer (c + s + t) h (j + 1) at hq
  simpa only [q, Submodule.coe_sub, layerMul_coe, layerVector_coe, outputIndex] using hq

theorem layerMul_preserves_next (c h j s t : ℕ) (hc : h + 1 ≤ c) (hj : j ≤ h)
    (p : finiteLayer c h j) (hp : p ∈ nextInLayer c h j) :
    layerMul c h j s t hc hj p ∈ nextInLayer (c + s + t) h j := by
  rw [← layerQuotientMap_kernel (c + s + t) h j (by omega) hj]
  change layerQuotientMap (c + s + t) h j hj (layerMul c h j s t hc hj p) = 0
  apply Subtype.ext
  rw [layerMul_diagonal]
  have hz : layerQuotientMap c h j hj p = 0 := by
    rw [← LinearMap.mem_ker, layerQuotientMap_kernel c h j hc hj]
    exact hp
  rw [hz]
  simp

abbrev TailIndex (c h j : ℕ) := {d : DeterminantIndex c h // j ≤ d.1.val}

def tailVector (c h j : ℕ) (d : TailIndex c h j) : Poly := indexedBasisVector c h d.val

theorem higherSpan_eq_tail (c h j : ℕ) (hc : h + 1 ≤ c) :
    higherSpan c h j = Submodule.span ℤ (Set.range (tailVector c h j)) := by
  unfold higherSpan
  congr 1
  ext x
  constructor
  · rintro ⟨k, i, hjk, hkh, hkc, hki, rfl⟩
    let d : DeterminantIndex c h := ⟨⟨k, by omega⟩, ⟨i, hki⟩⟩
    exact ⟨⟨d, hjk⟩, rfl⟩
  · rintro ⟨⟨d, hd⟩, rfl⟩
    exact ⟨d.1.val, d.2.val, hd, by have := d.1.isLt; omega,
      by have := d.1.isLt; omega, d.2.isLt, rfl⟩

theorem tailVector_linearIndependent (c h j : ℕ) (hc : h + 1 ≤ c) :
    LinearIndependent ℤ (tailVector c h j) :=
  (determinant_linearIndependent c h hc).comp Subtype.val Subtype.val_injective

/-- All determinant vectors of depth at least `j` form a basis of the actual finite layer. -/
def adaptedBasis (c h j : ℕ) (hc : h + 1 ≤ c) :
    Module.Basis (TailIndex c h j) ℤ (finiteLayer c h j) :=
  (Module.Basis.span (tailVector_linearIndependent c h j hc)).map
    (LinearEquiv.ofEq _ _ (by
      rw [← higherSpan_eq_tail c h j hc, ← finiteLayer_eq_higherSpan c h j hc]))

@[simp] theorem adaptedBasis_coe (c h j : ℕ) (hc : h + 1 ≤ c) (d : TailIndex c h j) :
    (adaptedBasis c h j hc d : Poly) = basisVector c h d.val.1.val d.val.2.val := by
  simp [adaptedBasis, tailVector, indexedBasisVector]

theorem terminal_layer (c h : ℕ) : finiteLayer c h (h + 1) = ⊥ := by
  simp [finiteLayer]

theorem finiteLayer_antitone (c h j k : ℕ) (hc : h + 1 ≤ c) (hjk : j ≤ k) :
    finiteLayer c h k ≤ finiteLayer c h j := by
  rw [finiteLayer_eq_higherSpan c h k hc, finiteLayer_eq_higherSpan c h j hc]
  apply Submodule.span_le.mpr
  rintro x ⟨l, i, hkl, hlh, hlc, hli, rfl⟩
  exact Submodule.subset_span ⟨l, i, le_trans hjk hkl, hlh, hlc, hli, rfl⟩

theorem nextInLayer_ambient (c h j : ℕ) (hc : h + 1 ≤ c) :
    (nextInLayer c h j).map (finiteLayer c h j).subtype = finiteLayer c h (j + 1) := by
  unfold nextInLayer
  rw [Submodule.map_comap_subtype]
  exact inf_eq_right.mpr (finiteLayer_antitone c h j (j + 1) hc (by omega))

theorem finiteLayer_zero (c h : ℕ) (hc : h + 1 ≤ c) :
    finiteLayer c h 0 = monomialSpace c h := by
  rw [finiteLayer_eq_higherSpan c h 0 hc, ← determinantSpan_eq_monomialSpace c h hc]
  simp [higherSpan, determinantSpan]

theorem filtrationQuotientEquiv_mk (c h j : ℕ) (hc : h + 1 ≤ c) (hj : j ≤ h)
    (p : finiteLayer c h j) :
    (filtrationQuotientEquiv c h j hc hj (Submodule.Quotient.mk p) : Binary) =
      diagonal ((layerEquiv c h j hj).symm p : Poly) := by
  rfl

end
end MatrixDimensionAudit.DeterminantQuotientBridge
