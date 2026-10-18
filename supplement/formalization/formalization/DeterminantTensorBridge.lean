import formalization.DeterminantQuotientBridge
import formalization.TensorRankBridge

/-! Coefficient tensors in the integral determinant bases. -/
namespace MatrixDimensionAudit.DeterminantTensorBridge
open DeterminantFiltrationBridge DeterminantBasisBridge DeterminantQuotientBridge
open OAI.MatrixMultiplication.Foundation
open scoped Matrix BigOperators
noncomputable section

/-- Extend a determinant-basis coordinate to the ambient polynomial ring using the
proved integer inverse of the monomial coefficient matrix. -/
def coordinate (c h : ℕ) (hc : h + 1 ≤ c) (d : DeterminantIndex c h) : Poly →ₗ[ℤ] ℤ :=
  ∑ m, expansionMatrix c h hc d m • MvPolynomial.lcoeff ℤ (indexExponent c h m)

theorem coordinate_apply (c h : ℕ) (hc : h + 1 ≤ c) (d : DeterminantIndex c h) (p : Poly) :
    coordinate c h hc d p =
      ∑ m, expansionMatrix c h hc d m * p.coeff (indexExponent c h m) := by
  simp [coordinate, LinearMap.sum_apply]

theorem coordinate_basis (c h : ℕ) (hc : h + 1 ≤ c) (d e : DeterminantIndex c h) :
    coordinate c h hc d (basisVector c h e.1.val e.2.val) = if d = e then 1 else 0 := by
  have he := congrArg (fun M => M d e) (expansionMatrix_mul_coordinateMatrix c h hc)
  simpa [coordinate_apply, Matrix.mul_apply, coordinateMatrix, indexedBasisVector,
    Matrix.one_apply] using he

theorem coordinate_standard (c h : ℕ) (hc : h + 1 ≤ c)
    (d : DeterminantIndex c h) (m : MonomialIndex c h) :
    coordinate c h hc d (standardMonomial c h m) = expansionMatrix c h hc d m := by
  simp [coordinate_apply, standardMonomial_coeff]

theorem coordinate_restrict (c h : ℕ) (hc : h + 1 ≤ c)
    (d : DeterminantIndex c h) (p : monomialSpace c h) :
    coordinate c h hc d (p : Poly) = (determinantBasis c h hc).repr p d := by
  have he : (coordinate c h hc d).comp (monomialSpace c h).subtype =
      (determinantBasis c h hc).coord d := by
    apply (determinantBasis c h hc).ext
    intro e
    simp [determinantBasis_coe, coordinate_basis, Module.Basis.coord_apply,
      Finsupp.single_apply, eq_comm]
  exact congrArg (fun f => f p) he

/-- A finite filtration tail has zero coordinates at every lower depth. -/
theorem coordinate_below_layer (c h j : ℕ) (hc : h + 1 ≤ c)
    (d : DeterminantIndex c h) (hd : d.1.val < j) {p : Poly} (hp : p ∈ finiteLayer c h j) :
    coordinate c h hc d p = 0 := by
  let q : finiteLayer c h j := ⟨p, hp⟩
  have hsum := congrArg (fun x : finiteLayer c h j => (x : Poly))
    ((adaptedBasis c h j hc).sum_repr q)
  simp only [Submodule.coe_sum, Submodule.coe_smul] at hsum
  change (∑ x, ((adaptedBasis c h j hc).repr q) x • (adaptedBasis c h j hc x : Poly)) = p at hsum
  rw [← hsum, map_sum]
  apply Finset.sum_eq_zero
  intro e he
  rw [map_smul, adaptedBasis_coe, coordinate_basis]
  have hne : d ≠ e.val := by
    intro heq
    have := e.property
    rw [← heq] at this
    omega
  simp [hne]

theorem basis_mem_layer (c h : ℕ) (hc : h + 1 ≤ c) (d : DeterminantIndex c h) :
    basisVector c h d.1.val d.2.val ∈ finiteLayer c h d.1.val := by
  rw [finiteLayer_eq_higherSpan c h d.1.val hc]
  exact Submodule.subset_span ⟨d.1.val, d.2.val, le_refl _,
    by have := d.1.isLt; omega, by have := d.1.isLt; omega, d.2.isLt, rfl⟩

theorem product_mem_layer (c h s t : ℕ) (hc : h + 1 ≤ c) (d : DeterminantIndex c h) :
    (u ^ s * v ^ t) * basisVector c h d.1.val d.2.val ∈
      finiteLayer (c + s + t) h d.1.val := by
  let p : finiteLayer c h d.1.val := ⟨_, basis_mem_layer c h hc d⟩
  have hm := (layerMul c h d.1.val s t hc (by have := d.1.isLt; omega) p).property
  simpa only [layerMul_coe] using hm

theorem integer_triangular (c h s t : ℕ) (hc : h + 1 ≤ c)
    (d : DeterminantIndex c h) (e : DeterminantIndex (c + s + t) h)
    (he : e.1.val < d.1.val) :
    coordinate (c + s + t) h (by omega) e
      ((u ^ s * v ^ t) * basisVector c h d.1.val d.2.val) = 0 :=
  coordinate_below_layer _ _ _ (by omega) e he (product_mem_layer c h s t hc d)

theorem determinantIndex_ext {c h : ℕ} {d e : DeterminantIndex c h}
    (hj : d.1.val = e.1.val) (hi : d.2.val = e.2.val) : d = e := by
  rcases d with ⟨⟨j, hjd⟩, ⟨i, hid⟩⟩
  rcases e with ⟨⟨k, hke⟩, ⟨l, hle⟩⟩
  dsimp at hj hi
  subst k
  subst l
  rfl

/-- The matching output quotient index, with all finite bounds checked. -/
def shiftedIndex (c h s t : ℕ) (hc : h + 1 ≤ c) (d : DeterminantIndex c h) :
    DeterminantIndex (c + s + t) h :=
  ⟨d.1, ⟨d.2.val + t, by have := d.1.isLt; have := d.2.isLt; omega⟩⟩

theorem integer_diagonal (c h s t : ℕ) (hc : h + 1 ≤ c)
    (d : DeterminantIndex c h) (e : DeterminantIndex (c + s + t) h)
    (he : e.1.val = d.1.val) :
    coordinate (c + s + t) h (by omega) e
      ((u ^ s * v ^ t) * basisVector c h d.1.val d.2.val) =
      if e.2.val = d.2.val + t then 1 else 0 := by
  let i : Fin ((c - d.1.val) + (h - d.1.val)) :=
    ⟨d.2.val, by have := d.1.isLt; have := d.2.isLt; omega⟩
  have hrem := finite_convolution_remainder c h d.1.val s t hc
    (by have := d.1.isLt; omega) i
  have hz := coordinate_below_layer (c + s + t) h (d.1.val + 1) (by omega) e
    (by omega) hrem
  rw [map_sub] at hz
  have hb := coordinate_basis (c + s + t) h (by omega) e (shiftedIndex c h s t hc d)
  have hcoeff : coordinate (c + s + t) h (by omega) e
      ((u ^ s * v ^ t) * basisVector c h d.1.val d.2.val) =
      if e = shiftedIndex c h s t hc d then 1 else 0 := by
    have hx := sub_eq_zero.mp hz
    exact hx.trans hb
  rw [hcoeff]
  congr 1
  apply propext
  constructor
  · intro hx
    exact congrArg (fun e => e.2.val) hx
  · intro hx
    exact determinantIndex_ext he hx


/-- The unchanged primed coordinate passes through multiplication. -/
def standardShift (r c h : ℕ) (a : Fin r) (m : MonomialIndex c h) :
    MonomialIndex (r + c - 1) h :=
  ⟨⟨m.1.val + a.val, by have := a.isLt; have := m.1.isLt; omega⟩, m.2⟩

def multiplier (r : ℕ) (a : Fin r) : Poly := u ^ (r - 1 - a.val) * v ^ a.val

theorem multiplier_standard (r c h : ℕ) (a : Fin r) (m : MonomialIndex c h) :
    multiplier r a * standardMonomial c h m =
      standardMonomial (r + c - 1) h (standardShift r c h a m) := by
  have he : r + c - 1 - 1 - (m.1.val + a.val) =
      (r - 1 - a.val) + (c - 1 - m.1.val) := by
    have := a.isLt; have := m.1.isLt; omega
  unfold multiplier standardMonomial monomial standardShift
  simp only
  rw [he]
  simp only [pow_add]
  ring

def source (F : Type) [CommRing F] (r c h : ℕ) :
    Tensor F (Fin r) (MonomialIndex c h) (MonomialIndex (r + c - 1) h) :=
  fun a m n => if a.val + m.1.val = n.1.val ∧ m.2 = n.2 then 1 else 0

def primedIdentity (F : Type) [CommRing F] (h : ℕ) :
    Tensor F Unit (Fin (h + 1)) (Fin (h + 1)) :=
  fun _ p q => if p = q then 1 else 0

/-- This is exactly convolution times the pass-through dot product. -/
theorem source_product (F : Type) [Field F] (r c h : ℕ) :
    source F r c h = Tensor.pullback (fun a => (a, ())) id id
      (Tensor.product (TensorRankBridge.convolution F r c) (primedIdentity F h)) := by
  funext a m n
  by_cases hs : a.val + m.1.val = n.1.val <;> by_cases hp : m.2 = n.2 <;>
    simp [source, Tensor.pullback, Tensor.product, TensorRankBridge.convolution,
      primedIdentity, hs, hp]

theorem source_shift (F : Type) [CommRing F] (r c h : ℕ)
    (a : Fin r) (m : MonomialIndex c h) (n : MonomialIndex (r + c - 1) h) :
    source F r c h a m n = if n = standardShift r c h a m then 1 else 0 := by
  have he : (a.val + m.1.val = n.1.val ∧ m.2 = n.2) ↔
      n = standardShift r c h a m := by
    constructor
    · rintro ⟨hs, hp⟩
      apply Prod.ext
      · apply Fin.ext; dsimp [standardShift]; omega
      · exact hp.symm
    · intro hn
      subst n
      simp [standardShift, Nat.add_comm]
  simp only [source, he]

/-- Explicit input basis columns and inverse output coordinates. -/
def transformed (F : Type) [CommRing F] (r c h : ℕ)
    (_hc : h + 1 ≤ c) (ho : h + 1 ≤ r + c - 1) :
    Tensor F (Fin r) (DeterminantIndex c h) (DeterminantIndex (r + c - 1) h) :=
  Tensor.restrict
    (fun a' a => if a = a' then 1 else 0)
    (fun d m => (coordinateMatrix c h m d : F))
    (fun e n => (expansionMatrix (r + c - 1) h ho e n : F))
    (source F r c h)

theorem transformed_sum (F : Type) [CommRing F] (r c h : ℕ)
    (hc : h + 1 ≤ c) (ho : h + 1 ≤ r + c - 1)
    (a : Fin r) (d : DeterminantIndex c h) (e : DeterminantIndex (r + c - 1) h) :
    transformed F r c h hc ho a d e =
      ∑ m, (coordinateMatrix c h m d : F) *
        (expansionMatrix (r + c - 1) h ho e (standardShift r c h a m) : F) := by
  simp [transformed, Tensor.restrict, source_shift]

theorem transformed_integer_coordinate (r c h : ℕ)
    (hc : h + 1 ≤ c) (ho : h + 1 ≤ r + c - 1)
    (a : Fin r) (d : DeterminantIndex c h) (e : DeterminantIndex (r + c - 1) h) :
    transformed ℤ r c h hc ho a d e =
      coordinate (r + c - 1) h ho e
        (multiplier r a * basisVector c h d.1.val d.2.val) := by
  have hb := determinantVector_expansion c h hc d
  change (∑ m, coordinateMatrix c h m d • standardMonomial c h m) =
    basisVector c h d.1.val d.2.val at hb
  rw [transformed_sum, ← hb, Finset.mul_sum]
  simp only [mul_smul_comm, map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro m hm
  rw [multiplier_standard, coordinate_standard]
  simp

theorem transformed_cast (F : Type) [CommRing F] (r c h : ℕ)
    (hc : h + 1 ≤ c) (ho : h + 1 ≤ r + c - 1)
    (a : Fin r) (d : DeterminantIndex c h) (e : DeterminantIndex (r + c - 1) h) :
    transformed F r c h hc ho a d e = (transformed ℤ r c h hc ho a d e : F) := by
  simp [transformed_sum, Int.cast_sum, Int.cast_mul]

private theorem integer_triangular_dim (c h s t o : ℕ) (hc : h + 1 ≤ c)
    (ho : o = c + s + t) (d : DeterminantIndex c h) (e : DeterminantIndex o h)
    (he : e.1.val < d.1.val) :
    coordinate o h (by omega) e ((u ^ s * v ^ t) * basisVector c h d.1.val d.2.val) = 0 := by
  subst o
  exact integer_triangular c h s t hc d e he

private theorem integer_diagonal_dim (c h s t o : ℕ) (hc : h + 1 ≤ c)
    (ho : o = c + s + t) (d : DeterminantIndex c h) (e : DeterminantIndex o h)
    (he : e.1.val = d.1.val) :
    coordinate o h (by omega) e ((u ^ s * v ^ t) * basisVector c h d.1.val d.2.val) =
      if e.2.val = d.2.val + t then 1 else 0 := by
  subst o
  exact integer_diagonal c h s t hc d e he

/-- The actual coefficient tensor in the explicit input/output bases is block triangular. -/
theorem transformed_triangular (F : Type) [CommRing F] (r c h : ℕ)
    (hc : h + 1 ≤ c) (ho : h + 1 ≤ r + c - 1)
    (a : Fin r) (d : DeterminantIndex c h) (e : DeterminantIndex (r + c - 1) h)
    (he : e.1.val < d.1.val) : transformed F r c h hc ho a d e = 0 := by
  rw [transformed_cast, transformed_integer_coordinate]
  have hout : r + c - 1 = c + (r - 1 - a.val) + a.val := by have := a.isLt; omega
  have hz := integer_triangular_dim c h (r - 1 - a.val) a.val (r + c - 1) hc hout d e he
  change coordinate (r + c - 1) h ho e
    ((u ^ (r - 1 - a.val) * v ^ a.val) * basisVector c h d.1.val d.2.val) = 0 at hz
  rw [show coordinate (r + c - 1) h ho e
    (multiplier r a * basisVector c h d.1.val d.2.val) = 0 from hz]
  simp

/-- Each equal-depth block has exactly the ordinary convolution coefficients. -/
theorem transformed_diagonal (F : Type) [CommRing F] (r c h : ℕ)
    (hc : h + 1 ≤ c) (ho : h + 1 ≤ r + c - 1)
    (a : Fin r) (d : DeterminantIndex c h) (e : DeterminantIndex (r + c - 1) h)
    (he : e.1.val = d.1.val) :
    transformed F r c h hc ho a d e = if a.val + d.2.val = e.2.val then 1 else 0 := by
  rw [transformed_cast, transformed_integer_coordinate]
  have hout : r + c - 1 = c + (r - 1 - a.val) + a.val := by have := a.isLt; omega
  have hz := integer_diagonal_dim c h (r - 1 - a.val) a.val (r + c - 1) hc hout d e he
  change coordinate (r + c - 1) h ho e
    (multiplier r a * basisVector c h d.1.val d.2.val) = _ at hz
  rw [hz]
  by_cases hi : e.2.val = d.2.val + a.val
  · have hi' : a.val + d.2.val = e.2.val := by omega
    simp [hi, hi']
  · have hi' : ¬a.val + d.2.val = e.2.val := by omega
    simp [hi, hi']


/-- Both inverse identities survive scalar extension, in every commutative ring. -/
theorem basis_matrix_inverse_cast (F : Type) [CommRing F] (c h : ℕ) (hc : h + 1 ≤ c) :
    (coordinateMatrix c h).map (Int.castRingHom F) *
        (expansionMatrix c h hc).map (Int.castRingHom F) = 1 ∧
      (expansionMatrix c h hc).map (Int.castRingHom F) *
        (coordinateMatrix c h).map (Int.castRingHom F) = 1 := by
  constructor
  · have he := congrArg (fun M : Matrix (MonomialIndex c h) (MonomialIndex c h) ℤ =>
        M.map (Int.castRingHom F)) (coordinateMatrix_mul_expansionMatrix c h hc)
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at he
    exact he
  · have he := congrArg (fun M : Matrix (DeterminantIndex c h) (DeterminantIndex c h) ℤ =>
        M.map (Int.castRingHom F)) (expansionMatrix_mul_coordinateMatrix c h hc)
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at he
    exact he

/-- Histogram counts use the same finite depth alphabet on both legs. -/
def histogram {n h : ℕ} (w : Fin n → Fin (h + 1)) (j : Fin (h + 1)) : ℕ :=
  ∑ i, if w i = j then 1 else 0

theorem histogram_card {n h : ℕ} (w : Fin n → Fin (h + 1)) (j : Fin (h + 1)) :
    histogram w j = (Finset.univ.filter (fun i => w i = j)).card := by
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rfl

theorem weighted_histogram {n h : ℕ} (w : Fin n → Fin (h + 1)) :
    ∑ i, (w i).val = ∑ j, histogram w j * j.val := by
  calc
    _ = ∑ i, ∑ j : Fin (h + 1), if w i = j then j.val else 0 := by simp
    _ = ∑ j : Fin (h + 1), ∑ i, if w i = j then j.val else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [histogram, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      split_ifs <;> simp

/-- Coordinatewise monotonicity plus equal histograms forces identical depth words. -/
theorem monotone_words_equal {n h : ℕ} (w v : Fin n → Fin (h + 1))
    (hle : ∀ i, (w i).val ≤ (v i).val) (hhist : histogram w = histogram v) : w = v := by
  have hsum : ∑ i, (w i).val = ∑ i, (v i).val := by
    rw [weighted_histogram w, weighted_histogram v, hhist]
  have he := (Finset.sum_eq_sum_iff_of_le (fun i _ => hle i)).mp hsum
  funext i
  exact Fin.ext (he i (Finset.mem_univ i))

def inputWord {c h n : ℕ} (y : Fin n → DeterminantIndex c h) : Fin n → Fin (h + 1) :=
  fun i => (y i).1

def keptInput (c h n : ℕ) (counts : Fin (h + 1) → ℕ) :=
  {y : Fin n → DeterminantIndex c h // histogram (inputWord y) = counts}

def keptOutput (r c h n : ℕ) (counts : Fin (h + 1) → ℕ) :=
  {z : Fin n → DeterminantIndex (r + c - 1) h // histogram (inputWord z) = counts}

def restricted (F : Type) [CommRing F] (r c h n : ℕ)
    (hc : h + 1 ≤ c) (ho : h + 1 ≤ r + c - 1) (counts : Fin (h + 1) → ℕ) :
    Tensor F (Fin n → Fin r) (keptInput c h n counts) (keptOutput r c h n counts) :=
  Tensor.pullback id Subtype.val Subtype.val
    (Tensor.power (transformed F r c h hc ho) n)

theorem supported_words_equal (F : Type) [CommRing F] (r c h n : ℕ)
    (hc : h + 1 ≤ c) (ho : h + 1 ≤ r + c - 1)
    (x : Fin n → Fin r) (y : Fin n → DeterminantIndex c h)
    (z : Fin n → DeterminantIndex (r + c - 1) h)
    (hs : ∀ i, transformed F r c h hc ho (x i) (y i) (z i) ≠ 0)
    (hhist : histogram (inputWord y) = histogram (inputWord z)) : inputWord y = inputWord z := by
  apply monotone_words_equal _ _ _ hhist
  intro i
  change (y i).1.val ≤ (z i).1.val
  by_contra hn
  have he : (z i).1.val < (y i).1.val := by omega
  exact hs i (transformed_triangular F r c h hc ho (x i) (y i) (z i) he)

/-- The actual fixed-histogram coordinate restriction has no cross-word coefficients. -/
theorem restricted_block_diagonal (F : Type) [Field F] (r c h n : ℕ)
    (hc : h + 1 ≤ c) (ho : h + 1 ≤ r + c - 1) (counts : Fin (h + 1) → ℕ)
    (x : Fin n → Fin r) (y : keptInput c h n counts) (z : keptOutput r c h n counts) :
    restricted F r c h n hc ho counts x y z =
      if inputWord y.val = inputWord z.val then
        ∏ i, (if (x i).val + (y.val i).2.val = (z.val i).2.val then 1 else 0)
      else 0 := by
  classical
  by_cases hw : inputWord y.val = inputWord z.val
  · simp only [restricted, Tensor.pullback, id_eq, Tensor.power, ite_eq_left hw]
    apply Finset.prod_congr rfl
    intro i hi
    exact transformed_diagonal F r c h hc ho (x i) (y.val i) (z.val i)
      (congrArg Fin.val (congrFun hw i)).symm
  · simp only [restricted, Tensor.pullback, id_eq, Tensor.power, ite_eq_right hw]
    by_contra hn
    have hs : ∀ i, transformed F r c h hc ho (x i) (y.val i) (z.val i) ≠ 0 := by
      intro i
      exact (Finset.prod_ne_zero_iff.mp hn) i (Finset.mem_univ i)
    exact hw (supported_words_equal F r c h n hc ho x y.val z.val hs
      (y.property.trans z.property.symm))

/-- The projections are ordinary restrictions in the pinned tensor API. -/
theorem restricted_eq_restrict (F : Type) [CommRing F] (r c h n : ℕ)
    (hc : h + 1 ≤ c) (ho : h + 1 ≤ r + c - 1) (counts : Fin (h + 1) → ℕ) :
    restricted F r c h n hc ho counts = Tensor.restrict
      (fun x' x => if x = x' then 1 else 0)
      (fun (y' : keptInput c h n counts) y => if y = y'.val then 1 else 0)
      (fun (z' : keptOutput r c h n counts) z => if z = z'.val then 1 else 0)
      (Tensor.power (transformed F r c h hc ho) n) :=
  Tensor.pullback_eq_restrict id Subtype.val Subtype.val _

theorem transformed_double_sum (F : Type) [CommRing F] (r c h : ℕ)
    (hc : h + 1 ≤ c) (ho : h + 1 ≤ r + c - 1)
    (a : Fin r) (d : DeterminantIndex c h) (e : DeterminantIndex (r + c - 1) h) :
    transformed F r c h hc ho a d e =
      ∑ m, ∑ k, (coordinateMatrix c h m d : F) *
        (expansionMatrix (r + c - 1) h ho e k : F) * source F r c h a m k := by
  simp [transformed, Tensor.restrict]

/-- The whole construction is one explicit ordinary restriction of the original
source power, with the first leg shared and unchanged. -/
theorem restricted_eq_source_restrict (F : Type) [CommRing F] (r c h n : ℕ)
    (hc : h + 1 ≤ c) (ho : h + 1 ≤ r + c - 1) (counts : Fin (h + 1) → ℕ) :
    restricted F r c h n hc ho counts = Tensor.restrict
      (fun x' x => if x = x' then 1 else 0)
      (fun (y : keptInput c h n counts) m =>
        ∏ i, (coordinateMatrix c h (m i) (y.val i) : F))
      (fun (z : keptOutput r c h n counts) k =>
        ∏ i, (expansionMatrix (r + c - 1) h ho (z.val i) (k i) : F))
      (Tensor.power (source F r c h) n) := by
  funext x y z
  simp only [restricted, Tensor.pullback, id_eq, Tensor.power, transformed_double_sum]
  simp only [Tensor.restrict]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, Tensor.power]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Finset.prod_mul_distrib]

def Word (h n : ℕ) (counts : Fin (h + 1) → ℕ) :=
  {w : Fin n → Fin (h + 1) // histogram w = counts}

def sectorInput (c h n : ℕ) (counts : Fin (h + 1) → ℕ) (w : Word h n counts) :=
  (i : Fin n) → Fin (c + h - 2 * (w.val i).val)

def sectorOutput (r c h n : ℕ) (counts : Fin (h + 1) → ℕ) (w : Word h n counts) :=
  (i : Fin n) → Fin (r + (c + h - 2 * (w.val i).val) - 1)

def sectorEmbeddingInput (c h n : ℕ) (counts : Fin (h + 1) → ℕ) (w : Word h n counts)
    (y : sectorInput c h n counts w) : keptInput c h n counts :=
  ⟨fun i => ⟨w.val i, y i⟩, w.property⟩

def sectorEmbeddingOutput (r c h n : ℕ) (hr : 0 < r) (hc : h + 1 ≤ c)
    (counts : Fin (h + 1) → ℕ) (w : Word h n counts)
    (z : sectorOutput r c h n counts w) : keptOutput r c h n counts :=
  ⟨fun i => ⟨w.val i, ⟨(z i).val, by have := (z i).isLt; have := (w.val i).isLt; omega⟩⟩,
    w.property⟩

/-- Each diagonal word sector is the product of its indicated convolution tensors.
All sectors retain the same first-leg coordinate space. -/
theorem sector_tensor_identity (F : Type) [Field F] (r c h n : ℕ)
    (hr : 0 < r) (hc : h + 1 ≤ c) (counts : Fin (h + 1) → ℕ) (w : Word h n counts)
    (x : Fin n → Fin r) (y : sectorInput c h n counts w) (z : sectorOutput r c h n counts w) :
    restricted F r c h n hc (by omega) counts x
      (sectorEmbeddingInput c h n counts w y)
      (sectorEmbeddingOutput r c h n hr hc counts w z) =
      ∏ i, TensorRankBridge.convolution F r (c + h - 2 * (w.val i).val) (x i) (y i) (z i) := by
  rw [restricted_block_diagonal]
  have hw : inputWord (sectorEmbeddingInput c h n counts w y).val =
      inputWord (sectorEmbeddingOutput r c h n hr hc counts w z).val := rfl
  rw [ite_eq_left hw]
  rfl

theorem sectorEmbeddingInput_covers (c h n : ℕ) (counts : Fin (h + 1) → ℕ)
    (y : keptInput c h n counts) :
    ∃ w : Word h n counts, ∃ v : sectorInput c h n counts w,
      sectorEmbeddingInput c h n counts w v = y := by
  refine ⟨⟨inputWord y.val, y.property⟩, (fun i => (y.val i).2), ?_⟩
  apply Subtype.ext
  rfl

theorem sectorEmbeddingOutput_covers (r c h n : ℕ) (hr : 0 < r) (hc : h + 1 ≤ c)
    (counts : Fin (h + 1) → ℕ) (z : keptOutput r c h n counts) :
    ∃ w : Word h n counts, ∃ v : sectorOutput r c h n counts w,
      sectorEmbeddingOutput r c h n hr hc counts w v = z := by
  let w : Word h n counts := ⟨inputWord z.val, z.property⟩
  let v : sectorOutput r c h n counts w := fun i =>
    ⟨(z.val i).2.val, by
      change (z.val i).2.val < r + (c + h - 2 * (z.val i).1.val) - 1
      have := (z.val i).1.isLt; have := (z.val i).2.isLt; omega⟩
  refine ⟨w, v, ?_⟩
  apply Subtype.ext
  rfl

def blockInput (c h j : ℕ) (hj : j ≤ h) (i : Fin (c + h - 2 * j)) :
    DeterminantIndex c h := ⟨⟨j, by omega⟩, i⟩

def blockOutput (r c h j : ℕ) (hr : 0 < r) (hc : h + 1 ≤ c) (hj : j ≤ h)
    (k : Fin (r + (c + h - 2 * j) - 1)) : DeterminantIndex (r + c - 1) h :=
  ⟨⟨j, by omega⟩, ⟨k.val, by
    change k.val < (r + c - 1) + h - 2 * j
    have := k.isLt; omega⟩⟩

/-- A whole equal-depth block is the actual convolution tensor of the expected width. -/
theorem diagonal_block (F : Type) [Field F] (r c h j : ℕ)
    (hr : 0 < r) (hc : h + 1 ≤ c) (hj : j ≤ h) :
    Tensor.pullback id (blockInput c h j hj) (blockOutput r c h j hr hc hj)
      (transformed F r c h hc (by omega)) =
      TensorRankBridge.convolution F r (c + h - 2 * j) := by
  funext a i k
  change transformed F r c h hc (by omega) a (blockInput c h j hj i)
    (blockOutput r c h j hr hc hj k) = _
  rw [transformed_diagonal F r c h hc (by omega) a
    (blockInput c h j hj i) (blockOutput r c h j hr hc hj k) (by rfl)]
  rfl

end
end MatrixDimensionAudit.DeterminantTensorBridge
