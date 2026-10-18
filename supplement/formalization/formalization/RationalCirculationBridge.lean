module
public import Mathlib

/-! Exact denominator clearing of finite nonnegative rational circulations. -/
@[expose] public section
namespace MatrixDimensionAudit.RationalCirculationBridge
open scoped BigOperators
noncomputable section
variable {E : Type} [Fintype E]

/-- A single explicit scale for every edge, including reset and return edges. -/
def commonDenominator (w : E → ℚ) : ℕ := ∏ e, (w e).den

theorem commonDenominator_pos (w : E → ℚ) : 0 < commonDenominator w :=
  Finset.prod_pos (fun e _ => (w e).den_pos)

theorem edge_denominator_dvd (w : E → ℚ) (e : E) : (w e).den ∣ commonDenominator w :=
  Finset.dvd_prod_of_mem (fun e => (w e).den) (Finset.mem_univ e)

/-- Natural edge multiplicities; no integer-circulation witness is supplied. -/
def integerCounts (w : E → ℚ) (e : E) : ℕ :=
  (commonDenominator w / (w e).den) * (w e).num.toNat

/-- Clearing really gives the same scale on every edge. -/
theorem integerCounts_cast (w : E → ℚ) (hw : ∀ e, 0 ≤ w e) (e : E) :
    (integerCounts w e : ℚ) = (commonDenominator w : ℚ) * w e := by
  have hn : 0 ≤ (w e).num := Rat.num_nonneg.mpr (hw e)
  have hnc : ((w e).num.toNat : ℚ) = ((w e).num : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg hn
  calc
    (integerCounts w e : ℚ) = ((commonDenominator w : ℚ) / (w e).den) * ((w e).num : ℚ) := by
      rw [integerCounts, Nat.cast_mul, Nat.cast_div_charZero (edge_denominator_dvd w e), hnc]
    _ = (commonDenominator w : ℚ) * (((w e).num : ℚ) / (w e).den) := by ring
    _ = (commonDenominator w : ℚ) * w e := by rw [Rat.num_div_den]

theorem integerCounts_eq_zero_iff (w : E → ℚ) (hw : ∀ e, 0 ≤ w e) (e : E) :
    integerCounts w e = 0 ↔ w e = 0 := by
  have hD : (commonDenominator w : ℚ) ≠ 0 := by exact_mod_cast (commonDenominator_pos w).ne'
  constructor
  · intro he
    have hc := integerCounts_cast w hw e
    rw [he, Nat.cast_zero] at hc
    exact (mul_eq_zero.mp hc.symm).resolve_left hD
  · intro he
    have hc := integerCounts_cast w hw e
    rw [he, mul_zero] at hc
    exact_mod_cast hc

theorem integerCounts_pos_iff (w : E → ℚ) (hw : ∀ e, 0 ≤ w e) (e : E) :
    0 < integerCounts w e ↔ 0 < w e := by
  rw [Nat.pos_iff_ne_zero]
  exact (not_congr (integerCounts_eq_zero_iff w hw e)).trans
    ⟨fun h => lt_of_le_of_ne (hw e) (fun he => h he.symm), fun h => h.ne'⟩

/-- A fixed integral return edge is scaled by exactly the common denominator. -/
theorem integerCounts_of_nat (w : E → ℚ) (hw : ∀ e, 0 ≤ w e) (e : E) (K : ℕ)
    (he : w e = K) : integerCounts w e = commonDenominator w * K := by
  have h := integerCounts_cast w hw e
  rw [he] at h
  exact_mod_cast h

def rationalMass {L : Type} [DecidableEq L] (w : E → ℚ) (label : E → L) (a : L) : ℚ :=
  ∑ e, if label e = a then w e else 0

def naturalMass {L : Type} [DecidableEq L] (counts : E → ℕ) (label : E → L) (a : L) : ℕ :=
  ∑ e, if label e = a then counts e else 0

/-- Every labeled finite fiber respects an exact pointwise scale. -/
theorem naturalMass_cast_of_scaling {L : Type} [DecidableEq L] (D : ℕ) (counts : E → ℕ) (w : E → ℚ)
    (scale : ∀ e, (counts e : ℚ) = (D : ℚ)*w e) (label : E → L) (a : L) :
    (naturalMass counts label a : ℚ) = (D : ℚ)*rationalMass w label a := by
  unfold naturalMass rationalMass
  rw [Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : label e = a
  · simpa only [he, ite_true] using scale e
  · simp [he]

/-- Every labeled fiber histogram is scaled by the same positive denominator. -/
theorem naturalMass_cast {L : Type} [DecidableEq L] (w : E → ℚ) (hw : ∀ e, 0 ≤ w e)
    (label : E → L) (a : L) :
    (naturalMass (integerCounts w) label a : ℚ) = (commonDenominator w : ℚ) * rationalMass w label a :=
  naturalMass_cast_of_scaling _ _ _ (integerCounts_cast w hw) label a

/-- A rational circulation is an edge-weight equation, with loops and parallel edges retained. -/
def IsRationalCirculation {V : Type} [DecidableEq V] (src dst : E → V) (w : E → ℚ) : Prop :=
  ∀ v, rationalMass w dst v = rationalMass w src v

def IsNaturalCirculation {V : Type} [DecidableEq V] (src dst : E → V) (counts : E → ℕ) : Prop :=
  ∀ v, naturalMass counts dst v = naturalMass counts src v

/-- The natural circulation is derived from the rational one, not assumed. -/
theorem integerCounts_circulation {V : Type} [DecidableEq V] (src dst : E → V)
    (w : E → ℚ) (hw : ∀ e, 0 ≤ w e) (balance : IsRationalCirculation src dst w) :
    IsNaturalCirculation src dst (integerCounts w) := by
  intro v
  have h : (naturalMass (integerCounts w) dst v : ℚ) = naturalMass (integerCounts w) src v := by
    rw [naturalMass_cast w hw, naturalMass_cast w hw, balance v]
  exact_mod_cast h

/-- Normalized edge proportions in any chosen fiber are unchanged. -/
theorem normalized_fiber {L : Type} [DecidableEq L] (w : E → ℚ) (hw : ∀ e, 0 ≤ w e)
    (label : E → L) (a : L) (e : E) :
    (integerCounts w e : ℚ) / naturalMass (integerCounts w) label a = w e / rationalMass w label a := by
  rw [integerCounts_cast w hw, naturalMass_cast w hw]
  exact mul_div_mul_left _ _ (by exact_mod_cast (commonDenominator_pos w).ne')


/-- Grouped sites are inactive exactly when their rational mass is zero. -/
theorem naturalMass_eq_zero_iff {L : Type} [DecidableEq L] (w : E → ℚ) (hw : ∀ e, 0 ≤ w e)
    (label : E → L) (a : L) : naturalMass (integerCounts w) label a=0 ↔ rationalMass w label a=0 := by
  have hD : (commonDenominator w : ℚ) ≠ 0 := by exact_mod_cast (commonDenominator_pos w).ne'
  constructor
  · intro he
    have h := naturalMass_cast w hw label a
    rw [he, Nat.cast_zero] at h
    exact (mul_eq_zero.mp h.symm).resolve_left hD
  · intro he
    have h := naturalMass_cast w hw label a
    rw [he, mul_zero] at h
    exact_mod_cast h

/-- Every empirical child histogram agrees with its rational fiber proportions. -/
theorem normalized_histogram {L J : Type} [DecidableEq L] [DecidableEq J]
    (w : E → ℚ) (hw : ∀ e, 0 ≤ w e) (coarse : E → L) (fine : E → J) (a : L) (b : J) :
    (naturalMass (integerCounts w) fine b : ℚ) / naturalMass (integerCounts w) coarse a =
      rationalMass w fine b / rationalMass w coarse a := by
  rw [naturalMass_cast w hw, naturalMass_cast w hw]
  exact mul_div_mul_left _ _ (by exact_mod_cast (commonDenominator_pos w).ne')

/-- Expand every edge identifier with its actual natural multiplicity. -/
def expandEdges (edges : List E) (counts : E → ℕ) : List E :=
  edges.flatMap (fun e => List.replicate (counts e) e)

omit [Fintype E] in
theorem expandEdges_map_count {L : Type} [DecidableEq L] (edges : List E) (counts : E → ℕ)
    (label : E → L) (a : L) :
    ((expandEdges edges counts).map label).count a =
      (edges.map (fun e => if label e = a then counts e else 0)).sum := by
  induction edges with
  | nil => rfl
  | cons e edges ih =>
      simp only [expandEdges, List.flatMap_cons, List.map_append, List.count_append,
        List.map_replicate, List.count_replicate, beq_iff_eq, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih]

/-- Enumerate the graph's finite edge set once, then expand its multiplicities. -/
def edgeWord (counts : E → ℕ) : List E :=
  expandEdges (List.ofFn (fun i : Fin (Fintype.card E) => (Fintype.equivFin E).symm i)) counts

/-- The actual finite word carries exactly the derived label histogram. -/
theorem edgeWord_map_count {L : Type} [DecidableEq L] (counts : E → ℕ) (label : E → L) (a : L) :
    ((edgeWord counts).map label).count a = naturalMass counts label a := by
  rw [edgeWord, expandEdges_map_count, List.map_ofFn, Fin.sum_ofFn]
  exact (Fintype.equivFin E).symm.sum_comp (fun e => if label e = a then counts e else 0)

/-- Exact conservation holds in the actual expanded edge list. -/
theorem edgeWord_circulation {V : Type} [DecidableEq V] (src dst : E → V)
    (w : E → ℚ) (hw : ∀ e, 0 ≤ w e) (balance : IsRationalCirculation src dst w) (v : V) :
    ((edgeWord (integerCounts w)).map dst).count v = ((edgeWord (integerCounts w)).map src).count v := by
  rw [edgeWord_map_count, edgeWord_map_count]
  exact integerCounts_circulation src dst w hw balance v

/-- The expanded list preserves every scaled weighted histogram, not just vertex balance. -/
theorem edgeWord_histogram_cast {L : Type} [DecidableEq L] (w : E → ℚ) (hw : ∀ e, 0 ≤ w e)
    (label : E → L) (a : L) :
    (((edgeWord (integerCounts w)).map label).count a : ℚ) =
      (commonDenominator w : ℚ) * rationalMass w label a := by
  rw [edgeWord_map_count, naturalMass_cast w hw]

/-- The supported integer circulation exists by explicit construction at a common scale. -/
theorem exists_supported_integer_circulation {V : Type} [DecidableEq V] (src dst : E → V)
    (w : E → ℚ) (hw : ∀ e, 0 ≤ w e) (balance : IsRationalCirculation src dst w) :
    ∃ D : ℕ, 0 < D ∧ ∃ counts : E → ℕ,
      (∀ e, (counts e : ℚ) = (D : ℚ)*w e) ∧
      (∀ e, counts e=0 ↔ w e=0) ∧ IsNaturalCirculation src dst counts :=
  ⟨commonDenominator w, commonDenominator_pos w, integerCounts w, integerCounts_cast w hw,
    integerCounts_eq_zero_iff w hw, integerCounts_circulation src dst w hw balance⟩


theorem edgeWord_count [DecidableEq E] (counts : E → ℕ) (e : E) :
    (edgeWord counts).count e = counts e := by
  simpa [naturalMass] using edgeWord_map_count counts id e

section Family
variable {I : Type} [Fintype I] {F : I → Type} [∀ i, Fintype (F i)]

/-- One denominator for a whole finite family, so all return scales agree. -/
def familyDenominator (w : ∀ i, F i → ℚ) : ℕ :=
  commonDenominator (fun e : Sigma F => w e.1 e.2)

def familyCounts (w : ∀ i, F i → ℚ) (i : I) (e : F i) : ℕ :=
  integerCounts (fun p : Sigma F => w p.1 p.2) ⟨i,e⟩

theorem familyDenominator_pos (w : ∀ i, F i → ℚ) : 0 < familyDenominator w :=
  commonDenominator_pos _

theorem familyCounts_cast (w : ∀ i, F i → ℚ) (hw : ∀ i e, 0 ≤ w i e) (i : I) (e : F i) :
    (familyCounts w i e : ℚ) = (familyDenominator w : ℚ)*w i e :=
  integerCounts_cast (fun p : Sigma F => w p.1 p.2) (fun p => hw p.1 p.2) ⟨i,e⟩

theorem familyCounts_eq_zero_iff (w : ∀ i, F i → ℚ) (hw : ∀ i e, 0 ≤ w i e) (i : I) (e : F i) :
    familyCounts w i e=0 ↔ w i e=0 :=
  integerCounts_eq_zero_iff (fun p : Sigma F => w p.1 p.2) (fun p => hw p.1 p.2) ⟨i,e⟩

theorem familyCounts_of_nat (w : ∀ i, F i → ℚ) (hw : ∀ i e, 0 ≤ w i e)
    (i : I) (e : F i) (K : ℕ) (he : w i e=K) :
    familyCounts w i e = familyDenominator w*K :=
  integerCounts_of_nat (fun p : Sigma F => w p.1 p.2) (fun p => hw p.1 p.2) ⟨i,e⟩ K he

/-- A single derived scale preserves each row circulation separately. -/
theorem familyCounts_circulation {V : I → Type} [∀ i, DecidableEq (V i)]
    (src dst : ∀ i, F i → V i) (w : ∀ i, F i → ℚ) (hw : ∀ i e, 0 ≤ w i e)
    (balance : ∀ i, IsRationalCirculation (src i) (dst i) (w i)) :
    ∀ i, IsNaturalCirculation (src i) (dst i) (familyCounts w i) := by
  intro i v
  have hd := naturalMass_cast_of_scaling (familyDenominator w) (familyCounts w i) (w i)
    (familyCounts_cast w hw i) (dst i) v
  have hs := naturalMass_cast_of_scaling (familyDenominator w) (familyCounts w i) (w i)
    (familyCounts_cast w hw i) (src i) v
  have he : (naturalMass (familyCounts w i) (dst i) v : ℚ) = naturalMass (familyCounts w i) (src i) v := by
    rw [hd,hs,balance i v]
  exact_mod_cast he

end Family
end
end MatrixDimensionAudit.RationalCirculationBridge
