import Std
import formalization.DimensionArithmetic

/-!
Finite conserved-flow potential bounds, with a row-two specialization.

Edges and boundary vertices are lists: repetitions represent nonnegative
integer multiplicities. Conservation is exact equality of multisets, expressed
by `List.Perm`. These theorems do not assume the potential telescope itself.

Check with Lean 4.34.1. Build the imported arithmetic helper into a temporary
module directory first; docs/lean-general-flow-progress.md gives exact commands.
No project-local compiled artifacts are required.
-/

namespace MatrixDimensionAudit
namespace GeneralFlow

structure Edge (Vertex : Type) where
  src : Vertex
  dst : Vertex

variable {Vertex : Type} {sources sinks : List Vertex} {edges : List (Edge Vertex)}

/-- Sources plus arriving edge ends equal sinks plus departing edge ends. -/
def Balanced (sources sinks : List Vertex) (edges : List (Edge Vertex)) : Prop :=
  (sources ++ edges.map Edge.dst).Perm (sinks ++ edges.map Edge.src)

theorem balanced_iff_counts [BEq Vertex] [LawfulBEq Vertex] :
    Balanced sources sinks edges ↔ ∀ v,
      sources.count v + (edges.map Edge.dst).count v =
        sinks.count v + (edges.map Edge.src).count v := by
  simp only [Balanced, List.perm_iff_count, List.count_append]

def intSum (vertices : List Vertex) (potential : Vertex → Int) : Int :=
  (vertices.map potential).sum

def natProduct (vertices : List Vertex) (potential : Vertex → Nat) : Nat :=
  (vertices.map potential).prod

theorem intSum_perm (p : a.Perm b) (potential : Vertex → Int) :
    intSum a potential = intSum b potential := by
  induction p with
  | nil => rfl
  | cons x p ih => simp [intSum] at ih ⊢; exact ih
  | swap x y l => simp [intSum, Int.add_left_comm]
  | trans p q ihp ihq => exact ihp.trans ihq

theorem natProduct_perm (p : a.Perm b) (potential : Vertex → Nat) :
    natProduct a potential = natProduct b potential := by
  induction p with
  | nil => rfl
  | cons x p ih => simpa [natProduct] using congrArg (fun n => potential x * n) ih
  | swap x y l => simp [natProduct, Nat.mul_left_comm]
  | trans p q ihp ihq => exact ihp.trans ihq

theorem additive_balance (h : Balanced sources sinks edges)
    (potential : Vertex → Int) :
    intSum sources potential + intSum (edges.map Edge.dst) potential =
      intSum sinks potential + intSum (edges.map Edge.src) potential := by
  have hp := intSum_perm h potential
  simpa [intSum, List.map_append, List.sum_append_int] using hp

theorem additive_edge_bound (edges : List (Edge Vertex))
    (potential : Vertex → Int) (cost : Edge Vertex → Int)
    (edgeBound : ∀ e ∈ edges, potential e.dst ≤ cost e + potential e.src) :
    intSum (edges.map Edge.dst) potential ≤
      (edges.map cost).sum + intSum (edges.map Edge.src) potential := by
  induction edges with
  | nil => simp [intSum]
  | cons e tail ih =>
    have he := edgeBound e (by simp)
    have ht := ih (by intro f hf; exact edgeBound f (by simp [hf]))
    simp only [List.map_cons, List.sum_cons, intSum] at ht ⊢
    omega

/-- Weak duality for every integer potential, including negative values. -/
theorem additive_weak_duality
    (h : Balanced sources sinks edges)
    (potential : Vertex → Int) (cost : Edge Vertex → Int)
    (edgeBound : ∀ e ∈ edges, potential e.dst ≤ cost e + potential e.src) :
    intSum sinks potential - intSum sources potential ≤ (edges.map cost).sum := by
  have hb := additive_balance h potential
  have he := additive_edge_bound edges potential cost edgeBound
  omega

theorem multiplicative_balance (h : Balanced sources sinks edges)
    (potential : Vertex → Nat) :
    natProduct sources potential * natProduct (edges.map Edge.dst) potential =
      natProduct sinks potential * natProduct (edges.map Edge.src) potential := by
  have hp := natProduct_perm h potential
  simpa [natProduct, List.map_append, List.prod_append] using hp

theorem multiplicative_edge_bound (edges : List (Edge Vertex))
    (potential : Vertex → Nat) (cost : Edge Vertex → Nat)
    (edgeBound : ∀ e ∈ edges, potential e.dst ≤ cost e * potential e.src) :
    natProduct (edges.map Edge.dst) potential ≤
      (edges.map cost).prod * natProduct (edges.map Edge.src) potential := by
  induction edges with
  | nil => simp [natProduct]
  | cons e tail ih =>
    have he := edgeBound e (by simp)
    have ht := ih (by intro f hf; exact edgeBound f (by simp [hf]))
    have hm := Nat.mul_le_mul he ht
    simpa [natProduct, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hm

theorem natProduct_pos (vertices : List Vertex) (potential : Vertex → Nat)
    (positive : ∀ v ∈ vertices, 0 < potential v) : 0 < natProduct vertices potential := by
  induction vertices with
  | nil => simp [natProduct]
  | cons v tail ih =>
    exact Nat.mul_pos (positive v (by simp))
      (ih (by intro w hw; exact positive w (by simp [hw])))

/-- Multiplicative weak duality; only consumed edge potentials must be positive. -/
theorem multiplicative_weak_duality
    (h : Balanced sources sinks edges)
    (potential : Vertex → Nat) (cost : Edge Vertex → Nat)
    (edgeBound : ∀ e ∈ edges, potential e.dst ≤ cost e * potential e.src)
    (positive : ∀ e ∈ edges, 0 < potential e.src) :
    natProduct sinks potential ≤ natProduct sources potential * (edges.map cost).prod := by
  have hb := multiplicative_balance h potential
  have he := multiplicative_edge_bound edges potential cost edgeBound
  have hm := Nat.mul_le_mul_left (natProduct sources potential) he
  have ht : 0 < natProduct (edges.map Edge.src) potential :=
    natProduct_pos _ _ (by
      intro v hv
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hv
      exact positive e he)
  apply Nat.le_of_mul_le_mul_right (c := natProduct (edges.map Edge.src) potential) _ ht
  rw [← hb]
  simpa [Nat.mul_assoc] using hm

/-- A legal selected child of an arbitrary-width split in row two. -/
structure RowTwoSplit where
  x : Fin 7
  h : Fin 7
  t : Fin 7
  x_lower : 1 ≤ x.val
  x_upper : x.val < 6
  h_lower : 1 ≤ h.val
  h_upper : h.val ≤ min x.val (6 - x.val)
  t_upper : t.val ≤ h.val

def RowTwoSplit.edge (e : RowTwoSplit) : Edge Nat :=
  ⟨e.x.val, e.x.val + e.h.val - 2 * e.t.val⟩

def RowTwoSplit.dimension (e : RowTwoSplit) : Nat := e.h.val + 1

theorem rowTwoSplit_local (e : RowTwoSplit) :
    rowTwoPotential e.edge.dst ≤ e.dimension * rowTwoPotential e.edge.src := by
  exact rowTwoPotential_legalSplits e.x e.h e.t e.x_lower e.x_upper
    e.h_lower e.h_upper e.t_upper

theorem rowTwoSplit_source_pos (e : RowTwoSplit) : 0 < rowTwoPotential e.edge.src := by
  have hx := e.x_lower
  have hy := e.x_upper
  have hv : e.x.val = 1 ∨ e.x.val = 2 ∨ e.x.val = 3 ∨ e.x.val = 4 ∨ e.x.val = 5 := by omega
  rcases hv with h | h | h | h | h <;> simp [RowTwoSplit.edge, h, rowTwoPotential]

theorem natProduct_replicate (count : Nat) (v : Vertex) (potential : Vertex → Nat) :
    natProduct (List.replicate count v) potential = potential v ^ count := by
  induction count with
  | zero => simp [natProduct]
  | succ count ih =>
    change potential v * natProduct (List.replicate count v) potential = _
    rw [ih, Nat.pow_succ, Nat.mul_comm]

/--
All-width row-two lower bound, proved from exact multiset conservation.
A reset 6 -> 1 is represented by one extra source at 1 and one sink at 6.
Thus K injected units and Z resets force product split dimensions >= 2^K*16^Z.
No acyclicity, deterministic rounding, or restricted width is assumed.
-/
theorem rowTwo_dimension_bound (splits : List RowTwoSplit) (K Z : Nat)
    (balance : Balanced (List.replicate (K + Z) 1)
      (List.replicate K 0 ++ List.replicate Z 6) (splits.map RowTwoSplit.edge)) :
    2 ^ K * 16 ^ Z ≤ (splits.map RowTwoSplit.dimension).prod := by
  -- A generic edge has lost the selected split width, so apply the edge-product
  -- inequality directly while retaining each `RowTwoSplit` as its label.
  have hedge : natProduct ((splits.map RowTwoSplit.edge).map Edge.dst) rowTwoPotential ≤
      (splits.map RowTwoSplit.dimension).prod *
      natProduct ((splits.map RowTwoSplit.edge).map Edge.src) rowTwoPotential := by
    clear balance
    induction splits with
    | nil => simp [natProduct]
    | cons e tail ih =>
      have hm := Nat.mul_le_mul (rowTwoSplit_local e) ih
      simpa [natProduct, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hm
  have hb := multiplicative_balance balance rowTwoPotential
  have hpos : 0 < natProduct ((splits.map RowTwoSplit.edge).map Edge.src) rowTwoPotential :=
    natProduct_pos _ _ (by
      intro v hv
      obtain ⟨edge, he, rfl⟩ := List.mem_map.mp hv
      obtain ⟨e, he', rfl⟩ := List.mem_map.mp he
      exact rowTwoSplit_source_pos e)
  have hs : natProduct (List.replicate (K + Z) 1) rowTwoPotential = 1 := by
    rw [natProduct_replicate]
    simp [rowTwoPotential]
  have ht : natProduct (List.replicate K 0 ++ List.replicate Z 6) rowTwoPotential =
      2 ^ K * 16 ^ Z := by
    simp only [natProduct, List.map_append, List.prod_append]
    change natProduct (List.replicate K 0) rowTwoPotential *
      natProduct (List.replicate Z 6) rowTwoPotential = _
    rw [natProduct_replicate, natProduct_replicate]
    rfl
  rw [hs, Nat.one_mul, ht] at hb
  rw [hb] at hedge
  exact Nat.le_of_mul_le_mul_right hedge hpos

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- Exact bounded certificate for every possible counterexample below 96. -/
theorem rowTwo_bounded_search :
    ∀ K : Fin 96, ∀ Z : Fin 24,
    ∀ j : Fin (96 / (K.val + 4 * Z.val) + 1),
      0 < K.val → 0 < Z.val → 0 < j.val →
      j.val * (K.val + 4 * Z.val) < 96 →
      ¬ (3 ^ K.val < 3 ^ Z.val * 2 ^ K.val ∧
        9 ^ (j.val * K.val) * 24 ^ Z.val < 10 ^ (j.val * K.val)) := by
  decide

/-- The bounded certificate is complete for arbitrary positive integers. -/
theorem rowTwo_reuse_objective (K Z j : Nat)
    (hK : 0 < K) (hZ : 0 < Z) (hj : 0 < j)
    (gain : 3 ^ K < 3 ^ Z * 2 ^ K)
    (reuse : 9 ^ (j * K) * 24 ^ Z < 10 ^ (j * K)) :
    96 ≤ j * (K + 4 * Z) := by
  apply Nat.le_of_not_lt
  intro small
  have hobj : K + 4 * Z ≤ j * (K + 4 * Z) := Nat.le_mul_of_pos_left _ hj
  have klt : K < 96 := by omega
  have zlt : Z < 24 := by omega
  have hden : 0 < K + 4 * Z := by omega
  have jbound : j < 96 / (K + 4 * Z) + 1 := by
    have hd : j ≤ 96 / (K + 4 * Z) := (Nat.le_div_iff_mul_le hden).mpr (by omega)
    omega
  exact rowTwo_bounded_search ⟨K, klt⟩ ⟨Z, zlt⟩ ⟨j, jbound⟩ hK hZ hj small ⟨gain, reuse⟩

/-- The relaxed integer objective 96 is attained; no flow existence is claimed. -/
theorem rowTwo_relaxed_minimizer :
    3 ^ 2 < 3 ^ 1 * 2 ^ 2 ∧
      9 ^ (16 * 2) * 24 ^ 1 < 10 ^ (16 * 2) ∧
      16 * (2 + 4 * 1) = 96 := by
  decide

/--
A source-side lower bound from legal row-two flow and the two integer necessary
conditions. Deriving these conditions from the paper's pooled exponent is a
separate, still unformalized bridge; it is not assumed to have been checked here.
-/
theorem rowTwo_conditional_sourceSide_bound (splits : List RowTwoSplit)
    (K Z N k j : Nat)
    (hK : 0 < K) (hZ : 0 < Z) (hN : 0 < N) (hk : 0 < k) (hj : 0 < j)
    (balance : Balanced (List.replicate (K + Z) 1)
      (List.replicate K 0 ++ List.replicate Z 6) (splits.map RowTwoSplit.edge))
    (gain : 3 ^ K < 3 ^ Z * 2 ^ K)
    (reuse : 9 ^ (j * K) * 24 ^ Z < 10 ^ (j * K)) :
    2 ^ 96 ≤ (splits.map RowTwoSplit.dimension).prod ^ (N * k * j) := by
  have hb := rowTwo_dimension_bound splits K Z balance
  have identity : 2 ^ K * 16 ^ Z = 2 ^ (K + 4 * Z) := by
    rw [Nat.pow_add]
    have hp : 16 ^ Z = 2 ^ (4 * Z) := by
      rw [Nat.pow_mul]
    rw [hp]
  rw [identity] at hb
  have hpow := Nat.pow_le_pow_left hb (N * k * j)
  rw [← Nat.pow_mul] at hpow
  have ho := rowTwo_reuse_objective K Z j hK hZ hj gain reuse
  have he : 96 ≤ (K + 4 * Z) * (N * k * j) := by
    have hm := Nat.le_mul_of_pos_left (j * (K + 4 * Z)) (Nat.mul_pos hN hk)
    have ht := Nat.le_trans ho hm
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using ht
  exact Nat.le_trans (Nat.pow_le_pow_right (by decide) he) hpow

#print axioms additive_balance
#print axioms additive_weak_duality
#print axioms multiplicative_balance
#print axioms multiplicative_weak_duality
#print axioms rowTwo_dimension_bound
#print axioms rowTwo_bounded_search
#print axioms rowTwo_reuse_objective
#print axioms rowTwo_conditional_sourceSide_bound

end GeneralFlow
end MatrixDimensionAudit
