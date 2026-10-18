import formalization.TriplingOddSourceBridge

namespace MatrixDimensionAudit.TriplingContextBridge
open OAI.MatrixMultiplication.Foundation
open TensorRankBridge TriplingRestrictionBridge TriplingLocalRecipeBridge TriplingLocalSourceBridge
open DependentSeparator SeparatorTensor
open scoped BigOperators

noncomputable section
attribute [local instance] TriplingLocalRecipeBridge.sectorYFinite TriplingLocalRecipeBridge.sectorZFinite

abbrev contextCoordinate {X X' U : Type} (f : X' → X) : (X' × U) → (X × U) :=
  fun x => (f x.1, x.2)

/-- Carry an unchanged spectator through a coordinate pullback. -/
theorem pullback_context {X Y Z X' Y' Z' U V W : Type}
    (T : Tensor ℚ X Y Z) (S : Tensor ℚ U V W)
    (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z) :
    Tensor.pullback (fun x => (fx x.1, x.2)) (fun y => (fy y.1, y.2))
      (fun z => (fz z.1, z.2)) (Tensor.product T S) =
      Tensor.product (Tensor.pullback fx fy fz T) S := rfl

def contextMatrix {X X' U : Type} (A : X' → X → ℚ) : (X' × U) → (X × U) → ℚ :=
  fun x u => A x.1 u.1 * projectionMatrix id x.2 u.2

/-- The spectator matrices are coordinate identities. The restriction acts on
one decomposition of the complete product, not on separate factor ranks. -/
theorem restrict_context {X Y Z X' Y' Z' U V W : Type}
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor ℚ X Y Z) (S : Tensor ℚ U V W)
    (A : X' → X → ℚ) (B : Y' → Y → ℚ) (C : Z' → Z → ℚ) :
    Tensor.restrict (contextMatrix (U := U) A) (contextMatrix (U := V) B)
      (contextMatrix (U := W) C) (Tensor.product T S) =
      Tensor.product (Tensor.restrict A B C T) S := by
  unfold contextMatrix
  rw [Tensor.restrict_product]
  have hi : Tensor.restrict (projectionMatrix id) (projectionMatrix id) (projectionMatrix id) S = S := by
    classical
    exact (Tensor.pullback_eq_restrict id id id S).symm
  rw [hi]

def gather {I X U : Type} : ((I × X) × U) ≃ (I × (X × U)) := Equiv.prodAssoc _ _ _

/-- A spectator is carried inside every actual copy with the same copy label. -/
theorem copies_context {I X Y Z U V W : Type} [DecidableEq I]
    (T : Tensor ℚ X Y Z) (S : Tensor ℚ U V W) :
    Tensor.product (Tensor.directSum (fun _ : I => T)) S =
      Tensor.pullback gather gather gather (Tensor.directSum (fun _ : I => Tensor.product T S)) := by
  funext x y z
  simp only [Tensor.product, Tensor.directSum, Tensor.pullback, gather, Equiv.prodAssoc_apply]
  split_ifs <;> simp

theorem copies_context_rank {X Y Z U V W : Type} (T : Tensor ℚ X Y Z)
    (S : Tensor ℚ U V W) (L R : Nat) (h : Tensor.RankAtMost (Tensor.product T S) R) :
    Tensor.RankAtMost (Tensor.product (Tensor.directSum (fun _ : Fin L => T)) S) (L * R) := by
  rw [copies_context]
  have hc := directSum_rankAtMost (fun _ : Fin L => Tensor.product T S) R (fun _ => h)
  simpa only [Fintype.card_fin] using hc.pullback gather gather gather

theorem cyclic_copies_context_rank {X Y Z U V W : Type} (T : Tensor ℚ X Y Z)
    (S : Tensor ℚ U V W) (L R : Nat)
    (h : Tensor.RankAtMost (Tensor.product (cyclicTriple ℚ T) S) R) :
    Tensor.RankAtMost (Tensor.product (cyclicTriple ℚ (Tensor.directSum (fun _ : Fin L => T))) S)
      (L ^ 3 * R) := by
  have hcard : Fintype.card ((Fin L × Fin L) × Fin L) = L ^ 3 := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    ring
  have he := directSum_rankAtMost
    (fun _ : (Fin L × Fin L) × Fin L => Tensor.product (cyclicTriple ℚ T) S) R (fun _ => h)
  rw [hcard] at he
  -- First distribute the spectator over the cubic copy sum, then collect the
  -- three original copy labels. These are different coordinate regroupings.
  have hd := (copies_context (I := (Fin L × Fin L) × Fin L) (cyclicTriple ℚ T) S)
  have hdRank : Tensor.RankAtMost
      (Tensor.product (Tensor.directSum (fun _ : (Fin L × Fin L) × Fin L => cyclicTriple ℚ T)) S)
      (L ^ 3 * R) := by
    rw [hd]
    exact he.pullback _ _ _
  have hh := hdRank.pullback
    (fun (x : (((Fin L × X) × (Fin L × Y)) × (Fin L × Z)) × U) => (collectCopies x.1, x.2))
    (fun (y : (((Fin L × Y) × (Fin L × Z)) × (Fin L × X)) × V) => (collectCopies y.1, y.2))
    (fun (z : (((Fin L × Z) × (Fin L × X)) × (Fin L × Y)) × W) => (collectCopies z.1, z.2))
  rw [pullback_context, ← cyclic_copy_sum] at hh
  exact hh

/-- The one complete cyclic-source/spectator decomposition survives the kept
coordinate maps. The first input remains shared before separation. -/
theorem matched_context_rank {U V W : Type} (S : Tensor ℚ U V W)
    (r N m R : Nat) (hr : 0 < r)
    (h : Tensor.RankAtMost (Tensor.product (cyclicTriple ℚ (Tensor.power (source ℚ r r) N)) S) R) :
    Tensor.RankAtMost (Tensor.product (cyclicTriple ℚ (dependentMatched (Tripling.blocks r r N m))) S) R := by
  have he : dependentMatched (Tripling.blocks r r N m) = Tensor.pullback id
      (fun y => (Tripling.keptEmbeddingY r r N m hr hr y).val)
      (fun z => (Tripling.keptEmbeddingZ r r N m hr hr z).val)
      (Tensor.power (source ℚ r r) N) := by
    rw [Tripling.matched_from_kept r r N m hr hr]
    rfl
  rw [he, cyclicTriple_pullback]
  rw [← pullback_context]
  exact h.pullback _ _ _

/-- Each nonzero sample costs ell³ copies of the complete source/context pair.
There is only one input rank certificate R. -/
theorem joint_sample_context_rank {U V W : Type} [Fintype U] [Fintype V] [Fintype W]
    (S : Tensor ℚ U V W) (r N m aux R : Nat) (hr : 0 < r) (ε : ℚ) (hε : ε ≠ 0)
    (h : Tensor.RankAtMost (Tensor.product (cyclicTriple ℚ (Tensor.power (source ℚ r r) N)) S) R) :
    Tensor.RankAtMost (Tensor.product (evaluate (jointFamily r N m aux) ε) S)
      (ell (Tripling.blockCount N m) aux ^ 3 * R) := by
  classical
  let T := dependentMatched (Tripling.blocks r r N m)
  let Cpy := Tensor.directSum (fun _ : Fin (ell (Tripling.blockCount N m) aux) => T)
  let A := liftMatrix (firstCardinal (Tripling.blockCount N m) aux (X := Fin N → Fin r))
  let B := liftMatrix (dependentSecond (n := aux) (Y := Tripling.blockY r r N m) ε)
  let C := liftMatrix (dependentThird (n := aux) (Z := Tripling.blockZ r r N m) ε)
  have hc := cyclic_copies_context_rank T S (ell (Tripling.blockCount N m) aux) R
    (matched_context_rank S r N m R hr h)
  have hp := hc.restrict
    (contextMatrix (U := U) (tripleMatrix A B C))
    (contextMatrix (U := V) (tripleMatrix B C A))
    (contextMatrix (U := W) (tripleMatrix C A B))
  change Tensor.RankAtMost (Tensor.restrict _ _ _ (Tensor.product (cyclicTriple ℚ Cpy) S)) _ at hp
  rw [restrict_context, triple_restrict] at hp
  have hs : Tensor.restrict A B C Cpy =
      evaluate (dependentFamily (n := aux) (Tripling.blocks r r N m)) ε :=
    dependent_restriction _ ε hε
  rw [hs] at hp
  rw [jointFamily_evaluate]
  exact hp

/-- Embed a fixed spectator as a polynomial tensor of degree zero. -/
def constantPolynomial {U V W : Type} (S : Tensor ℚ U V W) : Tensor (Polynomial ℚ) U V W :=
  fun u v w => Polynomial.C (S u v w)

theorem evaluate_product {X Y Z U V W : Type}
    (P : Tensor (Polynomial ℚ) X Y Z) (Q : Tensor (Polynomial ℚ) U V W) (ε : ℚ) :
    evaluate (Tensor.product P Q) ε = Tensor.product (evaluate P ε) (evaluate Q ε) := by
  funext x y z
  exact Polynomial.eval_mul

theorem evaluate_constant {U V W : Type} (S : Tensor ℚ U V W) (ε : ℚ) :
    evaluate (constantPolynomial S) ε = S := by
  funext u v w
  exact Polynomial.eval_C

/-- Two polynomial transformations share one parameter. Their degrees add,
and the product is exactified once, using k*(d+e)+1 joint evaluations. -/
theorem product_exactification_rank {X Y Z U V W : Type}
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype U] [Fintype V] [Fintype W]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    [DecidableEq U] [DecidableEq V] [DecidableEq W]
    (P : Tensor (Polynomial ℚ) X Y Z) (Q : Tensor (Polynomial ℚ) U V W)
    (k d e R : Nat) (hd : ∀ x y z, (P x y z).natDegree ≤ d)
    (he : ∀ u v w, (Q u v w).natDegree ≤ e)
    (samples : ∀ a : Fin (k * (d + e) + 1), Tensor.RankAtMost
      (Tensor.product (evaluate P (node a)) (evaluate Q (node a))) R) :
    Tensor.RankAtMost (Tensor.power (Tensor.product (evaluate P 0) (evaluate Q 0)) k)
      ((k * (d + e) + 1) * R ^ k) := by
  rw [← evaluate_product]
  apply tensor_power_exactification_rank _ k (d + e) R (tensor_product_degree P Q d e hd he)
  intro a
  rw [evaluate_product]
  exact samples a

/-- Split a power of a product using explicit word-of-pairs coordinates. -/
theorem power_product_split {X Y Z U V W : Type}
    (T : Tensor ℚ X Y Z) (S : Tensor ℚ U V W) (k : Nat) :
    Tensor.pullback (Tensor.directSumPowerEquiv X U k)
      (Tensor.directSumPowerEquiv Y V k) (Tensor.directSumPowerEquiv Z W k)
      (Tensor.power (Tensor.product T S) k) =
      Tensor.product (Tensor.power T k) (Tensor.power S k) := by
  funext x y z
  change (∏ i : Fin k, T (x.1 i) (y.1 i) (z.1 i) * S (x.2 i) (y.2 i) (z.2 i)) =
    (∏ i : Fin k, T (x.1 i) (y.1 i) (z.1 i)) * ∏ i : Fin k, S (x.2 i) (y.2 i) (z.2 i)
  exact Finset.prod_mul_distrib

/-- A genuine contextual rank certificate gives the complete contextual output
power after one degree-3d exactification. -/
theorem actual_context_recipe {U V W : Type} [Fintype U] [Fintype V] [Fintype W]
    (S : Tensor ℚ U V W) (r N m aux k R : Nat) (hr : 0 < r)
    (h : Tensor.RankAtMost (Tensor.product (cyclicTriple ℚ (Tensor.power (source ℚ r r) N)) S) R) :
    Tensor.RankAtMost (Tensor.power (Tensor.product (output r N m aux hr) S) k)
      ((3 * k * localDegree N m aux + 1) *
        ell (Tripling.blockCount N m) aux ^ (3 * k) * R ^ k) := by
  classical
  have hdegree : ∀ u v w, (constantPolynomial S u v w).natDegree ≤ 0 := by
    intro u v w
    simp only [constantPolynomial, Polynomial.natDegree_C, le_refl]
  have hs : ∀ a : Fin (k * (3 * localDegree N m aux + 0) + 1), Tensor.RankAtMost
      (Tensor.product (evaluate (jointFamily r N m aux) (node a))
        (evaluate (constantPolynomial S) (node a)))
      (ell (Tripling.blockCount N m) aux ^ 3 * R) := by
    intro a
    rw [evaluate_constant]
    exact joint_sample_context_rank S r N m aux R hr (node a)
      (Separator.rationalNode_nonzero a.val) h
  have hp := product_exactification_rank (jointFamily r N m aux) (constantPolynomial S) k
    (3 * localDegree N m aux) 0 (ell (Tripling.blockCount N m) aux ^ 3 * R)
    (jointFamily_degree r N m aux) hdegree hs
  rw [jointFamily_constant, evaluate_constant] at hp
  have hf := hp.pullback
    (fun (x : Fin k → (Index N m × ((child r N hr).X × (Fin aux × Fin aux))) × U) i =>
      (sourceX r N m aux hr (x i).1, (x i).2))
    (fun (y : Fin k → (Index N m × ((child r N hr).Y × (Fin aux × Fin aux))) × V) i =>
      (sourceY r N m aux hr (y i).1, (y i).2))
    (fun (z : Fin k → (Index N m × ((child r N hr).Z × (Fin aux × Fin aux))) × W) i =>
      (sourceZ r N m aux hr (z i).1, (z i).2))
  have hid : Tensor.pullback
      (fun (x : Fin k → (Index N m × ((child r N hr).X × (Fin aux × Fin aux))) × U) i =>
        (sourceX r N m aux hr (x i).1, (x i).2))
      (fun (y : Fin k → (Index N m × ((child r N hr).Y × (Fin aux × Fin aux))) × V) i =>
        (sourceY r N m aux hr (y i).1, (y i).2))
      (fun (z : Fin k → (Index N m × ((child r N hr).Z × (Fin aux × Fin aux))) × W) i =>
        (sourceZ r N m aux hr (z i).1, (z i).2))
      (Tensor.power (Tensor.product (cyclicTriple ℚ (separated r N m aux)) S) k) =
      Tensor.power (Tensor.product (output r N m aux hr) S) k := by
    funext x y z
    change (∏ i : Fin k, _) = ∏ i : Fin k, _
    apply Finset.prod_congr rfl
    intro i _
    exact congrArg (fun t => t * S (x i).2 (y i).2 (z i).2)
      (congrFun (congrFun (congrFun (full_constant_restriction r N m aux hr)
        (x i).1) (y i).1) (z i).1)
  rw [hid] at hf
  convert hf using 1
  simp only [Nat.add_zero, mul_pow, ← pow_mul]
  ring

/-- Reindex all independent sector triples and retain the spectator power in
 every output summand. No spectator rank certificate is assumed. -/
theorem actual_context_recipe_split {U V W : Type} [Fintype U] [Fintype V] [Fintype W]
    (S : Tensor ℚ U V W) (r N m aux k R : Nat) (hr : 0 < r)
    (h : Tensor.RankAtMost (Tensor.product (cyclicTriple ℚ (Tensor.power (source ℚ r r) N)) S) R) :
    Tensor.RankAtMost (Tensor.directSum (fun _ : Fin k → Index N m =>
      Tensor.product (Tensor.power (outputBlock r N aux hr) k) (Tensor.power S k)))
      ((3 * k * localDegree N m aux + 1) *
        ell (Tripling.blockCount N m) aux ^ (3 * k) * R ^ k) := by
  classical
  have hc := actual_context_recipe S r N m aux k R hr h
  have hs := hc.pullback
    (fun (x : Fin k → Index N m × (((child r N hr).X × (Fin aux × Fin aux)) × U)) i =>
      gather.symm (x i))
    (fun (y : Fin k → Index N m × (((child r N hr).Y × (Fin aux × Fin aux)) × V)) i =>
      gather.symm (y i))
    (fun (z : Fin k → Index N m × (((child r N hr).Z × (Fin aux × Fin aux)) × W)) i =>
      gather.symm (z i))
  have hid : Tensor.pullback
      (fun (x : Fin k → Index N m × (((child r N hr).X × (Fin aux × Fin aux)) × U)) i => gather.symm (x i))
      (fun (y : Fin k → Index N m × (((child r N hr).Y × (Fin aux × Fin aux)) × V)) i => gather.symm (y i))
      (fun (z : Fin k → Index N m × (((child r N hr).Z × (Fin aux × Fin aux)) × W)) i => gather.symm (z i))
      (Tensor.power (Tensor.product (output r N m aux hr) S) k) =
      Tensor.power (Tensor.directSum (fun _ : Index N m => Tensor.product (outputBlock r N aux hr) S)) k := by
    funext x y z
    change (∏ i : Fin k, _) = ∏ i : Fin k, _
    apply Finset.prod_congr rfl
    intro i _
    have hi := congrFun (congrFun (congrFun
      (copies_context (I := Index N m) (outputBlock r N aux hr) S)
      (gather.symm (x i))) (gather.symm (y i))) (gather.symm (z i))
    simpa only [output, Tensor.pullback, Equiv.apply_symm_apply] using hi
  rw [hid] at hs
  have ht := hs.directSum_const_of_power.directSum_pullback
    (Tensor.directSumPowerEquiv ((child r N hr).X × (Fin aux × Fin aux)) U k)
    (Tensor.directSumPowerEquiv ((child r N hr).Y × (Fin aux × Fin aux)) V k)
    (Tensor.directSumPowerEquiv ((child r N hr).Z × (Fin aux × Fin aux)) W k)
  simpa only [power_product_split] using ht

/-- Nested reset-power source coordinates, with the spectator held fixed. -/
theorem actual_context_reset_split {U V W : Type} [Fintype U] [Fintype V] [Fintype W]
    (S : Tensor ℚ U V W) (r N m aux k R : Nat) (hr : 2 ≤ r)
    (h : Tensor.RankAtMost (Tensor.product ((resetFactor ℚ false r hr).power N).tensor S) R) :
    Tensor.RankAtMost (Tensor.directSum (fun _ : Fin k → Index N m =>
      Tensor.product (Tensor.product ((child r N (by omega)).power k).tensor
        (Tensor.power (auxiliary aux) k)) (Tensor.power S k)))
      ((3 * k * localDegree N m aux + 1) *
        ell (Tripling.blockCount N m) aux ^ (3 * k) * R ^ k) := by
  have hf := h
  rw [← sourceFull_eq_reset r hr] at hf
  have hc := hf.pullback
    (contextCoordinate (U := U) (sourcePowerX r N (by omega)))
    (contextCoordinate (U := V) (sourcePowerY r N (by omega)))
    (contextCoordinate (U := W) (sourcePowerZ r N (by omega)))
  change Tensor.RankAtMost (Tensor.pullback _ _ _ (Tensor.product _ S)) _ at hc
  rw [pullback_context, ← source_power_reindex] at hc
  have ho := actual_context_recipe_split S r N m aux k R (by omega) hc
  have hs := ho.directSum_pullback
    (contextCoordinate (U := Fin k → U) (poweredBlockX r N aux k (by omega)))
    (contextCoordinate (U := Fin k → V) (poweredBlockY r N aux k (by omega)))
    (contextCoordinate (U := Fin k → W) (poweredBlockZ r N aux k (by omega)))
  simpa only [contextCoordinate, pullback_context, split_powered_block] using hs

/-- Transpose the complete product; the spectator is transposed too. -/
theorem transpose_product {X Y Z U V W : Type}
    (T : Tensor ℚ X Y Z) (S : Tensor ℚ U V W) :
    transposeInputs ℚ (Tensor.product T S) =
      Tensor.product (transposeInputs ℚ T) (transposeInputs ℚ S) := rfl

theorem transpose_directSum {I X Y Z : Type} [DecidableEq I] (T : I → Tensor ℚ X Y Z) :
    transposeInputs ℚ (Tensor.directSum T) = Tensor.directSum (fun i => transposeInputs ℚ (T i)) := by
  funext x y z
  by_cases hxy : x.1 = y.1 <;> by_cases hxz : x.1 = z.1 <;>
    by_cases hyz : y.1 = z.1 <;>
    simp_all [transposeInputs, Tensor.directSum, eq_comm]

/-- The only whole-leg transpose here also transposes the spectator. This is
valid for a pooled decomposition even when the two factors have no separate
rank certificates. -/
theorem positive_context_of_negative {U V W : Type} (S : Tensor ℚ U V W)
    (r b N R : Nat) (hr : 0 < r) (hb : 0 < b)
    (h : Tensor.RankAtMost (Tensor.product ((cyclicConvolution ℚ b r hb hr).power N).tensor S) R) :
    Tensor.RankAtMost (Tensor.product ((cyclicConvolution ℚ r b hr hb).power N).tensor
      (transposeInputs ℚ S)) R := by
  let A := cyclicConvolution ℚ b r hb hr
  let B := cyclicConvolution ℚ r b hr hb
  have hn := h.pullback
    (contextCoordinate (U := U) (PowerCoordinateBridge.xCoordinates ℚ A N).symm)
    (contextCoordinate (U := V) (PowerCoordinateBridge.yCoordinates ℚ A N).symm)
    (contextCoordinate (U := W) (PowerCoordinateBridge.zCoordinates ℚ A N).symm)
  rw [pullback_context, ← PowerCoordinateBridge.tensorPower_eq_pullback] at hn
  have ht := TriplingOddSourceBridge.rank_transpose hn
  rw [transpose_product] at ht
  have hp := ht.pullback
    (fun (x : (Fin N → B.X) × V) =>
      ((fun i => (TriplingOddSourceBridge.oddY r b hr hb).symm (x.1 i)), x.2))
    (fun (y : (Fin N → B.Y) × U) =>
      ((fun i => (TriplingOddSourceBridge.oddX r b hr hb).symm (y.1 i)), y.2))
    (fun (z : (Fin N → B.Z) × W) =>
      ((fun i => (TriplingOddSourceBridge.oddZ r b hr hb).symm (z.1 i)), z.2))
  rw [pullback_context (transposeInputs ℚ (Tensor.power A.tensor N)) (transposeInputs ℚ S)
    (fun (x : Fin N → B.X) i => (TriplingOddSourceBridge.oddY r b hr hb).symm (x i))
    (fun (y : Fin N → B.Y) i => (TriplingOddSourceBridge.oddX r b hr hb).symm (y i))
    (fun (z : Fin N → B.Z) i => (TriplingOddSourceBridge.oddZ r b hr hb).symm (z i))] at hp
  have he : Tensor.pullback
      (fun (x : Fin N → B.X) i => (TriplingOddSourceBridge.oddY r b hr hb).symm (x i))
      (fun (y : Fin N → B.Y) i => (TriplingOddSourceBridge.oddX r b hr hb).symm (y i))
      (fun (z : Fin N → B.Z) i => (TriplingOddSourceBridge.oddZ r b hr hb).symm (z i))
      (transposeInputs ℚ (Tensor.power A.tensor N)) = Tensor.power B.tensor N := by
    funext x y z
    change (∏ i : Fin N, _) = ∏ i : Fin N, _
    apply Finset.prod_congr rfl
    intro i _
    have hi := congrFun (congrFun (congrFun (TriplingOddSourceBridge.odd_tensor_identity r b hr hb)
      ((TriplingOddSourceBridge.oddX r b hr hb).symm (y i)))
      ((TriplingOddSourceBridge.oddY r b hr hb).symm (x i)))
      ((TriplingOddSourceBridge.oddZ r b hr hb).symm (z i))
    simpa only [Tensor.pullback, transposeInputs, Equiv.apply_symm_apply] using hi
  rw [he] at hp
  have ho := hp.pullback
    (contextCoordinate (U := V) (PowerCoordinateBridge.xCoordinates ℚ B N))
    (contextCoordinate (U := U) (PowerCoordinateBridge.yCoordinates ℚ B N))
    (contextCoordinate (U := W) (PowerCoordinateBridge.zCoordinates ℚ B N))
  rw [pullback_context, ← PowerCoordinateBridge.fullPower_eq_pullback] at ho
  exact ho

/-- An odd step preserves the spectator's orientation by leaving the local
output transposed. It never swaps the legs of one isolated input factor. -/
theorem actual_odd_context_reset_split {U V W : Type} [Fintype U] [Fintype V] [Fintype W]
    (S : Tensor ℚ U V W) (r N m aux k R : Nat) (hr : 2 ≤ r)
    (h : Tensor.RankAtMost (Tensor.product ((resetFactor ℚ true r hr).power N).tensor S) R) :
    Tensor.RankAtMost (Tensor.directSum (fun _ : Fin k → Index N m =>
      Tensor.product (transposeInputs ℚ (Tensor.product ((child r N (by omega)).power k).tensor
        (Tensor.power (auxiliary aux) k))) (Tensor.power S k)))
      ((3 * k * localDegree N m aux + 1) *
        ell (Tripling.blockCount N m) aux ^ (3 * k) * R ^ k) := by
  have hp : Tensor.RankAtMost (Tensor.product ((resetFactor ℚ false r hr).power N).tensor
      (transposeInputs ℚ S)) R :=
    positive_context_of_negative S r (4 * r - 1) N R (by omega) (by omega) h
  have ho := actual_context_reset_split (transposeInputs ℚ S) r N m aux k R hr hp
  have ht := TriplingOddSourceBridge.rank_transpose ho
  rw [transpose_directSum] at ht
  change Tensor.RankAtMost (Tensor.directSum (fun _ : Fin k → Index N m =>
    Tensor.product (transposeInputs ℚ (Tensor.product ((child r N (by omega)).power k).tensor
      (Tensor.power (auxiliary aux) k))) (Tensor.power S k))) _ at ht
  exact ht

end
end MatrixDimensionAudit.TriplingContextBridge

#print axioms MatrixDimensionAudit.TriplingContextBridge.contextCoordinate
#print axioms MatrixDimensionAudit.TriplingContextBridge.pullback_context
#print axioms MatrixDimensionAudit.TriplingContextBridge.contextMatrix
#print axioms MatrixDimensionAudit.TriplingContextBridge.restrict_context
#print axioms MatrixDimensionAudit.TriplingContextBridge.gather
#print axioms MatrixDimensionAudit.TriplingContextBridge.copies_context
#print axioms MatrixDimensionAudit.TriplingContextBridge.copies_context_rank
#print axioms MatrixDimensionAudit.TriplingContextBridge.cyclic_copies_context_rank
#print axioms MatrixDimensionAudit.TriplingContextBridge.matched_context_rank
#print axioms MatrixDimensionAudit.TriplingContextBridge.joint_sample_context_rank
#print axioms MatrixDimensionAudit.TriplingContextBridge.constantPolynomial
#print axioms MatrixDimensionAudit.TriplingContextBridge.evaluate_product
#print axioms MatrixDimensionAudit.TriplingContextBridge.evaluate_constant
#print axioms MatrixDimensionAudit.TriplingContextBridge.product_exactification_rank
#print axioms MatrixDimensionAudit.TriplingContextBridge.power_product_split
#print axioms MatrixDimensionAudit.TriplingContextBridge.actual_context_recipe
#print axioms MatrixDimensionAudit.TriplingContextBridge.actual_context_recipe_split
#print axioms MatrixDimensionAudit.TriplingContextBridge.actual_context_reset_split
#print axioms MatrixDimensionAudit.TriplingContextBridge.transpose_product
#print axioms MatrixDimensionAudit.TriplingContextBridge.transpose_directSum
#print axioms MatrixDimensionAudit.TriplingContextBridge.positive_context_of_negative
#print axioms MatrixDimensionAudit.TriplingContextBridge.actual_odd_context_reset_split
