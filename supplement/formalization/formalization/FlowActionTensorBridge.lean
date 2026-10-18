import formalization.DeterminantSplitRecipeBridge
import formalization.TriplingSectorModeBridge

/-! Population-expanded flow actions and their actual determinant histogram sectors. -/
namespace MatrixDimensionAudit.FlowActionTensorBridge
open GeneralRowSector WeightedSector DeterminantTensorBridge DeterminantSplitRecipeBridge
open scoped BigOperators
noncomputable section

/-- Descending state order agrees with increasing determinant depth. -/
def depthState (a : Action r) (j : Fin (a.h + 1)) : ℕ := a.x + a.h - 2 * j.val

def actionCounts (a : Action r) : Fin (a.h + 1) → ℕ := fun j => a.population (depthState a j)

def actionColumn (a : Action r) : ℕ := r - 1 + a.x

theorem action_column_legal (a : Action r) (hr : 2 ≤ r) : a.h + 1 ≤ actionColumn a := by
  have hh := a.h_upper
  unfold actionColumn
  omega

theorem depthState_injective (a : Action r) : Function.Injective (depthState a) := by
  intro j k he
  have hh := a.h_upper
  have hj := j.isLt
  have hk := k.isLt
  apply Fin.ext
  unfold depthState at he
  omega

/-- List and function enumeration agree in the same order. -/
theorem ofFn_nat_map {β : Type} (f : ℕ → β) (n : ℕ) :
    List.ofFn (fun i : Fin n => f i.val) = (List.range n).map f := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ', List.range_succ]
      simpa using congrArg (fun l => l ++ [f n]) ih

theorem children_ofFn (a : Action r) : a.children = List.ofFn (depthState a) := by
  exact (ofFn_nat_map (fun j => a.x + a.h - 2 * j) (a.h + 1)).symm

theorem depthState_mem (a : Action r) (j : Fin (a.h + 1)) : depthState a j ∈ a.children := by
  rw [children_ofFn]
  exact List.mem_ofFn.mpr ⟨j, rfl⟩

/-- Every action uses exactly the sum of its child populations. -/
theorem action_counts_sum (a : Action r) : ∑ j, actionCounts a j = a.width := by
  rw [Action.width, children_ofFn]
  simp only [List.map_ofFn, actionCounts]
  exact (Fin.sum_ofFn _).symm

theorem output_length (a : Action r) : a.output.length = a.width :=
  populationWord_length a.children a.population

/-- Histogram counts of a function agree with counts in its generated list. -/
theorem count_ofFn {α : Type} [DecidableEq α] {n : ℕ} (f : Fin n → α) (a : α) :
    (List.ofFn f).count a = ∑ i, if f i = a then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, Fin.sum_univ_succ]
      rw [List.count_cons, ih]
      simp only [beq_iff_eq]
      exact Nat.add_comm _ _

def encode (a : Action r) (w : Fin a.width → Fin (a.h + 1)) : List ℕ :=
  List.ofFn (fun i => depthState a (w i))

theorem encode_count (a : Action r) (w : Fin a.width → Fin (a.h + 1)) (j : Fin (a.h + 1)) :
    (encode a w).count (depthState a j) = histogram w j := by
  simp only [encode, count_ofFn, (depthState_injective a).eq_iff, histogram]

/-- The actual list-based sector condition is exactly the determinant depth histogram. -/
theorem encode_mem_iff (a : Action r) (w : Fin a.width → Fin (a.h + 1)) :
    encode a w ∈ typeSector a.children a.output ↔ histogram w = actionCounts a := by
  rw [mem_typeSector_iff]
  have hwords : encode a w ∈ words a.children a.output.length := by
    rw [mem_words_iff]
    constructor
    · simp [encode, output_length]
    · intro s hs
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hs
      exact depthState_mem a (w i)
  simp only [hwords, true_and]
  constructor
  · intro he
    funext j
    rw [← encode_count a w j, he]
    simp only [Action.output, populationWord_count _ _ a.children_nodup, depthState_mem, ite_true]
    rfl
  · intro he s
    by_cases hs : s ∈ a.children
    · rw [children_ofFn] at hs
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hs
      rw [encode_count, he]
      simp [Action.output, populationWord_count _ _ a.children_nodup, depthState_mem, actionCounts]
    · have hn : s ∉ encode a w := by
        intro hm
        obtain ⟨i, hi⟩ := List.mem_ofFn.mp hm
        exact hs (hi ▸ depthState_mem a (w i))
      simp [List.count_eq_zero.mpr hn, Action.output,
        populationWord_count _ _ a.children_nodup, hs]

/-- A finite type of precisely the existing list-sector members. -/
abbrev ActionSector (a : Action r) := {w : List ℕ // w ∈ (typeSector a.children a.output).toFinset}

def actionSectorMap (a : Action r) : Word a.h a.width (actionCounts a) → ActionSector a :=
  fun w => ⟨encode a w.val, List.mem_toFinset.mpr ((encode_mem_iff a w.val).mpr w.property)⟩

theorem actionSectorMap_injective (a : Action r) : Function.Injective (actionSectorMap a) := by
  intro w v he
  apply Subtype.ext
  have hl : encode a w.val = encode a v.val := congrArg Subtype.val he
  have hf := List.ofFn_inj.mp hl
  funext i
  exact depthState_injective a (congrFun hf i)

/-- Every original state-word sector is encoded by an actual depth word. -/
theorem actionSectorMap_surjective (a : Action r) : Function.Surjective (actionSectorMap a) := by
  intro w
  have hm := List.mem_toFinset.mp w.property
  have hw := (mem_typeSector_iff a.children a.output w.val).mp hm
  obtain ⟨hlen, hsupp⟩ := (mem_words_iff a.children w.val a.output.length).mp hw.1
  have hlen' : w.val.length = a.width := hlen.trans (output_length a)
  have hf : ∀ i : Fin a.width, ∃ j, depthState a j =
      w.val[i.val]'(by rw [hlen']; exact i.isLt) := by
    intro i
    have hc := hsupp _ (List.getElem_mem (l := w.val) (n := i.val) (by rw [hlen']; exact i.isLt))
    have hc' : w.val[i.val] ∈ List.ofFn (depthState a) := by
      simpa only [children_ofFn a] using hc
    exact List.mem_ofFn.mp hc'
  let f : Fin a.width → Fin (a.h + 1) := fun i => Classical.choose (hf i)
  have he : encode a f = w.val := by
    apply List.ext_getElem
    · simpa [encode] using hlen'.symm
    · intro i hi hj
      have hs := Classical.choose_spec (hf ⟨i, by simpa [encode] using hi⟩)
      simpa [encode, f] using hs
  have hhist : histogram f = actionCounts a := (encode_mem_iff a f).mp (he ▸ hm)
  refine ⟨⟨f, hhist⟩, ?_⟩
  exact Subtype.ext he

/-- Full finite-sector equivalence, rather than an assumed equality of counts. -/
def actionSectorEquiv (a : Action r) : ActionSector a ≃ Word a.h a.width (actionCounts a) :=
  (Equiv.ofBijective (actionSectorMap a)
    ⟨actionSectorMap_injective a, actionSectorMap_surjective a⟩).symm

/-- The scalar flow count is the actual local determinant block count. -/
theorem action_sector_count (a : Action r) : a.count = wordCount a.h a.width (actionCounts a) := by
  have he := Fintype.card_congr (actionSectorEquiv a)
  simpa only [ActionSector, Fintype.card_coe, List.toFinset_card_of_nodup a.sector_nodup,
    wordCount, Action.count, typeCount] using he


/-- The row's natural labels and the tensor restriction's constructors have the same order. -/
def labelCode : TriplingRestrictionBridge.Label → ℕ
  | .left => 0
  | .middle => 1
  | .right => 2

theorem labelCode_injective : Function.Injective labelCode := by
  intro a b he
  cases a <;> cases b <;> simp_all [labelCode]

theorem labelCode_mem (j : TriplingRestrictionBridge.Label) : labelCode j ∈ [0, 1, 2] := by
  cases j <;> simp [labelCode]

theorem labelCode_middle (j : TriplingRestrictionBridge.Label) :
    labelCode j = 1 ↔ j = .middle := by
  cases j <;> simp [labelCode]

theorem labelCode_covers {s : ℕ} (hs : s ∈ [0, 1, 2]) :
    ∃ j, labelCode j = s := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl
  · exact ⟨.left, rfl⟩
  · exact ⟨.middle, rfl⟩
  · exact ⟨.right, rfl⟩

def encodeTripling {Z : ℕ} (w : Fin Z → TriplingRestrictionBridge.Label) : List ℕ :=
  List.ofFn (fun i => labelCode (w i))

theorem encodeTripling_middle {Z : ℕ} (w : Fin Z → TriplingRestrictionBridge.Label) :
    (encodeTripling w).count 1 = TriplingRestrictionBridge.middleCount w := by
  rw [encodeTripling, count_ofFn]
  simp only [labelCode_middle, TriplingRestrictionBridge.middleCount,
    TriplingRestrictionBridge.middlePositions, Finset.card_filter]

/-- The row's existing tripling list condition is the actual tensor sector condition. -/
theorem encodeTripling_mem_iff {Z : ℕ} (w : Fin Z → TriplingRestrictionBridge.Label) :
    encodeTripling w ∈ RowTwoSectorProfile.triplingWords Z ↔
      TriplingRestrictionBridge.middleCount w = TriplingSectorModeBridge.mode Z := by
  have hw : encodeTripling w ∈ words [0, 1, 2] Z := by
    rw [mem_words_iff]
    constructor
    · simp [encodeTripling]
    · intro s hs
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hs
      exact labelCode_mem (w i)
  simp only [RowTwoSectorProfile.triplingWords, List.mem_filter, hw, true_and,
    beq_iff_eq, encodeTripling_middle, TriplingSectorModeBridge.mode]

abbrev RowTriplingSector (Z : ℕ) := {w : List ℕ // w ∈ (RowTwoSectorProfile.triplingWords Z).toFinset}

def rowTriplingMap (Z : ℕ) :
    TriplingRestrictionBridge.Word Z (TriplingSectorModeBridge.mode Z) → RowTriplingSector Z :=
  fun w => ⟨encodeTripling w.val, List.mem_toFinset.mpr ((encodeTripling_mem_iff w.val).mpr w.property)⟩

theorem rowTriplingMap_injective (Z : ℕ) : Function.Injective (rowTriplingMap Z) := by
  intro w v he
  apply Subtype.ext
  have hl : encodeTripling w.val = encodeTripling v.val := congrArg Subtype.val he
  have hf := List.ofFn_inj.mp hl
  funext i
  exact labelCode_injective (congrFun hf i)

theorem rowTriplingMap_surjective (Z : ℕ) : Function.Surjective (rowTriplingMap Z) := by
  intro w
  have hm := List.mem_toFinset.mp w.property
  have hw := (List.mem_filter.mp hm).1
  obtain ⟨hlen, hsupp⟩ := (mem_words_iff [0, 1, 2] w.val Z).mp hw
  have hf : ∀ i : Fin Z, ∃ j, labelCode j =
      w.val[i.val]'(by rw [hlen]; exact i.isLt) := by
    intro i
    exact labelCode_covers (hsupp _ (List.getElem_mem (l := w.val) (n := i.val)
      (by rw [hlen]; exact i.isLt)))
  let f : Fin Z → TriplingRestrictionBridge.Label := fun i => Classical.choose (hf i)
  have he : encodeTripling f = w.val := by
    apply List.ext_getElem
    · simpa [encodeTripling] using hlen.symm
    · intro i hi hj
      have hs := Classical.choose_spec (hf ⟨i, by simpa [encodeTripling] using hi⟩)
      simpa [encodeTripling, f] using hs
  have hmid := (encodeTripling_mem_iff f).mp (he ▸ hm)
  refine ⟨⟨f, hmid⟩, ?_⟩
  exact Subtype.ext he

/-- The reset-sector equivalence also retains every original word. -/
def rowTriplingEquiv (Z : ℕ) :
    RowTriplingSector Z ≃ TriplingRestrictionBridge.Word Z (TriplingSectorModeBridge.mode Z) :=
  (Equiv.ofBijective (rowTriplingMap Z) ⟨rowTriplingMap_injective Z, rowTriplingMap_surjective Z⟩).symm

theorem triplingWords_nodup (Z : ℕ) : (RowTwoSectorProfile.triplingWords Z).Nodup := by
  apply List.Nodup.filter
  exact words_nodup [0, 1, 2] Z (by decide)

/-- The row's scalar reset count is exactly the actual maximizing tensor block count. -/
theorem row_tripling_count (Z : ℕ) :
    GeneralRowSector.triplingCount Z =
      TriplingSectorCountBridge.count Z (TriplingSectorModeBridge.mode Z) := by
  have he := Fintype.card_congr (rowTriplingEquiv Z)
  simpa only [RowTriplingSector, Fintype.card_coe, List.toFinset_card_of_nodup (triplingWords_nodup Z),
    TriplingSectorCountBridge.count, GeneralRowSector.triplingCount, RowTwoSectorProfile.triplingCount] using he


/-- The action child column is exactly the column used by the tensor bridge. -/
theorem action_child_column (a : Action r) (hr : 2 ≤ r) (j : Fin (a.h + 1)) :
    actionColumn a + a.h - 2 * j.val = r - 1 + depthState a j := by
  have hh := a.h_upper
  have hj := j.isLt
  unfold actionColumn depthState
  omega

theorem action_count_factorial (a : Action r) :
    a.count = a.width.factorial / ∏ j, (actionCounts a j).factorial := by
  rw [action_sector_count]
  exact wordCount_factorial _ _ _ (action_counts_sum a)

theorem action_count_pos (a : Action r) : 0 < a.count := by
  rw [action_sector_count, wordCount_multinomial, ite_eq_left (action_counts_sum a)]
  exact Nat.multinomial_pos _ _

theorem row_tripling_count_choose (Z : ℕ) :
    GeneralRowSector.triplingCount Z = Z.choose ((Z + 1) / 3) * 2 ^ (Z - (Z + 1) / 3) := by
  rw [row_tripling_count, TriplingSectorCountBridge.count_eq_choose]
  rfl

theorem row_tripling_count_pos (Z : ℕ) : 0 < GeneralRowSector.triplingCount Z := by
  rw [row_tripling_count]
  exact TriplingSectorModeBridge.count_pos (TriplingSectorModeBridge.mode_le Z)

/-- Matched auxiliary dimension, with positivity supplied by the actual sector count. -/
def countedSeparator (M : ℕ) (hM : 0 < M) : FreeAuxiliaryBridge.Separator where
  blocks := M
  auxiliary := M
  localCopies := M + M - 1
  blocks_pos := hM
  auxiliary_pos := hM
  local_bound := Nat.le_refl _

def actionSeparator (a : Action r) : FreeAuxiliaryBridge.Separator :=
  countedSeparator a.count (action_count_pos a)

def triplingSeparator (Z : ℕ) : FreeAuxiliaryBridge.Separator :=
  countedSeparator (GeneralRowSector.triplingCount Z) (row_tripling_count_pos Z)

/-- Zero-width actions and zero resets contribute their valid one-sector relation. -/
def rowSeparators (actions : List (Action r)) (Z : ℕ) : List FreeAuxiliaryBridge.Separator :=
  actions.map actionSeparator ++ [triplingSeparator Z]

theorem row_separator_count (actions : List (Action r)) (Z : ℕ) :
    FreeAuxiliaryBridge.blockCount (rowSeparators actions Z) = actualSectorCount actions Z := by
  simp [FreeAuxiliaryBridge.blockCount, rowSeparators, actionSeparator, triplingSeparator,
    countedSeparator, actualSectorCount, totalCount, List.map_map, Function.comp_def]

theorem separator_count_append (a b : List FreeAuxiliaryBridge.Separator) :
    FreeAuxiliaryBridge.blockCount (a ++ b) =
      FreeAuxiliaryBridge.blockCount a * FreeAuxiliaryBridge.blockCount b := by
  simp [FreeAuxiliaryBridge.blockCount, List.map_append, List.prod_append]

def lowerSeparators : {n : ℕ} → AllRowProfile.LowerRows K n → List FreeAuxiliaryBridge.Separator
  | _, .nil => []
  | _, .cons row tail => rowSeparators row.actions row.Z ++ lowerSeparators tail

theorem lower_separator_count (rows : AllRowProfile.LowerRows K n) :
    FreeAuxiliaryBridge.blockCount (lowerSeparators rows) = rows.count := by
  induction rows with
  | nil => rfl
  | cons row tail ih =>
      rw [lowerSeparators, separator_count_append, row_separator_count, ih]
      rfl

def familySeparators (family : AllRowProfile.Family n K) : List FreeAuxiliaryBridge.Separator :=
  rowSeparators family.top.actions family.top.Z ++ lowerSeparators family.lower

/-- The count_eq premise of the existing global scalar interface is now derived from actual sectors. -/
theorem family_separator_count (family : AllRowProfile.Family n K) :
    FreeAuxiliaryBridge.blockCount (familySeparators family) = family.count := by
  rw [familySeparators, separator_count_append, row_separator_count, lower_separator_count]
  rfl

end
end MatrixDimensionAudit.FlowActionTensorBridge
