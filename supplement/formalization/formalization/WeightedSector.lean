import Std

/-!
Exact weighted type-sector inequality, using only Lean's standard library.

`words alphabet n` explicitly enumerates length-`n` words. `typeSector`
retains exactly the words with the same histogram as a reference word.
The main theorem counts this actual list; no multinomial inequality is
assumed. For a duplicate-free alphabet this is the usual type-sector count.
-/

namespace MatrixDimensionAudit
namespace WeightedSector

def words (alphabet : List Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | n + 1 => alphabet.flatMap (fun a => (words alphabet n).map (List.cons a))

def wordWeight (weight : Nat → Nat) (word : List Nat) : Nat :=
  (word.map weight).prod

def totalWeight (weight : Nat → Nat) (family : List (List Nat)) : Nat :=
  (family.map (wordWeight weight)).sum

def typeSector (alphabet reference : List Nat) : List (List Nat) :=
  (words alphabet reference.length).filter (fun word => decide (word.Perm reference))

def typeCount (alphabet reference : List Nat) : Nat :=
  (typeSector alphabet reference).length

def populationWord (alphabet : List Nat) (population : Nat → Nat) : List Nat :=
  alphabet.flatMap (fun a => List.replicate (population a) a)

/-- The enumeration includes exactly all words of the requested length. -/
theorem mem_words_iff (alphabet word : List Nat) (n : Nat) :
    word ∈ words alphabet n ↔ word.length = n ∧ ∀ a ∈ word, a ∈ alphabet := by
  induction n generalizing word with
  | zero =>
    cases word <;> simp [words]
  | succ n ih =>
    cases word with
    | nil => simp [words]
    | cons a tail =>
      simp [words, List.mem_flatMap, ih, and_assoc, and_left_comm, and_comm]

theorem prefixes_nodup (alphabet : List Nat) (family : List (List Nat))
    (ha : alphabet.Nodup) (hf : family.Nodup) :
    (alphabet.flatMap (fun a => family.map (List.cons a))).Nodup := by
  induction alphabet with
  | nil => simp
  | cons a tail ih =>
    obtain ⟨ha, ht⟩ := List.nodup_cons.mp ha
    rw [List.flatMap_cons, List.nodup_append]
    refine ⟨?_, ih ht, ?_⟩
    · exact List.Pairwise.map (List.cons a)
        (by intro u v hne heq; exact hne (List.cons.inj heq).2) hf
    · intro u hu v hv heq
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hu
      obtain ⟨b, hb, hv⟩ := List.mem_flatMap.mp hv
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hv
      exact ha ((List.cons.inj heq).1.symm ▸ hb)

theorem words_nodup (alphabet : List Nat) (n : Nat) (ha : alphabet.Nodup) :
    (words alphabet n).Nodup := by
  induction n with
  | zero => simp [words, List.nodup_cons]
  | succ n ih => exact prefixes_nodup alphabet _ ha ih

theorem typeSector_nodup (alphabet reference : List Nat) (ha : alphabet.Nodup) :
    (typeSector alphabet reference).Nodup := by
  exact List.Sublist.nodup (List.filter_sublist) (words_nodup alphabet _ ha)

theorem wordWeight_cons (weight : Nat → Nat) (a : Nat) (word : List Nat) :
    wordWeight weight (a :: word) = weight a * wordWeight weight word := rfl

theorem wordWeight_perm (weight : Nat → Nat) (p : left.Perm right) :
    wordWeight weight left = wordWeight weight right := by
  induction p with
  | nil => rfl
  | cons a p ih => simpa [wordWeight] using congrArg (fun n => weight a * n) ih
  | swap a b tail => simp [wordWeight, Nat.mul_left_comm]
  | trans p q hp hq => exact hp.trans hq

theorem totalWeight_append (weight : Nat → Nat) (left right : List (List Nat)) :
    totalWeight weight (left ++ right) = totalWeight weight left + totalWeight weight right := by
  simp [totalWeight, List.map_append]

theorem sum_mul_left (a : Nat) (values : List Nat) :
    (values.map (fun n => a * n)).sum = a * values.sum := by
  induction values with
  | nil => simp
  | cons n tail ih => simp [ih, Nat.mul_add]

theorem totalWeight_cons_map (weight : Nat → Nat) (a : Nat) (family : List (List Nat)) :
    totalWeight weight (family.map (List.cons a)) = weight a * totalWeight weight family := by
  simpa [totalWeight, List.map_map, Function.comp_def, wordWeight_cons] using
    sum_mul_left (weight a) (family.map (wordWeight weight))

theorem totalWeight_prefixes (weight : Nat → Nat)
    (alphabet : List Nat) (family : List (List Nat)) :
    totalWeight weight (alphabet.flatMap (fun a => family.map (List.cons a))) =
      (alphabet.map weight).sum * totalWeight weight family := by
  induction alphabet with
  | nil => simp [totalWeight]
  | cons a tail ih =>
    simp only [List.flatMap_cons, totalWeight_append, totalWeight_cons_map, ih,
      List.map_cons, List.sum_cons, Nat.add_mul]

/-- Direct distributive expansion of the weighted sum over all words. -/
theorem allWords_totalWeight (weight : Nat → Nat) (alphabet : List Nat) (n : Nat) :
    totalWeight weight (words alphabet n) = (alphabet.map weight).sum ^ n := by
  induction n with
  | zero => simp [words, totalWeight, wordWeight]
  | succ n ih =>
    rw [words, totalWeight_prefixes, ih, Nat.pow_succ, Nat.mul_comm]

theorem totalWeight_filter_le (weight : Nat → Nat)
    (predicate : List Nat → Bool) (family : List (List Nat)) :
    totalWeight weight (family.filter predicate) ≤ totalWeight weight family := by
  induction family with
  | nil => simp [totalWeight]
  | cons word tail ih =>
    cases hp : predicate word with
    | false =>
      simp only [List.filter_cons, hp, Bool.false_eq_true, ↓reduceIte,
        totalWeight, List.map_cons, List.sum_cons] at ih ⊢
      omega
    | true =>
      simp only [List.filter_cons, hp, ↓reduceIte, totalWeight,
        List.map_cons, List.sum_cons] at ih ⊢
      omega

theorem totalWeight_constant (weight : Nat → Nat) (family : List (List Nat)) (value : Nat)
    (constant : ∀ word ∈ family, wordWeight weight word = value) :
    totalWeight weight family = family.length * value := by
  induction family with
  | nil => simp [totalWeight]
  | cons word tail ih =>
    have hw := constant word (by simp)
    have ht := ih (by intro other hother; exact constant other (by simp [hother]))
    simp only [totalWeight, List.map_cons, List.sum_cons] at ht ⊢
    rw [hw, ht]
    simp [Nat.add_mul, Nat.add_comm]

/-- The filter is a genuine fixed-histogram condition. -/
theorem mem_typeSector_iff (alphabet reference word : List Nat) :
    word ∈ typeSector alphabet reference ↔
      word ∈ words alphabet reference.length ∧ ∀ a, word.count a = reference.count a := by
  simp [typeSector, List.perm_iff_count]

theorem typeSector_totalWeight (weight : Nat → Nat) (alphabet reference : List Nat) :
    totalWeight weight (typeSector alphabet reference) =
      typeCount alphabet reference * wordWeight weight reference := by
  apply totalWeight_constant
  intro word hword
  have hp : word.Perm reference := by
    have hm := (List.mem_filter.mp hword).2
    exact of_decide_eq_true hm
  exact wordWeight_perm weight hp

/-- Weighted multinomial single-type bound, proved by actual word inclusion. -/
theorem weighted_type_bound (weight : Nat → Nat) (alphabet reference : List Nat) :
    typeCount alphabet reference * wordWeight weight reference ≤
      (alphabet.map weight).sum ^ reference.length := by
  rw [← typeSector_totalWeight]
  rw [← allWords_totalWeight]
  exact totalWeight_filter_le weight _ _

theorem populationWord_length (alphabet : List Nat) (population : Nat → Nat) :
    (populationWord alphabet population).length = (alphabet.map population).sum := by
  induction alphabet with
  | nil => rfl
  | cons a tail ih => simp [populationWord, List.flatMap_cons]

theorem populationWord_count (alphabet : List Nat) (population : Nat → Nat)
    (ha : alphabet.Nodup) (a : Nat) :
    (populationWord alphabet population).count a = if a ∈ alphabet then population a else 0 := by
  induction alphabet with
  | nil => simp [populationWord]
  | cons b tail ih =>
    obtain ⟨hb, ht⟩ := List.nodup_cons.mp ha
    change (List.replicate (population b) b ++ populationWord tail population).count a = _
    rw [List.count_append, ih ht]
    by_cases heq : a = b
    · subst a
      simp [hb]
    · simp [heq, List.count_replicate, Ne.symm heq]

theorem wordWeight_replicate (weight : Nat → Nat) (a n : Nat) :
    wordWeight weight (List.replicate n a) = weight a ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change weight a * wordWeight weight (List.replicate n a) = _
    rw [ih, Nat.pow_succ, Nat.mul_comm]

theorem populationWord_weight (weight : Nat → Nat) (alphabet : List Nat)
    (population : Nat → Nat) :
    wordWeight weight (populationWord alphabet population) =
      (alphabet.map (fun a => weight a ^ population a)).prod := by
  induction alphabet with
  | nil => rfl
  | cons a tail ih =>
    change wordWeight weight (List.replicate (population a) a ++ populationWord tail population) = _
    simp only [wordWeight, List.map_append, List.prod_append] at ih ⊢
    change wordWeight weight (List.replicate (population a) a) * _ = _
    rw [wordWeight_replicate, ih]
    rfl

/-- The bound in population-product notation, for an arbitrary finite alphabet. -/
theorem weighted_population_bound (weight population : Nat → Nat) (alphabet : List Nat) :
    typeCount alphabet (populationWord alphabet population) *
        (alphabet.map (fun a => weight a ^ population a)).prod ≤
      (alphabet.map weight).sum ^ (alphabet.map population).sum := by
  have h := weighted_type_bound weight alphabet (populationWord alphabet population)
  rw [populationWord_weight, populationWord_length] at h
  exact h

/-- The form used when child profiles sum to arity times the parent profile. -/
theorem weighted_profile_bound (weight population : Nat → Nat) (alphabet : List Nat)
    (arity parentProfile : Nat)
    (profileIdentity : (alphabet.map weight).sum = arity * parentProfile) :
    typeCount alphabet (populationWord alphabet population) *
        (alphabet.map (fun a => weight a ^ population a)).prod ≤
      arity ^ (alphabet.map population).sum *
        parentProfile ^ (alphabet.map population).sum := by
  have h := weighted_population_bound weight population alphabet
  rw [profileIdentity, Nat.mul_pow] at h
  exact h

/-- No division or positivity is needed, including zero weights and empty types. -/
theorem unweighted_type_bound (alphabet reference : List Nat) :
    typeCount alphabet reference ≤ alphabet.length ^ reference.length := by
  have h := weighted_type_bound (fun _ => 1) alphabet reference
  have hp : ∀ word : List Nat, wordWeight (fun _ => 1) word = 1 := by
    intro word
    induction word with
    | nil => rfl
    | cons a tail ih => simpa only [wordWeight_cons, Nat.one_mul] using ih
  have hs : (alphabet.map (fun _ => 1)).sum = alphabet.length := by
    clear h
    induction alphabet with
    | nil => rfl
    | cons a tail ih => simp [ih, Nat.add_comm]
  simpa [hp, hs] using h

end WeightedSector
end MatrixDimensionAudit

#print axioms MatrixDimensionAudit.WeightedSector.allWords_totalWeight
#print axioms MatrixDimensionAudit.WeightedSector.mem_words_iff
#print axioms MatrixDimensionAudit.WeightedSector.mem_typeSector_iff
#print axioms MatrixDimensionAudit.WeightedSector.weighted_type_bound
#print axioms MatrixDimensionAudit.WeightedSector.weighted_population_bound
#print axioms MatrixDimensionAudit.WeightedSector.weighted_profile_bound
#print axioms MatrixDimensionAudit.WeightedSector.typeSector_nodup
#print axioms MatrixDimensionAudit.WeightedSector.unweighted_type_bound
