import formalization.FamilyRelativeExponentLimitBridge

/-! Coefficient transport of actual division-free programs and rational exponent bounds. -/
namespace MatrixDimensionAudit.RationalAlgorithmTransportBridge
open scoped BigOperators
open OAI.MatrixMultiplication.Arithmetic
noncomputable section
variable {F K : Type*} [Field F] [Field K]
variable {Input Register : Type*}

/-- Change only constant coefficients; retain inputs and register references. -/
def mapGate (h : F →+* K) : Gate F Input Register → Gate K Input Register
  | .constant c => .constant (h c)
  | .input i => .input i
  | .add i j => .add i j
  | .sub i j => .sub i j
  | .mul i j => .mul i j

theorem mapGate_cost (h : F →+* K) (g : Gate F Input Register) :
    (mapGate h g).cost = g.cost := by cases g <;> rfl

theorem mapGate_id (g : Gate F Input Register) : mapGate (RingHom.id F) g = g := by
  cases g <;> rfl

theorem mapGate_eval (h : F →+* K) (g : Gate F Input Register)
    (inputs : Input → F) (registers : Register → F) :
    (mapGate h g).eval (fun i => h (inputs i)) (fun j => h (registers j)) =
      h (g.eval inputs registers) := by
  cases g <;> simp [mapGate,Gate.eval]

/-- The transported program has exactly the same finite register count. -/
def mapProgram (h : F →+* K) : {r : Nat} → Program F Input r → Program K Input r
  | _, .nil => .nil
  | _, .step p g => .step (mapProgram h p) (mapGate h g)

theorem mapProgram_cost (h : F →+* K) {r : Nat} (p : Program F Input r) :
    (mapProgram h p).cost = p.cost := by
  induction p with
  | nil => rfl
  | step p g ih => simp only [mapProgram,Program.cost_step,mapGate_cost,ih]

theorem mapProgram_id {r : Nat} (p : Program F Input r) :
    mapProgram (RingHom.id F) p = p := by
  induction p with
  | nil => rfl
  | step p g ih => simp only [mapProgram,ih,mapGate_id]

theorem mapProgram_eval (h : F →+* K) {r : Nat} (p : Program F Input r)
    (inputs : Input → F) : ∀ i,
    (mapProgram h p).eval (fun j => h (inputs j)) i = h (p.eval inputs i) := by
  induction p with
  | nil => intro i; exact Fin.elim0 i
  | @step r p g ih =>
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change (mapGate h g).eval (fun j => h (inputs j))
        ((mapProgram h p).eval (fun j => h (inputs j))) = h (g.eval inputs (p.eval inputs))
      rw [show (mapProgram h p).eval (fun j => h (inputs j)) =
        (fun j => h (p.eval inputs j)) from funext ih]
      exact mapGate_eval h g inputs (p.eval inputs)
    · exact ih j

/-- A gate as a polynomial in the original input coordinates. -/
def gatePolynomial (g : Gate F Input Register)
    (registers : Register → MvPolynomial Input F) : MvPolynomial Input F :=
  match g with
  | .constant c => MvPolynomial.C c
  | .input i => MvPolynomial.X i
  | .add i j => registers i + registers j
  | .sub i j => registers i - registers j
  | .mul i j => registers i * registers j

/-- Symbolic semantics retain the same register indexing as the actual program. -/
def programPolynomial : {r : Nat} → Program F Input r → Fin r → MvPolynomial Input F
  | _, .nil => Fin.elim0
  | _, .step p g => Fin.cases (gatePolynomial g (programPolynomial p)) (programPolynomial p)

theorem eval₂_gatePolynomial (h : F →+* K) (x : Input → K)
    (g : Gate F Input Register) (registers : Register → MvPolynomial Input F) :
    MvPolynomial.eval₂ h x (gatePolynomial g registers) =
      (mapGate h g).eval x (fun i => MvPolynomial.eval₂ h x (registers i)) := by
  cases g <;> simp [gatePolynomial,mapGate,Gate.eval]

theorem eval₂_programPolynomial (h : F →+* K) (x : Input → K)
    {r : Nat} (p : Program F Input r) : ∀ i,
    MvPolynomial.eval₂ h x (programPolynomial p i) = (mapProgram h p).eval x i := by
  induction p with
  | nil => intro i; exact Fin.elim0 i
  | @step r p g ih =>
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change MvPolynomial.eval₂ h x (gatePolynomial g (programPolynomial p)) =
        (mapGate h g).eval x ((mapProgram h p).eval x)
      rw [eval₂_gatePolynomial]
      congr 1
      exact funext ih
    · exact ih j

/-- Preserve the actual output registers and every operation cost. -/
def mapMatrixAlgorithm (h : F →+* K) {a b c : Nat}
    (P : MatrixAlgorithm F a b c) : MatrixAlgorithm K a b c :=
  ⟨P.registers, mapProgram h P.program, P.output⟩

theorem mapMatrixAlgorithm_cost (h : F →+* K) {a b c : Nat}
    (P : MatrixAlgorithm F a b c) : (mapMatrixAlgorithm h P).cost = P.cost :=
  mapProgram_cost h P.program

/-- Correctness over an infinite source field is a polynomial identity, not
merely an identity on the image of a field homomorphism. -/
theorem matrixAlgorithm_polynomial_correct [Infinite F] {a b c : Nat}
    (P : MatrixAlgorithm F a b c) (hP : P.Correct) (i : Fin a) (k : Fin c) :
    programPolynomial P.program (P.output i k) =
      ∑ j : Fin b, MvPolynomial.X (.inl (i,j)) * MvPolynomial.X (.inr (j,k)) := by
  apply MvPolynomial.funext
  intro x
  let A : Matrix (Fin a) (Fin b) F := fun i j => x (.inl (i,j))
  let B : Matrix (Fin b) (Fin c) F := fun j k => x (.inr (j,k))
  have hx : matrixInputs A B = x := by
    funext t
    rcases t with ⟨i,j⟩ | ⟨j,k⟩ <;> rfl
  have hp := (MatrixAlgorithm.correct_iff_entries P).mp hP A B i k
  rw [hx] at hp
  simpa [MvPolynomial.eval,eval₂_programPolynomial,mapProgram_id,A,B] using hp

/-- A genuinely correct source program remains correct at arbitrary target
inputs. Polynomial extensionality supplies the step beyond rational inputs. -/
theorem mapMatrixAlgorithm_correct [Infinite F] (h : F →+* K) {a b c : Nat}
    (P : MatrixAlgorithm F a b c) (hP : P.Correct) : (mapMatrixAlgorithm h P).Correct := by
  apply (MatrixAlgorithm.correct_iff_entries (mapMatrixAlgorithm h P)).mpr
  intro A B i k
  have hp := congrArg (MvPolynomial.eval₂ h (matrixInputs A B))
    (matrixAlgorithm_polynomial_correct P hP i k)
  simpa [mapMatrixAlgorithm,eval₂_programPolynomial,matrixInputs] using hp

/-- Every rational arithmetic algorithm transports with unchanged cost. -/
def rationalAlgorithm (K : Type*) [Field K] [CharZero K] {a b c : Nat}
    (P : MatrixAlgorithm ℚ a b c) : MatrixAlgorithm K a b c :=
  mapMatrixAlgorithm (Rat.castHom K) P

theorem rationalAlgorithm_cost (K : Type*) [Field K] [CharZero K] {a b c : Nat}
    (P : MatrixAlgorithm ℚ a b c) : (rationalAlgorithm K P).cost = P.cost :=
  mapMatrixAlgorithm_cost _ P

theorem rationalAlgorithm_correct (K : Type*) [Field K] [CharZero K] {a b c : Nat}
    (P : MatrixAlgorithm ℚ a b c) (hP : P.Correct) : (rationalAlgorithm K P).Correct :=
  mapMatrixAlgorithm_correct _ P hP

/-- Transfer the actual size-indexed programs and keep the same uniform bound. -/
theorem admissibleExponent_transport (K : Type*) [Field K] [CharZero K] (p : ℝ)
    (hp : AdmissibleExponent ℚ p) : AdmissibleExponent K p := by
  intro ε hε
  obtain ⟨C,hC,hprograms⟩ := hp ε hε
  refine ⟨C,hC,?_⟩
  intro n hn
  obtain ⟨P,hP,hcost⟩ := hprograms n hn
  exact ⟨rationalAlgorithm K P,rationalAlgorithm_correct K P hP,
    by simpa only [rationalAlgorithm_cost] using hcost⟩

theorem nine_fourths_admissible (K : Type*) [Field K] [CharZero K] :
    AdmissibleExponent K (9/4 : ℝ) :=
  admissibleExponent_transport K _ FamilyRelativeExponentLimitBridge.nine_fourths_admissible

theorem omega_le_nine_fourths (K : Type*) [Field K] [CharZero K] :
    omega K ≤ (9/4 : ℝ) :=
  omega_le_of_admissibleExponent (nine_fourths_admissible K)

theorem algorithms_with_exponent_slack (K : Type*) [Field K] [CharZero K]
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : Nat, 1 ≤ n → ∃ P : MatrixAlgorithm K n n n,
      P.Correct ∧ (P.cost : ℝ) ≤ C * (n : ℝ)^((9/4 : ℝ)+ε) :=
  nine_fourths_admissible K ε hε

end
end MatrixDimensionAudit.RationalAlgorithmTransportBridge
