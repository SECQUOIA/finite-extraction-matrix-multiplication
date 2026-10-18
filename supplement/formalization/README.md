# Lean formalization (Section 11.3 of the paper)

This directory is a Lean 4 project that formalizes a simpler rational variant of the paper's construction. Its final theorems, in `formalization/RationalAlgorithmTransportBridge.lean`, are:

```lean
theorem omega_le_nine_fourths (K : Type*) [Field K] [CharZero K] : omega K ≤ (9/4 : ℝ)

theorem algorithms_with_exponent_slack (K : Type*) [Field K] [CharZero K] (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : Nat, 1 ≤ n → ∃ P : MatrixAlgorithm K n n n,
      P.Correct ∧ (P.cost : ℝ) ≤ C * (n : ℝ)^((9/4 : ℝ)+ε)
```

They live in the namespace `MatrixDimensionAudit.RationalAlgorithmTransportBridge`. For every field `K` of characteristic zero and every `ε > 0`, division-free straight-line programs over `K` multiply `n × n` matrices with at most `C n^(9/4+ε)` additions, subtractions and multiplications, for all `n ≥ 1`. Hence `ω ≤ 9/4` over `K`.

## The arithmetic model

Programs, their cost, correctness and `omega` come from the arithmetic model of OpenAI's Lean code for the 9/4 preprint (`OAI.LinearAlgebra.MatrixMultiplication.Model`), as adapted to arbitrary fields by Sela Navot. This project uses the copy vendored in Yuval Filmus's repository, which is its only direct dependency.

- A program is a finite sequence of gates: constants, inputs, and additions, subtractions and multiplications of earlier registers. There is no division gate.
- Additions, subtractions and multiplications, including multiplication by a constant, each cost 1. Constants and inputs cost 0.
- `Correct` means that the program's output equals `A * B` for all input matrices `A` and `B`.
- `omega F` is the infimum of the admissible exponents. The model proves that this set is bounded below by 2.

From that library the proof uses only:
- the model;
- generic program constructions (padding, composition, recursive block programs);
- basic tensor definitions.

It does not use the library's own proof of the 9/4 bound.

## Relation to the paper

The formal proof follows Sections 4, 5 and 7 of the paper, with rational maps as in Section 9.1. It includes:

- Lemmas 4.1, 4.3 and 4.5 (determinant filtration, type restrictions, tripling);
- the occupations of Proposition 5.3, as the unique nonnegative rational solution of their linear system with the row identity (5.3). The formulas and bounds (5.4) and (5.5) are not formalized;
- the three parts of Lemma 9.1:
  - the rational rank decompositions of convolution tensors;
  - the polynomial separator of H. Lü (arXiv:2610.18914, Proposition 2.1), formalized over ℚ in `SeparatorInterpolationBridge.lean`, `SeparatorTensorBridge.lean` and `DependentSeparatorBridge.lean`;
  - rational exactification;
- the restriction of Proposition 7.3;
- the pooled recursion of Lemma 2.4 for `p > 2`.

It differs from the paper in three ways:

1. It clears the denominators of the occupations instead of rounding them as in Section 6.
2. It uses only the formula for the profile `F` and bounds on `log F(a,a)`, not Theorem 3.2.
3. It reaches 9/4 through limits, so it gives no explicit constants, rates or seed sides.

Apart from Lemma 9.1, nothing in Sections 8–10 is formalized. That includes Theorem 1.2, the seeds of Theorem 1.1, Proposition 11.1 and Corollary 11.2. Some modules in the closure (`DimensionArithmetic`, `GeneralFlowCore`, `GeneralRowDimension`, `JointDimensionCertificate` and others) prove arithmetic consequences of source-side bounds under stated hypotheses. The paper does not rely on them.

All proofs use only Lean's standard axioms: `propext`, `Classical.choice` and `Quot.sound`. No file uses `sorry`, `admit`, custom axioms or `native_decide`.

## Build

You need `elan`, which installs the pinned toolchain from `lean-toolchain`. The pins are:

- Lean `leanprover/lean4:v4.35.0`;
- `YuvalFilmus/matrix-multiplication-block-identities` at commit `8e38460c2c04617692a64a826b09e8995ac8717d`, subdirectory `vendor/navot`;
- Mathlib at commit `ccbef15ebdb41c2addfac682131f83c75904c3c1`.

`lake-manifest.json` pins every transitive package.

From this directory:

```sh
lake exe cache get              # download the pinned dependencies and prebuilt Mathlib files
lake build                      # build the 65 modules in formalization/
lake env lean PrintAxioms.lean  # print the endpoint statements and their axioms
```

Do not run `lake update`, which would move the pins. The dependencies need about 6 GB of disk space.

## Files

- `formalization/*.lean`: the 65 modules in the import closure of `RationalAlgorithmTransportBridge`. The module names are `formalization.<File>`.
- `lakefile.lean`, `lean-toolchain`, `lake-manifest.json`: the Lake project.
- `PrintAxioms.lean`: the axiom check above.

The development was written in a larger research repository, where these modules sit beside others not needed here. The files are copied unchanged. Their comments sometimes refer to research notes and round numbers that are not part of this supplement.

## Credits

- **Arithmetic model and generic program library:** OpenAI's Lean formalization of the 9/4 preprint, as adapted by Navot (Zenodo, doi:10.5281/zenodo.23219128). It is distributed under Apache-2.0 within Filmus's repository, which is fetched at build time and not copied here.
- **Separator:** Lü, arXiv:2610.18914.
