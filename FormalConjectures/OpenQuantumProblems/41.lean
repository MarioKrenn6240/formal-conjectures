/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjectures.Util.ProblemImports

noncomputable section
open scoped BigOperators ComplexOrder

/-!
# Open Quantum Problem 41

Core definitions for the tripartite mixed-state formulation of OQP 41,
together with statement-only sanity checks for explicit benchmark families.
-/
namespace OpenQuantumProblem41

/- ## Basic structures -/

/-- Computational-basis indices for the `AB` subsystem. -/
abbrev ABIdx (dA dB : ℕ) := Fin dA × Fin dB

/-- Computational-basis indices for the `AC` subsystem. -/
abbrev ACIdx (dA dC : ℕ) := Fin dA × Fin dC

/-- Computational-basis indices for the `BC` subsystem. -/
abbrev BCIdx (dB dC : ℕ) := Fin dB × Fin dC

/-- Computational-basis indices for the full `ABC` system. -/
abbrev ABCIdx (dA dB dC : ℕ) := Fin dA × Fin dB × Fin dC

/-- Matrices on `H_A ⊗ H_B ⊗ H_C`, expressed in the computational basis. -/
abbrev TripartiteMatrix (dA dB dC : ℕ) :=
  Matrix (ABCIdx dA dB dC) (ABCIdx dA dB dC) ℂ

/-- Matrices on `H_A ⊗ H_B`. -/
abbrev BipartiteMatrixAB (dA dB : ℕ) :=
  Matrix (ABIdx dA dB) (ABIdx dA dB) ℂ

/-- Matrices on `H_A ⊗ H_C`. -/
abbrev BipartiteMatrixAC (dA dC : ℕ) :=
  Matrix (ACIdx dA dC) (ACIdx dA dC) ℂ

/-- Matrices on `H_B ⊗ H_C`. -/
abbrev BipartiteMatrixBC (dB dC : ℕ) :=
  Matrix (BCIdx dB dC) (BCIdx dB dC) ℂ

/-- A tripartite density matrix on `H_A ⊗ H_B ⊗ H_C`, represented in
computational-basis coordinates. -/
def IsDensityMatrix {dA dB dC : ℕ} (ρ : TripartiteMatrix dA dB dC) : Prop :=
  ρ.PosSemidef ∧ Matrix.trace ρ = (1 : ℂ)

/-- Partial trace over subsystem `A`. -/
def partialTraceA {dA dB dC : ℕ}
    (ρ : TripartiteMatrix dA dB dC) : BipartiteMatrixBC dB dC :=
  fun i j => ∑ a : Fin dA, ρ (a, i.1, i.2) (a, j.1, j.2)

/-- Partial trace over subsystem `B`. -/
def partialTraceB {dA dB dC : ℕ}
    (ρ : TripartiteMatrix dA dB dC) : BipartiteMatrixAC dA dC :=
  fun i j => ∑ b : Fin dB, ρ (i.1, b, i.2) (j.1, b, j.2)

/-- Partial trace over subsystem `C`. -/
def partialTraceC {dA dB dC : ℕ}
    (ρ : TripartiteMatrix dA dB dC) : BipartiteMatrixAB dA dB :=
  fun i j => ∑ c : Fin dC, ρ (i.1, i.2, c) (j.1, j.2, c)

/-- `r_{AB} = rank(Tr_C(ρ))`. -/
def marginalRankAB {dA dB dC : ℕ} (ρ : TripartiteMatrix dA dB dC) : ℕ :=
  Matrix.rank (partialTraceC ρ)

/-- `r_{AC} = rank(Tr_B(ρ))`. -/
def marginalRankAC {dA dB dC : ℕ} (ρ : TripartiteMatrix dA dB dC) : ℕ :=
  Matrix.rank (partialTraceB ρ)

/-- `r_{BC} = rank(Tr_A(ρ))`. -/
def marginalRankBC {dA dB dC : ℕ} (ρ : TripartiteMatrix dA dB dC) : ℕ :=
  Matrix.rank (partialTraceA ρ)

/-- The concrete rank inequality singled out on the OQP page. -/
def SatisfiesOQP41 {dA dB dC : ℕ} (ρ : TripartiteMatrix dA dB dC) : Prop :=
  marginalRankAB ρ ≤ marginalRankAC ρ * marginalRankBC ρ

/- ## Sanity checks and benchmark families -/

/-- The computational-basis rank-one projector `|a,b,c⟩⟨a,b,c|`. -/
def basisProjectorABC {dA dB dC : ℕ}
    (a₀ : Fin dA) (b₀ : Fin dB) (c₀ : Fin dC) : TripartiteMatrix dA dB dC :=
  fun i j =>
    if i = (a₀, b₀, c₀) ∧ j = (a₀, b₀, c₀) then (1 : ℂ) else 0

/-- The explicit product state `|000⟩⟨000|` on three qubits. -/
def productPure000 : TripartiteMatrix 2 2 2 :=
  basisProjectorABC 0 0 0

/-- A Bell state on `AB` tensored with a pure basis state on `C`.
As a density matrix, this is
`(1 / 2) • (|000⟩ + |110⟩)(⟨000| + ⟨110|)`. -/
def bellABWithPureC : TripartiteMatrix 2 2 2 :=
  fun i j =>
    if (i = (0, 0, 0) ∧ j = (0, 0, 0)) ∨
        (i = (0, 0, 0) ∧ j = (1, 1, 0)) ∨
        (i = (1, 1, 0) ∧ j = (0, 0, 0)) ∨
        (i = (1, 1, 0) ∧ j = (1, 1, 0))
    then (1 / 2 : ℂ) else 0

/-- The classical GHZ mixture
`(1 / 2)|000⟩⟨000| + (1 / 2)|111⟩⟨111|`. -/
def ghzClassicalMixture : TripartiteMatrix 2 2 2 :=
  fun i j =>
    if (i = (0, 0, 0) ∧ j = (0, 0, 0)) ∨
        (i = (1, 1, 1) ∧ j = (1, 1, 1))
    then (1 / 2 : ℂ) else 0

/-- The unnormalized identity on three qubits. This is positive semidefinite but has trace `8`,
so it should fail `IsDensityMatrix`. -/
def identity222 : TripartiteMatrix 2 2 2 :=
  (1 : TripartiteMatrix 2 2 2)

/-- A trace-one diagonal matrix on `2 ⊗ 1 ⊗ 1` with one negative eigenvalue.
This has the right trace but should fail positivity. -/
def traceOneNonPSD211 : TripartiteMatrix 2 1 1 :=
  fun i j =>
    if i = (0, 0, 0) ∧ j = (0, 0, 0) then (2 : ℂ)
    else if i = (1, 0, 0) ∧ j = (1, 0, 0) then (-1 : ℂ)
    else 0

/-- A diagonal matrix on `2 ⊗ 2 ⊗ 2` with signs depending on the parity of `(a,b)`.
Its `AB` marginal has full rank `4`, while its `AC` and `BC` marginals vanish.
So it explicitly violates the OQP41 rank inequality once positivity / normalization are dropped. -/
def signedParityDiagonal222 : TripartiteMatrix 2 2 2 :=
  fun i j =>
    if i = j then
      if i.1 = i.2.1 then (1 : ℂ) else (-1 : ℂ)
    else 0

/-- There are no density matrices if one of the local factors is zero-dimensional.
This is the closest analogue here to the `d = 0` benchmark sanity check from the SIC-POVM file. -/
@[category test, AMS 15 47 81 94]
theorem noDensityMatrix_of_zero_factor {dA dB dC : ℕ}
    (h : dA = 0 ∨ dB = 0 ∨ dC = 0) :
    ¬ ∃ ρ : TripartiteMatrix dA dB dC, IsDensityMatrix ρ := by
  sorry

/-- Any computational-basis projector is a density matrix. -/
@[category test, AMS 15 47 81 94]
theorem basisProjectorABC_isDensityMatrix {dA dB dC : ℕ}
    (a₀ : Fin dA) (b₀ : Fin dB) (c₀ : Fin dC) :
    IsDensityMatrix (basisProjectorABC a₀ b₀ c₀) := by
  sorry

/-- Any computational-basis projector has rank triple `(1,1,1)`. -/
@[category test, AMS 15 47 81 94]
theorem basisProjectorABC_ranks {dA dB dC : ℕ}
    (a₀ : Fin dA) (b₀ : Fin dB) (c₀ : Fin dC) :
    marginalRankAB (basisProjectorABC a₀ b₀ c₀) = 1 ∧
      marginalRankAC (basisProjectorABC a₀ b₀ c₀) = 1 ∧
      marginalRankBC (basisProjectorABC a₀ b₀ c₀) = 1 := by
  sorry

/-- Any computational-basis projector satisfies the OQP41 inequality. -/
@[category test, AMS 15 47 81 94]
theorem basisProjectorABC_satisfiesOQP41 {dA dB dC : ℕ}
    (a₀ : Fin dA) (b₀ : Fin dB) (c₀ : Fin dC) :
    SatisfiesOQP41 (basisProjectorABC a₀ b₀ c₀) := by
  sorry

/-- The explicit product state `|000⟩⟨000|` is a density matrix. -/
@[category test, AMS 15 47 81 94]
theorem productPure000_isDensityMatrix :
    IsDensityMatrix productPure000 := by
  sorry

/-- The explicit product state `|000⟩⟨000|` has rank triple `(1,1,1)`. -/
@[category test, AMS 15 47 81 94]
theorem productPure000_ranks :
    marginalRankAB productPure000 = 1 ∧
      marginalRankAC productPure000 = 1 ∧
      marginalRankBC productPure000 = 1 := by
  sorry

/-- The explicit product state `|000⟩⟨000|` is a concrete three-qubit benchmark witness. -/
@[category test, AMS 15 47 81 94]
theorem productPure000_satisfiesOQP41 :
    IsDensityMatrix productPure000 ∧
      marginalRankAB productPure000 = 1 ∧
      marginalRankAC productPure000 = 1 ∧
      marginalRankBC productPure000 = 1 ∧
      SatisfiesOQP41 productPure000 := by
  sorry

/-- The Bell-pair-on-`AB` witness is a density matrix. -/
@[category test, AMS 15 47 81 94]
theorem bellABWithPureC_isDensityMatrix :
    IsDensityMatrix bellABWithPureC := by
  sorry

/-- The Bell-pair-on-`AB` witness has rank triple `(1,2,2)`. -/
@[category test, AMS 15 47 81 94]
theorem bellABWithPureC_ranks :
    marginalRankAB bellABWithPureC = 1 ∧
      marginalRankAC bellABWithPureC = 2 ∧
      marginalRankBC bellABWithPureC = 2 := by
  sorry

/-- The Bell-pair-on-`AB` witness satisfies the OQP41 inequality. -/
@[category test, AMS 15 47 81 94]
theorem bellABWithPureC_satisfiesOQP41 :
    SatisfiesOQP41 bellABWithPureC := by
  sorry

/-- The classical GHZ mixture is a density matrix. -/
@[category test, AMS 15 47 81 94]
theorem ghzClassicalMixture_isDensityMatrix :
    IsDensityMatrix ghzClassicalMixture := by
  sorry

/-- The classical GHZ mixture has rank triple `(2,2,2)`. -/
@[category test, AMS 15 47 81 94]
theorem ghzClassicalMixture_ranks :
    marginalRankAB ghzClassicalMixture = 2 ∧
      marginalRankAC ghzClassicalMixture = 2 ∧
      marginalRankBC ghzClassicalMixture = 2 := by
  sorry

/-- The classical GHZ mixture satisfies the OQP41 inequality. -/
@[category test, AMS 15 47 81 94]
theorem ghzClassicalMixture_satisfiesOQP41 :
    SatisfiesOQP41 ghzClassicalMixture := by
  sorry

/-- The three-qubit identity matrix is positive semidefinite. -/
@[category test, AMS 15 47 81 94]
theorem identity222_posSemidef :
    identity222.PosSemidef := by
  sorry

/-- The three-qubit identity matrix is not a density matrix because its trace is not `1`. -/
@[category test, AMS 15 47 81 94]
theorem identity222_not_isDensityMatrix :
    ¬ IsDensityMatrix identity222 := by
  sorry

/-- The matrix `traceOneNonPSD211` has the correct trace `1`. -/
@[category test, AMS 15 47 81 94]
theorem traceOneNonPSD211_has_trace_one :
    Matrix.trace traceOneNonPSD211 = (1 : ℂ) := by
  sorry

/-- The matrix `traceOneNonPSD211` is not a density matrix because it is not positive semidefinite. -/
@[category test, AMS 15 47 81 94]
theorem traceOneNonPSD211_not_isDensityMatrix :
    ¬ IsDensityMatrix traceOneNonPSD211 := by
  sorry

/-- The signed parity diagonal has rank triple `(4,0,0)`. -/
@[category test, AMS 15 47 81 94]
theorem signedParityDiagonal222_ranks :
    marginalRankAB signedParityDiagonal222 = 4 ∧
      marginalRankAC signedParityDiagonal222 = 0 ∧
      marginalRankBC signedParityDiagonal222 = 0 := by
  sorry

/-- The signed parity diagonal explicitly fails the OQP41 inequality.
This is a useful check that the positivity / normalization hypotheses are doing real work. -/
@[category test, AMS 15 47 81 94]
theorem signedParityDiagonal222_not_satisfiesOQP41 :
    ¬ SatisfiesOQP41 signedParityDiagonal222 := by
  sorry

/-- The signed parity diagonal is also not a density matrix. -/
@[category test, AMS 15 47 81 94]
theorem signedParityDiagonal222_not_isDensityMatrix :
    ¬ IsDensityMatrix signedParityDiagonal222 := by
  sorry

/- ## Full conjecture -/

/-- Open Quantum Problem 41 in the explicit tripartite mixed-state form stated on the OQP page. -/
@[category research open, AMS 15 47 81 94]
theorem oqp_41 :
    answer(sorry) ↔
      ∀ dA dB dC : ℕ,
        1 ≤ dA →
        1 ≤ dB →
        1 ≤ dC →
        ∀ ρ : TripartiteMatrix dA dB dC,
          IsDensityMatrix ρ → SatisfiesOQP41 ρ := by
  sorry

end OpenQuantumProblem41
