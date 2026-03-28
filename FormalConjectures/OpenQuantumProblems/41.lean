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
# Open Quantum Problem 41: All rank inequalities for reduced states of quadripartite quantum states

## Mathematical problem

The OQP page states the following concrete conjecture.

Given any tripartite density matrix $\rho_{ABC}$, let
$r_{AB} = \operatorname{rank}(\operatorname{Tr}_C(\rho_{ABC}))$,
$r_{AC} = \operatorname{rank}(\operatorname{Tr}_B(\rho_{ABC}))$,
and $r_{BC} = \operatorname{rank}(\operatorname{Tr}_A(\rho_{ABC}))$
denote the ranks of the corresponding reduced states.
Prove or find a counterexample to the hypothesis
$r_{AB} \le r_{AC} r_{BC}$.

In this file we formalize exactly that tripartite mixed-state statement, using finite local dimensions
$d_A$, $d_B$, $d_C$ and computational-basis matrix coordinates. Thus a state on
$H_A \otimes H_B \otimes H_C$ is represented by a matrix on the index type
$\operatorname{Fin}(d_A) \times \operatorname{Fin}(d_B) \times \operatorname{Fin}(d_C)$, and the three relevant marginals are defined by the usual
partial-trace formulas.

## Background

The OQP title refers to reduced states of quadripartite pure states because the same inequality can
be reformulated, via purification, as a rank inequality for four-party pure states. Here we keep
only the explicit OQP formulation on tripartite density matrices.

## What this file formalizes

This file is organized around the predicate `SatisfiesOQP41 ρ`, which is the inequality
$marginalRankAB\,\rho \le marginalRankAC\,\rho \cdot marginalRankBC\,\rho$.

- the definitions `partialTraceA`, `partialTraceB`, `partialTraceC` for the three two-body marginals;
- the rank abbreviations `marginalRankAB`, `marginalRankAC`, `marginalRankBC`;
- a small library of sanity-check witnesses and non-witnesses, in the same spirit as the SIC-POVM
  benchmark file:
  * product basis projectors with rank triple $(1,1,1)$;
  * a Bell pair on $AB$ with a pure ancilla on $C$, with rank triple $(1,2,2)$;
  * a GHZ-type classical mixture with rank triple $(2,2,2)$;
  * matrices that fail to be density matrices, and one explicit matrix that violates the rank
    inequality once positivity / normalization assumptions are dropped;
- the open theorem `oqp_41`, expressing the OQP question for all finite local dimensions.

## References

*Primary source list entry:*
- IQOQI Vienna Open Quantum Problems, problem 41:
  https://oqp.iqoqi.oeaw.ac.at/all-rank-inequalities-for-reduced-states-of-quadripartite-quantum-states
- Master list of open quantum problems:
  https://oqp.iqoqi.oeaw.ac.at/open-quantum-problems
- Formal Conjectures issue #3458:
  https://github.com/google-deepmind/formal-conjectures/issues/3458

### Foundational reference
- J. Cadney, M. Huber, N. Linden, and A. Winter,
  *Inequalities for the Ranks of Quantum States*,
  Linear Algebra Appl. 452, 153-171 (2014), arXiv:1308.0539.
-/
namespace OpenQuantumProblem41

/- ## Basic structures -/

/-- Computational-basis indices for the $AB$ subsystem. -/
abbrev ABIdx (dA dB : ℕ) := Fin dA × Fin dB

/-- Computational-basis indices for the $AC$ subsystem. -/
abbrev ACIdx (dA dC : ℕ) := Fin dA × Fin dC

/-- Computational-basis indices for the $BC$ subsystem. -/
abbrev BCIdx (dB dC : ℕ) := Fin dB × Fin dC

/-- Computational-basis indices for the full $ABC$ system. -/
abbrev ABCIdx (dA dB dC : ℕ) := Fin dA × Fin dB × Fin dC

/-- Matrices on $H_A \otimes H_B \otimes H_C$, expressed in the computational basis. -/
abbrev TripartiteMatrix (dA dB dC : ℕ) :=
  Matrix (ABCIdx dA dB dC) (ABCIdx dA dB dC) ℂ

/-- Matrices on $H_A \otimes H_B$. -/
abbrev BipartiteMatrixAB (dA dB : ℕ) :=
  Matrix (ABIdx dA dB) (ABIdx dA dB) ℂ

/-- Matrices on $H_A \otimes H_C$. -/
abbrev BipartiteMatrixAC (dA dC : ℕ) :=
  Matrix (ACIdx dA dC) (ACIdx dA dC) ℂ

/-- Matrices on $H_B \otimes H_C$. -/
abbrev BipartiteMatrixBC (dB dC : ℕ) :=
  Matrix (BCIdx dB dC) (BCIdx dB dC) ℂ

/-- A tripartite density matrix on $H_A \otimes H_B \otimes H_C$, represented in computational-basis
coordinates. -/
def IsDensityMatrix {dA dB dC : ℕ} (ρ : TripartiteMatrix dA dB dC) : Prop :=
  ρ.PosSemidef ∧ Matrix.trace ρ = (1 : ℂ)

/-- Partial trace over subsystem $A$. -/
def partialTraceA {dA dB dC : ℕ}
    (ρ : TripartiteMatrix dA dB dC) : BipartiteMatrixBC dB dC :=
  fun i j => ∑ a : Fin dA, ρ (a, i.1, i.2) (a, j.1, j.2)

/-- Partial trace over subsystem $B$. -/
def partialTraceB {dA dB dC : ℕ}
    (ρ : TripartiteMatrix dA dB dC) : BipartiteMatrixAC dA dC :=
  fun i j => ∑ b : Fin dB, ρ (i.1, b, i.2) (j.1, b, j.2)

/-- Partial trace over subsystem $C$. -/
def partialTraceC {dA dB dC : ℕ}
    (ρ : TripartiteMatrix dA dB dC) : BipartiteMatrixAB dA dB :=
  fun i j => ∑ c : Fin dC, ρ (i.1, i.2, c) (j.1, j.2, c)

/-- $r_{AB} = \operatorname{rank}(\operatorname{Tr}_C(\rho_{ABC}))$. -/
def marginalRankAB {dA dB dC : ℕ} (ρ : TripartiteMatrix dA dB dC) : ℕ :=
  Matrix.rank (partialTraceC ρ)

/-- $r_{AC} = \operatorname{rank}(\operatorname{Tr}_B(\rho_{ABC}))$. -/
def marginalRankAC {dA dB dC : ℕ} (ρ : TripartiteMatrix dA dB dC) : ℕ :=
  Matrix.rank (partialTraceB ρ)

/-- $r_{BC} = \operatorname{rank}(\operatorname{Tr}_A(\rho_{ABC}))$. -/
def marginalRankBC {dA dB dC : ℕ} (ρ : TripartiteMatrix dA dB dC) : ℕ :=
  Matrix.rank (partialTraceA ρ)

/-- The concrete rank inequality singled out on the OQP page. -/
def SatisfiesOQP41 {dA dB dC : ℕ} (ρ : TripartiteMatrix dA dB dC) : Prop :=
  marginalRankAB ρ ≤ marginalRankAC ρ * marginalRankBC ρ

/-- Exact marginal-rank data proving the numerical OQP41 inequality yields `SatisfiesOQP41`. -/
@[category API, AMS 15 47 81 94]
lemma satisfiesOQP41_of_ranks {dA dB dC : ℕ} {ρ : TripartiteMatrix dA dB dC}
    {rAB rAC rBC : ℕ}
    (hAB : marginalRankAB ρ = rAB)
    (hAC : marginalRankAC ρ = rAC)
    (hBC : marginalRankBC ρ = rBC)
    (hineq : rAB ≤ rAC * rBC) :
    SatisfiesOQP41 ρ := by
  simpa [SatisfiesOQP41, hAB, hAC, hBC] using hineq

/-- Exact marginal-rank data disproving the numerical OQP41 inequality yields `¬ SatisfiesOQP41`. -/
@[category API, AMS 15 47 81 94]
lemma not_satisfiesOQP41_of_ranks {dA dB dC : ℕ} {ρ : TripartiteMatrix dA dB dC}
    {rAB rAC rBC : ℕ}
    (hAB : marginalRankAB ρ = rAB)
    (hAC : marginalRankAC ρ = rAC)
    (hBC : marginalRankBC ρ = rBC)
    (hineq : ¬ rAB ≤ rAC * rBC) :
    ¬ SatisfiesOQP41 ρ := by
  simpa [SatisfiesOQP41, hAB, hAC, hBC] using hineq

/- ## Sanity checks and benchmark families -/

/-- The computational-basis rank-one projector $|a,b,c\rangle\langle a,b,c|$. -/
def basisProjectorABC {dA dB dC : ℕ}
    (a₀ : Fin dA) (b₀ : Fin dB) (c₀ : Fin dC) : TripartiteMatrix dA dB dC :=
  fun i j =>
    if i = (a₀, b₀, c₀) ∧ j = (a₀, b₀, c₀) then (1 : ℂ) else 0

/-- The explicit product state $|000\rangle\langle 000|$ on three qubits. -/
def productPure000 : TripartiteMatrix 2 2 2 :=
  basisProjectorABC 0 0 0

/-- A Bell state on $AB$ tensored with a pure basis state on $C$.
As a density matrix, this is
$\frac{1}{2} (|000\rangle + |110\rangle)(\langle 000| + \langle 110|)$. -/
def bellABWithPureC : TripartiteMatrix 2 2 2 :=
  fun i j =>
    if (i = (0, 0, 0) ∧ j = (0, 0, 0)) ∨
        (i = (0, 0, 0) ∧ j = (1, 1, 0)) ∨
        (i = (1, 1, 0) ∧ j = (0, 0, 0)) ∨
        (i = (1, 1, 0) ∧ j = (1, 1, 0))
    then (1 / 2 : ℂ) else 0

/-- The classical GHZ mixture
$\frac{1}{2}|000\rangle\langle 000| + \frac{1}{2}|111\rangle\langle 111|$. -/
def ghzClassicalMixture : TripartiteMatrix 2 2 2 :=
  fun i j =>
    if (i = (0, 0, 0) ∧ j = (0, 0, 0)) ∨
        (i = (1, 1, 1) ∧ j = (1, 1, 1))
    then (1 / 2 : ℂ) else 0

/-- The unnormalized identity on three qubits. This is positive semidefinite but has trace $8$,
so it should fail `IsDensityMatrix`. -/
def identity222 : TripartiteMatrix 2 2 2 :=
  (1 : TripartiteMatrix 2 2 2)

/-- A trace-one diagonal matrix on $2 \otimes 1 \otimes 1$ with one negative eigenvalue.
This has the right trace but should fail positivity. -/
def traceOneNonPSD211 : TripartiteMatrix 2 1 1 :=
  fun i j =>
    if i = (0, 0, 0) ∧ j = (0, 0, 0) then (2 : ℂ)
    else if i = (1, 0, 0) ∧ j = (1, 0, 0) then (-1 : ℂ)
    else 0

/-- A diagonal matrix on $2 \otimes 2 \otimes 2$ with signs depending on the parity of $(a,b)$.
Its $AB$ marginal has full rank $4$, while its $AC$ and $BC$ marginals vanish.
So it explicitly violates the OQP41 rank inequality once positivity / normalization are dropped. -/
def signedParityDiagonal222 : TripartiteMatrix 2 2 2 :=
  fun i j =>
    if i = j then
      if i.1 = i.2.1 then (1 : ℂ) else (-1 : ℂ)
    else 0

/- ## Helper lemmas -/

section Helpers

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Computational-basis vector at $i_0$. -/
def basisVec (i₀ : ι) : ι → ℂ :=
  Pi.single i₀ 1

omit [Fintype ι] in
/-- The computational-basis vector $e_{i_0}$ is nonzero. -/
@[category API, AMS 15 47 81 94]
lemma basisVec_ne_zero (i₀ : ι) : basisVec i₀ ≠ 0 := by
  intro h
  have h₀ := congr_fun h i₀
  simp [basisVec] at h₀

/-- The rank-one projector onto a computational basis vector has rank $1$. -/
@[category API, AMS 15 47 81 94]
lemma rank_basisVec_projector (i₀ : ι) :
    Matrix.rank (Matrix.vecMulVec (basisVec i₀) (star (basisVec i₀))) = 1 := by
  rw [Matrix.rank_eq_finrank_span_cols]
  have hspan :
      Submodule.span ℂ
          (Set.range (fun j => (Matrix.vecMulVec (basisVec i₀) (star (basisVec i₀))).col j)) =
        ℂ ∙ basisVec i₀ := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact Submodule.mem_span_singleton.mpr ⟨star (basisVec i₀ j), by
        ext i
        by_cases hj : j = i₀
        · subst hj
          simp [basisVec, Matrix.vecMulVec_apply, mul_comm]
        · simp [basisVec, Matrix.vecMulVec_apply, hj, mul_comm]⟩
    · rw [Submodule.span_singleton_le_iff_mem]
      exact Submodule.subset_span ⟨i₀, by
        ext i
        simp [basisVec, Matrix.vecMulVec_apply]⟩
  rw [hspan, finrank_span_singleton (basisVec_ne_zero i₀)]

end Helpers

/-- A basis projector is the outer product of the corresponding computational basis vector. -/
@[category API, AMS 15 47 81 94]
lemma basisProjectorABC_eq_vecMulVec {dA dB dC : ℕ}
    (a₀ : Fin dA) (b₀ : Fin dB) (c₀ : Fin dC) :
    basisProjectorABC a₀ b₀ c₀ =
      Matrix.vecMulVec (basisVec (a₀, b₀, c₀)) (star (basisVec (a₀, b₀, c₀))) := by
  ext i j
  by_cases hi : i = (a₀, b₀, c₀) <;> by_cases hj : j = (a₀, b₀, c₀) <;>
    simp [basisProjectorABC, basisVec, hi, hj, Matrix.vecMulVec_apply]

/-- Tracing out $C$ from a basis projector leaves the corresponding basis projector on $AB$. -/
@[category API, AMS 15 47 81 94]
lemma partialTraceC_basisProjectorABC {dA dB dC : ℕ}
    (a₀ : Fin dA) (b₀ : Fin dB) (c₀ : Fin dC) :
    partialTraceC (basisProjectorABC a₀ b₀ c₀) =
      Matrix.vecMulVec (basisVec (a₀, b₀)) (star (basisVec (a₀, b₀))) := by
  ext i j
  by_cases hi : i = (a₀, b₀)
  · subst hi
    by_cases hj : j = (a₀, b₀)
    · subst hj
      simp [partialTraceC, basisProjectorABC, basisVec, Matrix.vecMulVec_apply]
    · have hj' : ¬ (j.1 = a₀ ∧ j.2 = b₀) := by
        intro h
        apply hj
        exact Prod.ext h.1 h.2
      have hsum :
          ∑ c : Fin dC, basisProjectorABC a₀ b₀ c₀ (a₀, b₀, c) (j.1, j.2, c) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro c hc
        have hfalse : ¬ (c = c₀ ∧ j.1 = a₀ ∧ j.2 = b₀ ∧ c = c₀) := by
          intro h
          exact hj' ⟨h.2.1, h.2.2.1⟩
        simp [basisProjectorABC, Prod.mk.injEq, hfalse]
      rw [partialTraceC, hsum]
      simp [basisVec, Matrix.vecMulVec_apply, hj]
  · by_cases hj : j = (a₀, b₀)
    · subst hj
      have hi' : ¬ (i.1 = a₀ ∧ i.2 = b₀) := by
        intro h
        apply hi
        exact Prod.ext h.1 h.2
      have hsum :
          ∑ c : Fin dC, basisProjectorABC a₀ b₀ c₀ (i.1, i.2, c) (a₀, b₀, c) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro c hc
        have hfalse : ¬ (i.1 = a₀ ∧ i.2 = b₀ ∧ c = c₀) := by
          intro h
          exact hi' ⟨h.1, h.2.1⟩
        simp [basisProjectorABC, Prod.mk.injEq, hfalse]
      rw [partialTraceC, hsum]
      simp [basisVec, Matrix.vecMulVec_apply, hi]
    · have hi' : ¬ (i.1 = a₀ ∧ i.2 = b₀) := by
        intro h
        apply hi
        exact Prod.ext h.1 h.2
      have hj' : ¬ (j.1 = a₀ ∧ j.2 = b₀) := by
        intro h
        apply hj
        exact Prod.ext h.1 h.2
      have hsum :
          ∑ c : Fin dC, basisProjectorABC a₀ b₀ c₀ (i.1, i.2, c) (j.1, j.2, c) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro c hc
        simp [basisProjectorABC, Prod.mk.injEq]
        intro hi1 hi2 hc0 hj1 hj2 hc0'
        exact hi' ⟨hi1, hi2⟩
      rw [partialTraceC, hsum]
      simp [basisVec, Matrix.vecMulVec_apply, hi, hj]

/-- Tracing out $B$ from a basis projector leaves the corresponding basis projector on $AC$. -/
@[category API, AMS 15 47 81 94]
lemma partialTraceB_basisProjectorABC {dA dB dC : ℕ}
    (a₀ : Fin dA) (c₀ : Fin dC) (b₀ : Fin dB) :
    partialTraceB (basisProjectorABC a₀ b₀ c₀) =
      Matrix.vecMulVec (basisVec (a₀, c₀)) (star (basisVec (a₀, c₀))) := by
  ext i j
  by_cases hi : i = (a₀, c₀)
  · subst hi
    by_cases hj : j = (a₀, c₀)
    · subst hj
      simp [partialTraceB, basisProjectorABC, basisVec, Matrix.vecMulVec_apply]
    · have hj' : ¬ (j.1 = a₀ ∧ j.2 = c₀) := by
        intro h
        apply hj
        exact Prod.ext h.1 h.2
      have hsum :
          ∑ b : Fin dB, basisProjectorABC a₀ b₀ c₀ (a₀, b, c₀) (j.1, b, j.2) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro b hb
        have hfalse : ¬ (b = b₀ ∧ j.1 = a₀ ∧ b = b₀ ∧ j.2 = c₀) := by
          intro h
          exact hj' ⟨h.2.1, h.2.2.2⟩
        simp [basisProjectorABC, Prod.mk.injEq, hfalse]
      rw [partialTraceB, hsum]
      simp [basisVec, Matrix.vecMulVec_apply, hj]
  · by_cases hj : j = (a₀, c₀)
    · subst hj
      have hi' : ¬ (i.1 = a₀ ∧ i.2 = c₀) := by
        intro h
        apply hi
        exact Prod.ext h.1 h.2
      have hsum :
          ∑ b : Fin dB, basisProjectorABC a₀ b₀ c₀ (i.1, b, i.2) (a₀, b, c₀) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro b hb
        simp [basisProjectorABC, Prod.mk.injEq]
        intro hi1 hb0 hi2 hb0'
        exact hi' ⟨hi1, hi2⟩
      rw [partialTraceB, hsum]
      simp [basisVec, Matrix.vecMulVec_apply, hi]
    · have hi' : ¬ (i.1 = a₀ ∧ i.2 = c₀) := by
        intro h
        apply hi
        exact Prod.ext h.1 h.2
      have hj' : ¬ (j.1 = a₀ ∧ j.2 = c₀) := by
        intro h
        apply hj
        exact Prod.ext h.1 h.2
      have hsum :
          ∑ b : Fin dB, basisProjectorABC a₀ b₀ c₀ (i.1, b, i.2) (j.1, b, j.2) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro b hb
        simp [basisProjectorABC, Prod.mk.injEq]
        intro hi1 hb0 hi2 hj1 hb0' hj2
        exact hi' ⟨hi1, hi2⟩
      rw [partialTraceB, hsum]
      simp [basisVec, Matrix.vecMulVec_apply, hi, hj]

/-- Tracing out $A$ from a basis projector leaves the corresponding basis projector on $BC$. -/
@[category API, AMS 15 47 81 94]
lemma partialTraceA_basisProjectorABC {dA dB dC : ℕ}
    (b₀ : Fin dB) (c₀ : Fin dC) (a₀ : Fin dA) :
    partialTraceA (basisProjectorABC a₀ b₀ c₀) =
      Matrix.vecMulVec (basisVec (b₀, c₀)) (star (basisVec (b₀, c₀))) := by
  ext i j
  by_cases hi : i = (b₀, c₀)
  · subst hi
    by_cases hj : j = (b₀, c₀)
    · subst hj
      simp [partialTraceA, basisProjectorABC, basisVec, Matrix.vecMulVec_apply]
    · simp [partialTraceA, basisProjectorABC, basisVec, Matrix.vecMulVec_apply, hj]
  · by_cases hj : j = (b₀, c₀)
    · subst hj
      simp [partialTraceA, basisProjectorABC, basisVec, Matrix.vecMulVec_apply, hi]
    · simp [partialTraceA, basisProjectorABC, basisVec, Matrix.vecMulVec_apply, hi, hj]

/-- The unnormalized Bell vector $|000\rangle + |110\rangle$ on $ABC$. -/
def bellABCVec : ABCIdx 2 2 2 → ℂ :=
  basisVec (0, 0, 0) + basisVec (1, 1, 0)

/-- The unnormalized Bell vector $|00\rangle + |11\rangle$ on $AB$. -/
def bellABVec : ABIdx 2 2 → ℂ :=
  basisVec (0, 0) + basisVec (1, 1)

/-- The diagonal entries of the $AC$ marginal of `bellABWithPureC`. -/
def bellACDiag : ACIdx 2 2 → ℂ
  | (0, 0) => 1 / 2
  | (1, 0) => 1 / 2
  | _ => 0

/-- The diagonal entries of the $BC$ marginal of `bellABWithPureC`. -/
def bellBCDiag : BCIdx 2 2 → ℂ
  | (0, 0) => 1 / 2
  | (1, 0) => 1 / 2
  | _ => 0

/-- The diagonal entries of the $AB$ marginal of `ghzClassicalMixture`. -/
def ghzABDiag : ABIdx 2 2 → ℂ
  | (0, 0) => 1 / 2
  | (1, 1) => 1 / 2
  | _ => 0

/-- The diagonal entries of the $AC$ marginal of `ghzClassicalMixture`. -/
def ghzACDiag : ACIdx 2 2 → ℂ
  | (0, 0) => 1 / 2
  | (1, 1) => 1 / 2
  | _ => 0

/-- The diagonal entries of the $BC$ marginal of `ghzClassicalMixture`. -/
def ghzBCDiag : BCIdx 2 2 → ℂ
  | (0, 0) => 1 / 2
  | (1, 1) => 1 / 2
  | _ => 0

/-- The diagonal entries of the $AB$ marginal of `signedParityDiagonal222`. -/
def signedParityABDiag : ABIdx 2 2 → ℂ
  | (0, 0) => 2
  | (0, 1) => -2
  | (1, 0) => -2
  | (1, 1) => 2

/-- The $AC$ diagonal of the Bell witness has exactly two nonzero entries. -/
@[category API, AMS 15 47 81 94]
lemma bellACDiag_nonzero_card :
    Fintype.card {i : ACIdx 2 2 // bellACDiag i ≠ 0} = 2 := by
  classical
  let e : {i : ACIdx 2 2 // bellACDiag i ≠ 0} ≃ Fin 2 :=
    { toFun := fun i => if i.1 = (0, 0) then 0 else 1
      invFun := fun
        | 0 => ⟨(0, 0), by simp [bellACDiag]⟩
        | 1 => ⟨(1, 0), by simp [bellACDiag]⟩
      left_inv := by
        rintro ⟨⟨a, c⟩, hi⟩
        fin_cases a <;> fin_cases c <;> simp [bellACDiag] at hi ⊢
      right_inv := by intro i; fin_cases i <;> rfl }
  rw [Fintype.card_congr e]
  simp

/-- The $BC$ diagonal of the Bell witness has exactly two nonzero entries. -/
@[category API, AMS 15 47 81 94]
lemma bellBCDiag_nonzero_card :
    Fintype.card {i : BCIdx 2 2 // bellBCDiag i ≠ 0} = 2 := by
  classical
  let e : {i : BCIdx 2 2 // bellBCDiag i ≠ 0} ≃ Fin 2 :=
    { toFun := fun i => if i.1 = (0, 0) then 0 else 1
      invFun := fun
        | 0 => ⟨(0, 0), by simp [bellBCDiag]⟩
        | 1 => ⟨(1, 0), by simp [bellBCDiag]⟩
      left_inv := by
        rintro ⟨⟨b, c⟩, hi⟩
        fin_cases b <;> fin_cases c <;> simp [bellBCDiag] at hi ⊢
      right_inv := by intro i; fin_cases i <;> rfl }
  rw [Fintype.card_congr e]
  simp

/-- The $AB$ diagonal of the GHZ mixture has exactly two nonzero entries. -/
@[category API, AMS 15 47 81 94]
lemma ghzABDiag_nonzero_card :
    Fintype.card {i : ABIdx 2 2 // ghzABDiag i ≠ 0} = 2 := by
  classical
  let e : {i : ABIdx 2 2 // ghzABDiag i ≠ 0} ≃ Fin 2 :=
    { toFun := fun i => if i.1 = (0, 0) then 0 else 1
      invFun := fun
        | 0 => ⟨(0, 0), by simp [ghzABDiag]⟩
        | 1 => ⟨(1, 1), by simp [ghzABDiag]⟩
      left_inv := by
        rintro ⟨⟨a, b⟩, hi⟩
        fin_cases a <;> fin_cases b <;> simp [ghzABDiag] at hi ⊢
      right_inv := by intro i; fin_cases i <;> rfl }
  rw [Fintype.card_congr e]
  simp

/-- The $AC$ diagonal of the GHZ mixture has exactly two nonzero entries. -/
@[category API, AMS 15 47 81 94]
lemma ghzACDiag_nonzero_card :
    Fintype.card {i : ACIdx 2 2 // ghzACDiag i ≠ 0} = 2 := by
  classical
  let e : {i : ACIdx 2 2 // ghzACDiag i ≠ 0} ≃ Fin 2 :=
    { toFun := fun i => if i.1 = (0, 0) then 0 else 1
      invFun := fun
        | 0 => ⟨(0, 0), by simp [ghzACDiag]⟩
        | 1 => ⟨(1, 1), by simp [ghzACDiag]⟩
      left_inv := by
        rintro ⟨⟨a, c⟩, hi⟩
        fin_cases a <;> fin_cases c <;> simp [ghzACDiag] at hi ⊢
      right_inv := by intro i; fin_cases i <;> rfl }
  rw [Fintype.card_congr e]
  simp

/-- The $BC$ diagonal of the GHZ mixture has exactly two nonzero entries. -/
@[category API, AMS 15 47 81 94]
lemma ghzBCDiag_nonzero_card :
    Fintype.card {i : BCIdx 2 2 // ghzBCDiag i ≠ 0} = 2 := by
  classical
  let e : {i : BCIdx 2 2 // ghzBCDiag i ≠ 0} ≃ Fin 2 :=
    { toFun := fun i => if i.1 = (0, 0) then 0 else 1
      invFun := fun
        | 0 => ⟨(0, 0), by simp [ghzBCDiag]⟩
        | 1 => ⟨(1, 1), by simp [ghzBCDiag]⟩
      left_inv := by
        rintro ⟨⟨b, c⟩, hi⟩
        fin_cases b <;> fin_cases c <;> simp [ghzBCDiag] at hi ⊢
      right_inv := by intro i; fin_cases i <;> rfl }
  rw [Fintype.card_congr e]
  simp

/-- The $AB$ diagonal of the signed-parity witness has exactly four nonzero entries. -/
@[category API, AMS 15 47 81 94]
lemma signedParityABDiag_nonzero_card :
    Fintype.card {i : ABIdx 2 2 // signedParityABDiag i ≠ 0} = 4 := by
  classical
  let e : {i : ABIdx 2 2 // signedParityABDiag i ≠ 0} ≃ ABIdx 2 2 :=
    { toFun := fun i => i.1
      invFun := fun i => ⟨i, by
        rcases i with ⟨a, b⟩
        fin_cases a <;> fin_cases b <;> simp [signedParityABDiag]⟩
      left_inv := by intro i; cases i; rfl
      right_inv := by intro i; rfl }
  rw [Fintype.card_congr e]
  norm_num [ABIdx]

/-- The Bell vector on $AB$ is nonzero. -/
@[category API, AMS 15 47 81 94]
lemma bellABVec_ne_zero : bellABVec ≠ 0 := by
  intro h
  have h₀ := congr_fun h (0, 0)
  simp [bellABVec, basisVec] at h₀

/-- The normalized Bell projector on $AB$ has rank $1$. -/
@[category API, AMS 15 47 81 94]
lemma rank_half_bellABVec_projector :
    Matrix.rank ((1 / 2 : ℂ) • Matrix.vecMulVec bellABVec (star bellABVec)) = 1 := by
  rw [Matrix.rank_eq_finrank_span_cols]
  have hspan :
      Submodule.span ℂ
          (Set.range (fun j => (((1 / 2 : ℂ) • Matrix.vecMulVec bellABVec (star bellABVec))).col j)) =
        ℂ ∙ bellABVec := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact Submodule.mem_span_singleton.mpr ⟨(1 / 2 : ℂ) * star (bellABVec j), by
        ext i
        rcases j with ⟨aj, bj⟩
        rcases i with ⟨ai, bi⟩
        fin_cases aj <;> fin_cases bj <;> fin_cases ai <;> fin_cases bi <;>
          simp [bellABVec, basisVec, Matrix.vecMulVec_apply, mul_comm]⟩
    · rw [Submodule.span_singleton_le_iff_mem]
      have hmem :
          (((1 / 2 : ℂ) • Matrix.vecMulVec bellABVec (star bellABVec)).col (0, 0)) ∈
            Submodule.span ℂ
              (Set.range
                (fun j => (((1 / 2 : ℂ) • Matrix.vecMulVec bellABVec (star bellABVec))).col j)) := by
        exact Submodule.subset_span ⟨(0, 0), rfl⟩
      have hscaled :
          (2 : ℂ) • (((1 / 2 : ℂ) • Matrix.vecMulVec bellABVec (star bellABVec)).col (0, 0)) ∈
            Submodule.span ℂ
              (Set.range
                (fun j => (((1 / 2 : ℂ) • Matrix.vecMulVec bellABVec (star bellABVec))).col j)) := by
        exact Submodule.smul_mem _ _ hmem
      have hcol :
          bellABVec =
            (2 : ℂ) • (((1 / 2 : ℂ) • Matrix.vecMulVec bellABVec (star bellABVec)).col (0, 0)) := by
        ext i
        rcases i with ⟨ai, bi⟩
        fin_cases ai <;> fin_cases bi <;>
          simp [bellABVec, basisVec, Matrix.vecMulVec_apply, mul_comm]
      exact Eq.ndrec hscaled hcol.symm
  rw [hspan, finrank_span_singleton bellABVec_ne_zero]

/-- The Bell witness is the projector onto `bellABCVec`, scaled by $\frac{1}{2}$. -/
@[category API, AMS 15 47 81 94]
lemma bellABWithPureC_eq_smul_vecMulVec :
    bellABWithPureC = (1 / 2 : ℂ) • Matrix.vecMulVec bellABCVec (star bellABCVec) := by
  ext i j
  rcases i with ⟨ai, bi, ci⟩
  rcases j with ⟨aj, bj, cj⟩
  fin_cases ai <;> fin_cases bi <;> fin_cases ci <;>
    fin_cases aj <;> fin_cases bj <;> fin_cases cj <;>
    simp [bellABWithPureC, bellABCVec, basisVec, Matrix.vecMulVec_apply]

/-- Tracing out $C$ from the Bell witness gives the Bell projector on $AB$. -/
@[category API, AMS 15 47 81 94]
lemma partialTraceC_bellABWithPureC :
    partialTraceC bellABWithPureC = (1 / 2 : ℂ) • Matrix.vecMulVec bellABVec (star bellABVec) := by
  ext i j
  rcases i with ⟨ai, bi⟩
  rcases j with ⟨aj, bj⟩
  fin_cases ai <;> fin_cases bi <;> fin_cases aj <;> fin_cases bj <;>
    simp [partialTraceC, bellABWithPureC, bellABVec, basisVec, Matrix.vecMulVec_apply]

/-- Tracing out $B$ from the Bell witness gives the diagonal state `bellACDiag`. -/
@[category API, AMS 15 47 81 94]
lemma partialTraceB_bellABWithPureC :
    partialTraceB bellABWithPureC = Matrix.diagonal bellACDiag := by
  ext i j
  rcases i with ⟨ai, ci⟩
  rcases j with ⟨aj, cj⟩
  fin_cases ai <;> fin_cases ci <;> fin_cases aj <;> fin_cases cj <;>
    simp [partialTraceB, bellABWithPureC, bellACDiag]

/-- Tracing out $A$ from the Bell witness gives the diagonal state `bellBCDiag`. -/
@[category API, AMS 15 47 81 94]
lemma partialTraceA_bellABWithPureC :
    partialTraceA bellABWithPureC = Matrix.diagonal bellBCDiag := by
  ext i j
  rcases i with ⟨bi, ci⟩
  rcases j with ⟨bj, cj⟩
  fin_cases bi <;> fin_cases ci <;> fin_cases bj <;> fin_cases cj <;>
    simp [partialTraceA, bellABWithPureC, bellBCDiag]

/-- The GHZ mixture is the sum of two basis projectors, each scaled by $\frac{1}{2}$. -/
@[category API, AMS 15 47 81 94]
lemma ghzClassicalMixture_eq :
    ghzClassicalMixture =
      (1 / 2 : ℂ) • basisProjectorABC 0 0 0 + (1 / 2 : ℂ) • basisProjectorABC 1 1 1 := by
  ext i j
  rcases i with ⟨ai, bi, ci⟩
  rcases j with ⟨aj, bj, cj⟩
  fin_cases ai <;> fin_cases bi <;> fin_cases ci <;>
    fin_cases aj <;> fin_cases bj <;> fin_cases cj <;>
    simp [ghzClassicalMixture, basisProjectorABC]

/-- Tracing out $C$ from the GHZ mixture gives the diagonal state `ghzABDiag`. -/
@[category API, AMS 15 47 81 94]
lemma partialTraceC_ghzClassicalMixture :
    partialTraceC ghzClassicalMixture = Matrix.diagonal ghzABDiag := by
  ext i j
  rcases i with ⟨ai, bi⟩
  rcases j with ⟨aj, bj⟩
  fin_cases ai <;> fin_cases bi <;> fin_cases aj <;> fin_cases bj <;>
    simp [partialTraceC, ghzClassicalMixture, ghzABDiag]

/-- Tracing out $B$ from the GHZ mixture gives the diagonal state `ghzACDiag`. -/
@[category API, AMS 15 47 81 94]
lemma partialTraceB_ghzClassicalMixture :
    partialTraceB ghzClassicalMixture = Matrix.diagonal ghzACDiag := by
  ext i j
  rcases i with ⟨ai, ci⟩
  rcases j with ⟨aj, cj⟩
  fin_cases ai <;> fin_cases ci <;> fin_cases aj <;> fin_cases cj <;>
    simp [partialTraceB, ghzClassicalMixture, ghzACDiag]

/-- Tracing out $A$ from the GHZ mixture gives the diagonal state `ghzBCDiag`. -/
@[category API, AMS 15 47 81 94]
lemma partialTraceA_ghzClassicalMixture :
    partialTraceA ghzClassicalMixture = Matrix.diagonal ghzBCDiag := by
  ext i j
  rcases i with ⟨bi, ci⟩
  rcases j with ⟨bj, cj⟩
  fin_cases bi <;> fin_cases ci <;> fin_cases bj <;> fin_cases cj <;>
    simp [partialTraceA, ghzClassicalMixture, ghzBCDiag]

/-- Tracing out $C$ from the signed-parity witness gives the diagonal state `signedParityABDiag`. -/
@[category API, AMS 15 47 81 94]
lemma partialTraceC_signedParityDiagonal222 :
    partialTraceC signedParityDiagonal222 = Matrix.diagonal signedParityABDiag := by
  ext i j
  rcases i with ⟨ai, bi⟩
  rcases j with ⟨aj, bj⟩
  fin_cases ai <;> fin_cases bi <;> fin_cases aj <;> fin_cases bj <;>
    simp [partialTraceC, signedParityDiagonal222, signedParityABDiag]

/-- Tracing out $B$ from the signed-parity witness gives the zero matrix. -/
@[category API, AMS 15 47 81 94]
lemma partialTraceB_signedParityDiagonal222 :
    partialTraceB signedParityDiagonal222 = 0 := by
  ext i j
  rcases i with ⟨ai, ci⟩
  rcases j with ⟨aj, cj⟩
  fin_cases ai <;> fin_cases ci <;> fin_cases aj <;> fin_cases cj <;>
    simp [partialTraceB, signedParityDiagonal222]

/-- Tracing out $A$ from the signed-parity witness gives the zero matrix. -/
@[category API, AMS 15 47 81 94]
lemma partialTraceA_signedParityDiagonal222 :
    partialTraceA signedParityDiagonal222 = 0 := by
  ext i j
  rcases i with ⟨bi, ci⟩
  rcases j with ⟨bj, cj⟩
  fin_cases bi <;> fin_cases ci <;> fin_cases bj <;> fin_cases cj <;>
    simp [partialTraceA, signedParityDiagonal222]

/-- There are no density matrices if one of the local factors is zero-dimensional.
This is the closest analogue here to the $d = 0$ benchmark sanity check from the SIC-POVM file. -/
@[category test, AMS 15 47 81 94]
theorem noDensityMatrix_of_zero_factor {dA dB dC : ℕ}
    (h : dA = 0 ∨ dB = 0 ∨ dC = 0) :
    ¬ ∃ ρ : TripartiteMatrix dA dB dC, IsDensityMatrix ρ := by
  rcases h with rfl | rfl | rfl <;> simp [IsDensityMatrix]

/-- Any computational-basis projector is a density matrix. -/
@[category test, AMS 15 47 81 94]
theorem basisProjectorABC_isDensityMatrix {dA dB dC : ℕ}
    (a₀ : Fin dA) (b₀ : Fin dB) (c₀ : Fin dC) :
    IsDensityMatrix (basisProjectorABC a₀ b₀ c₀) := by
  rw [basisProjectorABC_eq_vecMulVec]
  constructor
  · simpa using Matrix.posSemidef_vecMulVec_self_star (basisVec (a₀, b₀, c₀))
  · simp [basisVec, Matrix.trace_vecMulVec]

/-- Any computational-basis projector has rank triple $(1,1,1)$. -/
@[category test, AMS 15 47 81 94]
theorem basisProjectorABC_ranks {dA dB dC : ℕ}
    (a₀ : Fin dA) (b₀ : Fin dB) (c₀ : Fin dC) :
    marginalRankAB (basisProjectorABC a₀ b₀ c₀) = 1 ∧
      marginalRankAC (basisProjectorABC a₀ b₀ c₀) = 1 ∧
      marginalRankBC (basisProjectorABC a₀ b₀ c₀) = 1 := by
  constructor
  · rw [marginalRankAB, partialTraceC_basisProjectorABC]
    exact rank_basisVec_projector (a₀, b₀)
  · constructor
    · rw [marginalRankAC, partialTraceB_basisProjectorABC]
      exact rank_basisVec_projector (a₀, c₀)
    · rw [marginalRankBC, partialTraceA_basisProjectorABC]
      exact rank_basisVec_projector (b₀, c₀)

/-- Any computational-basis projector satisfies the OQP41 inequality. -/
@[category test, AMS 15 47 81 94]
theorem basisProjectorABC_satisfiesOQP41 {dA dB dC : ℕ}
    (a₀ : Fin dA) (b₀ : Fin dB) (c₀ : Fin dC) :
    SatisfiesOQP41 (basisProjectorABC a₀ b₀ c₀) := by
  obtain ⟨hAB, hAC, hBC⟩ := basisProjectorABC_ranks a₀ b₀ c₀
  exact satisfiesOQP41_of_ranks hAB hAC hBC (by norm_num)

/-- The explicit product state $|000\rangle\langle 000|$ is a density matrix. -/
@[category test, AMS 15 47 81 94]
theorem productPure000_isDensityMatrix :
    IsDensityMatrix productPure000 := by
  simpa [productPure000] using
    basisProjectorABC_isDensityMatrix (0 : Fin 2) (0 : Fin 2) (0 : Fin 2)

/-- The explicit product state $|000\rangle\langle 000|$ has rank triple $(1,1,1)$. -/
@[category test, AMS 15 47 81 94]
theorem productPure000_ranks :
    marginalRankAB productPure000 = 1 ∧
      marginalRankAC productPure000 = 1 ∧
      marginalRankBC productPure000 = 1 := by
  simpa [productPure000] using
    basisProjectorABC_ranks (0 : Fin 2) (0 : Fin 2) (0 : Fin 2)

/-- The explicit product state $|000\rangle\langle 000|$ is a concrete three-qubit benchmark witness. -/
@[category test, AMS 15 47 81 94]
theorem productPure000_satisfiesOQP41 :
    IsDensityMatrix productPure000 ∧
      marginalRankAB productPure000 = 1 ∧
      marginalRankAC productPure000 = 1 ∧
      marginalRankBC productPure000 = 1 ∧
      SatisfiesOQP41 productPure000 := by
  obtain ⟨hAB, hAC, hBC⟩ := productPure000_ranks
  exact ⟨productPure000_isDensityMatrix, hAB, hAC, hBC,
    satisfiesOQP41_of_ranks hAB hAC hBC (by norm_num)⟩

/-- The Bell-pair-on-$AB$ witness is a density matrix. -/
@[category test, AMS 15 47 81 94]
theorem bellABWithPureC_isDensityMatrix :
    IsDensityMatrix bellABWithPureC := by
  rw [bellABWithPureC_eq_smul_vecMulVec]
  constructor
  · exact (Matrix.posSemidef_vecMulVec_self_star bellABCVec).smul (by positivity)
  · norm_num [bellABCVec, basisVec, Matrix.trace_vecMulVec]

/-- The Bell-pair-on-$AB$ witness has rank triple $(1,2,2)$. -/
@[category test, AMS 15 47 81 94]
theorem bellABWithPureC_ranks :
    marginalRankAB bellABWithPureC = 1 ∧
      marginalRankAC bellABWithPureC = 2 ∧
      marginalRankBC bellABWithPureC = 2 := by
  constructor
  · rw [marginalRankAB, partialTraceC_bellABWithPureC]
    exact rank_half_bellABVec_projector
  · constructor
    · rw [marginalRankAC, partialTraceB_bellABWithPureC, Matrix.rank_diagonal]
      exact bellACDiag_nonzero_card
    · rw [marginalRankBC, partialTraceA_bellABWithPureC, Matrix.rank_diagonal]
      exact bellBCDiag_nonzero_card

/-- The Bell-pair-on-$AB$ witness satisfies the OQP41 inequality. -/
@[category test, AMS 15 47 81 94]
theorem bellABWithPureC_satisfiesOQP41 :
    SatisfiesOQP41 bellABWithPureC := by
  obtain ⟨hAB, hAC, hBC⟩ := bellABWithPureC_ranks
  exact satisfiesOQP41_of_ranks hAB hAC hBC (by norm_num)

/-- The classical GHZ mixture is a density matrix. -/
@[category test, AMS 15 47 81 94]
theorem ghzClassicalMixture_isDensityMatrix :
    IsDensityMatrix ghzClassicalMixture := by
  rw [ghzClassicalMixture_eq]
  constructor
  · exact ((basisProjectorABC_isDensityMatrix (0 : Fin 2) (0 : Fin 2) (0 : Fin 2)).1.smul
        (by positivity)).add
      ((basisProjectorABC_isDensityMatrix (1 : Fin 2) (1 : Fin 2) (1 : Fin 2)).1.smul
        (by positivity))
  · rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
      (basisProjectorABC_isDensityMatrix (0 : Fin 2) (0 : Fin 2) (0 : Fin 2)).2,
      (basisProjectorABC_isDensityMatrix (1 : Fin 2) (1 : Fin 2) (1 : Fin 2)).2]
    norm_num

/-- The classical GHZ mixture has rank triple $(2,2,2)$. -/
@[category test, AMS 15 47 81 94]
theorem ghzClassicalMixture_ranks :
    marginalRankAB ghzClassicalMixture = 2 ∧
      marginalRankAC ghzClassicalMixture = 2 ∧
      marginalRankBC ghzClassicalMixture = 2 := by
  constructor
  · rw [marginalRankAB, partialTraceC_ghzClassicalMixture, Matrix.rank_diagonal]
    exact ghzABDiag_nonzero_card
  · constructor
    · rw [marginalRankAC, partialTraceB_ghzClassicalMixture, Matrix.rank_diagonal]
      exact ghzACDiag_nonzero_card
    · rw [marginalRankBC, partialTraceA_ghzClassicalMixture, Matrix.rank_diagonal]
      exact ghzBCDiag_nonzero_card

/-- The classical GHZ mixture satisfies the OQP41 inequality. -/
@[category test, AMS 15 47 81 94]
theorem ghzClassicalMixture_satisfiesOQP41 :
    SatisfiesOQP41 ghzClassicalMixture := by
  obtain ⟨hAB, hAC, hBC⟩ := ghzClassicalMixture_ranks
  exact satisfiesOQP41_of_ranks hAB hAC hBC (by norm_num)

/-- The three-qubit identity matrix is positive semidefinite. -/
@[category test, AMS 15 47 81 94]
theorem identity222_posSemidef :
    identity222.PosSemidef := by
  simpa [identity222] using (Matrix.PosSemidef.one : (1 : TripartiteMatrix 2 2 2).PosSemidef)

/-- The three-qubit identity matrix is not a density matrix because its trace is not $1$. -/
@[category test, AMS 15 47 81 94]
theorem identity222_not_isDensityMatrix :
    ¬ IsDensityMatrix identity222 := by
  intro hρ
  norm_num [IsDensityMatrix, identity222] at hρ

/-- The matrix `traceOneNonPSD211` has the correct trace $1$. -/
@[category test, AMS 15 47 81 94]
theorem traceOneNonPSD211_has_trace_one :
    Matrix.trace traceOneNonPSD211 = (1 : ℂ) := by
  simp [traceOneNonPSD211, Matrix.trace, Fintype.sum_prod_type, Fin.sum_univ_two]
  norm_num

/-- The matrix `traceOneNonPSD211` is not a density matrix because it is not positive semidefinite. -/
@[category test, AMS 15 47 81 94]
theorem traceOneNonPSD211_not_isDensityMatrix :
    ¬ IsDensityMatrix traceOneNonPSD211 := by
  rintro ⟨hPSD, htrace⟩
  have hnonneg := hPSD.re_dotProduct_nonneg (basisVec (1, 0, 0))
  norm_num [traceOneNonPSD211, basisVec, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type, Fin.sum_univ_two] at hnonneg

/-- The signed parity diagonal has rank triple $(4,0,0)$. -/
@[category test, AMS 15 47 81 94]
theorem signedParityDiagonal222_ranks :
    marginalRankAB signedParityDiagonal222 = 4 ∧
      marginalRankAC signedParityDiagonal222 = 0 ∧
      marginalRankBC signedParityDiagonal222 = 0 := by
  constructor
  · rw [marginalRankAB, partialTraceC_signedParityDiagonal222, Matrix.rank_diagonal]
    exact signedParityABDiag_nonzero_card
  · constructor
    · rw [marginalRankAC, partialTraceB_signedParityDiagonal222]
      simp
    · rw [marginalRankBC, partialTraceA_signedParityDiagonal222]
      simp

/-- The signed parity diagonal explicitly fails the OQP41 inequality.
This is a useful check that the positivity / normalization hypotheses are doing real work. -/
@[category test, AMS 15 47 81 94]
theorem signedParityDiagonal222_not_satisfiesOQP41 :
    ¬ SatisfiesOQP41 signedParityDiagonal222 := by
  obtain ⟨hAB, hAC, hBC⟩ := signedParityDiagonal222_ranks
  exact not_satisfiesOQP41_of_ranks hAB hAC hBC (by norm_num)

/-- The signed parity diagonal is also not a density matrix. -/
@[category test, AMS 15 47 81 94]
theorem signedParityDiagonal222_not_isDensityMatrix :
    ¬ IsDensityMatrix signedParityDiagonal222 := by
  intro hρ
  have htrace := hρ.2
  simp [signedParityDiagonal222, Matrix.trace, Fintype.sum_prod_type, Fin.sum_univ_two] at htrace
  norm_num at htrace

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
