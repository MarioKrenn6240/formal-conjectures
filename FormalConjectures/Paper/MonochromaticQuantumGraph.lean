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

open scoped Matrix
open scoped NNReal

namespace PM

/-- Vertices of `K_N`. -/
abbrev V (N : Nat) := Fin N

/-- Edge label for `K_N` with endpoint indices in `Fin D`.

We *intend* to build edges only with `u < v` (so undirected edges are represented once),
and our enumeration always pairs the first vertex in an ordered list with a later vertex.
-/
structure EdgeN (N D : Nat) where
  u : V N
  v : V N
  i : Fin D
  j : Fin D
deriving DecidableEq

/-- Weights on edges. -/
abbrev WeightsN (N D : Nat) (α : Type) := EdgeN N D → α

/-- Helper: build an `EdgeN` from endpoints and endpoint indices. -/
def mkEdge {N D : Nat} (u v : V N) (i j : Fin D) : EdgeN N D :=
  ⟨u, v, i, j⟩

/-- Ordered vertex list `[0,1,2,...,N-1]`. -/
def vertices : (N : Nat) → List (V N)
  | 0 => []
  | N + 1 =>
      (0 : Fin (N + 1)) :: (vertices N).map Fin.succ

/-!
## allEqual: "all indices are equal"

We define it as a chain equality along the ordered vertex list:
ι v0 = ι v1 ∧ ι v1 = ι v2 ∧ ...
This is equivalent to "all indices equal" and is decidable.
-/

/-- Chain-equality along a list of vertices. -/
def allEqualList {N D : Nat} (ι : V N → Fin D) : List (V N) → Prop
  | [] => True
  | [_] => True
  | v :: w :: vs => ι v = ι w ∧ allEqualList ι (w :: vs)

/-- All indices equal on `Fin N` (using the canonical ordered vertex list). -/
def allEqual {N D : Nat} (ι : V N → Fin D) : Prop :=
  allEqualList (N := N) (D := D) ι (vertices N)

/-- Computable decidability for `allEqualList`. -/
def allEqualListDec {N D : Nat} (ι : V N → Fin D) :
    (L : List (V N)) → Decidable (allEqualList (N := N) (D := D) ι L)
  | [] => isTrue trivial
  | [_] => isTrue trivial
  | v :: w :: vs =>
      match (inferInstance : Decidable (ι v = ι w)) with
      | isTrue hvw =>
          match allEqualListDec ι (w :: vs) with
          | isTrue hrest => isTrue ⟨hvw, hrest⟩
          | isFalse hrest => isFalse (fun h => hrest h.2)
      | isFalse hvw =>
          isFalse (fun h => hvw h.1)

/-- Instance: `allEqualList ι L` is decidable. -/
instance {N D : Nat} (ι : V N → Fin D) (L : List (V N)) :
    Decidable (allEqualList (N := N) (D := D) ι L) :=
  allEqualListDec (N := N) (D := D) ι L

/-- Instance: `allEqual ι` is decidable. -/
instance {N D : Nat} (ι : V N → Fin D) : Decidable (allEqual (N := N) (D := D) ι) := by
  unfold allEqual
  infer_instance

/-!
## Perfect matching sum, general N
-/

/-- Auxiliary matching sum with fuel `n`. -/
def pmSumListAux {α : Type} [Semiring α] {N D : Nat}
    (W : WeightsN N D α) (ι : V N → Fin D) :
    Nat → List (V N) → α
  | 0, _ => 1
  | 1, _ => 0
  | _ + 2, [] => 1
  | _ + 2, [_] => 0
  | n + 2, v :: vs =>
      (vs.map (fun u =>
          W (mkEdge (N := N) (D := D) v u (ι v) (ι u)) *
            pmSumListAux (N := N) (D := D) W ι n (vs.erase u)
        )).sum

/-- Matching sum on a list: run the auxiliary with fuel = list length. -/
def pmSumList {α : Type} [Semiring α] {N D : Nat}
    (W : WeightsN N D α) (ι : V N → Fin D) (L : List (V N)) : α :=
  pmSumListAux (N := N) (D := D) W ι L.length L

/-- The perfect-matching sum for `K_N`: use the canonical ordered vertex list. -/
def pmSumN {α : Type} [Semiring α] (N D : Nat)
    (W : WeightsN N D α) (ι : V N → Fin D) : α :=
  pmSumList (N := N) (D := D) W ι (vertices N)

/-- The general equation system for `K_N`. -/
def EqSystemN {α : Type} [Semiring α] (N D : Nat) (W : WeightsN N D α) : Prop :=
  ∀ ι : V N → Fin D,
    pmSumN (N := N) (D := D) W ι =
      (if allEqual (N := N) (D := D) ι then (1 : α) else (0 : α))

/-!
# Witnesses & theorems (sanity checks)

These proofs are computation-heavy (`fin_cases` + `simp`), so we increase the heartbeat limit locally.
-/

/-! ## N = 4, D = 2 (works over any semiring α): witness & proof -/
section N4_D2
variable {α : Type} [Semiring α]

def Witness4_d2 : WeightsN 4 2 α :=
  fun e =>
    if e = mkEdge (N := 4) (D := 2) 0 1 0 0 then (1 : α) else
    if e = mkEdge (N := 4) (D := 2) 2 3 0 0 then (1 : α) else
    if e = mkEdge (N := 4) (D := 2) 0 2 1 1 then (1 : α) else
    if e = mkEdge (N := 4) (D := 2) 1 3 1 1 then (1 : α) else
    (0 : α)

set_option maxHeartbeats 5000000 in
@[category test, AMS 05 14 81]
theorem eqSystem4_has_solution_d2 :
    ∃ W : WeightsN 4 2 α, EqSystemN (N := 4) (D := 2) W := by
  classical
  refine ⟨Witness4_d2 (α := α), ?_⟩
  intro ι

  have h :
      ∀ a b c d : Fin 2,
        pmSumN (N := 4) (D := 2) (W := Witness4_d2 (α := α)) ![a, b, c, d] =
          (if allEqual (N := 4) (D := 2) ![a, b, c, d] then (1 : α) else (0 : α)) := by
    intro a b c d
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      simp [pmSumN, pmSumList, pmSumListAux, vertices,
        allEqual, allEqualList, Witness4_d2, mkEdge]

  have hι : ι = ![ι 0, ι 1, ι 2, ι 3] := by
    funext k
    fin_cases k <;> simp

  rw [hι]
  exact h (ι 0) (ι 1) (ι 2) (ι 3)

end N4_D2

/-! ## N = 4, D = 3 over ℂ: witness & proof -/

def Witness4_d3 : WeightsN 4 3 ℂ :=
  fun e =>
    if e = mkEdge (N := 4) (D := 3) 0 1 0 0 then (1 : ℂ) else
    if e = mkEdge (N := 4) (D := 3) 2 3 0 0 then (1 : ℂ) else
    if e = mkEdge (N := 4) (D := 3) 0 2 1 1 then (1 : ℂ) else
    if e = mkEdge (N := 4) (D := 3) 1 3 1 1 then (1 : ℂ) else
    if e = mkEdge (N := 4) (D := 3) 0 3 2 2 then (1 : ℂ) else
    if e = mkEdge (N := 4) (D := 3) 1 2 2 2 then (1 : ℂ) else
    (0 : ℂ)

set_option maxHeartbeats 5000000 in
@[category test, AMS 05 14 81]
theorem eqSystem4_has_solution_d3 :
    ∃ W : WeightsN 4 3 ℂ, EqSystemN (N := 4) (D := 3) W := by
  classical
  refine ⟨Witness4_d3, ?_⟩
  intro ι

  have h :
      ∀ a b c d : Fin 3,
        pmSumN (N := 4) (D := 3) (W := Witness4_d3) ![a, b, c, d] =
          (if allEqual (N := 4) (D := 3) ![a, b, c, d] then (1 : ℂ) else (0 : ℂ)) := by
    intro a b c d
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      simp [pmSumN, pmSumList, pmSumListAux, vertices,
        allEqual, allEqualList, Witness4_d3, mkEdge]

  have hι : ι = ![ι 0, ι 1, ι 2, ι 3] := by
    funext k
    fin_cases k <;> simp

  rw [hι]
  exact h (ι 0) (ι 1) (ι 2) (ι 3)

/-! ## N = 6, D = 2 (works over any semiring α): witness & proof -/
section N6_D2
variable {α : Type} [Semiring α]

def Witness6_d2 : WeightsN 6 2 α :=
  fun e =>
    if e = mkEdge (N := 6) (D := 2) 0 1 0 0 then (1 : α) else
    if e = mkEdge (N := 6) (D := 2) 2 3 0 0 then (1 : α) else
    if e = mkEdge (N := 6) (D := 2) 4 5 0 0 then (1 : α) else
    if e = mkEdge (N := 6) (D := 2) 0 5 1 1 then (1 : α) else
    if e = mkEdge (N := 6) (D := 2) 1 2 1 1 then (1 : α) else
    if e = mkEdge (N := 6) (D := 2) 3 4 1 1 then (1 : α) else
    (0 : α)

set_option maxHeartbeats 5000000 in
@[category test, AMS 05 14 81]
theorem eqSystem6_has_solution_d2 :
    ∃ W : WeightsN 6 2 α, EqSystemN (N := 6) (D := 2) W := by
  classical
  refine ⟨Witness6_d2 (α := α), ?_⟩
  intro ι

  have h :
      ∀ a b c d e f : Fin 2,
        pmSumN (N := 6) (D := 2) (W := Witness6_d2 (α := α)) ![a, b, c, d, e, f] =
          (if allEqual (N := 6) (D := 2) ![a, b, c, d, e, f] then (1 : α) else (0 : α)) := by
    intro a b c d e f
    fin_cases a <;> fin_cases b <;> fin_cases c <;>
    fin_cases d <;> fin_cases e <;> fin_cases f <;>
      simp [pmSumN, pmSumList, pmSumListAux, vertices,
        allEqual, allEqualList, Witness6_d2, mkEdge]

  have hι : ι = ![ι 0, ι 1, ι 2, ι 3, ι 4, ι 5] := by
    funext k
    fin_cases k <;> simp

  rw [hι]
  exact h (ι 0) (ι 1) (ι 2) (ι 3) (ι 4) (ι 5)

end N6_D2

/-!
# Known obstruction for nonnegative real weights (Bogdanov)

Informal proof (“Bogdanov's lemma”): see
https://mathoverflow.net/a/311021/531914

We record it as a `research solved` statement over `ℝ≥0`, without formalizing the proof here.
-/
@[category research solved, AMS 05 14 81]
theorem eqSystem_no_solution_nnreal_even_ge6_ge3 :
    ∀ N D : Nat,
      N ≥ 6 → Even N → D ≥ 3 →
        ¬ ∃ W : WeightsN N D ℝ≥0, EqSystemN (N := N) (D := D) W := by
  sorry

/-!
# Open conjectures (formal-conjectures style)
-/

@[category research open, AMS 05 14 81]
theorem eqSystem4_no_solution_d4 :
    answer(sorry) ↔
      ¬ ∃ W : WeightsN 4 4 ℂ, EqSystemN (N := 4) (D := 4) W := by
  sorry

@[category research open, AMS 05 14 81]
theorem eqSystem4_no_solution_ge4 :
    answer(sorry) ↔
      ∀ D : Nat, D ≥ 4 →
        ¬ ∃ W : WeightsN 4 D ℂ, EqSystemN (N := 4) (D := D) W := by
  sorry

@[category research open, AMS 05 14 81]
theorem eqSystem6_no_solution_d3 :
    answer(sorry) ↔
      ¬ ∃ W : WeightsN 6 3 ℂ, EqSystemN (N := 6) (D := 3) W := by
  sorry

@[category research open, AMS 05 14 81]
theorem eqSystem6_no_solution_ge3 :
    answer(sorry) ↔
      ∀ D : Nat, D ≥ 3 →
        ¬ ∃ W : WeightsN 6 D ℂ, EqSystemN (N := 6) (D := D) W := by
  sorry

@[category research open, AMS 05 14 81]
theorem eqSystem_no_solution_ge6_ge3 :
    answer(sorry) ↔
      ∀ N D : Nat, N ≥ 6 → D ≥ 3 →
        ¬ ∃ W : WeightsN N D ℂ, EqSystemN (N := N) (D := D) W := by
  sorry

end PM
