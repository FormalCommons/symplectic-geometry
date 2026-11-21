/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Topology.Instances.Matrix

/-!
# Derivatives of matrix-valued functions

A function `A : 𝕜 → Matrix m n F` has derivative `A'` exactly when each entry `A · i j` has
derivative `A' i j` (`hasDerivWithinAt_matrix`, and `hasDerivAt_matrix` for `HasDerivAt`).
Through the entries, a derivative at `t` is one within every set
(`HasDerivAt.matrix_hasDerivWithinAt`), as for normed spaces. From this we get the derivatives of
a constant (`hasDerivWithinAt_matrix_const`) and of a transpose
(`HasDerivWithinAt.matrix_transpose`), and the product rule for products of possibly rectangular
matrices with entries in a normed `𝕜`-algebra (`HasDerivWithinAt.matrix_mul`).

Matrices carry their default topology, that of functions `m → n → F`; no matrix norm is needed.
The names follow `Continuous.matrix_elem`, `Continuous.matrix_transpose` and
`Continuous.matrix_mul`.
-/

public section

open Matrix

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {F : Type*} [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] {l m n : Type*} [Finite n] {s : Set 𝕜} {t : 𝕜}

/-- A matrix-valued function has derivative `A'` within `s` at `t` if and only if each of its
entries has the corresponding entry of `A'` as derivative. -/
theorem hasDerivWithinAt_matrix {A : 𝕜 → Matrix m n F} {A' : Matrix m n F} :
    HasDerivWithinAt A A' s t ↔ ∀ i j, HasDerivWithinAt (fun r ↦ A r i j) (A' i j) s t := by
  have := Fintype.ofFinite n
  -- `Matrix m n F` has no `NormedAddCommGroup` instance of its own, so we read the goal on the
  -- function type `m → n → F` that it unfolds to, where `hasDerivWithinAt_pi` applies.
  change HasDerivWithinAt (F := m → n → F) A A' s t ↔ _
  exact hasDerivWithinAt_pi.trans (forall_congr' fun _ ↦ hasDerivWithinAt_pi)

/-- A matrix-valued function has derivative `A'` at `t` if and only if each of its entries has the
corresponding entry of `A'` as derivative. -/
theorem hasDerivAt_matrix {A : 𝕜 → Matrix m n F} {A' : Matrix m n F} :
    HasDerivAt A A' t ↔ ∀ i j, HasDerivAt (fun r ↦ A r i j) (A' i j) t := by
  have := Fintype.ofFinite n
  -- As in `hasDerivWithinAt_matrix`, we read the goal on `m → n → F`, where `hasDerivAt_pi`
  -- applies.
  change HasDerivAt (F := m → n → F) A A' t ↔ _
  exact hasDerivAt_pi.trans (forall_congr' fun _ ↦ hasDerivAt_pi)

/-- A matrix-valued function with derivative `A'` at `t` has derivative `A'` within every set at
`t`: the matrix form of `HasDerivAt.hasDerivWithinAt`. -/
theorem HasDerivAt.matrix_hasDerivWithinAt {A : 𝕜 → Matrix m n F} {A' : Matrix m n F}
    (hA : HasDerivAt A A' t) : HasDerivWithinAt A A' s t :=
  hasDerivWithinAt_matrix.2 fun i j ↦ (hasDerivAt_matrix.1 hA i j).hasDerivWithinAt

/-- The entries of a differentiable matrix-valued function are differentiable. -/
theorem HasDerivWithinAt.matrix_elem {A : 𝕜 → Matrix m n F} {A' : Matrix m n F}
    (hA : HasDerivWithinAt A A' s t) (i : m) (j : n) :
    HasDerivWithinAt (fun r ↦ A r i j) (A' i j) s t :=
  hasDerivWithinAt_matrix.1 hA i j

/-- A constant matrix-valued function has derivative `0`. -/
theorem hasDerivWithinAt_matrix_const (C : Matrix m n F) (s : Set 𝕜) (t : 𝕜) :
    HasDerivWithinAt (fun _ ↦ C) 0 s t :=
  hasDerivWithinAt_matrix.2 fun i j ↦ hasDerivWithinAt_const t s (C i j)

/-- The derivative of the transpose is the transpose of the derivative. -/
theorem HasDerivWithinAt.matrix_transpose [Finite m] {A : 𝕜 → Matrix m n F} {A' : Matrix m n F}
    (hA : HasDerivWithinAt A A' s t) : HasDerivWithinAt (fun r ↦ (A r)ᵀ) A'ᵀ s t :=
  hasDerivWithinAt_matrix.2 fun i j ↦ hA.matrix_elem j i

/-- **Product rule** for matrix-valued functions with entries in a normed `𝕜`-algebra:
`(A B)' = A' B + A B'`. -/
theorem HasDerivWithinAt.matrix_mul {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕜 𝔸] [Fintype m]
    {A : 𝕜 → Matrix l m 𝔸} {B : 𝕜 → Matrix m n 𝔸} {A' : Matrix l m 𝔸} {B' : Matrix m n 𝔸}
    (hA : HasDerivWithinAt A A' s t) (hB : HasDerivWithinAt B B' s t) :
    HasDerivWithinAt (fun r ↦ A r * B r) (A' * B t + A t * B') s t := by
  refine hasDerivWithinAt_matrix.2 fun i j ↦ ?_
  simpa only [Matrix.mul_apply, Matrix.add_apply, ← Finset.sum_add_distrib] using
    HasDerivWithinAt.fun_sum (u := Finset.univ) fun k _ ↦
      (hA.matrix_elem i k).fun_mul (hB.matrix_elem k j)

end
