/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Derivatives of matrix-valued functions

A function `A : 𝕜 → Matrix m n F` has derivative `A'` exactly when each entry `A · i j` has
derivative `A' i j` (`hasDerivWithinAt_matrix`, and `hasDerivAt_matrix` for `HasDerivAt`).
Through the entries, the two notions agree as they do for normed spaces
(`hasDerivWithinAt_matrix_univ`, `HasDerivAt.matrix_hasDerivWithinAt`). From this we get the
derivatives of a constant (`hasDerivWithinAt_matrix_const`) and of a transpose
(`HasDerivWithinAt.matrix_transpose`), and the product rule for products of possibly
rectangular matrices with entries in a normed `𝕜`-algebra (`HasDerivWithinAt.matrix_mul`, and
`HasDerivAt.matrix_mul_const`, `HasDerivAt.matrix_const_mul` for a constant factor). A function
that a shift of the variable multiplies by a constant matrix, `Z (r + a) = Z r * g`, has
derivative `Z' * g` at `t + a` if it has derivative `Z'` at `t`
(`HasDerivAt.matrix_of_forall_add_eq_mul`). For
square matrices over a complete field, the derivative of the inverse at an invertible value is
`-X⁻¹ X' X⁻¹` (`HasDerivWithinAt.matrix_inv`), from Mathlib's `hasFDerivAt_ringInverse`.

Matrices carry their default topology, that of functions `m → n → F`; no matrix norm is needed,
except inside the proof of `HasDerivWithinAt.matrix_inv`, which reads the matrices in the `L^∞`
operator norm `Matrix.linftyOpNormedRing` to apply `hasFDerivAt_ringInverse`.
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

/-- A matrix-valued function has derivative `A'` within `univ` at `t` exactly when it has
derivative `A'` at `t`: the matrix form of `hasDerivWithinAt_univ`. -/
theorem hasDerivWithinAt_matrix_univ {A : 𝕜 → Matrix m n F} {A' : Matrix m n F} :
    HasDerivWithinAt A A' Set.univ t ↔ HasDerivAt A A' t :=
  hasDerivWithinAt_matrix.trans <| (forall₂_congr fun _ _ ↦ hasDerivWithinAt_univ).trans
    hasDerivAt_matrix.symm

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

/-- **Product rule** with a constant right factor, for matrix-valued functions with entries in a
normed `𝕜`-algebra: `(A C)' = A' C`. -/
theorem HasDerivAt.matrix_mul_const {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕜 𝔸] [Fintype m]
    {A : 𝕜 → Matrix l m 𝔸} {A' : Matrix l m 𝔸} (hA : HasDerivAt A A' t) (C : Matrix m n 𝔸) :
    HasDerivAt (fun r ↦ A r * C) (A' * C) t := by
  have h := (hasDerivWithinAt_matrix_univ.2 hA).matrix_mul (hasDerivWithinAt_matrix_const C _ t)
  rwa [Matrix.mul_zero, add_zero, hasDerivWithinAt_matrix_univ] at h

/-- **Product rule** with a constant left factor, for matrix-valued functions with entries in a
normed `𝕜`-algebra: `(C B)' = C B'`. -/
theorem HasDerivAt.matrix_const_mul {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕜 𝔸] [Fintype m]
    {B : 𝕜 → Matrix m n 𝔸} {B' : Matrix m n 𝔸} (hB : HasDerivAt B B' t) (C : Matrix l m 𝔸) :
    HasDerivAt (fun r ↦ C * B r) (C * B') t := by
  have h := (hasDerivWithinAt_matrix_const C _ t).matrix_mul (hasDerivWithinAt_matrix_univ.2 hB)
  rwa [Matrix.zero_mul, zero_add, hasDerivWithinAt_matrix_univ] at h

/-- If a shift of the variable multiplies a matrix-valued function by a constant matrix,
`Z (r + a) = Z r * g` for all `r`, and `Z` has derivative `Z'` at `t`, then `Z` has derivative
`Z' * g` at `t + a`. -/
theorem HasDerivAt.matrix_of_forall_add_eq_mul {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕜 𝔸]
    [Fintype m] {Z : 𝕜 → Matrix l m 𝔸} {Z' : Matrix l m 𝔸} {g : Matrix m m 𝔸} {a : 𝕜}
    (hg : ∀ r, Z (r + a) = Z r * g) (hZ : HasDerivAt Z Z' t) : HasDerivAt Z (Z' * g) (t + a) := by
  have hs : HasDerivAt (fun r ↦ Z (r - a)) Z' (t + a) := hasDerivAt_matrix.2 fun i j ↦
    HasDerivAt.comp_sub_const (f := fun r ↦ Z r i j) (t + a) a
      (by simpa using hasDerivAt_matrix.1 hZ i j)
  convert hs.matrix_mul_const g using 1
  exact funext fun r ↦ by rw [← hg, sub_add_cancel]

/-- **Derivative of the inverse** of a matrix-valued function, at a point where the value is
invertible: `(X⁻¹)' = -X⁻¹ X' X⁻¹`. -/
theorem HasDerivWithinAt.matrix_inv [CompleteSpace 𝕜] [Fintype n] [DecidableEq n]
    {X : 𝕜 → Matrix n n 𝕜} {X' : Matrix n n 𝕜}
    (hX : HasDerivWithinAt X X' s t) (ht : IsUnit (X t)) :
    HasDerivWithinAt (fun r ↦ (X r)⁻¹) (-((X t)⁻¹ * X' * (X t)⁻¹)) s t := by
  -- Mathlib's derivative of `Ring.inverse` needs a normed ring structure; we choose the
  -- `L^∞` operator norm. It induces the default topology of matrices, so `hX` and the goal,
  -- stated for that topology, are read in this norm as they are.
  let _ : NormedRing (Matrix n n 𝕜) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra 𝕜 (Matrix n n 𝕜) := Matrix.linftyOpNormedAlgebra
  have : @CompleteSpace (Matrix n n 𝕜) PseudoMetricSpace.toUniformSpace :=
    FiniteDimensional.completeSpace 𝕜 _
  obtain ⟨u, hu⟩ := ht
  have hi := (hasFDerivAt_ringInverse (𝕜 := 𝕜) u).comp_hasDerivWithinAt_of_eq t hX hu
  simp only [Matrix.nonsing_inv_eq_ringInverse, ← hu, Ring.inverse_unit]
  rwa [neg_apply, ContinuousLinearMap.mulLeftRight_apply] at hi

end
