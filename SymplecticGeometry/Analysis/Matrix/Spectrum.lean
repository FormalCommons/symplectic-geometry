/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Matrix.Spectrum
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Coordinates
import TauCeti.Analysis.Matrix.Spectrum

/-!
# A Hermitian matrix in the coordinates of its eigenvector basis

For a Hermitian matrix `A` over `ℝ` or `ℂ`, Mathlib's `Matrix.IsHermitian.eigenvectorBasis` is an
orthonormal basis of `EuclideanSpace 𝕜 n` of eigenvectors of `A`, with eigenvalues
`λ = hA.eigenvalues`. Write `x_i` for the coordinates of `x` in that basis. This file reads `A` in
these coordinates: `A` multiplies `x_i` by `λ i`, the quadratic form `re ⟪A x, x⟫` is
`∑ i, λ i * ‖x_i‖ ^ 2`, and `x` lies in the sum of the eigenspaces of the eigenvalues `λ i` with
`x_i ≠ 0`.

The action of `A` on its eigenvectors is Tau Ceti's
`Matrix.IsHermitian.toEuclideanLin_eigenvectorBasis`. The coordinate formula is Tau Ceti's
`OrthonormalBasis.repr_apply_of_eigenbasis` for that basis, and the quadratic form is read off
Tau Ceti's `Matrix.IsHermitian.inner_toEuclideanLin_sum_smul_eigenvectorBasis`.

## Main results

* `Matrix.IsHermitian.repr_toEuclideanLin`: the coordinates of `A x` are `λ i * x_i`.
* `Matrix.IsHermitian.re_inner_toEuclideanLin_self`: `re ⟪A x, x⟫ = ∑ i, λ i * ‖x_i‖ ^ 2`.
* `Matrix.IsHermitian.mem_iSup_eigenspace`: if every `λ i` with `x_i ≠ 0` lies in a set `S`,
  then `x` lies in the sum of the eigenspaces of `A` for the eigenvalues in `S`.
-/

public section

open Finset
open scoped InnerProductSpace

namespace Matrix.IsHermitian

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜] {A : Matrix n n 𝕜}
  (hA : A.IsHermitian)
include hA

/-- The coordinates of `A x` in the eigenvector basis of a Hermitian matrix `A` are those of `x`
multiplied by the eigenvalues. -/
theorem repr_toEuclideanLin (x : EuclideanSpace 𝕜 n) (i : n) :
    hA.eigenvectorBasis.repr (toEuclideanLin A x) i =
      hA.eigenvalues i * hA.eigenvectorBasis.repr x i :=
  hA.eigenvectorBasis.repr_apply_of_eigenbasis _ hA.toEuclideanLin_eigenvectorBasis x i

/-- The quadratic form of a Hermitian matrix `A` in its eigenvector basis:
`re ⟪A x, x⟫ = ∑ i, λ i * ‖x_i‖ ^ 2`, with `λ i` the eigenvalues and `x_i` the coordinates of `x`
in the eigenvector basis. -/
theorem re_inner_toEuclideanLin_self (x : EuclideanSpace 𝕜 n) :
    RCLike.re ⟪toEuclideanLin A x, x⟫_𝕜 =
      ∑ i, hA.eigenvalues i * ‖hA.eigenvectorBasis.repr x i‖ ^ 2 := by
  rw [← inner_conj_symm, RCLike.conj_re]
  conv_lhs => rw [← hA.eigenvectorBasis.sum_repr x]
  rw [hA.inner_toEuclideanLin_sum_smul_eigenvectorBasis, map_sum]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [← RCLike.ofReal_pow, ← RCLike.ofReal_mul, RCLike.ofReal_re]

/-- If every eigenvalue `hA.eigenvalues i` with `x_i ≠ 0` lies in `S`, `x_i` the coordinates of
`x` in the eigenvector basis of a Hermitian matrix `A`, then `x` lies in the sum of the
eigenspaces of `A` for the eigenvalues in `S`. -/
theorem mem_iSup_eigenspace {S : Set ℝ} {x : EuclideanSpace 𝕜 n}
    (hS : ∀ i, hA.eigenvectorBasis.repr x i ≠ 0 → hA.eigenvalues i ∈ S) :
    x ∈ ⨆ μ ∈ S, Module.End.eigenspace (toEuclideanLin A) (μ : 𝕜) := by
  rw [← hA.eigenvectorBasis.sum_repr x]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  by_cases h : hA.eigenvectorBasis.repr x i = 0
  · simp [h]
  refine Submodule.smul_mem _ _ (Submodule.mem_iSup_of_mem (hA.eigenvalues i)
    (Submodule.mem_iSup_of_mem (hS i h) ?_))
  rw [Module.End.mem_eigenspace_iff, hA.toEuclideanLin_eigenvectorBasis]

end Matrix.IsHermitian

end
