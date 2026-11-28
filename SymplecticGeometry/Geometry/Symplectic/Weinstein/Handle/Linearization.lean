/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Index
public import TauCeti.Geometry.Manifold.Morse.Basic
public import SymplecticGeometry.Geometry.Symplectic.Weinstein.Basic
import SymplecticGeometry.Geometry.Manifold.Morse.Linearization
import SymplecticGeometry.Geometry.Symplectic.Liouville.VectorField
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal

/-!
# The index bound for a Weinstein structure

For a Weinstein structure `(σ, X, f)` and a nondegenerate critical point `p` of `f`, the stable
subspace of the linearization of `X` at `p` has dimension the Morse index of `f` at `p`
(`TauCeti.IsGradientLike.finrank_stableSubspace_eq_manifoldMorseIndex`, in
`Geometry/Manifold/Morse/Linearization.lean`). At a zero of a Liouville field the form vanishes
on that subspace (`TauCeti.IsLiouvilleVectorField.apply_eq_zero_of_mem_stableSubspace`, in
`Geometry/Symplectic/Liouville/VectorField.lean`). As `σ` is symplectic, this isotropic subspace
has at most half the dimension of the manifold, which bounds the Morse index.

## Main results

* `SymplecticGeometry.IsWeinsteinStructure.two_mul_manifoldMorseIndex_le`: at a nondegenerate
  critical point of a Weinstein structure, twice the Morse index is at most the dimension.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  Proposition 11.9 (a), for the isotropy of the stable subspace, and the dimension bound stated
  after its parts
-/

public section

open Module
open scoped ContDiff Manifold

namespace SymplecticGeometry

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {σ : SmoothTwoForm 𝓘(ℝ, E) M} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ}

/-- **The index bound for a Weinstein structure.** At a nondegenerate critical point `p` of the
function of a Weinstein structure on a manifold modelled on `E`, twice the Morse index is at most
`dim E`: the stable subspace of the linearization of the field at `p` is isotropic for the
symplectic form, and has dimension the Morse index. -/
theorem IsWeinsteinStructure.two_mul_manifoldMorseIndex_le (hW : IsWeinsteinStructure σ X f)
    {p : M} (hp : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f p) :
    2 * manifoldMorseIndex 𝓘(ℝ, E) f p ≤ finrank ℝ E := by
  have hXp := hW.mdifferentiableAt_field p
  have hp0 : X p = 0 := hW.isGradientLike.eq_zero_iff.2 hp.mem_criticalPoints
  rw [← hW.isGradientLike.finrank_stableSubspace_eq_manifoldMorseIndex hp hXp rfl]
  refine LinearMap.BilinForm.two_mul_finrank_le_finrank_of_le_orthogonal
    (hW.isSymplectic.isNondegenerate.nondegenerate_bilinFormAt p) fun w hw ↦
      LinearMap.BilinForm.mem_orthogonal_iff.2 fun v hv ↦ ?_
  rw [SmoothForm.bilinFormAt_apply, SmoothBundleForm.eval₂_apply]
  exact hW.isLiouvilleVectorField.apply_eq_zero_of_mem_stableSubspace hp0 rfl hv hw

end SymplecticGeometry
