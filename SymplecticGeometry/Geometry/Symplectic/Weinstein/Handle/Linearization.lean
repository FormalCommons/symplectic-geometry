/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.ODE.Linear
public import TauCeti.Geometry.Manifold.Morse.Index
public import TauCeti.Geometry.Manifold.Morse.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Linearization
public import TauCeti.Geometry.Symplectic.Liouville.VectorField
public import SymplecticGeometry.Geometry.Symplectic.Weinstein.Basic
import SymplecticGeometry.Geometry.Manifold.Morse.Linearization
import TauCeti.Analysis.Normed.Module.Alternating.Curry
import SymplecticGeometry.Analysis.ODE.Linear
import SymplecticGeometry.Geometry.Symplectic.Liouville.VectorField
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal

/-!
# The stable subspace at a zero of a Liouville field, and the index bound

At a zero `p` of a Liouville vector field `Z` of a two-form `σ`, the linearization `A` of `Z`
(Tau Ceti's `TauCeti.sectionLinearization`) satisfies `σ_p (A u, v) + σ_p (u, A v) = σ_p (u, v)`
(`TauCeti.IsLiouvilleVectorField.apply_sectionLinearization_add`). Along the flow of `A` the
form `σ_p` then grows like `e ^ t`, so it vanishes on the stable subspace of `A`.

For a Weinstein structure `(σ, X, f)` and a nondegenerate critical point `p` of `f`, the stable
subspace of the linearization of `X` at `p` has dimension the Morse index of `f` at `p`
(`TauCeti.IsGradientLike.finrank_stableSubspace_eq_manifoldMorseIndex`, in
`Geometry/Manifold/Morse/Linearization.lean`). As `σ` is symplectic, this subspace is isotropic,
so the Morse index is at most half the dimension of the manifold.

## Main results

* `TauCeti.IsLiouvilleVectorField.apply_eq_zero_of_mem_stableSubspace`: at a zero of a Liouville
  field, the form vanishes on the stable subspace of the linearization.
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

namespace TauCeti

/-! ### Isotropy of the stable subspace at a zero of a Liouville field -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H N : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I 1 N]

/-- **The stable subspace at a zero of a Liouville field is isotropic.** Let `Z` be a Liouville
vector field of a two-form `σ` on a boundaryless manifold, let `p` be a zero of `Z`, and let `A`
be the linearization of `Z` at `p`. Then `σ_p (u, v) = 0` for all `u`, `v` in the stable
subspace of `A`. -/
theorem IsLiouvilleVectorField.apply_eq_zero_of_mem_stableSubspace [CompleteSpace E]
    {σ : RoughForm I N ℝ 2} {Z : (x : N) → TangentSpace I x} (hZ : IsLiouvilleVectorField σ Z)
    {p : N} (hp : Z p = 0) {A : E →L[ℝ] E} (hA : A = sectionLinearization (F := E) I id Z p)
    {u v : E} (hu : u ∈ A.stableSubspace) (hv : v ∈ A.stableSubspace) : σ p ![u, v] = 0 := by
  subst hA
  -- The value of `σ` at `p`, an alternating map on the tangent space `E` at `p`.
  let σ₀ : E [⋀^Fin 2]→L[ℝ] ℝ := σ p
  have hB (u v : E) : ContinuousAlternatingMap.flatL ℝ E ℝ σ₀ u v = σ p ![u, v] :=
    ContinuousAlternatingMap.flatL_apply_apply σ₀ u v
  rw [← hB]
  refine ContinuousLinearMap.apply_eq_zero_of_mem_stableSubspace (fun u v ↦ ?_) hu hv
  simp only [hB]
  exact hZ.apply_sectionLinearization_add hp u v

end TauCeti

/-! ### The index bound for a Weinstein structure -/

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
