/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import SymplecticGeometry.Geometry.Manifold.Degree.Global
public import TauCeti.Geometry.Manifold.Orientation.Sphere
import TauCeti.Analysis.InnerProductSpace.Reflection
import TauCeti.Geometry.Diffeomorphism.Sphere
import TauCeti.Geometry.Manifold.Degree.Collapse
import TauCeti.Geometry.Sphere.Connected

/-!
# A map of degree one onto the sphere

Every compact nonempty Hausdorff manifold `M` of dimension `n ≥ 1`, modelled on `ℝⁿ`, with
an orientation, has a smooth map to the unit sphere `Sⁿ` of an oriented real inner product
space of dimension `n + 1` whose mapping degree `TauCeti.degree` is `1`, for the
outward-normal orientation `o.sphereOrientation` of the sphere
(`SymplecticGeometry.exists_contMDiff_degree_eq_one`). In particular every closed oriented
surface maps with degree one onto `S²`.

Tau Ceti's `TauCeti.exists_contMDiff_sphere_isRegularValue_preimage_eq_singleton` gives a smooth
map `f : M → Sⁿ`, collapsing the complement of a coordinate ball around a point `x₀` to a point,
with a regular value `y` whose fibre is `{x₀}`. Its degree is therefore the orientation sign of
`f` at `x₀` (`TauCeti.degree_eq_orientationSign_of_preimage_eq_singleton`), which is `1` or `-1`.
In the second case the reflection of the sphere across the hyperplane orthogonal to `y`, which
reverses its orientation (`Orientation.isOrientationReversingAt_unitSphereEquiv`), turns `f` into
a map of degree `1`.

## Main results

* `SymplecticGeometry.exists_contMDiff_degree_eq_one`: a compact nonempty Hausdorff oriented
  manifold of dimension `n ≥ 1` has a smooth map of degree one to `Sⁿ`.

## References

* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia, 1965,
  §5 and §7.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 17, section Degree Theory.
-/

public section

open Function Metric Module Set
open scoped ContDiff Manifold

namespace SymplecticGeometry

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [T2Space M] [IsManifold (𝓡 n) ∞ M] [Fact (finrank ℝ F = n + 1)]
  [CompactSpace M] [Nonempty M]

/-- **A map of degree one onto the sphere.** A compact nonempty Hausdorff manifold `M` of
dimension `n ≥ 1`, modelled on `ℝⁿ` and oriented by `o`, has a smooth map to the unit sphere of
an oriented real inner product space of dimension `n + 1` whose degree is `1`, for the
outward-normal orientation `o'.sphereOrientation` of the sphere. -/
theorem exists_contMDiff_degree_eq_one [NeZero n]
    (o : TauCeti.Manifold.Orientation (𝓡 n) M (Fin n))
    (o' : Orientation ℝ F (Fin (n + 1))) :
    ∃ f : M → sphere (0 : F) 1, ContMDiff (𝓡 n) (𝓡 n) ∞ f ∧
      TauCeti.degree o o'.sphereOrientation f = 1 := by
  have : ConnectedSpace (sphere (0 : F) 1) := TauCeti.connectedSpace_sphere n
  have : FiniteDimensional ℝ F := .of_fact_finrank_eq_succ n
  obtain ⟨f, y, hf, hy, hfib⟩ :=
    TauCeti.exists_contMDiff_sphere_isRegularValue_preimage_eq_singleton (E := F) (I := 𝓡 n)
      finrank_euclideanSpace_fin (Classical.arbitrary M)
  have hinv : (mfderiv (𝓡 n) (𝓡 n) f (Classical.arbitrary M)).IsInvertible :=
    (TauCeti.isRegularPoint_iff_isInvertible_mfderiv rfl).1 (hy.isRegularPoint <| by
      rw [← mem_singleton_iff, ← mem_preimage, hfib]
      exact mem_singleton _)
  set v : F := (y : F)
  have hdeg := TauCeti.degree_eq_orientationSign_of_preimage_eq_singleton o o'.sphereOrientation
    hf hf.continuous.isProperMap hfib hinv
  rcases TauCeti.Manifold.Orientation.orientationSign_eq_one_or_eq_neg_one
    (o := o) (o' := o'.sphereOrientation) hinv with h | h
  · exact ⟨f, hf, hdeg.trans h⟩
  -- Otherwise compose with the reflection across `v^⊥`, which reverses the orientation.
  set R := ((ℝ ∙ v)ᗮ.reflection).unitSphereEquiv
  have hdet : LinearMap.det (((ℝ ∙ v)ᗮ.reflection).toLinearEquiv : F →ₗ[ℝ] F) < 0 := by
    have hv0 : v ≠ 0 := ne_zero_of_mem_unit_sphere y
    rw [← LinearEquiv.coe_det, TauCeti.linearEquiv_det_reflection_orthogonal_singleton hv0]
    exact neg_one_lt_zero
  have hR : ContMDiff (𝓡 n) (𝓡 n) ∞ R := LinearIsometryEquiv.contMDiff_unitSphereEquiv _
  have hsign : TauCeti.Manifold.Orientation.orientationSign o o'.sphereOrientation (R ∘ f)
      (Classical.arbitrary M) = 1 := by
    rw [TauCeti.Manifold.Orientation.orientationSign_comp (hR.mdifferentiable (by simp) _)
      (hf.mdifferentiable (by simp) _), h,
      TauCeti.Manifold.Orientation.orientationSign_of_isOrientationReversingAt
        (o'.isOrientationReversingAt_unitSphereEquiv hdet _)]
    norm_num
  have hinv' : (mfderiv (𝓡 n) (𝓡 n) (R ∘ f) (Classical.arbitrary M)).IsInvertible := by
    by_contra hni
    rw [TauCeti.Manifold.Orientation.orientationSign_of_not_isInvertible hni] at hsign
    exact zero_ne_one hsign
  have hfib' : (R ∘ f) ⁻¹' {R y} = {Classical.arbitrary M} := by
    rw [preimage_comp, ← image_singleton (f := R), R.injective.preimage_image, hfib]
  refine ⟨R ∘ f, hR.comp hf, ?_⟩
  rw [TauCeti.degree_eq_orientationSign_of_preimage_eq_singleton o o'.sphereOrientation
    (hR.comp hf) (hR.comp hf).continuous.isProperMap hfib' hinv', hsign]

end SymplecticGeometry

end
