/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Congr
public import TauCeti.Geometry.Diffeomorphism.Sphere
public import TauCeti.Geometry.Manifold.Orientation.Preserving
public import TauCeti.Geometry.Manifold.Orientation.Sphere
public import SymplecticGeometry.Geometry.Diffeomorphism.OrthogonalSphere
public import SymplecticGeometry.Geometry.Manifold.Orientation.Diffeomorph
import SymplecticGeometry.Geometry.Manifold.Orientation.Reindex

/-!
# The orientation-preserving subgroup of a diffeomorphism group

Tau Ceti's `Diffeomorph.orientationPreservingSubgroup hn o` is the subgroup of `C^n`
self-diffeomorphisms of a manifold `M` that preserve an orientation `o` at every point. This file
shows how it depends on `o` and how it behaves under conjugation.

* `Diffeomorph.orientationPreservingSubgroup_neg`: a diffeomorphism preserves `o` exactly when it
  preserves `-o`, so the subgroup is the same for both.
* `Diffeomorph.orientationPreservingSubgroup_reindex`: reindexing `o` does not change the subgroup.
* `Diffeomorph.map_orientationPreservingSubgroup_diffCongr`: conjugation by a diffeomorphism
  `e : M → N`, Tau Ceti's `Diffeomorph.diffCongr e`, maps the subgroup for `o` onto the subgroup
  for the orientation `o.map e hn hι` carried to `N` along `e`.
* `TauCeti.range_specialOrthogonalToDiffSphere_le`: the rotations `SO(n + 1)`, restricted to the
  unit sphere `Sⁿ` by `TauCeti.specialOrthogonalToDiffSphere n m`, preserve the
  outward-normal orientation `o.sphereOrientation` of every orientation `o` of `ℝⁿ⁺¹`, by Tau
  Ceti's `Orientation.isOrientationPreservingAt_unitSphereEquiv`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 15.
-/

public section

open Module TauCeti.Manifold

open scoped Manifold ContDiff

namespace Diffeomorph

variable {E E' H H' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [TopologicalSpace H]
  [TopologicalSpace H'] {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'}
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] [TopologicalSpace N]
  [ChartedSpace H' N] [IsManifold I' 1 N] {ι : Type*} [Fintype ι] {n : ℕ∞ω}

/-- A diffeomorphism preserves an orientation at every point exactly when it preserves the
opposite orientation at every point. -/
@[simp]
theorem orientationPreservingSubgroup_neg (hn : n ≠ 0) (o : Orientation I M ι) :
    orientationPreservingSubgroup hn (-o) = orientationPreservingSubgroup hn o := by
  ext f
  simp only [mem_orientationPreservingSubgroup_iff, Orientation.isOrientationPreservingAt_neg_left,
    Orientation.isOrientationReversingAt_neg_right]

/-- Reindexing an orientation does not change the diffeomorphisms that preserve it. -/
@[simp]
theorem orientationPreservingSubgroup_reindex (hn : n ≠ 0) (o : Orientation I M ι)
    {ι' : Type*} [Fintype ι'] (σ : ι ≃ ι') :
    orientationPreservingSubgroup hn (o.reindex σ) = orientationPreservingSubgroup hn o := by
  ext f
  simp [mem_orientationPreservingSubgroup_iff]

/-- Conjugation by a diffeomorphism `e : M → N`, `φ ↦ e ∘ φ ∘ e⁻¹`, maps the diffeomorphisms of
`M` preserving an orientation `o` onto the diffeomorphisms of `N` preserving the orientation
carried from `o` along `e`. -/
theorem map_orientationPreservingSubgroup_diffCongr (hn : n ≠ 0) (o : Orientation I M ι)
    (e : M ≃ₘ^n⟮I, I'⟯ N) (hι : Fintype.card ι = finrank ℝ E') :
    (orientationPreservingSubgroup hn o).map (diffCongr e).toMonoidHom =
      orientationPreservingSubgroup hn (o.map e hn hι) := by
  ext ψ
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, mem_orientationPreservingSubgroup_iff]
  constructor
  · rintro ⟨φ, hφ, rfl⟩ y
    have hcoe : ⇑(diffCongr e φ) = e ∘ φ ∘ e.symm := funext (diffCongr_apply_apply e φ)
    rw [hcoe]
    exact (Orientation.isOrientationPreservingAt_map o e hn hι _).comp
      ((hφ _).comp (Orientation.isOrientationPreservingAt_map_symm o e hn hι y))
  · intro hψ
    refine ⟨(diffCongr e).symm ψ, fun x ↦ ?_, MulEquiv.apply_symm_apply _ ψ⟩
    have hcoe : ⇑((diffCongr e).symm ψ) = e.symm ∘ ψ ∘ e := by
      rw [diffCongr_symm]
      exact funext (diffCongr_apply_apply e.symm ψ)
    rw [hcoe]
    exact (Orientation.isOrientationPreservingAt_map_symm o e hn hι _).comp
      ((hψ _).comp (Orientation.isOrientationPreservingAt_map o e hn hι x))

end Diffeomorph

namespace TauCeti

open Metric Matrix

/-- The rotations `SO(n + 1)` of `ℝⁿ⁺¹` restrict to diffeomorphisms of the unit sphere `Sⁿ` that
preserve the outward-normal orientation `o.sphereOrientation` at every point, for every
orientation `o` of `ℝⁿ⁺¹`. -/
theorem range_specialOrthogonalToDiffSphere_le {n : ℕ}
    [Fact (finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1)] {m : ℕ∞ω} (hm : m ≠ 0)
    (o : _root_.Orientation ℝ (EuclideanSpace ℝ (Fin (n + 1))) (Fin (n + 1))) :
    (specialOrthogonalToDiffSphere n m).range ≤
      Diffeomorph.orientationPreservingSubgroup hm o.sphereOrientation := by
  rintro _ ⟨A, rfl⟩
  rw [Diffeomorph.mem_orientationPreservingSubgroup_iff]
  intro u
  rw [specialOrthogonalToDiffSphere_apply, orthogonalToDiffSphere_apply,
    LinearIsometryEquiv.unitSphereDiffHom_apply, LinearIsometryEquiv.coe_unitSphereDiffeomorph]
  refine o.isOrientationPreservingAt_unitSphereEquiv ?_ u
  have he : ∀ e : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)),
      (e.toLinearEquiv : _ →ₗ[ℝ] _) = e.toLinearIsometry.toLinearMap :=
    fun e ↦ LinearMap.ext fun _ ↦ by simp
  rw [he, UnitaryGroup.det_toLinearIsometryEquiv, specialOrthogonalGroup.coe_toOrthogonalGroup,
    (mem_specialOrthogonalGroup_iff.1 A.property).2]
  exact one_pos

end TauCeti

end
