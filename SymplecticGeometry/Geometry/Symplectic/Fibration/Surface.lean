/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Fibration.Basic
public import SymplecticGeometry.Geometry.Manifold.FiberBundle.StructureGroup
public import TauCeti.Geometry.Manifold.Orientation.Preserving
public import TauCeti.AlgebraicTopology.Singular.SurfaceGenus
public import Mathlib.Geometry.Manifold.Instances.Real
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Integration.Positivity
import SymplecticGeometry.Geometry.Manifold.FiberBundle.MapFiber
import SymplecticGeometry.Geometry.Manifold.FiberBundle.RestrictsTo
import SymplecticGeometry.Geometry.Manifold.Orientation.PositiveForm
import SymplecticGeometry.Geometry.Manifold.VectorBundle.Symplectic.RealChernClass
import SymplecticGeometry.Geometry.Symplectic.Fibration.AreaForm
import SymplecticGeometry.Geometry.Symplectic.Fibration.ChernClass
import SymplecticGeometry.Geometry.Symplectic.Fibration.Thurston
import SymplecticGeometry.Geometry.Symplectic.Manifold.Surface
import SymplecticGeometry.Geometry.Symplectic.Manifold.Volume

/-!
# Symplectic forms on surface bundles

Let `A` be a smooth atlas of `proj : M → B` whose model fibre is a closed connected surface `F`
with an orientation `o`, and whose coordinate changes preserve `o`. If `M` is compact, the genus
`g` of `F` is not one, and `B` is compact, connected and has a symplectic form `β`, then some
symplectic form on `M` is compatible with the oriented atlas `A`, for the orientation of `β` on
the base and `o` on the fibre ([McDuffSalamon2017], Theorem 6.2.2).

The proof takes the elementary route that replaces the reduction of the structure group.

1. A form `σ₀` on `F` positive for `o` with integral one
   (`TauCeti.exists_smoothForm_isPositive_integralTopForm_eq_one`) is an
   area form, hence symplectic (`TauCeti.Manifold.Orientation.IsPositive.isSymplectic`), and its
   symplectic orientation is `o`
   (`TauCeti.SmoothTwoForm.IsNondegenerate.volumeOrientation_eq_of_isPositive`).
2. Summing such forms against a partition of unity of `B` gives a form on `M` whose fibre
   pull-backs are positive with integral one
   (`TauCeti.MapFiber.Atlas.exists_restricts_isPositive_area`), and
   Moser's argument with a parameter turns `A` into a symplectic atlas `A'` for `(F, σ₀)` whose
   coordinate changes with `A` preserve `o`
   (`TauCeti.MapFiber.Atlas.exists_symplecticAtlas_of_oriented`).
3. On `F`, `c₁(TF) = (2 - 2 g) [σ₀]`
   (`SymplecticGeometry.realFirstChernClass_tangent_eq_of_surface`), and `2 - 2 g ≠ 0`, so the
   Chern class criterion
   (`TauCeti.MapFiber.Atlas.exists_isSymplectic_compatible_of_realFirstChernClass_eq`) gives a
   symplectic form `θ` on `M` that restricts to `σ₀` along `A'`.
4. Along a chart of `A`, the fibre pull-back of `θ` is the pull-back of `σ₀` by a coordinate
   change with `A'`, an orientation-preserving diffeomorphism, so it is positive for `o`
   (`Diffeomorph.mem_orientationPreservingSubgroup_iff_isPositive_mpullback`): it is nondegenerate
   with symplectic orientation `o`. Thurston's forms `θ + K proj^* β` are then compatible with `A`
   for large `K`
   (`TauCeti.MapFiber.Atlas.exists_forall_ge_isOrientedCompatible_add_smul_mpullback`).

The hypothesis `surfaceGenus F ≠ 1` cannot be dropped: the Hopf surface `S¹ × S³` fibres over
the two-sphere with torus fibres and carries no symplectic form, since its second Betti number
is zero ([McDuffSalamon2017], §6.2). That counterexample is not built here.

## Main results

* `TauCeti.MapFiber.Atlas.exists_isSymplectic_compatible_oriented`: a symplectic form compatible
  with an oriented atlas of a surface bundle over a compact connected symplectic base, when the
  fibre genus is not one.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §6.2 (Theorem 6.2.2).
-/

public section

open Bundle SymplecticGeometry
open scoped Manifold ContDiff

namespace TauCeti.MapFiber.Atlas

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {B : Type*}
  [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB ∞ B] [BoundarylessManifold IB B]
  [T2Space B]
  {F : Type} [TopologicalSpace F] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) F]
  [IsManifold (𝓡 2) ∞ F] [T2Space F] [CompactSpace F] [ConnectedSpace F]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [FiniteDimensional ℝ EM]
  {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM} [IM.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M] [IsManifold IM ∞ M] [T2Space M]
  {proj : M → B} {A : Atlas F proj}

/-- **Symplectic forms on surface bundles.** Let `A` be a smooth atlas of `proj : M → B` with
compact Hausdorff total space modelled without boundary, whose model fibre is a compact connected
Hausdorff surface `F` of genus `surfaceGenus F ≠ 1` with an orientation `o`, and whose coordinate
changes preserve `o`. Let the base be compact, connected, Hausdorff and boundaryless, with a
symplectic form `β`. Then some two-form on `M` is compatible with the oriented atlas `A`, for the
symplectic orientation of `β` on the base and `o` on the fibre: it is symplectic, its fibre
pull-backs are nondegenerate with symplectic orientation `o`, and every chart of `A` preserves
orientation.

Milestone: *Symplectic forms on surface bundles with fibre genus different from one*. -/
theorem exists_isSymplectic_compatible_oriented [CompactSpace M] [CompactSpace B]
    [ConnectedSpace B] (hA : A.IsContMDiff ∞ IB (𝓡 2) IM)
    {o : Manifold.Orientation (𝓡 2) F (Fin 2)}
    (hH : A.HasStructureGroup (Diffeomorph.orientationPreservingSubgroup (n := ∞) (by simp) o))
    (hg : surfaceGenus F ≠ 1) {β : SmoothTwoForm IB B} (hβ : β.IsSymplectic) :
    ∃ τ : SmoothTwoForm IM M,
      A.IsOrientedCompatible hA (hβ.isNondegenerate.orientation rfl) o τ := by
  have : Nonempty F := ‹ConnectedSpace F›.toNonempty
  -- An area form `σ₀` of integral one on `F`, and a symplectic atlas `A'` for `(F, σ₀)`.
  obtain ⟨σ₀, hσ₀, hσ₀1⟩ := exists_smoothForm_isPositive_integralTopForm_eq_one o
  obtain ⟨τ₀, hτ₀⟩ := exists_restricts_isPositive_area hA hH
  obtain ⟨A', hA', hH', -, hAA', hbase⟩ := exists_symplecticAtlas_of_oriented hA hH hσ₀
    (τ := τ₀) fun b b' hb' ↦ ⟨(hτ₀ b b' hb').1, (hτ₀ b b' hb').2.trans hσ₀1.symm⟩
  have hσ := hσ₀.isSymplectic
  have : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 * Module.finrank ℂ ℂ) :=
    ⟨by simp⟩
  -- The Chern class criterion, with `c₁(TF) = (2 - 2 g) [σ₀]`.
  have hc := realFirstChernClass_tangent_eq_of_surface ℂ o hσ
    (hσ.isNondegenerate.volumeOrientation_eq_of_isPositive _ hσ₀)
  rw [hσ₀1, div_one] at hc
  have hc0 : (2 - 2 * surfaceGenus F : ℝ) ≠ 0 := fun h ↦
    hg (by exact_mod_cast (by linarith : (surfaceGenus F : ℝ) = 1))
  obtain ⟨θ, hθ, hθA'⟩ :=
    exists_isSymplectic_compatible_of_realFirstChernClass_eq ℂ hA' hH' hσ hc0 hc hβ
  -- Along `A`, the fibre pull-backs of `θ` are pull-backs of `σ₀` by orientation-preserving
  -- coordinate changes, so they are positive for `o`.
  have hpos : ∀ b b' (hb' : b' ∈ (A.trivAt b).baseSet),
      o.IsPositive (SmoothForm.mpullback _ ((A.trivAt b).contMDiff_fiberInclusionMap
        (hA.contMDiffOn_trivAt_symm b) hb') θ).val := fun b b' hb' ↦ by
    have hb'' : b' ∈ (A'.trivAt b).baseSet := hbase b ▸ hb'
    obtain ⟨φ, hφ, hφe⟩ := coordChangeMem_iff.1 hAA' b b b' hb' hb''
    rw [SmoothForm.coe_mpullback,
      Trivialization.mpullback_fiberInclusionMap_eq_mpullback_coordChange
        (hA'.mdifferentiable_trivAt (by simp) b) hb' hb'' (hφe ▸ φ.mdifferentiable (by simp)),
      restrictsTo_iff.1 hθA' b b' hb'', ← hφe]
    exact (Diffeomorph.mem_orientationPreservingSubgroup_iff_isPositive_mpullback hσ₀).1 hφ
  obtain ⟨K₀, hK₀⟩ := exists_forall_ge_isOrientedCompatible_add_smul_mpullback hA
    (fun b b' hb' ↦ (hpos b b' hb').isSymplectic.isNondegenerate)
    (fun b b' hb' ↦
      SmoothTwoForm.IsNondegenerate.orientation_eq_of_isPositive _ _ (hpos b b' hb'))
    hθ.isClosed hβ rfl
  exact ⟨_, hK₀ K₀ le_rfl⟩

end TauCeti.MapFiber.Atlas

end
