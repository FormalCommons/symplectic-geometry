/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Complex.HomologicalOrientation
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import TauCeti.Geometry.Manifold.IsManifold.RestrictScalars
public import TauCeti.Geometry.Symplectic.Manifold.JHolomorphic
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
public import SymplecticGeometry.Topology.OpenPartialHomeomorph.SourceRestrict
import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.OrientedChart
import TauCeti.Geometry.Manifold.MFDeriv.ModelChart
import TauCeti.Geometry.Symplectic.Manifold.Orientation
public import SymplecticGeometry.LinearAlgebra.Complex.Finrank

/-!
# Charts that carry a tamed almost complex structure to `i`

Let `M` be a complex curve, and let a smooth two-form `σ` on `M` tame both a smooth almost
complex structure `J` and the complex structure `i` of `M`. This file shows that a smooth
partial diffeomorphism `ψ : M → ℂ` whose derivative at a point `z` carries `J` to multiplication
by `i` preserves the complex orientation at `z`, in the homological sense: the translated chart
`x ↦ ψ x - ψ z` carries the local orientation of `complexManifoldHomologicalOrientation` at `z`
to the local orientation of `ℂ` at the origin given by `complexOrientation ℂ`
(`SymplecticGeometry.localHomologyMap_sub_complexManifoldHomologicalOrientation_of_tames`).
For the sphere `OnePoint ℂ`, this is the orientation hypothesis of
`TauCeti.VectorBundleOrientation.sectionIndex_eq_analyticOrderNatAt` for the charts of
`SymplecticGeometry.exists_trivialization_analyticAt_of_mem_twistOneKernel`.

By
`TauCeti.Manifold.Orientation.localHomologyMap_sub_toHomologicalOrientation_of_hasFDerivAt` it is
enough that the derivative `D` of `ψ` at `z` carry the tangent orientation at `z` to
`complexOrientation ℂ`. Since `σ` tames both `J` and `i`, the complex orientation of `J` is the
symplectic orientation of `σ`, hence that of `i`, which is the complex orientation of `M`
(`TauCeti.SmoothTwoForm.Tames.orientation_eq`,
`TauCeti.SmoothAlmostComplexStructure.orientation_ofComplexManifold`). Since `D` carries `J` to
`i`, it preserves the complex orientations
(`TauCeti.SmoothAlmostComplexStructure.isOrientationPreservingAt_orientation`).

## Main results

* `SymplecticGeometry.localHomologyMap_sub_complexManifoldHomologicalOrientation_of_tames`.

## References

* [D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*][McDuffSalamon2012],
  Appendix C.
-/

public section

open TauCeti TauCeti.Manifold
open scoped Manifold ContDiff TauCeti.ComplexManifold

namespace SymplecticGeometry

variable {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ, ℂ) ∞ M] {J : SmoothAlmostComplexStructure 𝓘(ℝ, ℂ) M}

/-- **Charts carrying a tamed `J` to `i` preserve the complex orientation.** Let `M` be a
complex curve, and let a two-form `σ` on `M` tame both `J` and the complex structure `i` of `M`.
Let `ψ` be a smooth partial diffeomorphism from `M` to `ℂ` whose derivative at a point `z` of
its source carries `J` to multiplication by `i`. Then the translated chart `x ↦ ψ x - ψ z`
carries the local orientation at `z` of the complex orientation
`complexManifoldHomologicalOrientation` of `M` to the local orientation of `ℂ` at the origin
given by `complexOrientation ℂ`, indexed by `Fin (1 + 1)`. -/
theorem localHomologyMap_sub_complexManifoldHomologicalOrientation_of_tames
    {σ : SmoothTwoForm 𝓘(ℝ, ℂ) M} (hJ : σ.Tames J)
    (hi : σ.Tames (SmoothAlmostComplexStructure.ofComplexManifold ℂ M))
    (ψ : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) M ℂ ∞) {z : M} (hz : z ∈ ψ.source)
    (hψ : IsPseudoholomorphicAt J (SmoothAlmostComplexStructure.ofComplexManifold ℂ ℂ) ψ z) :
    localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ))
        (ψ.toOpenPartialHomeomorph.centeredSourceRestrict z) (S := {⟨z, hz⟩}) (T := {0})
        (ψ.toOpenPartialHomeomorph.centeredSourceRestrict_preimage_zero hz).subset (1 + 1)
        ((ψ.toOpenPartialHomeomorph.open_source.isOpenEmbedding_subtypeVal.localOrientationEquiv
          ⟨z, hz⟩ (1 + 1)).symm
          (complexManifoldHomologicalOrientation ℂ M (r := 0) (by simp) z)).val =
      ((Orientation.reindex ℝ ℂ (finCongr Complex.two_mul_finrank_self)
        (complexOrientation ℂ)).localOrientation (by simp)).val := by
  -- The derivative `D` of `ψ` at `z`, read on `ℂ`, the tangent space of both sides.
  obtain ⟨D, hD⟩ : ∃ D : ℂ ≃L[ℝ] ℂ, (D : ℂ →L[ℝ] ℂ) = mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψ z :=
    (ψ.isLocalDiffeomorphAt _ _ ∞ hz).isInvertible_mfderiv (by simp)
  have hDf : HasFDerivAt (ψ.toOpenPartialHomeomorph ∘ (extChartAt 𝓘(ℝ, ℂ) z).symm)
      (D : ℂ →L[ℝ] ℂ) (extChartAt 𝓘(ℝ, ℂ) z z) :=
    hasMFDerivAt_iff_hasFDerivAt_comp_chartAt_symm.1
      (hD ▸ ((ψ.isLocalDiffeomorphAt _ _ ∞ hz).mdifferentiableAt (by simp)).hasMFDerivAt)
  -- Since `σ` tames `J` and `i`, the complex orientation of `J` is that of `M`, and `ψ`,
  -- which carries `J` to `i`, preserves the complex orientations.
  have hk := finrank_real_of_complex ℂ
  have hJi : J.orientation hk = complexManifoldOrientation ℂ M := by
    rw [← hJ.orientation_eq hk, ← SmoothAlmostComplexStructure.orientation_ofComplexManifold,
      ← hi.orientation_eq hk]
  have hpres := J.isOrientationPreservingAt_orientation
    (J₂ := SmoothAlmostComplexStructure.ofComplexManifold ℂ ℂ) hk hk (f := ψ) (x := z)
    hψ.mfderiv_apply_commute (by rw [← hD]; exact D.injective)
  rw [hJi, SmoothAlmostComplexStructure.orientation_ofComplexManifold,
    Manifold.Orientation.isOrientationPreservingAt_iff_of_coe_eq _ _ _ _ D hD,
    orientationAt_complexManifoldOrientation_eq_complexOrientation,
    orientationAt_complexManifoldOrientation_eq_complexOrientation] at hpres
  rw [complexManifoldHomologicalOrientation_def,
    Manifold.Orientation.localHomologyMap_sub_toHomologicalOrientation_of_hasFDerivAt _ _
      (by simp) _ hz hDf,
    orientationAt_complexManifoldOrientationOfFinrank]
  -- The tangent space at `z` is `ℂ`, so the reindexing commutes with `D`.
  congr 2
  exact (Orientation.map_reindex (M := ℂ) D.toLinearEquiv _ _).trans (congrArg _ hpres)

end SymplecticGeometry

end
