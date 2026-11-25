/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.ZeroOneForm
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Chart

/-!
# Two `(0,1)`-projections read in the charts of a finite bundle atlas

Let `M` be a complex manifold modelled on `E`, with its complex structure `i`
(`TauCeti.SmoothAlmostComplexStructure.ofComplexManifold`), let `J` be a second almost complex
structure on `M`, and let `A` be a finite bundle atlas of a complex vector bundle `V → M`. For a
`V`-valued one-form `η`, the `(0,1)`-part for `i` of the `(0,1)`-part for `J` of `η`, read in
chart `i` of `A` at a point of the chart image, is the complex-antilinear part of
`½ (η' + i • η' ∘ K)`, where `η'` is the reading of `η` and `K = J.inChart (A.center i)` the
reading of `J` (`TauCeti.FiniteBundleAtlas.coord_tangentHom_zeroOnePart_zeroOnePart`).

The outer `(0,1)`-part, for `i`, is read as a complex-antilinear part by Tau Ceti's
`TauCeti.FiniteBundleAtlas.coord_tangentHom_zeroOnePart`; this file adds the reading of the
inner `(0,1)`-part, for `J`.

## References

* [D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*][McDuffSalamon2012],
  Appendix C.1.
-/

public section

open Bundle
open scoped Manifold ContDiff TauCeti.ComplexManifold

namespace TauCeti.FiniteBundleAtlas

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, ContinuousSMul ℂ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [VectorBundle ℂ F V]
  (A : FiniteBundleAtlas E M F V) (J : SmoothAlmostComplexStructure 𝓘(ℝ, E) M)

/-- On the image of chart `i`, the reading of the `(0,1)`-part for the complex structure of `M`
of the `(0,1)`-part for `J` of a one-form `η` is the complex-antilinear part of
`½ (η' + i • η' ∘ K)`, for the reading `η'` of `η` and the reading `K` of `J` in chart `i`. -/
theorem coord_tangentHom_zeroOnePart_zeroOnePart {i : Fin A.n} {z : E} (hz : z ∈ A.image i)
    (η : Π x, TangentSpace 𝓘(ℝ, E) x →L[ℝ] V x) :
    A.tangentHom.coord i
        (fun x ↦ (SmoothAlmostComplexStructure.ofComplexManifold E M).zeroOnePart
          (J.zeroOnePart (η x))) z =
      ContinuousLinearMap.complexAntilinearPartL ((2⁻¹ : ℝ) •
        (A.tangentHom.coord i η z +
          Complex.I • (A.tangentHom.coord i η z).comp (J.inChart (A.center i) z))) := by
  have hxs := A.dom_subset_chart_source i (A.symm_mem_dom hz)
  rw [A.coord_tangentHom_zeroOnePart, coord_tangentHom, coord_tangentHom,
    SmoothAlmostComplexStructure.inChart_def]
  congr 1
  ext v
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
    SmoothAlmostComplexStructure.zeroOnePart_apply, smul_apply,
    add_apply, map_smul, map_add]
  have hb : (A.chart i).symm z ∈ (trivializationAt E (TangentSpace 𝓘(ℝ, E)) (A.center i)).baseSet :=
    by simpa using hxs
  rw [extChartAt_coe_symm, modelWithCornersSelf_coe_symm, Function.comp_id,
    Trivialization.symmL_continuousLinearMapAt _ hb,
    Trivialization.coe_continuousLinearMapAt_eq_coe_continuousLinearMapAt ℝ ℂ, map_smul,
    ← Trivialization.coe_continuousLinearMapAt_eq_coe_continuousLinearMapAt ℝ ℂ]

end TauCeti.FiniteBundleAtlas

end
