/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Canonical
public import TauCeti.Topology.Algebra.Module.FiniteDimension
import SymplecticGeometry.Topology.Algebra.Module.Alternating.Basic

/-!
# The coordinate form of a chart as a pull-back

Tau Ceti's `TauCeti.CanonicalBundle.coordForm I x₀ b` is the coordinate form `dz₁ ∧ ⋯ ∧ dzₙ` of
the chart at `x₀`, defined through the trivialization of the tangent bundle. This file identifies
it, on the source of the chart, with the pull-back of the determinant form `b.continuousDet` of
the model space by the differential of the extended chart
(`TauCeti.CanonicalBundle.coordForm_eq_compContinuousLinearMap_mfderiv`). In that form the
coordinate form makes sense for any chart of the maximal atlas, and the chain rule computes its
pull-backs: if `e ∘ f` agrees near `z` with `F ∘ χ` for a map `F : E → E`, then the form of `e`
pulled back by the differential of `f` is `det (DF (χ z))` times the form of `χ`
(`Module.Basis.continuousDet_compContinuousLinearMap_mfderiv_comp`). When `f` is the identity,
this compares the forms of two charts `e` and `χ` directly
(`Module.Basis.continuousDet_compContinuousLinearMap_mfderiv_of_eventuallyEq`).

When the model space is finite-dimensional, the fibres of the canonical bundle are
finite-dimensional by Tau Ceti's `ContinuousAlternatingMap.instModuleFinite`, whose file this
one imports so that instance search finds it wherever this file is imported. Over a complete
field they then carry their module topology (`TauCeti.CanonicalBundle.instIsModuleTopology`),
as every finite-dimensional Hausdorff topological vector space does.

## References

* [P. Griffiths, J. Harris, *Principles of Algebraic Geometry*][GriffithsHarris1978], Chapter 1,
  §1 (the canonical bundle of a complex manifold).
-/

public section

open scoped Manifold

namespace TauCeti.CanonicalBundle

variable {𝕜 E H : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type*}
  [TopologicalSpace M] [ChartedSpace H M]

/-- A fibre of the canonical bundle of a manifold modelled on a finite-dimensional space carries
the module topology. -/
instance instIsModuleTopology [FiniteDimensional 𝕜 E] (x : M) :
    IsModuleTopology 𝕜 (CanonicalBundle I M x) :=
  isModuleTopologyOfFiniteDimensional

variable [IsManifold I 1 M]

/-- On the source of the chart at `x₀`, the coordinate form of that chart is the determinant form
of `b` pulled back by the differential of the extended chart. -/
theorem coordForm_eq_compContinuousLinearMap_mfderiv {x₀ x : M}
    (hx : x ∈ (chartAt H x₀).source) (b : Module.Basis (Fin (Module.finrank 𝕜 E)) 𝕜 E) :
    coordForm I x₀ b x =
      b.continuousDet.compContinuousLinearMap (mfderiv I 𝓘(𝕜, E) (extChartAt I x₀) x) := by
  ext v
  rw [coordForm_apply, TangentBundle.continuousLinearMapAt_trivializationAt hx,
    ← Module.Basis.continuousDet_apply]
  exact (ContinuousAlternatingMap.compContinuousLinearMap_apply (M' := TangentSpace I x)
    (M := E) b.continuousDet _ v).symm

end TauCeti.CanonicalBundle

namespace Module.Basis

variable {𝕜 E H H' : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [TopologicalSpace H] [TopologicalSpace H'] {I : ModelWithCorners 𝕜 E H}
  {I' : ModelWithCorners 𝕜 E H'} {M N : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace H' N] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The chain rule for coordinate forms.** Let `f : M → N`, `e : N → E` and `χ : M → E` be
differentiable at the points concerned, and `F : E → E` differentiable at `χ z`, with `e ∘ f`
equal to `F ∘ χ` near `z`. Then the determinant form of `b` pulled back by the differential of
`e` at `f z` and then by that of `f` at `z` is `det (DF (χ z))` times the determinant form of
`b` pulled back by the differential of `χ` at `z`. -/
theorem continuousDet_compContinuousLinearMap_mfderiv_comp (b : Module.Basis ι 𝕜 E) {f : M → N}
    {e : N → E} {χ : M → E} {F : E → E} {z : M} (he : MDifferentiableAt I' 𝓘(𝕜, E) e (f z))
    (hf : MDifferentiableAt I I' f z) (hχ : MDifferentiableAt I 𝓘(𝕜, E) χ z)
    (hF : DifferentiableAt 𝕜 F (χ z)) (heq : e ∘ f =ᶠ[nhds z] F ∘ χ) :
    (b.continuousDet.compContinuousLinearMap (mfderiv I' 𝓘(𝕜, E) e (f z))).compContinuousLinearMap
        (mfderiv I I' f z) =
      LinearMap.det (fderiv 𝕜 F (χ z) : E →ₗ[𝕜] E) •
        b.continuousDet.compContinuousLinearMap (mfderiv I 𝓘(𝕜, E) χ z) := by
  have key := (mfderiv_comp z he hf).symm.trans (heq.mfderiv_eq.trans
    ((hF.hasFDerivAt.hasMFDerivAt.comp z hχ.hasMFDerivAt).mfderiv))
  ext v
  have h : b.det (mfderiv I' 𝓘(𝕜, E) e (f z) ∘ (mfderiv I I' f z ∘ v)) =
      b.det ((fderiv 𝕜 F (χ z) : E →ₗ[𝕜] E) ∘ (mfderiv I 𝓘(𝕜, E) χ z ∘ v)) :=
    congrArg (fun L : E →L[𝕜] E ↦ b.det (L ∘ v)) key
  rw [Basis.det_comp, ← Basis.continuousDet_apply, ← Basis.continuousDet_apply] at h
  -- The two sides of `h` are those of the goal applied to `v`, by the definitions of
  -- `compContinuousLinearMap` and of the scalar action. The rewriting lemmas for these do not
  -- unify here, where the tangent spaces are `E` only by definition, so the goal is closed by
  -- `exact`.
  exact h

/-- **The chain rule for the coordinate forms of two charts.** Let `χ : M → E` be differentiable
at `z`, `F : E → E` differentiable at `χ z`, and `e : M → E` equal to `F ∘ χ` near `z`. Then the
determinant form of `b` pulled back by the differential of `e` at `z` is `det (DF (χ z))` times
the determinant form of `b` pulled back by the differential of `χ` at `z`.
This is `continuousDet_compContinuousLinearMap_mfderiv_comp` with `f` the identity. -/
theorem continuousDet_compContinuousLinearMap_mfderiv_of_eventuallyEq (b : Module.Basis ι 𝕜 E)
    {e χ : M → E} {F : E → E} {z : M} (hχ : MDifferentiableAt I 𝓘(𝕜, E) χ z)
    (hF : DifferentiableAt 𝕜 F (χ z)) (heq : e =ᶠ[nhds z] F ∘ χ) :
    b.continuousDet.compContinuousLinearMap (mfderiv I 𝓘(𝕜, E) e z) =
      LinearMap.det (fderiv 𝕜 F (χ z) : E →ₗ[𝕜] E) •
        b.continuousDet.compContinuousLinearMap (mfderiv I 𝓘(𝕜, E) χ z) := by
  have he : MDifferentiableAt I 𝓘(𝕜, E) e z :=
    (hF.mdifferentiableAt.comp z hχ).congr_of_eventuallyEq heq
  rw [← b.continuousDet_compContinuousLinearMap_mfderiv_comp he mdifferentiableAt_id hχ hF heq,
    mfderiv_id]
  exact (ContinuousAlternatingMap.compContinuousLinearMap_id _).symm

end Module.Basis

end
