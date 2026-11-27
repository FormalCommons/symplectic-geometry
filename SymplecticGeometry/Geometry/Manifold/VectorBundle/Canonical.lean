/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Canonical
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import SymplecticGeometry.Analysis.Normed.Module.Alternating.TopDegree
import SymplecticGeometry.Topology.Algebra.Module.Alternating.Basic
import SymplecticGeometry.Topology.Algebra.Module.Alternating.TopDegree
import TauCeti.Analysis.Calculus.FDeriv.Det.Basic

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

For any map `f : M → E` that is `C^n` at `x`, with `k + 1 ≤ n`, the determinant form pulled back
by the differential of `f` is a section of the canonical bundle that is `C^k` at `x`
(`TauCeti.CanonicalBundle.contMDiffAt_continuousDet_compContinuousLinearMap_mfderiv`): in the
trivialization of the tangent bundle at `x`, it is the determinant of the differential of `f` read
in tangent coordinates, a `C^k` function by Mathlib's `ContMDiffAt.mfderiv_const`, times the
constant determinant form. So the coordinate form of a chart `e` of the maximal atlas of an order
`n ≥ k + 1` is a local frame of the canonical bundle over `e.source`: it is a `C^k` section there,
holomorphic for a complex manifold
(`TauCeti.CanonicalBundle.contMDiffOn_continuousDet_compContinuousLinearMap_mfderiv_extend`), and
it vanishes nowhere there, since the differential of the extended chart is invertible
(`Module.Basis.continuousDet_compContinuousLinearMap_mfderiv_extend_ne_zero`).

## References

* [P. Griffiths, J. Harris, *Principles of Algebraic Geometry*][GriffithsHarris1978], Chapter 1,
  §1 (the canonical bundle of a complex manifold).
-/

public section

open scoped Manifold

namespace TauCeti.CanonicalBundle

variable {𝕜 E H : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type*}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

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

/-- **The pull-back of the determinant form by a `C^n` map is `C^k`.** If `f : M → E` is `C^n` at
`x` and `k + 1 ≤ n`, then the determinant form of `b` pulled back by the differential of `f` is a
section of the canonical bundle that is `C^k` at `x`. -/
theorem contMDiffAt_continuousDet_compContinuousLinearMap_mfderiv {f : M → E} {x : M}
    {k n : WithTop ℕ∞} (hf : ContMDiffAt I 𝓘(𝕜, E) n f x) (hkn : k + 1 ≤ n)
    (b : Module.Basis (Fin (Module.finrank 𝕜 E)) 𝕜 E) :
    ContMDiffAt I (I.prod 𝓘(𝕜, E [⋀^Fin (Module.finrank 𝕜 E)]→L[𝕜] 𝕜)) k
      (fun x ↦ Bundle.TotalSpace.mk' (E [⋀^Fin (Module.finrank 𝕜 E)]→L[𝕜] 𝕜)
        (E := CanonicalBundle I M) x
        (b.continuousDet.compContinuousLinearMap (mfderiv I 𝓘(𝕜, E) f x))) x := by
  rw [Bundle.contMDiffAt_section_iff x]
  -- In the trivialization at `x`, the form is `det D • b.continuousDet`, where `D` is the
  -- differential of `f` in tangent coordinates at `x`, a `C^k` function.
  have hD := ContMDiffAt.mfderiv_const hf hkn
  refine (((ContinuousLinearMap.contDiff_det (𝕜 := 𝕜) (E := E)).smul
    (contDiff_const (c := b.continuousDet))).contMDiff.contMDiffAt.comp x
    hD).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y ↦ ?_)
  simp only [FiberBundle.trivializationAt_continuousAlternatingMap_apply_snd, Function.comp_apply,
    inTangentCoordinates, ContinuousLinearMap.inCoordinates,
    TangentBundle.continuousLinearMapAt_model_space]
  ext v
  rw [Pi.smul_apply', ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  set L := ((1 : E →L[𝕜] E) ∘SL mfderiv I 𝓘(𝕜, E) f y ∘SL
    (trivializationAt E (TangentSpace I) (id x)).symmL 𝕜 (id y))
  have h := congrArg (fun ω ↦ ω v) (b.continuousDet.compContinuousLinearMap_eq_det_smul b L)
  rw [ContinuousAlternatingMap.smul_apply, smul_eq_mul] at h
  -- The left side of the goal is that of `h` by the definition of `compContinuousLinearMap`;
  -- its rewriting lemmas do not unify here, where the tangent spaces are `E` only by
  -- definition, so the goal is closed by `exact`.
  exact h

/-- **The coordinate form of a chart of the maximal atlas is `C^k`.** For `e` in the maximal atlas
of an order `n ≥ k + 1`, the determinant form of `b` pulled back by the differential of the
extended chart `e.extend I` is a `C^k` section of the canonical bundle over `e.source`; for a
complex manifold and `k = n = ω` it is holomorphic. Together with
`Module.Basis.continuousDet_compContinuousLinearMap_mfderiv_extend_ne_zero` it is a local frame
there. -/
theorem contMDiffOn_continuousDet_compContinuousLinearMap_mfderiv_extend
    {e : OpenPartialHomeomorph M H} {k n : WithTop ℕ∞} (he : e ∈ IsManifold.maximalAtlas I n M)
    (hkn : k + 1 ≤ n) (b : Module.Basis (Fin (Module.finrank 𝕜 E)) 𝕜 E) :
    ContMDiffOn I (I.prod 𝓘(𝕜, E [⋀^Fin (Module.finrank 𝕜 E)]→L[𝕜] 𝕜)) k
      (fun x ↦ Bundle.TotalSpace.mk' (E [⋀^Fin (Module.finrank 𝕜 E)]→L[𝕜] 𝕜)
        (E := CanonicalBundle I M) x
        (b.continuousDet.compContinuousLinearMap (mfderiv I 𝓘(𝕜, E) (e.extend I) x)))
      e.source := fun _ hx ↦
  (contMDiffAt_continuousDet_compContinuousLinearMap_mfderiv (e.contMDiffAt_extend he hx) hkn
    b).contMDiffWithinAt

end TauCeti.CanonicalBundle

namespace Module.Basis

variable {𝕜 E H H' : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [TopologicalSpace H] [TopologicalSpace H'] {I : ModelWithCorners 𝕜 E H}
  {I' : ModelWithCorners 𝕜 E H'} {M N : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace H' N] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The coordinate form of a chart of the maximal atlas does not vanish.** For `e` in the
maximal atlas of order `n ≥ 1`, the determinant form of `b` pulled back by the differential of the
extended chart `e.extend I` is nonzero at every point of `e.source`. -/
theorem continuousDet_compContinuousLinearMap_mfderiv_extend_ne_zero (b : Module.Basis ι 𝕜 E)
    {e : OpenPartialHomeomorph M H} {n : WithTop ℕ∞} (he : e ∈ IsManifold.maximalAtlas I n M)
    (hn : 1 ≤ n) {x : M} (hx : x ∈ e.source) :
    b.continuousDet.compContinuousLinearMap (mfderiv I 𝓘(𝕜, E) (e.extend I) x) ≠ 0 :=
  b.continuousDet_compContinuousLinearMap_ne_zero
    (isInvertible_mfderiv_extend (IsManifold.maximalAtlas_subset_of_le hn he) hx)

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
