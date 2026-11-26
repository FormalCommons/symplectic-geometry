/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
import SymplecticGeometry.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Basic

/-!
# The inclusion of an open subset, and differentials of maps between open subsets

The inclusion `Subtype.val : U → M` of an open subset `U` of a charted space `M` is differentiable
(`mdifferentiableAt_subtypeVal`, `mdifferentiable_subtypeVal`), since it is smooth at every
regularity (Mathlib's `contMDiff_subtypeVal`). Its differential is Tau Ceti's
`TauCeti.Manifold.mfderiv_subtype_val`.

A map between open subsets that agrees near a point with a map `A` of the ambient manifolds has the
differential of `A` there (`TauCeti.Manifold.mfderiv_apply_of_subtype_val_comp_eventuallyEq`). This
generalizes Tau Ceti's `TauCeti.Manifold.mfderiv_apply_of_subtype_val_comp_eq`, which asks for the
maps to agree everywhere, and its proof is that of Tau Ceti's lemma with
`Filter.EventuallyEq.mfderiv_eq` in place of a rewrite.

Restricting a map `g` on an open subset `V` to a smaller open subset `U` does not change its
differential (`TauCeti.Manifold.mfderiv_comp_inclusion_apply`), whether or not `g` is
differentiable. This is the analogue for `Opens.inclusion` of Tau Ceti's
`TauCeti.Manifold.mfderiv_comp_subtype_val_apply`, and its proof follows that of Tau Ceti's lemma,
with Mathlib's `StructureGroupoid.LocalInvariantProp.liftPropAt_iff_comp_inclusion` for the case
where `g` is not differentiable.
-/

public section

namespace SymplecticGeometry

open TopologicalSpace

variable {𝕜 E H M : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M]
  {U : Opens M}

/-- The inclusion of an open subset is differentiable at each point. -/
theorem mdifferentiableAt_subtypeVal {x : U} : MDifferentiableAt I I (Subtype.val : U → M) x :=
  (contMDiff_subtypeVal (n := 1) x).mdifferentiableAt one_ne_zero

/-- The inclusion of an open subset is differentiable. -/
theorem mdifferentiable_subtypeVal : MDifferentiable I I (Subtype.val : U → M) :=
  fun _ ↦ mdifferentiableAt_subtypeVal

end SymplecticGeometry

namespace TauCeti.Manifold

open TopologicalSpace
open scoped Topology

variable {𝕜 E H M E' H' M' : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  [TopologicalSpace M'] [ChartedSpace H' M']

/-- If a map `f` between open subsets agrees near `x`, read in the ambient manifolds, with a map
`A` of the ambient manifolds, then the differential of `f` at `x` is that of `A` at `x`, on the
common model spaces of the tangent spaces (both are `0` when `f` is not differentiable at `x`). -/
theorem mfderiv_apply_of_subtype_val_comp_eventuallyEq {U : Opens M} {V : Opens M'} {f : U → V}
    {A : M → M'} {x : U} (hcomp : Subtype.val ∘ f =ᶠ[𝓝 x] A ∘ Subtype.val)
    (v : TangentSpace I x) :
    mfderiv I I' f x v = mfderiv I I' A x v := by
  rw [← mfderiv_subtype_val_comp_apply, hcomp.mfderiv_eq, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, tangentSpaceCast_apply]
  exact mfderiv_comp_subtype_val_apply v

/-- Restricting a map `g` on an open subset `V` to an open subset `U ≤ V` does not change its
differential: at `x : U`, the differential of `g ∘ Opens.inclusion h` is that of `g` at
`Opens.inclusion h x`, on the common model space of the tangent spaces (both are `0` when `g` is
not differentiable there). -/
theorem mfderiv_comp_inclusion_apply {U V : Opens M} (h : U ≤ V) {g : V → M'} (x : U)
    (v : TangentSpace I x) :
    mfderiv I I' (g ∘ Opens.inclusion h) x v = mfderiv I I' g (Opens.inclusion h x) v := by
  by_cases hg : MDifferentiableAt I I' g (Opens.inclusion h x)
  · exact (mfderiv_comp_apply x hg
      ((contMDiff_inclusion (n := 1) h).mdifferentiableAt one_ne_zero) v).trans
      (congrArg _ (mfderiv_inclusion_apply h x v))
  · have hgi : ¬MDifferentiableAt I I' (g ∘ Opens.inclusion h) x :=
      (differentiableWithinAt_localInvariantProp.liftPropAt_iff_comp_inclusion h g x).not.mp hg
    rw [mfderiv_zero_of_not_mdifferentiableAt hg, mfderiv_zero_of_not_mdifferentiableAt hgi]
    rfl

end TauCeti.Manifold

end
