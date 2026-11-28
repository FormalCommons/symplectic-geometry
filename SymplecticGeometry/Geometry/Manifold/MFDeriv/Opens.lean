/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
import SymplecticGeometry.Geometry.Manifold.IsManifold.Basic
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition
import TauCeti.Geometry.Manifold.MFDeriv.Opens

/-!
# The inclusion of an open subset, and differentials of maps between open subsets

The inclusion `Subtype.val : U → M` of an open subset `U` of a charted space `M` is differentiable
(`mdifferentiableAt_subtypeVal`, `mdifferentiable_subtypeVal`), since it is smooth at every
regularity (Mathlib's `contMDiff_subtypeVal`). For the same reason, so is the inclusion
`Opens.inclusion h : U → V` of open subsets (`mdifferentiableAt_inclusion`,
`mdifferentiable_inclusion`, from Mathlib's `contMDiff_inclusion`). The differential of
`Subtype.val` is Tau Ceti's
`TauCeti.Manifold.mfderiv_subtype_val`.

A map between open subsets that agrees near a point with a map `A` of the ambient manifolds has the
differential of `A` there (`mfderiv_apply_of_subtypeVal_comp_eventuallyEq`). This
generalizes Tau Ceti's `TauCeti.Manifold.mfderiv_apply_of_subtype_val_comp_eq`, which asks for the
maps to agree everywhere, and its proof is that of Tau Ceti's lemma with
`Filter.EventuallyEq.mfderiv_eq` in place of a rewrite.

Restricting a map `g` on an open subset `V` to a smaller open subset `U` does not change its
differential (`mfderiv_comp_inclusion_apply`), whether or not `g` is
differentiable. Since `Opens.inclusion h` is a local diffeomorphism
(`isLocalDiffeomorph_inclusion`), this is Tau Ceti's chain rule
`IsLocalDiffeomorphAt.mfderiv_comp` for precomposition with a local diffeomorphism, combined with
the differential of the inclusion, `TauCeti.Manifold.mfderiv_inclusion_apply`.

On an open subset of a normed space with its model `𝓘(𝕜, E)`, the derivative of the restriction
of a map `f`, read with `mvfderiv` or with `mfderiv`, is the Fréchet derivative of `f`
(`TauCeti.Manifold.mvfderiv_modelSpace_comp_subtype_val_apply`,
`mfderiv_modelSpace_comp_subtypeVal_apply`): Tau Ceti's
`TauCeti.Manifold.mvfderiv_comp_subtype_val` followed by `TauCeti.mvfderiv_eq_fderiv_apply`.

The `mvfderiv` lemma is about Tau Ceti's `mvfderiv`, so it sits in `TauCeti.Manifold` next to
Tau Ceti's own; the other lemmas are in the root namespace, as Mathlib's lemmas on
`MDifferentiable` and `mfderiv` are.
-/

public section

open scoped Manifold

open TopologicalSpace
open scoped Topology

variable {𝕜 E H M E' H' M' : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  [TopologicalSpace M'] [ChartedSpace H' M']

/-- The inclusion of an open subset is differentiable at each point. -/
theorem mdifferentiableAt_subtypeVal {U : Opens M} {x : U} :
    MDifferentiableAt I I (Subtype.val : U → M) x :=
  (contMDiff_subtypeVal (n := 1) x).mdifferentiableAt one_ne_zero

/-- The inclusion of an open subset is differentiable. -/
theorem mdifferentiable_subtypeVal {U : Opens M} : MDifferentiable I I (Subtype.val : U → M) :=
  fun _ ↦ mdifferentiableAt_subtypeVal

/-- The inclusion `Opens.inclusion h : U → V` of an open subset `U` into an open subset `V ≥ U` is
differentiable at each point. -/
theorem mdifferentiableAt_inclusion {U V : Opens M} (h : U ≤ V) {x : U} :
    MDifferentiableAt I I (Opens.inclusion h) x :=
  (contMDiff_inclusion (n := 1) h x).mdifferentiableAt one_ne_zero

/-- The inclusion `Opens.inclusion h : U → V` of an open subset `U` into an open subset `V ≥ U` is
differentiable. -/
theorem mdifferentiable_inclusion {U V : Opens M} (h : U ≤ V) :
    MDifferentiable I I (Opens.inclusion h) :=
  fun _ ↦ mdifferentiableAt_inclusion h

namespace TauCeti.Manifold

/-- On an open subset `U` of a normed space `E`, read with the model `𝓘(𝕜, E)`, the derivative
`mvfderiv` at `x : U` of the restriction `f ∘ Subtype.val` of a map `f : E → E'` is the Fréchet
derivative of `f` at `x` (both are `0` when `f` is not differentiable there). -/
theorem mvfderiv_modelSpace_comp_subtype_val_apply {U : Opens E} {f : E → E'} {x : U}
    (v : TangentSpace 𝓘(𝕜, E) x) :
    mvfderiv 𝓘(𝕜, E) (f ∘ Subtype.val) x v = fderiv 𝕜 f x v := by
  rw [mvfderiv_comp_subtype_val]
  exact mvfderiv_eq_fderiv_apply f x v

end TauCeti.Manifold

open TauCeti TauCeti.Manifold

/-- If a map `f` between open subsets agrees near `x`, read in the ambient manifolds, with a map
`A` of the ambient manifolds, then the differential of `f` at `x` is that of `A` at `x`, on the
common model spaces of the tangent spaces (both are `0` when `f` is not differentiable at `x`). -/
theorem mfderiv_apply_of_subtypeVal_comp_eventuallyEq {U : Opens M} {V : Opens M'} {f : U → V}
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
  rw [(isLocalDiffeomorph_inclusion (n := 1) h x).mfderiv_comp one_ne_zero g,
    ContinuousLinearMap.comp_apply, mfderiv_inclusion_apply]

/-- On an open subset `U` of a normed space `E`, read with the model `𝓘(𝕜, E)`, the differential
at `x : U` of the restriction `f ∘ Subtype.val` of a map `f : E → E'` is the Fréchet derivative of
`f` at `x` (both are `0` when `f` is not differentiable there). -/
theorem mfderiv_modelSpace_comp_subtypeVal_apply {U : Opens E} {f : E → E'} {x : U}
    (v : TangentSpace 𝓘(𝕜, E) x) :
    mfderiv 𝓘(𝕜, E) 𝓘(𝕜, E') (f ∘ Subtype.val) x v = fderiv 𝕜 f x v := by
  rw [← mvfderiv_apply_eq_mfderiv_apply]
  exact mvfderiv_modelSpace_comp_subtype_val_apply (f := f) v

end
