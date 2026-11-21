/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Contact.Gray
public import SymplecticGeometry.Geometry.Contact.Moser
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Flow.Family

/-!
# Naturality of the Gray vector field

Let `α` be a one-form on `ℝ × N`, representing the family of its slices `α_t = ι_t^* α`, and let
`f : M → N` be smooth with bijective differentials. The slices of the pullback `(id × f)^* α` are
the pullbacks `f^* α_t`, and the slices of its time derivative are the pullbacks of the slices of
`∂_t α`. So if `α_t` is a contact form, the differential of `f` carries the Gray vector of the
pulled-back family at time `t` and point `x` to the Gray vector of `α` at time `t` and point
`f x` (`TauCeti.SmoothForm.mfderiv_grayVectorField_mpullback_prodMap`). The case of an open subset
`U ⊆ N`, `f = Subtype.val`, says that the Gray vector field of a family restricted to `ℝ × U`
is the restriction of the Gray vector field
(`TauCeti.SmoothForm.tangentSpaceOpenEquiv_grayVectorField_mpullback_prodMap_subtype_val`).
This lets one compare Gray vector fields of local defining families of a contact family that
live on different open sets.

## Main results

* `TauCeti.SmoothForm.mfderiv_grayVectorField_mpullback_prodMap`: naturality of the Gray vector
  field under `id × f` for maps `f` with bijective differentials.
* `TauCeti.SmoothForm.tangentSpaceOpenEquiv_grayVectorField_mpullback_prodMap_subtype_val`:
  its restriction to an open subset.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Theorem 2.2.2 (Gray stability) and its proof.
-/

public section

open TopologicalSpace
open scoped ContDiff Manifold

namespace TauCeti.SmoothForm

variable {E H M F H' N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold I ∞ M] [IsManifold J ∞ N] [I.Boundaryless] [J.Boundaryless]
  {α : SmoothForm (𝓘(ℝ, ℝ).prod J) (ℝ × N) ℝ 1}

/-- **Naturality of the Gray vector field.** Let `α` be a one-form on `ℝ × N` whose slice `α_t`
at time `t` is a contact form, and let `f : M → N` be smooth with bijective differentials. Then
the differential of `f` at `x` sends the Gray vector at time `t` and point `x` of the
pulled-back family `(id × f)^* α` to the Gray vector of `α` at time `t` and point `f x`. -/
theorem mfderiv_grayVectorField_mpullback_prodMap [FiniteDimensional ℝ E] {t : ℝ}
    (hc : (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).IsContactForm)
    (f : M → N) (hf : ContMDiff I J ∞ f)
    (hdf : ∀ x, Function.Bijective (mfderiv I J f x)) (x : M) :
    mfderiv I J f x
        ((mpullback (Prod.map id f) (contMDiff_id.prodMap hf) α).grayVectorField t x) =
      α.grayVectorField t (f x) := by
  rw [grayVectorField_def, grayVectorField_def, mpullback_prodMk_mpullback_prodMap,
    mpullback_prodMk_timeDeriv_mpullback_prodMap]
  exact hc.mfderiv_contactMoserVectorField_mpullback f hf hdf _ x

/-- **The Gray vector field restricts to open subsets.** Let `α` be a one-form on `ℝ × N` whose
slice `α_t` at time `t` is a contact form, and let `U ⊆ N` be open. Under the canonical
identification of tangent spaces, the Gray vector at time `t` and point `x ∈ U` of the
restriction of `α` to `ℝ × U` is the Gray vector of `α` at time `t` and point `x`. -/
theorem tangentSpaceOpenEquiv_grayVectorField_mpullback_prodMap_subtype_val
    [FiniteDimensional ℝ F] {t : ℝ}
    (hc : (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).IsContactForm)
    (U : Opens N) (x : U) :
    Manifold.tangentSpaceOpenEquiv x
        ((mpullback (Prod.map id Subtype.val) (contMDiff_id.prodMap contMDiff_subtypeVal)
          α).grayVectorField t x) =
      α.grayVectorField t x := by
  simpa only [Manifold.mfderiv_subtype_val, ContinuousLinearEquiv.coe_coe] using
    mfderiv_grayVectorField_mpullback_prodMap hc Subtype.val contMDiff_subtypeVal
      (fun y ↦ Manifold.mfderiv_subtype_val (I := J) y ▸
        (Manifold.tangentSpaceOpenEquiv (I := J) y).bijective) x

end TauCeti.SmoothForm

end
