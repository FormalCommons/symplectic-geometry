/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Contact.Moser
public import TauCeti.Geometry.Contact.Pullback
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Tangent.Basic

/-!
# Naturality of the contact-Moser vector field

For a contact form `α` on `N`, a one-form `β` on `N` and a smooth map `f : M → N` whose
differentials are bijective, the differential of `f` carries the horizontal contact-Moser vector
of the pulled-back pair `(f^* α, f^* β)` at `x` to the contact-Moser vector of `(α, β)` at `f x`
(`TauCeti.SmoothForm.IsContactForm.mfderiv_contactMoserVectorField_mpullback`). Restriction to an
open subset `U ⊆ N` is the case `f = Subtype.val`, in which the differential is the canonical
identification of tangent spaces
(`TauCeti.SmoothForm.IsContactForm.contactMoserVectorField_mpullback_subtype_val`); a
diffeomorphism is another case.

The proof is that of Tau Ceti's
`TauCeti.SmoothForm.IsContactForm.mfderiv_reebVectorField_mpullback`
for the Reeb field, with Tau Ceti's characterization
`TauCeti.SmoothForm.IsContactForm.eq_contactMoserVectorField_iff` in place of the
characterization of the Reeb field.

## Main results

* `TauCeti.SmoothForm.IsContactForm.mfderiv_contactMoserVectorField_mpullback`: naturality of the
  contact-Moser vector field under maps with bijective differentials.
* `TauCeti.SmoothForm.IsContactForm.contactMoserVectorField_mpullback_subtype_val`: its
  restriction to an open subset.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Theorem 2.2.2 (Gray stability) and its proof.
-/

public section

open TopologicalSpace
open scoped ContDiff Manifold

namespace TauCeti.SmoothForm.IsContactForm

variable {E H M F H' N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold I ∞ M] [IsManifold J ∞ N] [FiniteDimensional ℝ E]
  {α : SmoothForm J N ℝ 1}

/-- **Naturality of the contact-Moser vector field.** If `α` is a contact form on `N` and
`f : M → N` is smooth with bijective differentials, then for every one-form `β` on `N` the
differential of `f` at `x` sends the contact-Moser vector of `(f^* α, f^* β)` at `x` to the
contact-Moser vector of `(α, β)` at `f x`. -/
theorem mfderiv_contactMoserVectorField_mpullback (hα : α.IsContactForm)
    (f : M → N) (hf : ContMDiff I J ∞ f)
    (hdf : ∀ x, Function.Bijective (mfderiv I J f x)) (β : SmoothForm J N ℝ 1) (x : M) :
    mfderiv I J f x ((SmoothForm.mpullback f hf α).contactMoserVectorField
        (SmoothForm.mpullback f hf β) x) =
      α.contactMoserVectorField β (f x) := by
  have : FiniteDimensional ℝ F := LinearEquiv.finiteDimensional
    (LinearEquiv.ofBijective (mfderiv I J f x).toLinearMap (hdf x) :
      TangentSpace I x ≃ₗ[ℝ] TangentSpace J (f x))
  have hβ := hα.mpullback f hf hdf
  have hY :=
    (hβ.eq_contactMoserVectorField_iff (β := SmoothForm.mpullback f hf β) (x := x)).1 rfl
  simp only [mpullback_apply_one, mextDeriv_mpullback_apply_two, kerDistribution_mpullback,
    Submodule.mem_comap, ContinuousLinearMap.coe_coe] at hY
  refine hα.eq_contactMoserVectorField_iff.2 ⟨hY.1, fun w hw ↦ ?_⟩
  obtain ⟨u, rfl⟩ := (hdf x).2 w
  exact hY.2 u hw

/-- **The contact-Moser vector field restricts to open subsets.** For a contact form `α` on `N`,
a one-form `β` and an open subset `U ⊆ N`, the contact-Moser vector of the restrictions of
`α` and `β` to `U` at `x` is, under the canonical identification of tangent spaces, the
contact-Moser vector of `(α, β)` at `x`. -/
theorem contactMoserVectorField_mpullback_subtype_val [FiniteDimensional ℝ F]
    (hα : α.IsContactForm) (U : Opens N) (β : SmoothForm J N ℝ 1) (x : U) :
    Manifold.tangentSpaceOpenEquiv x
        ((SmoothForm.mpullback Subtype.val contMDiff_subtypeVal α).contactMoserVectorField
          (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal β) x) =
      α.contactMoserVectorField β x := by
  simpa only [Manifold.mfderiv_subtype_val, ContinuousLinearEquiv.coe_coe] using
    hα.mfderiv_contactMoserVectorField_mpullback Subtype.val contMDiff_subtypeVal
      Manifold.bijective_mfderiv_subtype_val β x

end TauCeti.SmoothForm.IsContactForm

end
