/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Contact.Moser
public import TauCeti.Geometry.Contact.Pullback
import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Leibniz
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset

/-!
# The contact-Moser vector field: change of defining form and naturality

This file proves two properties of Tau Ceti's horizontal contact-Moser vector field.

First, Tau Ceti's `TauCeti.SmoothForm.IsContactForm.contactMoserVectorField_of_eq_smul` compares
the contact-Moser vector fields of `(α, β)` and of `(f α, f β + g α)` everywhere on `M`. This file
proves the same comparison at a single point `x`, with the two forms related only near `x`, the
multiplier `f` only differentiable and nonzero at `x`, and the second forms related only at `x`.
The proof is that of Tau Ceti's `contactMoserVectorField_of_eq_smul`, with the relation between
the two forms asked for only near `x`.

Second, for a contact form `α` on `N`, a one-form `β` on `N` and a smooth map `f : M → N` whose
differentials are bijective, the differential of `f` carries the contact-Moser vector of the
pulled-back pair `(f^* α, f^* β)` at `x` to the contact-Moser vector of `(α, β)` at `f x`.
Restriction to an open subset `U ⊆ N` is the case `f = Subtype.val`, in which the differential is
the canonical identification of tangent spaces; a diffeomorphism is another case. The proof is
that of Tau Ceti's `TauCeti.SmoothForm.IsContactForm.mfderiv_reebVectorField_mpullback` for the
Reeb field, with Tau Ceti's characterization
`TauCeti.SmoothForm.IsContactForm.eq_contactMoserVectorField_iff` in place of the
characterization of the Reeb field.

## Main results

* `TauCeti.SmoothForm.IsContactForm.contactMoserVectorField_apply_of_eventuallyEq_smul`: the
  contact-Moser vector at `x` of `(α, β)` is unchanged when `α` is replaced, near `x`, by `f α`
  and `β_x` by `f(x) β_x + c α_x`.
* `TauCeti.SmoothForm.IsContactForm.mfderiv_contactMoserVectorField_mpullback`: naturality of the
  contact-Moser vector field under maps with bijective differentials.
* `IsContactForm.tangentSpaceOpenEquiv_contactMoserVectorField_mpullback_subtypeVal` (in the
  namespace `TauCeti.SmoothForm`): its restriction to an open subset.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge Studies in Advanced Mathematics 109
  (2008), Theorem 2.2.2 (Gray stability) and its proof, which Tau Ceti's contact-Moser file
  follows.
-/

public section

open Filter TopologicalSpace
open scoped Manifold Topology ContDiff

namespace TauCeti.SmoothForm

variable {E H M F H' N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold I ∞ M] [IsManifold J ∞ N] [FiniteDimensional ℝ E]

/-- **The contact-Moser vector at a point under a change of defining form.** Let `α` and `α'` be
contact forms on `M` with `α' = f α` near `x`, for a function `f` differentiable at `x` with
`f x ≠ 0`, and let `β'_x = f(x) β_x + c α_x` for some `c : ℝ`. Then the contact-Moser vectors of
`(α, β)` and of `(α', β')` at `x` agree. Both forms are contact on all of `M`; only their relation,
and that of `β` and `β'`, is local. No sign of `f` is needed. -/
theorem IsContactForm.contactMoserVectorField_apply_of_eventuallyEq_smul
    {α α' β β' : SmoothForm I M ℝ 1} (hα : α.IsContactForm) (hα' : α'.IsContactForm)
    {f : M → ℝ} {x : M} {c : ℝ} (hf : MDifferentiableAt I 𝓘(ℝ) f x) (hfx : f x ≠ 0)
    (h : ∀ᶠ y in 𝓝 x, α'.val y = f y • α.val y)
    (hβ : β'.val x = f x • β.val x + c • α.val x) :
    α'.contactMoserVectorField β' x = α.contactMoserVectorField β x := by
  symm
  have hY := hα.apply_contactMoserVectorField β x
  have h₀ : α'.val x = f x • α.val x := h.self_of_nhds
  refine hα'.eq_contactMoserVectorField_iff.2 ⟨by simp [h₀, hY], fun w hw ↦ ?_⟩
  have hwα : α.val x ![w] = 0 := by
    have := mem_kerDistribution.1 hw
    rw [h₀, ContinuousAlternatingMap.smul_apply, smul_eq_mul] at this
    exact (mul_eq_zero.1 this).resolve_left hfx
  have hd := (hα.eq_contactMoserVectorField_iff (β := β) (x := x)).1 rfl
  rw [mextDeriv_congr_of_eventuallyEq h, TauCeti.mextDeriv_fun_smul_apply hf
    (α.mdifferentiableAt x), hY, hwα, hβ]
  simp only [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
    smul_eq_mul, hwα, mul_zero, sub_zero, zero_add, add_zero]
  rw [← mul_add, hd.2 w (mem_kerDistribution.2 hwα), mul_zero]

/-- **Naturality of the contact-Moser vector field.** If `α` is a contact form on `N` and
`f : M → N` is smooth with bijective differentials, then for every one-form `β` on `N` the
differential of `f` at `x` sends the contact-Moser vector of `(f^* α, f^* β)` at `x` to the
contact-Moser vector of `(α, β)` at `f x`. -/
theorem IsContactForm.mfderiv_contactMoserVectorField_mpullback {α : SmoothForm J N ℝ 1}
    (hα : α.IsContactForm) (f : M → N) (hf : ContMDiff I J ∞ f)
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
theorem IsContactForm.tangentSpaceOpenEquiv_contactMoserVectorField_mpullback_subtypeVal
    [FiniteDimensional ℝ F] {α : SmoothForm J N ℝ 1} (hα : α.IsContactForm) (U : Opens N)
    (β : SmoothForm J N ℝ 1) (x : U) :
    Manifold.tangentSpaceOpenEquiv x
        ((SmoothForm.mpullback Subtype.val contMDiff_subtypeVal α).contactMoserVectorField
          (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal β) x) =
      α.contactMoserVectorField β x := by
  simpa only [Manifold.mfderiv_subtype_val, ContinuousLinearEquiv.coe_coe] using
    hα.mfderiv_contactMoserVectorField_mpullback Subtype.val contMDiff_subtypeVal
      (fun y ↦ TauCeti.bijective_mfderiv_subtype_val (I := J) y) β x

end TauCeti.SmoothForm

end
