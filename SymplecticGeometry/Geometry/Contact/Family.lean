/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Real
public import TauCeti.Geometry.Contact.Distribution
public import TauCeti.Geometry.Contact.Gray
public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Leibniz

/-!
# Smooth families of contact structures

A family `ξ : unitInterval → Π x : M, Submodule ℝ (TangentSpace I x)` of distributions on `M` is a
smooth family of contact structures, `SymplecticGeometry.IsContactFamily ξ`, when near every point
`(t, x)` of the cylinder `[0, 1] × M` there is a smooth one-form `α` on the cylinder whose slices
`α_s = ι_s^* α`, `ι_s = Prod.mk s`, are contact at the nearby points `(s, y)` and have kernel
`ξ s y` there. No global defining form is asked for, so the family need not be coorientable, and
the neighbourhoods are taken in the cylinder, since a non-coorientable family need not be defined
by one form on `[0, 1] × U` for an open `U ⊆ M`.

Each member `ξ t` of such a family is a smooth contact structure in Tau Ceti's sense,
`TauCeti.IsContactDistribution I ∞ (ξ t)`, and a one-form on the cylinder all of whose slices are
contact forms defines one.

The Gray vector field of a family of contact forms on `ℝ × M` (`TauCeti.SmoothForm.grayVectorField`)
does not change at `(t, x)` when the family is multiplied by a function `f` which is
differentiable and nonzero at `(t, x)`, even when the two families are so related only near
`(t, x)`. This makes the Gray field of a non-coorientable family well defined through local
defining forms. It rests on the pointwise form of the same fact for Tau Ceti's contact-Moser
vector field.

## Main definitions

* `SymplecticGeometry.IsContactFamily ξ`: `ξ` is a smooth family of contact structures over
  `[0, 1]`.

## Main results

* `SymplecticGeometry.IsContactFamily.of_isContactForm`: a one-form on the cylinder whose slices are
  contact forms defines a smooth family of contact structures by its kernels.
* `SymplecticGeometry.IsContactFamily.isContactDistribution`: each member of a smooth family of
  contact structures is a smooth contact structure.
* `TauCeti.SmoothForm.IsContactForm.contactMoserVectorField_apply_of_eventuallyEq_smul`: the
  contact-Moser vector at `x` of `(α, β)` is unchanged when `α` is replaced, near `x`, by `f α`
  and `β_x` by `f(x) β_x + c α_x`.
* `TauCeti.SmoothForm.grayVectorField_eq_of_eventuallyEq_smul`: the Gray vector at `(t, x)`
  of a family whose slice at `t` is a contact form is unchanged when the family is multiplied,
  near `(t, x)`, by a function nonzero at `(t, x)`.

The proof of `contactMoserVectorField_apply_of_eventuallyEq_smul` is that of Tau Ceti's
`TauCeti.SmoothForm.IsContactForm.contactMoserVectorField_of_eq_smul`, with the relation between
the two forms asked for only near `x`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §3.5,
  the discussion of Gray stability on pp. 135–136 and Exercise 3.5.21.
* H. Geiges, *An Introduction to Contact Topology*, Cambridge Studies in Advanced Mathematics 109
  (2008), Theorem 2.2.2 (Gray stability) and its proof, which Tau Ceti's contact-Moser and Gray
  files follow.
-/

public section

noncomputable section

open Set Filter Function Module Bundle
open scoped Manifold Topology ContDiff

namespace SymplecticGeometry

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- A family `ξ` of distributions on `M`, indexed by `t ∈ [0, 1]`, is a **smooth family of contact
structures** when near every point of the cylinder `[0, 1] × M` it is given by a smooth one-form
`α` on the cylinder: at every nearby point `(s, y)` the slice `α_s = ι_s^* α` is a contact form at
`y` and its kernel there is `ξ s y`. -/
def IsContactFamily (ξ : unitInterval → Π x : M, Submodule ℝ (TangentSpace I x)) : Prop :=
  ∀ p : unitInterval × M, ∃ α : TauCeti.SmoothForm ((𝓡∂ 1).prod I) (unitInterval × M) ℝ 1,
    ∀ᶠ q in 𝓝 p,
      TauCeti.IsContactFormAt (TauCeti.SmoothForm.mpullback (Prod.mk q.1)
        (contMDiff_const.prodMk contMDiff_id) α).val q.2 ∧
      ξ q.1 q.2 = (TauCeti.SmoothForm.mpullback (Prod.mk q.1)
        (contMDiff_const.prodMk contMDiff_id) α).kerDistribution q.2

variable {ξ : unitInterval → Π x : M, Submodule ℝ (TangentSpace I x)}

/-- The definition of a smooth family of contact structures. -/
theorem isContactFamily_def : IsContactFamily ξ ↔
    ∀ p : unitInterval × M, ∃ α : TauCeti.SmoothForm ((𝓡∂ 1).prod I) (unitInterval × M) ℝ 1,
      ∀ᶠ q in 𝓝 p,
        TauCeti.IsContactFormAt (TauCeti.SmoothForm.mpullback (Prod.mk q.1)
          (contMDiff_const.prodMk contMDiff_id) α).val q.2 ∧
        ξ q.1 q.2 = (TauCeti.SmoothForm.mpullback (Prod.mk q.1)
          (contMDiff_const.prodMk contMDiff_id) α).kerDistribution q.2 :=
  Iff.rfl

/-- A smooth family of contact structures, with the kernels of the slices of the local defining
forms written as the vectors `v` for which `α` vanishes on the vertical vector `(0, v)`. -/
theorem isContactFamily_iff : IsContactFamily ξ ↔
    ∀ p : unitInterval × M, ∃ α : TauCeti.SmoothForm ((𝓡∂ 1).prod I) (unitInterval × M) ℝ 1,
      ∀ᶠ q in 𝓝 p,
        TauCeti.IsContactFormAt (TauCeti.SmoothForm.mpullback (Prod.mk q.1)
          (contMDiff_const.prodMk contMDiff_id) α).val q.2 ∧
        ∀ v : TangentSpace I q.2,
          v ∈ ξ q.1 q.2 ↔ α.val q ![((0 : EuclideanSpace ℝ (Fin 1)), v)] = 0 := by
  refine forall_congr' fun p ↦ exists_congr fun α ↦
    eventually_congr (.of_forall fun q ↦ and_congr_right' ?_)
  rw [SetLike.ext_iff]
  refine forall_congr' fun v ↦ ?_
  rw [TauCeti.SmoothForm.mem_kerDistribution, TauCeti.SmoothForm.mpullback_apply,
    mfderiv_prod_right]
  -- The slice inclusion `Prod.mk t` sends `v` to the vertical vector `(0, v)`.
  congr! 3
  ext i : 1
  fin_cases i
  exact ContinuousLinearMap.inr_apply v

namespace IsContactFamily

/-- **A family of contact forms defines a smooth family of contact structures**: if every slice
`α_t` of a one-form `α` on the cylinder `[0, 1] × M` is a contact form, then the kernels of the
slices form a smooth family of contact structures. -/
theorem of_isContactForm (α : TauCeti.SmoothForm ((𝓡∂ 1).prod I) (unitInterval × M) ℝ 1)
    (hc : ∀ t, (TauCeti.SmoothForm.mpullback (Prod.mk t)
      (contMDiff_const.prodMk contMDiff_id) α).IsContactForm) :
    IsContactFamily fun t ↦ (TauCeti.SmoothForm.mpullback (Prod.mk t)
      (contMDiff_const.prodMk contMDiff_id) α).kerDistribution :=
  fun _ ↦ ⟨α, .of_forall fun q ↦
    ⟨TauCeti.SmoothForm.isContactForm_iff_forall_isContactFormAt.1 (hc q.1) q.2, rfl⟩⟩

variable [FiniteDimensional ℝ E]

/-- **Each member of a smooth family of contact structures is a contact structure**: for every
`t ∈ [0, 1]`, the distribution `ξ t` is a smooth contact structure on `M`. -/
theorem isContactDistribution (hξ : IsContactFamily ξ) (t : unitInterval) :
    TauCeti.IsContactDistribution I ∞ (ξ t) := by
  have : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := IsManifold.of_le (n := ∞) (by simp)
  -- Near each `x`, the slice at `t` of a local defining form defines `ξ t` and is contact.
  have hloc (x : M) : ∃ β : TauCeti.SmoothForm I M ℝ 1, ∀ᶠ y in 𝓝 x,
      TauCeti.IsContactFormAt β.val y ∧ ξ t y = β.kerDistribution y := by
    obtain ⟨α, hα⟩ := hξ (t, x)
    exact ⟨TauCeti.SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α,
      ((continuous_const.prodMk continuous_id).continuousAt.eventually hα).mono
      fun _ h ↦ h⟩
  have hD : TauCeti.IsContMDiffDistribution I ∞ (finrank ℝ E - 1) (ξ t) := by
    refine TauCeti.IsContMDiffDistribution.of_mem_nhds fun x ↦ ?_
    obtain ⟨β, hβ⟩ := hloc x
    obtain ⟨U, hU, hxU, X, hX⟩ :=
      TauCeti.SmoothForm.exists_isDistributionFrameOn_kerDistribution (n := ∞)
        hβ.self_of_nhds.1.ne_zero
    refine ⟨U ∩ {y | ξ t y = β.kerDistribution y}, inter_mem (hU.mem_nhds hxU)
      (hβ.mono fun _ h ↦ h.2), X, ?_⟩
    have hX' := hX.mono (inter_subset_left (t := {y | ξ t y = β.kerDistribution y}))
    exact ⟨hX'.contMDiffOn, hX'.linearIndependent, fun hy ↦ (hX'.span_eq hy).trans hy.2.symm⟩
  refine (TauCeti.isContactDistribution_iff_forall_exists_isContactFormAt hD (by simp)).2
    fun x ↦ ?_
  obtain ⟨β, hβ⟩ := hloc x
  refine ⟨β.val, β.mdifferentiableAt x, hβ.mono fun y h ↦ ?_, hβ.self_of_nhds.1⟩
  rw [h.2, TauCeti.SmoothForm.kerDistribution_eq_ker]

end IsContactFamily

end SymplecticGeometry

namespace TauCeti.SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

/-- **The contact-Moser vector at a point under a change of defining form.** Let `α` and `α'` be
contact forms with `α' = f α` near `x`, for a function `f` differentiable at `x` with `f x ≠ 0`,
and let `β'_x = f(x) β_x + c α_x` for some `c : ℝ`. Then the contact-Moser vectors of `(α, β)` and
of `(α', β')` at `x` agree. No sign of `f` is needed, and nothing is asked away from `x`. -/
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

/-- **The Gray vector at a point does not depend on the defining family.** Let `α` and `α'` be
one-forms on `ℝ × M` whose slices at time `t` are contact forms, with `α' = f α` near `(t, x)` for
a function `f` differentiable at `(t, x)` with `f (t, x) ≠ 0`. Then their Gray vector fields
agree at time `t` and the point `x`. -/
theorem grayVectorField_eq_of_eventuallyEq_smul [I.Boundaryless]
    {α α' : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) ℝ 1} {f : ℝ × M → ℝ} {t : ℝ} {x : M}
    (hc : (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).IsContactForm)
    (hc' : (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α').IsContactForm)
    (hf : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) f (t, x)) (hfx : f (t, x) ≠ 0)
    (h : ∀ᶠ q in 𝓝 (t, x), α'.val q = f q • α.val q) :
    α'.grayVectorField t x = α.grayVectorField t x := by
  -- Where `α' = f • α`, the same holds for the values of the slices.
  have hslice {q : ℝ × M} (hq : α'.val q = f q • α.val q) :
      (mpullback (Prod.mk q.1) (contMDiff_const.prodMk contMDiff_id) α').val q.2 =
        f q • (mpullback (Prod.mk q.1) (contMDiff_const.prodMk contMDiff_id) α).val q.2 := by
    ext v
    simp [hq]
  have hfu : HasDerivAt (fun u ↦ f (u, x)) (deriv (fun u ↦ f (u, x)) t) t :=
    (mdifferentiableAt_iff_differentiableAt.1 (hf.comp t
      ((contMDiff_id.prodMk contMDiff_const : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) 1
        fun u : ℝ ↦ (u, x)).mdifferentiableAt one_ne_zero))).hasDerivAt
  have hβ := (hasDerivAt_mpullback_prodMk_timeDeriv α' t x).unique
    (((hfu.smul (hasDerivAt_mpullback_prodMk_timeDeriv α t x))).congr_of_eventuallyEq
      (((continuous_id.prodMk continuous_const).continuousAt.eventually h).mono
        fun u hu ↦ hslice hu))
  rw [grayVectorField_def, grayVectorField_def]
  exact hc.contactMoserVectorField_apply_of_eventuallyEq_smul hc' (f := fun y ↦ f (t, y))
    (hf.comp x ((contMDiff_const.prodMk contMDiff_id :
      ContMDiff I (𝓘(ℝ, ℝ).prod I) 1 (Prod.mk t)).mdifferentiableAt one_ne_zero)) hfx
    (((continuous_const.prodMk continuous_id).continuousAt.eventually h).mono
      fun y hy ↦ hslice hy) hβ

end TauCeti.SmoothForm

end
