/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Real
public import SymplecticGeometry.Geometry.Contact.Levi
public import SymplecticGeometry.Geometry.Contact.Moser
public import SymplecticGeometry.Geometry.Manifold.IsManifold.Basic
public import TauCeti.Geometry.Contact.Distribution
public import TauCeti.Geometry.Contact.Gray

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

Let `α` and `α'` be one-forms on `ℝ × M` whose slices at `t` are contact forms. If their slices
satisfy `α'_u = f(u, ·) α_u` near `(t, x)`, for times `u` in a set `s ∋ t` such as `[0, 1]` and a
function `f` differentiable and nonzero at `(t, x)`, then their Gray vector fields
(`TauCeti.SmoothForm.grayVectorField`) agree at `(t, x)`. The `dt` components of the forms play no
role, and no relation is asked at times outside `s`, so two local defining forms of a family over
`[0, 1]` can be compared at `t = 0` and `t = 1` too. This makes the Gray field of
a non-coorientable family well defined through local defining forms. It rests on the pointwise form
of the same fact for Tau Ceti's contact-Moser vector field, in
`SymplecticGeometry.Geometry.Contact.Moser`.

## Main definitions

* `SymplecticGeometry.IsContactFamily ξ`: `ξ` is a smooth family of contact structures over
  `[0, 1]`.

## Main results

* `SymplecticGeometry.IsContactFamily.of_isContactForm`: a one-form on the cylinder whose slices are
  contact forms defines a smooth family of contact structures by its kernels.
* `SymplecticGeometry.IsContactFamily.isContactDistribution`: each member of a smooth family of
  contact structures is a smooth contact structure.
* `TauCeti.SmoothForm.grayVectorField_eq_of_eventuallyEq_smul`: the Gray vector at `(t, x)` of a
  family whose slice at `t` is a contact form is unchanged when the slices at times of `s` are
  multiplied, near `(t, x)`, by a function nonzero at `(t, x)`.

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
  -- Near each `x`, the slice at `t` of a local defining form defines `ξ t` and is contact.
  have hloc (x : M) : ∃ β : TauCeti.SmoothForm I M ℝ 1, ∀ᶠ y in 𝓝 x,
      TauCeti.IsContactFormAt β.val y ∧ ξ t y = β.kerDistribution y := by
    obtain ⟨α, hα⟩ := hξ (t, x)
    exact ⟨TauCeti.SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α,
      ((continuous_const.prodMk continuous_id).continuousAt.eventually hα).mono
      fun _ h ↦ h⟩
  have hD : TauCeti.IsContMDiffDistribution I ∞ (finrank ℝ E - 1) (ξ t) :=
    .of_forall_eventuallyEq_kerDistribution fun x ↦
      have ⟨β, hβ⟩ := hloc x
      ⟨β, hβ.self_of_nhds.1.ne_zero, hβ.mono fun _ h ↦ h.2⟩
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

/-- **The Gray vector at a point does not depend on the defining family.** Let `α` and `α'` be
one-forms on `ℝ × M` whose slices at time `t` are contact forms, and let `s ∋ t` be a set of times
on which derivatives at `t` are unique, such as `[0, 1]`. Suppose that the slices satisfy
`α'_u = f(u, ·) α_u` at the points `(u, y)` of `s × M` near `(t, x)`, for a function `f` with
`f (t, x) ≠ 0` that is differentiable within `s` in time at `t` and differentiable in space at
`x`. Then the Gray vector fields of `α` and `α'` agree at time `t` and the point `x`. -/
theorem grayVectorField_eq_of_eventuallyEq_smul [I.Boundaryless]
    {α α' : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) ℝ 1} {f : ℝ × M → ℝ} {s : Set ℝ} {t : ℝ}
    {x : M} (hs : UniqueDiffWithinAt ℝ s t) (ht : t ∈ s)
    (hc : (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).IsContactForm)
    (hc' : (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α').IsContactForm)
    (hft : DifferentiableWithinAt ℝ (fun u ↦ f (u, x)) s t)
    (hfy : MDifferentiableAt I 𝓘(ℝ) (fun y ↦ f (t, y)) x) (hf₀ : f (t, x) ≠ 0)
    (h : ∀ᶠ q in 𝓝[s ×ˢ univ] (t, x),
      (mpullback (Prod.mk q.1) (contMDiff_const.prodMk contMDiff_id) α').val q.2 =
        f q • (mpullback (Prod.mk q.1) (contMDiff_const.prodMk contMDiff_id) α).val q.2) :
    α'.grayVectorField t x = α.grayVectorField t x := by
  -- The relation holds near `x` at time `t`, and near `t` within `s` at the point `x`.
  have hy := (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within (fun y : M ↦ (t, y))
    ((continuous_const.prodMk continuous_id).tendsto x)
    (.of_forall fun y ↦ mk_mem_prod ht (mem_univ y))).eventually h
  have hu := (((continuous_id.prodMk continuous_const).continuousWithinAt
    (x := t)).tendsto_nhdsWithin (t := s ×ˢ univ) fun _ hu ↦ ⟨hu, mem_univ x⟩).eventually h
  -- The velocities of the slices are related by the product rule.
  have hβ := hs.eq_deriv _ (hasDerivAt_mpullback_prodMk_timeDeriv α' t x).hasDerivWithinAt
    ((hft.hasDerivWithinAt.smul (hasDerivAt_mpullback_prodMk_timeDeriv α t x).hasDerivWithinAt
      ).congr_of_eventuallyEq hu (h.self_of_nhdsWithin ⟨ht, mem_univ x⟩))
  rw [grayVectorField_def, grayVectorField_def]
  exact hc.contactMoserVectorField_apply_of_eventuallyEq_smul hc' hfy hf₀ hy hβ

end TauCeti.SmoothForm

end
