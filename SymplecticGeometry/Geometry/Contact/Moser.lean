/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Contact.Moser
import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Leibniz

/-!
# The contact-Moser vector at a point under a change of defining form

Tau Ceti's `TauCeti.SmoothForm.IsContactForm.contactMoserVectorField_of_eq_smul` compares the
contact-Moser vector fields of `(α, β)` and of `(f α, f β + g α)` everywhere on `M`. This file
proves the same comparison at a single point `x`, with the two forms related only near `x`, the
multiplier `f` only differentiable and nonzero at `x`, and the second forms related only at `x`.

## Main results

* `TauCeti.SmoothForm.IsContactForm.contactMoserVectorField_apply_of_eventuallyEq_smul`: the
  contact-Moser vector at `x` of `(α, β)` is unchanged when `α` is replaced, near `x`, by `f α`
  and `β_x` by `f(x) β_x + c α_x`.

The proof is that of Tau Ceti's
`TauCeti.SmoothForm.IsContactForm.contactMoserVectorField_of_eq_smul`, with the relation between
the two forms asked for only near `x`.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge Studies in Advanced Mathematics 109
  (2008), Theorem 2.2.2 (Gray stability) and its proof, which Tau Ceti's contact-Moser file
  follows.
-/

public section

open Filter
open scoped Manifold Topology ContDiff

namespace TauCeti.SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

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

end TauCeti.SmoothForm

end
