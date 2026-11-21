/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Contact.Levi

/-!
# Distributions that are locally the kernel of a one-form

Tau Ceti's `TauCeti.SmoothForm.isContMDiffDistribution_kerDistribution` shows that the kernel of a
nowhere vanishing smooth one-form is a smooth hyperplane field. This file proves the local version:
a distribution that near each point is the kernel of a smooth one-form not vanishing at that point
is a smooth hyperplane field. Such a distribution need not be the kernel of one global form, as
for a contact structure that is not coorientable.

## Main results

* `TauCeti.IsContMDiffDistribution.of_forall_eventuallyEq_kerDistribution`: a distribution that
  near each point `x` is `ker β` for a smooth one-form `β` with `β_x ≠ 0` is a `C^n`
  distribution of rank `dim E - 1`.

The proof restricts the local frames of Tau Ceti's
`TauCeti.SmoothForm.exists_isDistributionFrameOn_kerDistribution`, as Tau Ceti's
`TauCeti.SmoothForm.isContMDiffDistribution_kerDistribution` uses them for a global form.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge Studies in Advanced Mathematics 109
  (2008), §1.1, where contact structures are defined locally by one-forms.
-/

public section

open Set Filter Module
open scoped Manifold Topology ContDiff

namespace TauCeti.IsContMDiffDistribution

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 2 M] {n : ℕ∞ω} [ENat.LEInfty n] [IsManifold I (n + 1) M]

/-- **A distribution that is locally the kernel of a one-form is a smooth hyperplane field.** If
near each point `x` the distribution `D` is the kernel of a smooth one-form `β` with `β_x ≠ 0`,
then `D` is a `C^n` distribution of rank `dim E - 1`. -/
theorem of_forall_eventuallyEq_kerDistribution {D : Π x : M, Submodule ℝ (TangentSpace I x)}
    (h : ∀ x, ∃ β : SmoothForm I M ℝ 1, β.val x ≠ 0 ∧ ∀ᶠ y in 𝓝 x, D y = β.kerDistribution y) :
    IsContMDiffDistribution I n (finrank ℝ E - 1) D := by
  refine of_mem_nhds fun x ↦ ?_
  obtain ⟨β, hβx, hβ⟩ := h x
  obtain ⟨U, hU, hxU, X, hX⟩ := SmoothForm.exists_isDistributionFrameOn_kerDistribution (n := n) hβx
  refine ⟨U ∩ {y | D y = β.kerDistribution y}, inter_mem (hU.mem_nhds hxU) hβ, X, ?_⟩
  have hX' := hX.mono (inter_subset_left (t := {y | D y = β.kerDistribution y}))
  exact ⟨hX'.contMDiffOn, hX'.linearIndependent, fun hy ↦ (hX'.span_eq hy).trans hy.2.symm⟩

end TauCeti.IsContMDiffDistribution

end
