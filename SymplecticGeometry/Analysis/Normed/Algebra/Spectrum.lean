/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.Spectrum

/-!
# Joint continuity of the resolvent

In a complete normed algebra `A` over a nontrivially normed field `𝕜`, the resolvent
`(a, z) ↦ (z1 - a)⁻¹` is continuous, as a function of the pair, at every `(a, z)` with `z` in
the resolvent set of `a` (`spectrum.continuousAt_resolvent_prod`). This follows from the
continuity of inversion at units, Mathlib's `NormedRing.inverse_continuousAt`.
-/

public section

/-- The resolvent `(a, z) ↦ (z1 - a)⁻¹` is jointly continuous at every point `(a, z)` with `z` in
the resolvent set of `a`. -/
theorem spectrum.continuousAt_resolvent_prod {𝕜 A : Type*} [NontriviallyNormedField 𝕜]
    [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A] {a : A} {z : 𝕜}
    (hz : z ∈ resolventSet 𝕜 a) :
    ContinuousAt (fun p : A × 𝕜 ↦ resolvent p.1 p.2) (a, z) := by
  have hu := spectrum.mem_resolventSet_iff.mp hz
  simp only [resolvent]
  refine ContinuousAt.comp_of_eq (NormedRing.inverse_continuousAt hu.unit) ?_ hu.unit_spec.symm
  fun_prop

end
