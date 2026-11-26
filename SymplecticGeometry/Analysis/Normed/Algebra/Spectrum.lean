/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import TauCeti.Analysis.Calculus.ContinuousLinearMapInverse

/-!
# Joint continuity of the resolvent

In a normed algebra `A` over a nontrivially normed field `𝕜` whose geometric series are summable
(for instance a complete one), the resolvent `(a, z) ↦ (z1 - a)⁻¹` is continuous, as a function
of the pair, at every `(a, z)` with `z` in the resolvent set of `a`
(`spectrum.continuousAt_resolvent_prod`). This follows from the continuity of the ring inverse
at units, Tau Ceti's `ContinuousAt.ringInverse`.
-/

public section

/-- The resolvent `(a, z) ↦ (z1 - a)⁻¹` is jointly continuous at every point `(a, z)` with `z` in
the resolvent set of `a`. -/
theorem spectrum.continuousAt_resolvent_prod {𝕜 A : Type*} [NontriviallyNormedField 𝕜]
    [NormedRing A] [NormedAlgebra 𝕜 A] [HasSummableGeomSeries A] {a : A} {z : 𝕜}
    (hz : z ∈ resolventSet 𝕜 a) :
    ContinuousAt (fun p : A × 𝕜 ↦ resolvent p.1 p.2) (a, z) :=
  ContinuousAt.ringInverse (by fun_prop) (spectrum.mem_resolventSet_iff.mp hz)

end
