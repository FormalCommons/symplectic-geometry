/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Positivity

/-!
# Integrals of top forms positive on every positive basis

A continuous, compactly supported top form on a nonempty oriented manifold of positive dimension
that is positive on every positively oriented tangent basis has positive integral
(`TauCeti.integralTopForm_pos_of_forall_pos`). This is Tau Ceti's `TauCeti.integralTopForm_pos`,
whose hypothesis of a point and a basis where the form is positive is met at any point, by a
positively oriented basis of its tangent space (`Orientation.someBasis`).

## Main results

* `TauCeti.integralTopForm_pos_of_forall_pos`: a top form positive on every positively oriented
  tangent basis of a nonempty manifold has positive integral.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  Proposition 16.6.
-/

public section

open scoped Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] {k : ℕ}

/-- **Positivity of integration.** On a nonempty oriented manifold of positive dimension, a
continuous, compactly supported top form that is positive on every positively oriented tangent
basis has positive integral. -/
theorem integralTopForm_pos_of_forall_pos [NeZero k] [Nonempty M]
    (o : Manifold.Orientation I M (Fin k)) {φ : RoughForm I M ℝ k} (hφ : IsSmoothForm I 0 φ)
    (hc : IsCompact (_root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) φ))
    (hpos : ∀ x (c : Module.Basis (Fin k) ℝ (TangentSpace I x)),
      c.orientation = o.orientationAt x → 0 < φ x c) :
    0 < integralTopForm o φ := by
  obtain ⟨x⟩ := ‹Nonempty M›
  have hb := (o.orientationAt x).someBasis_orientation (o.finrank_tangentSpace_eq x).symm
  exact integralTopForm_pos o hφ hc (fun y c hc ↦ (hpos y c hc).le) ⟨x, _, hb, hpos x _ hb⟩

end TauCeti

end
