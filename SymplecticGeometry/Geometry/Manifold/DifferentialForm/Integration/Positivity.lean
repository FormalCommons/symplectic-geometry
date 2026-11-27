/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Positivity
import TauCeti.Geometry.Manifold.Orientation.TopForm.Existence

/-!
# Integrals of top forms positive on every positive basis

A continuous, compactly supported top form on a nonempty oriented manifold of positive dimension
that is positive on every positively oriented tangent basis has positive integral
(`TauCeti.integralTopForm_pos_of_forall_pos`). This is Tau Ceti's `TauCeti.integralTopForm_pos`,
whose hypothesis of a point and a basis where the form is positive is met at any point, by a
positively oriented basis of its tangent space (`Orientation.someBasis`).

On a nonempty compact Hausdorff oriented manifold of positive dimension, Tau Ceti's
`TauCeti.exists_topForm_of_orientation` gives a smooth top form positive for the orientation; its
integral is then positive, and dividing by it gives such a form of integral one
(`TauCeti.exists_smoothForm_pos_integralTopForm_eq_one`).

## Main results

* `TauCeti.integralTopForm_pos_of_forall_pos`: a top form positive on every positively oriented
  tangent basis of a nonempty manifold has positive integral.
* `TauCeti.exists_smoothForm_pos_integralTopForm_eq_one`: a nonempty compact Hausdorff oriented
  manifold carries a smooth top form, positive for the orientation, of integral one.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  Proposition 16.6.
-/

public section

open scoped Manifold ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {k : ℕ}

/-- **Positivity of integration.** On a nonempty oriented manifold of positive dimension, a
continuous, compactly supported top form that is positive on every positively oriented tangent
basis has positive integral. -/
theorem integralTopForm_pos_of_forall_pos [IsManifold I 1 M] [NeZero k] [Nonempty M]
    (o : Manifold.Orientation I M (Fin k)) {φ : RoughForm I M ℝ k} (hφ : IsSmoothForm I 0 φ)
    (hc : IsCompact (_root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) φ))
    (hpos : ∀ x (c : Module.Basis (Fin k) ℝ (TangentSpace I x)),
      c.orientation = o.orientationAt x → 0 < φ x c) :
    0 < integralTopForm o φ := by
  obtain ⟨x⟩ := ‹Nonempty M›
  have hb := (o.orientationAt x).someBasis_orientation (o.finrank_tangentSpace_eq x).symm
  exact integralTopForm_pos o hφ hc (fun y c hc ↦ (hpos y c hc).le) ⟨x, _, hb, hpos x _ hb⟩

/-- **Positive top forms of integral one.** On a nonempty compact Hausdorff manifold of positive
dimension with an orientation `o`, some smooth top form takes a positive value on every basis
with the orientation of `o` and has integral one. -/
theorem exists_smoothForm_pos_integralTopForm_eq_one [IsManifold I ∞ M] [T2Space M]
    [CompactSpace M] [Nonempty M] [NeZero k] (o : Manifold.Orientation I M (Fin k)) :
    ∃ σ : SmoothForm I M ℝ k, (∀ x (c : Module.Basis (Fin k) ℝ (TangentSpace I x)),
      c.orientation = o.orientationAt x → 0 < σ.val x c) ∧ integralTopForm o σ.val = 1 := by
  obtain ⟨φ, -, hφ⟩ := exists_topForm_of_orientation o
  have hpos : 0 < integralTopForm o φ.val :=
    integralTopForm_pos_of_forall_pos o (φ.isSmoothForm.of_le (by simp))
      (isClosed_tsupport _).isCompact fun y c hc ↦ (hφ y c).2 hc
  refine ⟨(integralTopForm o φ.val)⁻¹ • φ, fun y c hc ↦ ?_, ?_⟩
  · simpa using mul_pos (inv_pos.2 hpos) ((hφ y c).2 hc)
  · rw [Submodule.coe_smul, integralTopForm_smul, inv_mul_cancel₀ hpos.ne']

end TauCeti

end
