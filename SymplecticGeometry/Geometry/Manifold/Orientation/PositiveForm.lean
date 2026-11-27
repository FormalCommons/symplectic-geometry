/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.Preserving
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.TopForm
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Positivity
import TauCeti.Geometry.Manifold.Orientation.TopForm.Existence

/-!
# Top forms positive for an orientation

A top form `φ` on an oriented manifold is *positive* for the orientation `o` when it takes a
positive value on every tangent basis whose orientation is that of `o`. This file shows that
positivity is carried back along maps that preserve orientation: if `f` preserves the
orientations `o` and `o'` at `x`, and `φ` is positive for `o'` at `f x`, then `f^* φ` is positive
for `o` at `x`, since the derivative of `f` at `x` carries a positively oriented basis to one.
It also shows that a nonempty compact Hausdorff oriented manifold carries a smooth top form
positive for its orientation with integral one: Tau Ceti's
`TauCeti.exists_topForm_of_orientation`, divided by its integral, which is positive.

## Main results

* `TauCeti.Manifold.Orientation.IsOrientationPreservingAt.mpullback_apply_pos`: pull-backs along
  orientation-preserving maps keep top forms positive.
* `TauCeti.exists_smoothForm_pos_integralTopForm_eq_one`: a positive smooth top form of integral
  one.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 15 and Proposition 16.6.
-/

public section

open scoped Manifold ContDiff

namespace TauCeti.Manifold.Orientation

variable {E H M E' H' M' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M']
  [ChartedSpace H' M'] [IsManifold I' 1 M'] {k : ℕ}

/-- **Pull-backs of positive top forms.** Let `f` preserve the orientations `o` and `o'` at `x`,
and let the top form `φ` take a positive value at `f x` on every basis with the orientation of
`o'` there. Then its pull-back `f^* φ` takes a positive value at `x` on every basis with the
orientation of `o` there. -/
theorem IsOrientationPreservingAt.mpullback_apply_pos {o : Manifold.Orientation I M (Fin k)}
    {o' : Manifold.Orientation I' M' (Fin k)} {f : M → M'} {x : M}
    (hf : IsOrientationPreservingAt o o' f x) {φ : RoughForm I' M' ℝ k}
    (hφ : ∀ c : Module.Basis (Fin k) ℝ (TangentSpace I' (f x)),
      c.orientation = o'.orientationAt (f x) → 0 < φ (f x) c)
    (c : Module.Basis (Fin k) ℝ (TangentSpace I x)) (hc : c.orientation = o.orientationAt x) :
    0 < mpullback I I' f φ x c := by
  obtain ⟨e, he, hmap⟩ := (isOrientationPreservingAt_iff _ _ _ _).1 hf
  -- The derivative carries `c` to the basis `c.map e`, which has the orientation of `o'`.
  have h := hφ (c.map e.toLinearEquiv) (by rw [Module.Basis.orientation_map, hc, hmap])
  rw [mpullback_apply]
  convert h using 2
  funext i
  simp [← he]

end TauCeti.Manifold.Orientation

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M] [Nonempty M] {k : ℕ} [NeZero k]

/-- **Positive top forms of integral one.** On a nonempty compact Hausdorff manifold with an
orientation `o`, some smooth top form takes a positive value on every basis with the orientation
of `o` and has integral one. -/
theorem exists_smoothForm_pos_integralTopForm_eq_one (o : Manifold.Orientation I M (Fin k)) :
    ∃ σ : SmoothForm I M ℝ k, (∀ x (c : Module.Basis (Fin k) ℝ (TangentSpace I x)),
      c.orientation = o.orientationAt x → 0 < σ.val x c) ∧ integralTopForm o σ.val = 1 := by
  obtain ⟨φ, -, hφ⟩ := exists_topForm_of_orientation o
  obtain ⟨x⟩ := ‹Nonempty M›
  -- `TangentSpace I x` is the model space `E` by definition
  have hx : Module.finrank ℝ (TangentSpace I x) = k := by simpa using o.card_eq.symm
  let c := (Module.finBasisOfFinrankEq ℝ (TangentSpace I x) hx).adjustToOrientation
    (o.orientationAt x)
  have hc : c.orientation = o.orientationAt x := Module.Basis.orientation_adjustToOrientation _ _
  have hpos : 0 < integralTopForm o φ.val :=
    integralTopForm_pos o (φ.isSmoothForm.of_le (by simp)) (isClosed_tsupport _).isCompact
      (fun y c hc ↦ ((hφ y c).2 hc).le) ⟨x, c, hc, (hφ x c).2 hc⟩
  refine ⟨(integralTopForm o φ.val)⁻¹ • φ, fun y c hc ↦ ?_, ?_⟩
  · simpa using mul_pos (inv_pos.2 hpos) ((hφ y c).2 hc)
  · rw [Submodule.coe_smul, integralTopForm_smul, inv_mul_cancel₀ hpos.ne']

end TauCeti

end
