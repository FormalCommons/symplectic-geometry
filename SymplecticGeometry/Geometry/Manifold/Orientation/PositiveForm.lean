/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.Preserving
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Basic

/-!
# Top forms positive for an orientation

A top form `φ` on an oriented manifold is *positive* for the orientation `o` when it takes a
positive value on every tangent basis whose orientation is that of `o`. This file shows that
positivity is carried back along maps that preserve orientation: if `f` preserves the
orientations `o` and `o'` at `x`, and `φ` is positive for `o'` at `f x`, then `f^* φ` is positive
for `o` at `x`, since the derivative of `f` at `x` carries a positively oriented basis to one.

## Main results

* `TauCeti.Manifold.Orientation.IsOrientationPreservingAt.mpullback_apply_pos`: pull-backs along
  orientation-preserving maps keep top forms positive.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 15.
-/

public section

open scoped Manifold

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

end
