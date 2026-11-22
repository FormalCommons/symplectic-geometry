/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.OpenSubset
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic

/-!
# The tangent orientations of a restricted orientation

The tangent space of an open subset `U` of a manifold `M` at a point `x` is the tangent space of
`M` at `x`: both are the model space `E`, and the derivative of the inclusion `U → M` is the
identity of `E` (`TauCeti.Manifold.mfderiv_subtype_val`). Tau Ceti's
`TauCeti.Manifold.Orientation.restrict` pulls an orientation of `M` back to `U`. Here its
orientation at each point is computed: it is that of the orientation of `M` at the same point.

## Main results

* `TauCeti.Manifold.Orientation.orientationAt_restrict`: the restriction of `o` to `U` has, at
  each point of `U`, the orientation that `o` has there.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in Mathematics
  218, Springer (2013), Chapter 15 (orientations of open submanifolds).
-/

public section

open TopologicalSpace

namespace TauCeti.Manifold.Orientation

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] {ι : Type*} [Fintype ι]

/-- At each point of an open subset `U`, the restriction of `o` to `U` has the orientation that
`o` has at that point; both are orientations of the model space `E`. -/
@[simp]
theorem orientationAt_restrict (o : Orientation I M ι) (U : Opens M) (x : U) :
    (o.restrict U).orientationAt x = o.orientationAt (x : M) := by
  have h := (isOrientationPreservingAt_iff_of_coe_eq (o.restrict U) o Subtype.val x
    (TauCeti.Manifold.tangentSpaceOpenEquiv x) (TauCeti.Manifold.mfderiv_subtype_val x).symm).1
    (o.isOrientationPreservingAt_restrict U x)
  have he : (TauCeti.Manifold.tangentSpaceOpenEquiv (I := I) x).toLinearEquiv =
      LinearEquiv.refl ℝ (TangentSpace I x) :=
    LinearEquiv.ext (TauCeti.Manifold.tangentSpaceOpenEquiv_apply x)
  rw [← h, he]
  exact (Equiv.ext_iff.mp (_root_.Orientation.map_refl ι) _).symm

end TauCeti.Manifold.Orientation

end
