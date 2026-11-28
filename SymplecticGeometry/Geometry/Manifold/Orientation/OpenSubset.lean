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

Tau Ceti identifies the tangent space of an open subset `U` of a manifold `M` at a point `x` with
the tangent space of `M` at `x` through `TauCeti.Manifold.tangentSpaceOpenEquiv x`, which is the
derivative of the inclusion `U → M` (`TauCeti.Manifold.mfderiv_subtype_val`). Tau Ceti's
`TauCeti.Manifold.Orientation.restrict` pulls an orientation of `M` back to `U`. Here its
orientation at each point is computed: through that identification, it is the orientation of `M`
at the same point.

## Main results

* `TauCeti.Manifold.Orientation.orientationAt_restrict`: Tau Ceti's
  `TauCeti.Manifold.Orientation.map_orientationAt_restrict` without the transport,
  which is possible since `tangentSpaceOpenEquiv x` is the identity.
* `TauCeti.Manifold.Orientation.isOrientationPreservingAt_restrict_iff`: a map into `U` preserves
  orientation into the restriction of `o` exactly when its composite with the inclusion of `U`
  preserves orientation into `o`.

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

/-- At each point `x` of an open subset `U`, the tangent orientation of the restriction of `o` to
`U` is that of `o` at `x`, the two tangent spaces being identified through
`TauCeti.Manifold.tangentSpaceOpenEquiv x`, which is the identity. The two sides have types that
agree only after unfolding `TangentSpace`; Tau Ceti's `map_orientationAt_restrict` states the
equality with the identification made explicit. -/
theorem orientationAt_restrict (o : Orientation I M ι) (U : Opens M) (x : U) :
    (o.restrict U).orientationAt x = o.orientationAt (x : M) := by
  have he : (TauCeti.Manifold.tangentSpaceOpenEquiv (I := I) x).toLinearEquiv =
      LinearEquiv.refl ℝ (TangentSpace I x) :=
    LinearEquiv.ext (TauCeti.Manifold.tangentSpaceOpenEquiv_apply x)
  rw [← map_orientationAt_restrict o U x, he]
  exact (Equiv.ext_iff.mp (_root_.Orientation.map_refl ι) _).symm

/-- A map `f` into an open subset `U` of `M` preserves orientation at `x`, from `o'` to the
restriction of `o` to `U`, exactly when its composite with the inclusion of `U` preserves
orientation at `x`, from `o'` to `o`. -/
theorem isOrientationPreservingAt_restrict_iff {E' H' N : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [TopologicalSpace H']
    {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' 1 N]
    {o : Orientation I M ι} {U : Opens M} {o' : Orientation I' N ι} {f : N → U} {x : N} :
    IsOrientationPreservingAt o' (o.restrict U) f x ↔
      IsOrientationPreservingAt o' o (Subtype.val ∘ f) x :=
  ⟨fun h ↦ (o.isOrientationPreservingAt_restrict U (f x)).comp h, fun h ↦
    .of_comp (o.isOrientationPreservingAt_restrict U (f x)) h
      (TauCeti.Manifold.mdifferentiableAt_subtype_val_comp_iff.1
        (mdifferentiableAt_of_isInvertible_mfderiv h.isInvertible_mfderiv))⟩

end TauCeti.Manifold.Orientation

end
