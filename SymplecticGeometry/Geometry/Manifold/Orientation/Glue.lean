/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.Pullback

/-!
# Gluing an orientation from a family of pieces

Let `f k : M k → X`, for `k` in a nonempty index type `κ`, be `C^n` local diffeomorphisms,
`n ≠ 0`, on a common model, whose ranges cover `X`, and let `o k` be an orientation of `M k`. If
at any `x : M k` and `y : M l` with `f k x = f l y` the derivatives of
`f k` and `f l` carry the tangent orientations of `o k` and `o l` to the same orientation of the
tangent space of `X`, then `X` has exactly one orientation that every `f k` preserves, from `o k`,
at every point.

Tau Ceti's `TauCeti.Manifold.Orientation.glue` does this for two pieces. Here the family is
arbitrary, as when a surface is capped with one disc for each boundary circle; neither Tau Ceti
nor Mathlib orients a sigma type, which would reduce this to two pieces.

Unlike `glue`, no piece need be injective: the hypothesis with `k = l` already says that the
orientation carried along `f k` depends only on the point of `X`.

The construction and its proofs follow those of `TauCeti.Manifold.Orientation.glue`,
`TauCeti.Manifold.Orientation.isOrientationPreservingAt_glue_left` and
`TauCeti.Manifold.Orientation.eq_glue_iff`: the tangent orientation at a point of `X` is carried
from a chosen preimage, the hypothesis makes it independent of the choice, and it is locally
constant by `IsLocalDiffeomorphAt.eventually_mapOrientation_eq`, so that
`TauCeti.Manifold.Orientation.ofVectorBundleOrientation` makes it an orientation.

## Main definitions

* `TauCeti.Manifold.Orientation.iGlue`: the orientation glued from the orientations of the pieces.

## Main results

* `TauCeti.Manifold.Orientation.isOrientationPreservingAt_iGlue`: each `f k` preserves orientation
  from `o k` to the glued orientation.
* `TauCeti.Manifold.Orientation.eq_iGlue_iff`: this property characterizes the glued orientation.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in Mathematics
  218, Springer (2013), Chapter 15 (orientations, and their pullbacks along local
  diffeomorphisms).
-/

public section

noncomputable section

open Set Function Filter Module
open scoped Manifold Topology

namespace TauCeti.Manifold.Orientation

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {n : WithTop ℕ∞} [NeZero n]
  {κ : Type*} {M : κ → Type*} [∀ k, TopologicalSpace (M k)]
  [∀ k, ChartedSpace H (M k)] [∀ k, IsManifold I 1 (M k)]
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I 1 X]
  {ι : Type*} [Fintype ι] {f : ∀ k, M k → X}
  (hf : ∀ k, IsLocalDiffeomorph I I n (f k))
  (hcov : ⋃ k, range (f k) = univ) (o : ∀ k, Orientation I (M k) ι)

/-- The tangent orientation of `X` at `f k x`, carried from `o k` by the derivative of `f k`. -/
private def iCarry (k : κ) (x : M k) : _root_.Orientation ℝ (TangentSpace I (f k x)) ι :=
  _root_.Orientation.map ι ((hf k x).mfderivToContinuousLinearEquiv (NeZero.ne n)).toLinearEquiv
    ((o k).orientationAt x)

/-- The tangent orientation of `X` at `p`, carried from a chosen preimage of `p`. -/
private def iGlueAt (p : X) : _root_.Orientation ℝ (TangentSpace I p) ι :=
  -- The tangent spaces of `X` are all the model space, so the orientation at `f k x` is one at `p`.
  have hp := mem_iUnion.1 (hcov ▸ mem_univ p)
  iCarry hf o hp.choose (mem_range.1 hp.choose_spec).choose

variable {o}
  (h : ∀ k l (x : M k) (y : M l), f k x = f l y →
    _root_.Orientation.map ι ((hf k x).mfderivToContinuousLinearEquiv (NeZero.ne n)).toLinearEquiv
        ((o k).orientationAt x) =
      _root_.Orientation.map ι ((hf l y).mfderivToContinuousLinearEquiv (NeZero.ne n)).toLinearEquiv
        ((o l).orientationAt y))

omit [IsManifold I 1 X] in
include h in
private theorem iGlueAt_apply (k : κ) (x : M k) : iGlueAt hf hcov o (f k x) = iCarry hf o k x := by
  have hp := mem_iUnion.1 (hcov ▸ mem_univ (f k x))
  exact h _ _ _ _ (mem_range.1 hp.choose_spec).choose_spec

variable [Nonempty κ]

open Classical in
/-- **Gluing an orientation from a family of pieces.** Let `f k : M k → X`, `k : κ` with `κ`
nonempty, be `C^n` local diffeomorphisms, `n ≠ 0`, whose ranges cover `X`, and let `o k` orient
`M k`. If at any `x : M k` and `y : M l` with `f k x = f l y` the derivatives of `f k` and `f l`
carry the tangent orientations of `o k` and `o l` to the same orientation, then `X` carries the
orientation whose tangent orientation is carried from `o k` along `f k` for every `k`
(`TauCeti.Manifold.Orientation.isOrientationPreservingAt_iGlue`). -/
def iGlue : Orientation I X ι :=
  -- The model orientation only selects a representative lift, which the quotient forgets.
  have hι := (o (Classical.arbitrary κ)).card_eq
  ofVectorBundleOrientation
    (((finBasisOfFinrankEq ℝ E hι.symm).reindex (Fintype.equivFin ι).symm).orientation) hι
    ⟨iGlueAt hf hcov o, fun b ↦ by
      -- Near the image of a point of `M k`, the tangent orientations are carried from `o k` by a
      -- local diffeomorphism, so they are locally constant.
      obtain ⟨k, x, rfl⟩ := mem_iUnion.1 (hcov ▸ mem_univ b)
      exact (hf k x).eventually_mapOrientation_eq (o k) (iGlueAt hf hcov o)
        (.of_forall fun x' ↦ ⟨(hf k x').mfderivToContinuousLinearEquiv (NeZero.ne n), rfl,
          (iGlueAt_apply hf hcov h k x').symm⟩)⟩

/-- Each `f k` preserves orientation from `o k` to the glued orientation. -/
theorem isOrientationPreservingAt_iGlue (k : κ) (x : M k) :
    IsOrientationPreservingAt (o k) (iGlue hf hcov h) (f k) x := by
  refine (isOrientationPreservingAt_iff_of_coe_eq _ _ _ x
    ((hf k x).mfderivToContinuousLinearEquiv (NeZero.ne n))
    ((hf k x).mfderivToContinuousLinearEquiv_coe _)).2 ?_
  rw [iGlue, orientationAt_ofVectorBundleOrientation]
  exact (iGlueAt_apply hf hcov h k x).symm

/-- **The glued orientation is characterized by the pieces.** An orientation of `X` is the glued
orientation exactly when every `f k` preserves orientation from `o k` to it, at every point. -/
theorem eq_iGlue_iff {o' : Orientation I X ι} :
    o' = iGlue hf hcov h ↔ ∀ k x, IsOrientationPreservingAt (o k) o' (f k) x := by
  refine ⟨?_, fun ho ↦ ?_⟩
  · rintro rfl
    exact isOrientationPreservingAt_iGlue hf hcov h
  ext p
  obtain ⟨k, x, rfl⟩ := mem_iUnion.1 (hcov ▸ mem_univ p)
  exact (ho k x).orientationAt_eq (isOrientationPreservingAt_iGlue hf hcov h k x)

end TauCeti.Manifold.Orientation
