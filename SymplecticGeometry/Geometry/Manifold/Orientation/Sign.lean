/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.Sign
import TauCeti.Geometry.Manifold.Orientation.Pullback
import TauCeti.Topology.Algebra.Module.Determinant

/-!
# More on the orientation sign

This file adds to Tau Ceti's orientation sign `TauCeti.Manifold.Orientation.orientationSign`:

* it depends only on the germ of the map (`Filter.EventuallyEq.orientationSign_eq`), as do
  preservation and reversal of orientation;
* at a fixed point of a self-map, with the same orientation on both sides, it is the sign of the
  determinant of the derivative (`TauCeti.Manifold.Orientation.orientationSign_of_apply_eq`),
  since an automorphism of an oriented vector space preserves the orientation exactly when its
  determinant is positive (`Orientation.map_eq_iff_det_pos`). Its proof moves the tangent
  orientation at `f x` to `x` as the proof of Tau Ceti's
  `TauCeti.Manifold.Orientation.isOrientationPreservingAt_of_apply_eq_of_mfderiv_eq_id` does;
* it is constant on a preconnected set on which the map is `C¹` with invertible derivative
  (`IsPreconnected.orientationSign_eq`), since so is preservation of orientation (Tau Ceti's
  `IsPreconnected.isOrientationPreservingAt_iff`), applied to the orientation on the target and
  to its opposite. It gives
  `TauCeti.SmoothCollar.orientationSign_eq_neg_one_pow` on the slices of a collar.

Applied to the identity, local constancy of the sign
(`TauCeti.Manifold.Orientation.eventually_orientationSign_eq`) shows that two orientations which
agree on a dense set agree everywhere (`TauCeti.Manifold.Orientation.eq_of_dense`).

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in Mathematics
  218, Springer (2013), Chapter 15.
-/

public section

open Set Filter
open scoped Manifold Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]
  {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold J 1 N]
  {ι : Type*} [Fintype ι]

namespace Manifold.Orientation

variable {o : Manifold.Orientation I M ι} {o' : Manifold.Orientation J N ι} {f g : M → N}
  {x : M}

/-- A map that agrees near `x` with a map preserving orientation at `x` preserves it there. -/
theorem IsOrientationPreservingAt.congr_of_eventuallyEq (hf : IsOrientationPreservingAt o o' f x)
    (h : f =ᶠ[𝓝 x] g) : IsOrientationPreservingAt o o' g x := by
  obtain ⟨e, he, ho⟩ := (isOrientationPreservingAt_iff o o' f x).1 hf
  -- The tangent spaces at `f x` and `g x` are both the model space, so `e` serves for `g`.
  refine (isOrientationPreservingAt_iff o o' g x).2 ⟨e, he.trans h.mfderiv_eq, ho.trans ?_⟩
  rw [h.eq_of_nhds]

/-- A map that agrees near `x` with a map reversing orientation at `x` reverses it there. -/
theorem IsOrientationReversingAt.congr_of_eventuallyEq (hf : IsOrientationReversingAt o o' f x)
    (h : f =ᶠ[𝓝 x] g) : IsOrientationReversingAt o o' g x := by
  obtain ⟨e, he, ho⟩ := (isOrientationReversingAt_iff o o' f x).1 hf
  -- The tangent spaces at `f x` and `g x` are both the model space, so `e` serves for `g`.
  refine (isOrientationReversingAt_iff o o' g x).2 ⟨e, he.trans h.mfderiv_eq, ho.trans ?_⟩
  rw [h.eq_of_nhds]

end Manifold.Orientation

open Manifold.Orientation in
/-- Maps that agree near `x` have the same orientation sign at `x`. -/
theorem _root_.Filter.EventuallyEq.orientationSign_eq {o : Manifold.Orientation I M ι}
    {o' : Manifold.Orientation J N ι} {f g : M → N} {x : M} (h : f =ᶠ[𝓝 x] g) :
    orientationSign o o' f x = orientationSign o o' g x := by
  have hp : IsOrientationPreservingAt o o' f x ↔ IsOrientationPreservingAt o o' g x :=
    ⟨fun hf ↦ hf.congr_of_eventuallyEq h, fun hg ↦ hg.congr_of_eventuallyEq h.symm⟩
  have hr : IsOrientationReversingAt o o' f x ↔ IsOrientationReversingAt o o' g x :=
    ⟨fun hf ↦ hf.congr_of_eventuallyEq h, fun hg ↦ hg.congr_of_eventuallyEq h.symm⟩
  classical
  rw [orientationSign_def, orientationSign_def]
  exact if_congr hp rfl (if_congr hr rfl rfl)

namespace Manifold.Orientation

variable {o : Manifold.Orientation I M ι} {o' : Manifold.Orientation J N ι} {f : M → N}

/-- **The orientation sign at a fixed point.** If `f : M → M` fixes `x`, its orientation sign at
`x`, for one orientation `o` on both sides, is the sign of the determinant of its derivative at
`x`, an endomorphism of the model space. -/
theorem orientationSign_of_apply_eq (o : Manifold.Orientation I M ι) {f : M → M} {x : M}
    (hx : f x = x) :
    orientationSign o o f x = SignType.sign ((mfderiv I I f x : E →L[ℝ] E).det) := by
  by_cases hd : (mfderiv I I f x : E →L[ℝ] E).det = 0
  · rw [hd, sign_zero, SignType.coe_zero, orientationSign_eq_zero_iff]
    rintro ⟨e, he⟩
    rw [← he] at hd
    exact (e : E ≃L[ℝ] E).det_coe_ne_zero hd
  let e : TangentSpace I x ≃L[ℝ] TangentSpace I (f x) :=
    (mfderiv I I f x : E →L[ℝ] E).toContinuousLinearEquivOfDetNeZero hd
  have he : (e : TangentSpace I x →L[ℝ] TangentSpace I (f x)) = mfderiv I I f x :=
    (mfderiv I I f x : E →L[ℝ] E).coe_toContinuousLinearEquivOfDetNeZero hd
  /- The tangent orientation at `f x` lives on the tangent space at `f x`; generalize the point to
    substitute `x` for it along `hx`. -/
  have key : ∀ (y : M) (_ : y = x) (L : TangentSpace I x ≃ₗ[ℝ] TangentSpace I y),
      (_root_.Orientation.map ι L (o.orientationAt x) = o.orientationAt y ↔
        0 < LinearMap.det (L : E ≃ₗ[ℝ] E).toLinearMap) ∧
      (_root_.Orientation.map ι L (o.orientationAt x) = -o.orientationAt y ↔
        LinearMap.det (L : E ≃ₗ[ℝ] E).toLinearMap < 0) := by
    rintro y rfl L
    exact ⟨_root_.Orientation.map_eq_iff_det_pos _ _ o.card_eq,
      _root_.Orientation.map_eq_neg_iff_det_neg _ _ o.card_eq⟩
  have hP := (isOrientationPreservingAt_iff_of_coe_eq o o f x e he).trans
    (key _ hx e.toLinearEquiv).1
  have hR := (isOrientationReversingAt_iff_of_coe_eq o o f x e he).trans
    (key _ hx e.toLinearEquiv).2
  have hdet : LinearMap.det (e.toLinearEquiv : E ≃ₗ[ℝ] E).toLinearMap =
      (mfderiv I I f x : E →L[ℝ] E).det := by
    rw [← he]
    rfl
  rw [hdet] at hP hR
  rcases lt_or_gt_of_ne hd with h | h
  · rw [orientationSign_of_isOrientationReversingAt (hR.2 h), sign_neg h, SignType.coe_neg_one]
  · rw [orientationSign_of_isOrientationPreservingAt (hP.2 h), sign_pos h, SignType.coe_one]

/-- **The orientation sign is constant on preconnected sets.** On a preconnected set on which `f`
is `C¹` with invertible derivative, the orientation sign of `f` takes a single value. -/
theorem _root_.IsPreconnected.orientationSign_eq {s : Set M} (hs : IsPreconnected s)
    (hf : ∀ y ∈ s, ContMDiffAt I J 1 f y) (hd : ∀ y ∈ s, (mfderiv I J f y).IsInvertible)
    {x y : M} (hx : x ∈ s) (hy : y ∈ s) :
    orientationSign o o' f x = orientationSign o o' f y := by
  -- A sign `1` at `x` is a sign `1` at `y`, for any orientation of the target.
  have key (o'' : Manifold.Orientation J N ι) (h : orientationSign o o'' f x = 1) :
      orientationSign o o'' f y = 1 := by
    rw [orientationSign_eq_one_iff] at h ⊢
    exact (hs.isOrientationPreservingAt_iff hf hd o o'' hx hy).1 h
  rcases orientationSign_eq_one_or_eq_neg_one (o := o) (o' := o') (hd x hx) with h | h
  · rw [h, key o' h]
  · have h' := key (-o') (by rw [orientationSign_neg_right, h, neg_neg])
    rw [orientationSign_neg_right, neg_eq_iff_eq_neg] at h'
    rw [h, h']

/-- **Orientations agreeing on a dense set are equal.** Two orientations of `M` whose tangent
orientations agree at every point of a dense set are equal. -/
theorem eq_of_dense {o₁ o₂ : Manifold.Orientation I M ι} {s : Set M} (hs : Dense s)
    (h : ∀ x ∈ s, o₁.orientationAt x = o₂.orientationAt x) : o₁ = o₂ := by
  let σ : M → ℤ := orientationSign o₁ o₂ id
  have hσ : IsLocallyConstant σ := (IsLocallyConstant.iff_eventually_eq σ).2 fun z ↦
    eventually_orientationSign_eq contMDiffAt_id
      (isOrientationPreservingAt_id o₁ z).isInvertible_mfderiv
  have hσs : s ⊆ σ ⁻¹' {1} := fun x hx ↦ by
    obtain ⟨e, he, ho⟩ := (isOrientationPreservingAt_iff o₁ o₁ id x).1
      (isOrientationPreservingAt_id o₁ x)
    exact orientationSign_of_isOrientationPreservingAt
      ((isOrientationPreservingAt_iff o₁ o₂ id x).2 ⟨e, he, ho.trans (h x hx)⟩)
  have hclosed : IsClosed (σ ⁻¹' {1}) := hσ.isClosed_fiber 1
  ext x
  have hx : σ x = 1 := (hs.closure_eq ▸ hclosed.closure_subset_iff.2 hσs) (mem_univ x)
  exact (isOrientationPreservingAt_id o₁ x).orientationAt_eq (orientationSign_eq_one_iff.1 hx)

end Manifold.Orientation

end TauCeti
