/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Symplectic.Manifold.JHolomorphic
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm

/-!
# Pull-backs of two-forms along pseudoholomorphic maps

Let `f : M → N` be a smooth map that is pseudoholomorphic for almost complex structures `J` on
`M` and `K` on `N`, so that `df ∘ J = K ∘ df`, and let `σ` be a smooth two-form on `N`.

* If `σ` is `K`-invariant, then `f^* σ` is `J`-invariant
  (`TauCeti.SmoothTwoForm.Invariant.mpullback`).
* If `σ` tames `K`, then `f^* σ (v, J v) = σ (df v, K df v)` is nonnegative for every tangent
  vector `v`, and positive when `df v ≠ 0` (`TauCeti.SmoothTwoForm.Tames.eval₂_mpullback_nonneg`,
  `TauCeti.SmoothTwoForm.Tames.eval₂_mpullback_pos`).

So `f^* σ` tames `J` where `df` is injective; for a sum of such pull-backs, it is enough that the
differentials of the maps have no common nonzero kernel vector. These adapt Tau Ceti's
`TauCeti.SmoothTwoForm.Invariant.pullback` and `TauCeti.SmoothTwoForm.Tames.pullback`, from
pull-backs of almost complex structures along diffeomorphisms to pseudoholomorphic maps.

## References

* [D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*][McDuffSalamon2012],
  §2.2.
-/

public section

open scoped ContDiff Manifold

namespace TauCeti.SmoothTwoForm

variable {E H M E' H' N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' ∞ N]
  {J : SmoothAlmostComplexStructure I M} {K : SmoothAlmostComplexStructure I' N}
  {σ : SmoothTwoForm I' N} {f : M → N} {x : M}

/-- The pull-back of a `K`-invariant two-form along a `(J, K)`-pseudoholomorphic map is
`J`-invariant. -/
theorem Invariant.mpullback (hσ : σ.Invariant K) (hf : IsPseudoholomorphic J K f)
    (hf' : ContMDiff I I' ∞ f) : SmoothTwoForm.Invariant (SmoothForm.mpullback f hf' σ) J :=
  invariant_iff.2 fun x v w ↦ by
    rw [SmoothForm.eval₂_mpullback, SmoothForm.eval₂_mpullback,
      (hf.isPseudoholomorphicAt x).mfderiv_apply_commute,
      (hf.isPseudoholomorphicAt x).mfderiv_apply_commute, hσ.apply]

/-- If `σ` tames `K` and `f` is `(J, K)`-pseudoholomorphic at `x`, then `f^* σ (v, J v) > 0` for
every tangent vector `v` at `x` with `df_x v ≠ 0`. -/
theorem Tames.eval₂_mpullback_pos (hσ : σ.Tames K) (hf : IsPseudoholomorphicAt J K f x)
    (hf' : ContMDiff I I' ∞ f) {v : TangentSpace I x} (hv : mfderiv I I' f x v ≠ 0) :
    0 < (SmoothForm.mpullback f hf' σ).eval₂ x v (J x v) := by
  rw [SmoothForm.eval₂_mpullback, hf.mfderiv_apply_commute]
  exact tames_iff.1 hσ _ _ hv

/-- If `σ` tames `K` and `f` is `(J, K)`-pseudoholomorphic at `x`, then `f^* σ (v, J v) ≥ 0` for
every tangent vector `v` at `x`. -/
theorem Tames.eval₂_mpullback_nonneg (hσ : σ.Tames K) (hf : IsPseudoholomorphicAt J K f x)
    (hf' : ContMDiff I I' ∞ f) (v : TangentSpace I x) :
    0 ≤ (SmoothForm.mpullback f hf' σ).eval₂ x v (J x v) := by
  by_cases hv : mfderiv I I' f x v = 0
  · rw [SmoothForm.eval₂_mpullback, hf.mfderiv_apply_commute, hv]
    simp
  · exact (hσ.eval₂_mpullback_pos hf hf' hv).le

end TauCeti.SmoothTwoForm

end
