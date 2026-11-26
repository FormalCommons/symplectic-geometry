/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Distribution.VectorBundle

/-!
# Distributions as families of subspaces of the tangent bundle with local frames

A distribution on a manifold is a family of subspaces of the tangent spaces, and the tangent
spaces are the fibres of the tangent bundle. Its `C^n` local frames as a distribution are
therefore the same as its `C^n` local frames as a family of subspaces of the tangent bundle.
Tau Ceti's `TauCeti.IsContMDiffDistribution.hasLocalContMDiffSubbundleFrames` passes from the
first to the second; this file proves the converse, so that results on subbundle frames, such as
orthogonal complements or kernels of bundle maps, give distributions.

## Main results

* `TauCeti.HasLocalContMDiffSubbundleFrames.isContMDiffDistribution`: a family of subspaces of
  the tangent spaces with `C^n` local frames of size `k` is a `C^n` distribution of rank `k`.
* `TauCeti.isContMDiffDistribution_iff_hasLocalContMDiffSubbundleFrames`: both notions agree.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapters 10
  and 19, for local frames of subbundles and of distributions.
-/

public section

open scoped Manifold ContDiff

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] {n : ℕ∞ω} {k : ℕ}
  {D : Π x : M, Submodule 𝕜 (TangentSpace I x)}

/-- A family of subspaces of the tangent spaces with `C^n` local frames of size `k`, as a family
of subspaces of the tangent bundle, is a `C^n` distribution of rank `k`. -/
theorem HasLocalContMDiffSubbundleFrames.isContMDiffDistribution
    (hD : HasLocalContMDiffSubbundleFrames I n E (Fin k) D) :
    IsContMDiffDistribution I n k D :=
  isContMDiffDistribution_iff.mpr fun x ↦ by
    obtain ⟨U, hU, hx, X, hX, hXs⟩ := hasLocalContMDiffSubbundleFrames_iff.mp hD x
    exact ⟨U, hU, hx, X, ⟨hXs, hX.linearIndependent, hX.span_eq⟩⟩

/-- A family of subspaces of the tangent spaces is a `C^n` distribution of rank `k` exactly when
it has `C^n` local frames of size `k` as a family of subspaces of the tangent bundle. -/
theorem isContMDiffDistribution_iff_hasLocalContMDiffSubbundleFrames :
    IsContMDiffDistribution I n k D ↔ HasLocalContMDiffSubbundleFrames I n E (Fin k) D :=
  ⟨IsContMDiffDistribution.hasLocalContMDiffSubbundleFrames,
    HasLocalContMDiffSubbundleFrames.isContMDiffDistribution⟩

end TauCeti

end
