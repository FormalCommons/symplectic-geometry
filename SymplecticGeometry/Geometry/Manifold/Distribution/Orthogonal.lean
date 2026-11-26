/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Orthogonal
public import SymplecticGeometry.Geometry.Manifold.Distribution.VectorBundle

/-!
# Orthogonals of distributions for a smooth field of bilinear forms

Let `D` be a `C^n` distribution of rank `k` on a manifold `M` modelled on a finite-dimensional
space `E`, and `β` a `C^n` field of continuous bilinear forms on the tangent spaces. If `D x` and
its `β x`-orthogonal are complementary at every point, which holds when every `β x` is reflexive
and nondegenerate on `D x`, then the `β`-orthogonals of `D` form a `C^n` distribution of rank
`dim M - k`. This is the bilinear-form counterpart of Tau Ceti's metric
`TauCeti.IsContMDiffDistribution.orthogonal`.

The proof goes through local frames. Tau Ceti's
`TauCeti.IsContMDiffDistribution.hasLocalContMDiffSubbundleFrames` gives `D` local frames as a
family of subspaces of the tangent bundle, and
`TauCeti.HasLocalContMDiffSubbundleFrames.orthogonal_of_isCompl` and
`TauCeti.HasLocalContMDiffSubbundleFrames.orthogonal` give frames of its orthogonal. The
converse `TauCeti.HasLocalContMDiffSubbundleFrames.isContMDiffDistribution`, in
`SymplecticGeometry.Geometry.Manifold.Distribution.VectorBundle`, makes these frames a
distribution again.

## Main results

* `TauCeti.IsContMDiffDistribution.bilinFormOrthogonal_of_isCompl`,
  `TauCeti.IsContMDiffDistribution.bilinFormOrthogonal`: the `β`-orthogonal of a `C^n`
  distribution of rank `k` is a `C^n` distribution of rank `dim M - k`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 10,
  for orthogonal complements of subbundles.
* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §3.4,
  where symplectic orthogonal complements of subbundles are used.
-/

public section

open Bundle Module
open scoped Manifold ContDiff

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] {n : ℕ∞ω} {k : ℕ}
  {D : Π x : M, Submodule 𝕜 (TangentSpace I x)}

namespace IsContMDiffDistribution

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]
  {β : Π x : M, TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] 𝕜}

/-- **Orthogonals of a distribution for a field of bilinear forms.** Let `β` be a `C^n` field of
continuous bilinear forms on the tangent spaces of a `C^(n + 1)` manifold modelled on a
finite-dimensional space `E`, and `D` a `C^n` distribution of rank `k` such that `D x` and its
`β x`-orthogonal are complementary at every point. Then the `β`-orthogonals of `D` form a `C^n`
distribution of rank `finrank 𝕜 E - k`. -/
theorem bilinFormOrthogonal_of_isCompl [IsManifold I (n + 1) M]
    (hD : IsContMDiffDistribution I n k D)
    (hβ : ContMDiff I (I.prod 𝓘(𝕜, E →L[𝕜] E →L[𝕜] 𝕜)) n
      (fun x ↦ TotalSpace.mk' (E →L[𝕜] E →L[𝕜] 𝕜) x (β x)))
    (hc : ∀ x, IsCompl (D x) (LinearMap.BilinForm.orthogonal (β x).toLinearMap₁₂ (D x))) :
    IsContMDiffDistribution I n (finrank 𝕜 E - k)
      fun x ↦ LinearMap.BilinForm.orthogonal (β x).toLinearMap₁₂ (D x) :=
  let : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  (hD.hasLocalContMDiffSubbundleFrames.orthogonal_of_isCompl hβ hc).isContMDiffDistribution

/-- **Orthogonals of a distribution for a field of reflexive forms.** Let `β` be a `C^n` field of
continuous bilinear forms on the tangent spaces of a `C^(n + 1)` manifold modelled on a
finite-dimensional space `E`, each of them reflexive (for instance symmetric or alternating), and
`D` a `C^n` distribution of rank `k` on which every `β x` is nondegenerate. Then the
`β`-orthogonals of `D` form a `C^n` distribution of rank `finrank 𝕜 E - k`. -/
theorem bilinFormOrthogonal [IsManifold I (n + 1) M]
    (hD : IsContMDiffDistribution I n k D)
    (hβ : ContMDiff I (I.prod 𝓘(𝕜, E →L[𝕜] E →L[𝕜] 𝕜)) n
      (fun x ↦ TotalSpace.mk' (E →L[𝕜] E →L[𝕜] 𝕜) x (β x)))
    (hrefl : ∀ x, LinearMap.BilinForm.IsRefl (β x).toLinearMap₁₂)
    (hnd : ∀ x, (LinearMap.BilinForm.restrict (β x).toLinearMap₁₂ (D x)).Nondegenerate) :
    IsContMDiffDistribution I n (finrank 𝕜 E - k)
      fun x ↦ LinearMap.BilinForm.orthogonal (β x).toLinearMap₁₂ (D x) :=
  let : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  (hD.hasLocalContMDiffSubbundleFrames.orthogonal hβ hrefl hnd).isContMDiffDistribution

end IsContMDiffDistribution

end TauCeti

end
