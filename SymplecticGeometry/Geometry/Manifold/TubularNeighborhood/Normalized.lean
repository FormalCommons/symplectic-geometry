/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.ZeroSection
import SymplecticGeometry.Geometry.Manifold.VectorBundle.ZeroSection

/-!
# The normal derivative of a map out of the normal bundle

Let `f : M → N` be a smooth embedding with normal bundle `ν`, and let `Φ : ν → N` be a map, such
as a tubular neighbourhood of `f` (Tau Ceti's `exists_diffeomorph_normalBundle_subset`, composed
with the inclusion of its open image). At each `x : M` its *normal derivative*
`f.normalFiberDeriv hn hdim Φ x` is the endomorphism of the fibre `ν_x` that sends `v` to the
normal class of the differential of `Φ` at the zero vector `0_x`, applied to the vertical vector
that Tau Ceti's splitting `TauCeti.Bundle.zeroSectionTangentEquiv` attaches to `v`. When
`Φ (0_x) = f x` this is a normal vector at `f x`; the definition reads the target tangent space
as the model space and does not need it.

The splitting is read in the preferred trivialization at `x`, but the normal derivative depends
on no trivialization: it is the normal class of the velocity at `0` of `t ↦ Φ ⟨x, t • v⟩`
(`normalFiberDeriv_apply_eq_mfderiv_smul`), by
`TauCeti.Bundle.mfderiv_zeroSectionTangentEquiv_symm_inr`.
The fibres carry no norm, so the restriction of `Φ` to a fibre is differentiated through a
continuous linear map `L : Q →L[ℝ] ν_x` from a normed space `Q`, as Tau Ceti's
`mfderiv_normalExp_fiber_zero_apply` does with the orthogonal complement of the tangent range: the
normal derivative of `L u` is the normal class of the derivative at `0` of `w ↦ Φ ⟨x, L w⟩`,
applied to `u` (`normalFiberDeriv_apply_eq_mfderiv_comp`).

## Main definitions

* `TauCeti.SmoothEmbedding.normalFiberDeriv`: the normal derivative of a map out of the normal
  bundle along the zero section, as a continuous linear endomorphism of each fibre.

## Main results

* `TauCeti.SmoothEmbedding.normalFiberDeriv_apply_eq_mfderiv_smul`: the normal derivative of `v`
  is the normal class of the velocity of `t ↦ Φ ⟨x, t • v⟩` at `0`.
* `TauCeti.SmoothEmbedding.normalFiberDeriv_apply_eq_mfderiv_comp`: the same, read through a
  continuous linear parametrization of the fibre by a normed space.

## References

* [M. W. Hirsch, *Differential Topology*][Hirsch1976], Chapter 4.
-/

public section

noncomputable section

open Bundle Module
open scoped Manifold ContDiff

namespace TauCeti.SmoothEmbedding

variable {E V P H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ V G}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]

/-- The normal derivative of a map `Φ` out of the normal bundle of a smooth embedding `f`, at
`x`: the continuous linear endomorphism of the normal space at `x` that sends `v` to the normal
class of the differential of `Φ` at the zero vector over `x`, applied to the vertical vector of
`v` in the splitting `TauCeti.Bundle.zeroSectionTangentEquiv x`. For a tube, `Φ (0_x) = f x`, and
the differential takes values in the tangent space at `f x`. -/
def normalFiberDeriv (f : SmoothEmbedding I J ∞ M N) (hn : (∞ : ℕ∞ω) ≠ 0)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E)
    (Φ : TotalSpace P (fun x ↦ f.NormalSpace x hn) → N) (x : M) :
    f.NormalSpace x hn →L[ℝ] f.NormalSpace x hn :=
  letI := f.normalSpaceFiberBundle hn hdim
  haveI := f.normalSpaceVectorBundle hn hdim
  (f.normalClassL x hn).comp ((mfderiv (I.prod 𝓘(ℝ, P)) J Φ (zeroSection P _ x)).comp
    ((Bundle.zeroSectionTangentEquiv (I := I) x).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.inr ℝ (TangentSpace I x) (f.NormalSpace x hn))))

/-- The normal derivative of `Φ` at `x` sends `v` to the normal class of the differential of `Φ`
at `0_x` applied to the vertical vector `(0, v)`. -/
theorem normalFiberDeriv_apply (f : SmoothEmbedding I J ∞ M N) (hn : (∞ : ℕ∞ω) ≠ 0)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E)
    (Φ : TotalSpace P (fun x ↦ f.NormalSpace x hn) → N) (x : M) (v : f.NormalSpace x hn) :
    letI := f.normalSpaceFiberBundle hn hdim
    haveI := f.normalSpaceVectorBundle hn hdim
    f.normalFiberDeriv hn hdim Φ x v =
      f.normalClassL x hn (mfderiv (I.prod 𝓘(ℝ, P)) J Φ (zeroSection P _ x)
        ((Bundle.zeroSectionTangentEquiv (I := I) x).symm (0, v))) :=
  (rfl)

/-- If `Φ` is differentiable at the zero vector over `x`, its normal derivative at `x` sends `v`
to the normal class of the velocity at `0` of the curve `t ↦ Φ ⟨x, t • v⟩`; in particular it does
not depend on a trivialization. -/
theorem normalFiberDeriv_apply_eq_mfderiv_smul (f : SmoothEmbedding I J ∞ M N)
    (hn : (∞ : ℕ∞ω) ≠ 0) (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E)
    {Φ : TotalSpace P (fun x ↦ f.NormalSpace x hn) → N} {x : M}
    (hΦ : letI := f.normalSpaceFiberBundle hn hdim
      MDifferentiableAt (I.prod 𝓘(ℝ, P)) J Φ (zeroSection P _ x))
    (v : f.NormalSpace x hn) :
    f.normalFiberDeriv hn hdim Φ x v =
      f.normalClassL x hn (mfderiv 𝓘(ℝ) J (fun t : ℝ ↦ Φ ⟨x, t • v⟩) 0 (1 : ℝ)) := by
  let := f.normalSpaceFiberBundle hn hdim
  have := f.normalSpaceVectorBundle hn hdim
  rw [normalFiberDeriv_apply, Bundle.mfderiv_zeroSectionTangentEquiv_symm_inr hΦ]

/-- Let `L : Q →L[ℝ] ν_x` be a continuous linear map from a normed space to the normal space at
`x`, such that `w ↦ Φ ⟨x, L w⟩` is differentiable at `0`. If `Φ` is differentiable at the zero
vector over `x`, its normal derivative at `x` sends `L u` to the normal class of the derivative at
`0` of `w ↦ Φ ⟨x, L w⟩` applied to `u`. -/
theorem normalFiberDeriv_apply_eq_mfderiv_comp (f : SmoothEmbedding I J ∞ M N)
    (hn : (∞ : ℕ∞ω) ≠ 0) (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E)
    {Φ : TotalSpace P (fun x ↦ f.NormalSpace x hn) → N} {x : M}
    (hΦ : letI := f.normalSpaceFiberBundle hn hdim
      MDifferentiableAt (I.prod 𝓘(ℝ, P)) J Φ (zeroSection P _ x))
    {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q] (L : Q →L[ℝ] f.NormalSpace x hn)
    (hL : MDifferentiableAt 𝓘(ℝ, Q) J (fun w : Q ↦ Φ ⟨x, L w⟩) 0) (u : Q) :
    f.normalFiberDeriv hn hdim Φ x (L u) =
      f.normalClassL x hn (mfderiv 𝓘(ℝ, Q) J (fun w : Q ↦ Φ ⟨x, L w⟩) 0 u) := by
  rw [normalFiberDeriv_apply_eq_mfderiv_smul f hn hdim hΦ]
  -- The curve `t ↦ Φ ⟨x, t • L u⟩` is `w ↦ Φ ⟨x, L w⟩` along the line `t ↦ t • u`.
  have e : (fun t : ℝ ↦ Φ ⟨x, t • L u⟩) =
      (fun w : Q ↦ Φ ⟨x, L w⟩) ∘ ContinuousLinearMap.toSpanSingleton ℝ u := by
    funext t
    simp
  have hℓ : HasMFDerivAt 𝓘(ℝ) 𝓘(ℝ, Q) (ContinuousLinearMap.toSpanSingleton ℝ u) 0
      (ContinuousLinearMap.toSpanSingleton ℝ u) :=
    (ContinuousLinearMap.toSpanSingleton ℝ u).hasFDerivAt.hasMFDerivAt
  have hℓ1 : ContinuousLinearMap.toSpanSingleton ℝ u 1 = u := by simp
  -- The ascription `: V` makes the motive non-dependent: every tangent space of `N` is `V`.
  have key := (congrArg (fun F : ℝ → N ↦ (mfderiv 𝓘(ℝ) J F 0 (1 : ℝ) : V)) e).trans
    (mfderiv_comp_apply_of_eq (0 : ℝ) hL hℓ.mdifferentiableAt (map_zero _) (1 : ℝ))
  rw [hℓ.mfderiv] at key
  exact (congrArg (f.normalClassL x hn) key).trans (congrArg (fun w : Q ↦
    f.normalClassL x hn (mfderiv 𝓘(ℝ, Q) J (fun w : Q ↦ Φ ⟨x, L w⟩) 0 w)) hℓ1)

end TauCeti.SmoothEmbedding

end
