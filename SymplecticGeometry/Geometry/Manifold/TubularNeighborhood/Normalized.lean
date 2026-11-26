/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.MFDeriv.Translation
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.ZeroSection
public import TauCeti.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Geometry.Manifold.TubularNeighborhood.Existence
import Mathlib.Geometry.Manifold.VectorBundle.Pullback
import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.Quotient
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.Basic
import SymplecticGeometry.Geometry.Manifold.VectorBundle.ZeroSection

/-!
# Normalized tubes

This file defines the normal derivative of a map out of the normal bundle of a smooth embedding,
and the tubes whose normal derivative is the identity.

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

If the differential of `Φ` at `0_x` is injective and `Φ` agrees with `f` on the zero section
near `x`, the normal derivative at `x` is bijective (`bijective_normalFiberDeriv`). Indeed the
differential of `Φ` sends a horizontal vector `(u, 0)` to the differential of `f` applied to
`u` (`TauCeti.Bundle.mfderiv_zeroSectionTangentEquiv_symm_inl`); so if a vertical vector
`(0, v)` goes to a vector tangent to `f`, it has the same image as some `(u, 0)`, hence equals
it, and `v = 0`. An injective endomorphism of the finite-dimensional fibre is bijective. For a
tube, a local diffeomorphism at `0_x`, this gives the automorphism `normalFiberDerivEquiv`.

If `Φ` is smooth at every zero vector and equals `f` on the zero section, the normal derivative
depends smoothly on `x` (`contMDiff_normalFiberDeriv`). The velocities at `0` of the rays
`t ↦ Φ ⟨x, t • v⟩` form a smooth map into the pull-back of the tangent bundle of `N` along `f`
(`Bundle.contMDiff_mfderiv_smul_curve`, which holds for any smooth vector bundle), and Tau Ceti's
`contMDiff_normalQuotientMap` says that taking their normal classes is smooth. For a tube, Tau
Ceti's `TauCeti.bundleDiffeomorph` turns the automorphisms `normalFiberDerivEquiv` into the
diffeomorphism `normalFiberDerivDiffeomorph` of the total space over the identity of `M`; its
inverse acts on each fibre by the inverse of the normal derivative, and both fix the zero section.

Precomposing a map with the diffeomorphism `bundleDiffeomorph Ψ` given by fibrewise automorphisms
`Ψ x` composes its normal derivative at `x` with `Ψ x`
(`normalFiberDeriv_comp_bundleDiffeomorph`), since it turns each ray `t ↦ ⟨x, t • v⟩` into the
ray of `Ψ x v`. A *normalized tube* (`IsNormalizedTube`) is a diffeomorphism of the total space
of the normal bundle onto an open set of `N`, equal to `f` on the zero section, whose normal
derivative is the identity; read in the preferred trivialization at `x`, this says that the
differential at `0_x` sends each vertical vector `(0, w)` to a vector whose normal class has
coordinate `w` (`normalFiberDeriv_eq_id_iff`). Precomposing a tube of Tau Ceti's
`exists_diffeomorph_normalBundle_subset` with the diffeomorphism given by the inverses of its
normal derivative normalizes it (`isNormalizedTube_comp_bundleEquiv`). That diffeomorphism is the
inverse of `normalFiberDerivDiffeomorph`, so any tube equal to `f` on the zero section is
normalized by precomposing it with that inverse
(`isNormalizedTube_normalFiberDerivDiffeomorph_symm_trans`), and normalized tubes exist inside
every open set containing the range of `f` (`exists_isNormalizedTube_subset`).

A normalized tube also preserves fibre coordinates to first order: if `g : P → N` has
derivative `A` at `0` whose normal classes are the vectors of the fibre over `x` with the
coordinates given by the preferred trivialization `e` at `x`, then a lift `h` of `g`
through the tube that sends `0` to the zero vector over `x` has fibre coordinate
`w ↦ (e (h w)).2` with derivative the identity at `0`
(`IsNormalizedTube.hasFDerivAt_trivializationAt_snd`). The differential `D` of the tube at `0_x`
sends horizontal vectors to tangent vectors of `f` and vertical vectors `(0, w)` to vectors
with normal class of coordinate `w`; so the normal class of `D v` has coordinate the second
component of `v`, and the chain rule applied to `h`, which is differentiable since the tube is a
local diffeomorphism (`MDifferentiableAt.of_comp_isLocalDiffeomorph`), gives the claim.

## Main definitions

* `TauCeti.SmoothEmbedding.normalFiberDeriv`: the normal derivative of a map out of the normal
  bundle along the zero section, as a continuous linear endomorphism of each fibre.
* `TauCeti.SmoothEmbedding.normalFiberDerivEquiv`: the normal derivative at `x` of a map that is
  a local diffeomorphism at `0_x` and restricts to `f` on the zero section near `x`, as a
  continuous linear automorphism of the fibre at `x`.
* `TauCeti.SmoothEmbedding.normalFiberDerivDiffeomorph`: for a map that is a local
  diffeomorphism at each zero vector and restricts to `f` on the zero section, the diffeomorphism
  of the total space of the normal bundle given on each fibre by the normal derivative.
* `TauCeti.SmoothEmbedding.IsNormalizedTube`: a diffeomorphism of the total space of the normal
  bundle onto an open set, equal to `f` on the zero section, with normal derivative the identity.

## Main results

* `TauCeti.SmoothEmbedding.normalFiberDeriv_apply_eq_mfderiv_smul`: the normal derivative of `v`
  is the normal class of the velocity of `t ↦ Φ ⟨x, t • v⟩` at `0`.
* `TauCeti.SmoothEmbedding.normalFiberDeriv_apply_eq_mfderiv_comp`: the same, read through a
  continuous linear parametrization of the fibre by a normed space.
* `TauCeti.SmoothEmbedding.bijective_normalFiberDeriv`: the normal derivative is bijective when
  the differential at the zero vector is injective and the map restricts to `f` on the zero
  section.
* `TauCeti.SmoothEmbedding.contMDiff_normalFiberDeriv`: the normal derivative of a map that is
  smooth along the zero section and restricts to `f` on it is smooth as a map of total spaces.
* `TauCeti.SmoothEmbedding.normalFiberDerivDiffeomorph_symm_apply`,
  `TauCeti.SmoothEmbedding.normalFiberDerivDiffeomorph_symm_zeroSection`: the inverse
  diffeomorphism applies the inverse of the normal derivative on each fibre and fixes the zero
  section.
* `TauCeti.SmoothEmbedding.normalFiberDeriv_comp_bundleDiffeomorph`: precomposing with the
  diffeomorphism of fibrewise automorphisms `Ψ x` composes the normal derivative with `Ψ x`.
* `TauCeti.SmoothEmbedding.isNormalizedTube_comp_bundleEquiv`: a tube precomposed with fibrewise
  inverses of its normal derivative is normalized.
* `TauCeti.SmoothEmbedding.isNormalizedTube_normalFiberDerivDiffeomorph_symm_trans`: a tube equal
  to `f` on the zero section, precomposed with the inverse of `normalFiberDerivDiffeomorph`, is
  normalized.
* `TauCeti.SmoothEmbedding.exists_isNormalizedTube_subset`: every open set containing the range
  of `f` contains the image of a normalized tube.
* `TauCeti.SmoothEmbedding.IsNormalizedTube.hasFDerivAt_trivializationAt_snd`: the fibre coordinate,
  in the preferred trivialization at `x`, of a lift through a normalized tube of a map whose
  derivative has the fibre coordinates as normal classes has derivative the identity.

## References

* [M. W. Hirsch, *Differential Topology*][Hirsch1976], Chapter 4.
-/

public section

noncomputable section

open Bundle Module
open scoped Manifold ContDiff Topology

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

/-- The normal derivative of `Φ` at `x` is the normal class of the differential of `Φ` at `0_x`,
composed with the inclusion of the fibre as the vertical vectors of the splitting
`TauCeti.Bundle.zeroSectionTangentEquiv x`. -/
theorem normalFiberDeriv_def (f : SmoothEmbedding I J ∞ M N) (hn : (∞ : ℕ∞ω) ≠ 0)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E)
    (Φ : TotalSpace P (fun x ↦ f.NormalSpace x hn) → N) (x : M) :
    letI := f.normalSpaceFiberBundle hn hdim
    haveI := f.normalSpaceVectorBundle hn hdim
    f.normalFiberDeriv hn hdim Φ x =
      (f.normalClassL x hn).comp ((mfderiv (I.prod 𝓘(ℝ, P)) J Φ (zeroSection P _ x)).comp
        ((Bundle.zeroSectionTangentEquiv (I := I) x).symm.toContinuousLinearMap.comp
          (ContinuousLinearMap.inr ℝ (TangentSpace I x) (f.NormalSpace x hn)))) :=
  (rfl)

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
`x`. If `Φ` is differentiable at the zero vector over `x`, its normal derivative at `x` sends `L u`
to the normal class of the derivative at `0` of `w ↦ Φ ⟨x, L w⟩` applied to `u`. -/
theorem normalFiberDeriv_apply_eq_mfderiv_comp (f : SmoothEmbedding I J ∞ M N)
    (hn : (∞ : ℕ∞ω) ≠ 0) (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E)
    {Φ : TotalSpace P (fun x ↦ f.NormalSpace x hn) → N} {x : M}
    (hΦ : letI := f.normalSpaceFiberBundle hn hdim
      MDifferentiableAt (I.prod 𝓘(ℝ, P)) J Φ (zeroSection P _ x))
    {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q] (L : Q →L[ℝ] f.NormalSpace x hn)
    (u : Q) :
    f.normalFiberDeriv hn hdim Φ x (L u) =
      f.normalClassL x hn (mfderiv 𝓘(ℝ, Q) J (fun w : Q ↦ Φ ⟨x, L w⟩) 0 u) := by
  let := f.normalSpaceFiberBundle hn hdim
  have := f.normalSpaceVectorBundle hn hdim
  have hm : MDifferentiableAt 𝓘(ℝ, Q) (I.prod 𝓘(ℝ, P))
      (fun w : Q ↦ (⟨x, L w⟩ : TotalSpace P (fun x ↦ f.NormalSpace x hn))) 0 :=
    (Bundle.contMDiff_totalSpaceMk_comp (V := fun x ↦ f.NormalSpace x hn) (n := 1) x L
      0).mdifferentiableAt one_ne_zero
  have h0 : (⟨x, L 0⟩ : TotalSpace P (fun x ↦ f.NormalSpace x hn)) = zeroSection P _ x := by
    simp [zeroSection]
  have hL : MDifferentiableAt 𝓘(ℝ, Q) J (fun w : Q ↦ Φ ⟨x, L w⟩) (0 + (0 : ℝ) • u) := by
    rw [zero_smul, zero_add]
    exact MDifferentiableAt.comp_of_eq (0 : Q) hΦ hm h0
  rw [normalFiberDeriv_apply_eq_mfderiv_smul f hn hdim hΦ]
  -- The curve `t ↦ Φ ⟨x, t • L u⟩` is `w ↦ Φ ⟨x, L w⟩` along the line `t ↦ 0 + t • u`.
  have e : (fun t : ℝ ↦ Φ ⟨x, t • L u⟩) = fun t : ℝ ↦ (fun w : Q ↦ Φ ⟨x, L w⟩) (0 + t • u) := by
    funext t
    simp
  -- The ascription `: V` makes the motive non-dependent: every tangent space of `N` is `V`.
  have h : (mfderiv 𝓘(ℝ) J (fun t : ℝ ↦ (fun w : Q ↦ Φ ⟨x, L w⟩) (0 + t • u)) 0 (1 : ℝ) : V) =
      mfderiv 𝓘(ℝ, Q) J (fun w : Q ↦ Φ ⟨x, L w⟩) (0 + (0 : ℝ) • u) u :=
    hL.mfderiv_comp_add_smul_apply_one
  rw [zero_smul, zero_add] at h
  exact congrArg (f.normalClassL x hn)
    ((congrArg (fun F : ℝ → N ↦ (mfderiv 𝓘(ℝ) J F 0 (1 : ℝ) : V)) e).trans h)

/-- Let `Φ` be differentiable at the zero vector over `x`, with injective differential there, and
equal to `f` on the zero section near `x`. Then the normal derivative of `Φ` at `x` is bijective. -/
theorem bijective_normalFiberDeriv (f : SmoothEmbedding I J ∞ M N) (hn : (∞ : ℕ∞ω) ≠ 0)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E)
    {Φ : TotalSpace P (fun x ↦ f.NormalSpace x hn) → N} {x : M}
    (hΦ : letI := f.normalSpaceFiberBundle hn hdim
      MDifferentiableAt (I.prod 𝓘(ℝ, P)) J Φ (zeroSection P _ x))
    (hinj : letI := f.normalSpaceFiberBundle hn hdim
      Function.Injective (mfderiv (I.prod 𝓘(ℝ, P)) J Φ (zeroSection P _ x)))
    (hfΦ : Φ ∘ zeroSection P _ =ᶠ[𝓝 x] f) :
    Function.Bijective (f.normalFiberDeriv hn hdim Φ x) := by
  let := f.normalSpaceFiberBundle hn hdim
  have := f.normalSpaceVectorBundle hn hdim
  -- A vertical vector `(0, v)` whose image is the differential of `f` applied to `u` has the image
  -- of the horizontal vector `(u, 0)`, so `(0, v) = (u, 0)` and `v = 0`.
  have hD : Function.Injective (f.normalFiberDeriv hn hdim Φ x) := by
    refine (injective_iff_map_eq_zero _).2 fun v hv ↦ ?_
    rw [normalFiberDeriv_apply] at hv
    obtain ⟨u, hu⟩ :=
      (f.normalClass_eq_zero_iff x hn _).1 ((f.normalClassL_apply x hn _).symm.trans hv)
    have h := hinj ((Bundle.mfderiv_zeroSectionTangentEquiv_symm_inl hΦ hfΦ u).trans hu)
    exact (congrArg Prod.snd ((Bundle.zeroSectionTangentEquiv (I := I) x).symm.injective h)).symm
  exact ⟨hD, LinearMap.injective_iff_surjective
    (f := (f.normalFiberDeriv hn hdim Φ x : f.NormalSpace x hn →ₗ[ℝ] _)).1 hD⟩

/-- The normal derivative at `x` of a map `Φ` out of the normal bundle that is a local
diffeomorphism at the zero vector over `x` and equal to `f` on the zero section near `x`, such as
a tubular neighbourhood of `f`, as a continuous linear automorphism of the normal space at `x`. -/
def normalFiberDerivEquiv (f : SmoothEmbedding I J ∞ M N) (hn : (∞ : ℕ∞ω) ≠ 0)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E)
    {Φ : TotalSpace P (fun x ↦ f.NormalSpace x hn) → N} {x : M}
    (hΦ : letI := f.normalSpaceFiberBundle hn hdim
      IsLocalDiffeomorphAt (I.prod 𝓘(ℝ, P)) J ∞ Φ (zeroSection P _ x))
    (hfΦ : Φ ∘ zeroSection P _ =ᶠ[𝓝 x] f) :
    f.NormalSpace x hn ≃L[ℝ] f.NormalSpace x hn :=
  letI := f.normalSpaceFiberBundle hn hdim
  (LinearEquiv.ofBijective (f.normalFiberDeriv hn hdim Φ x : f.NormalSpace x hn →ₗ[ℝ] _)
    (bijective_normalFiberDeriv f hn hdim (hΦ.mdifferentiableAt hn)
      (hΦ.isInvertible_mfderiv hn).injective hfΦ)).toContinuousLinearEquiv

/-- `normalFiberDerivEquiv` is the normal derivative, which is bijective, made a linear equivalence
and then, the normal space being finite-dimensional, a continuous linear equivalence. -/
theorem normalFiberDerivEquiv_def (f : SmoothEmbedding I J ∞ M N) (hn : (∞ : ℕ∞ω) ≠ 0)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E)
    {Φ : TotalSpace P (fun x ↦ f.NormalSpace x hn) → N} {x : M}
    (hΦ : letI := f.normalSpaceFiberBundle hn hdim
      IsLocalDiffeomorphAt (I.prod 𝓘(ℝ, P)) J ∞ Φ (zeroSection P _ x))
    (hfΦ : Φ ∘ zeroSection P _ =ᶠ[𝓝 x] f) :
    letI := f.normalSpaceFiberBundle hn hdim
    f.normalFiberDerivEquiv hn hdim hΦ hfΦ =
      (LinearEquiv.ofBijective (f.normalFiberDeriv hn hdim Φ x : f.NormalSpace x hn →ₗ[ℝ] _)
        (bijective_normalFiberDeriv f hn hdim (hΦ.mdifferentiableAt hn)
          (hΦ.isInvertible_mfderiv hn).injective hfΦ)).toContinuousLinearEquiv :=
  (rfl)

/-- The continuous linear automorphism `normalFiberDerivEquiv` applies the normal derivative. -/
@[simp]
theorem normalFiberDerivEquiv_apply (f : SmoothEmbedding I J ∞ M N) (hn : (∞ : ℕ∞ω) ≠ 0)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E)
    {Φ : TotalSpace P (fun x ↦ f.NormalSpace x hn) → N} {x : M}
    (hΦ : letI := f.normalSpaceFiberBundle hn hdim
      IsLocalDiffeomorphAt (I.prod 𝓘(ℝ, P)) J ∞ Φ (zeroSection P _ x))
    (hfΦ : Φ ∘ zeroSection P _ =ᶠ[𝓝 x] f) (v : f.NormalSpace x hn) :
    f.normalFiberDerivEquiv hn hdim hΦ hfΦ v = f.normalFiberDeriv hn hdim Φ x v := by
  rw [normalFiberDerivEquiv_def, LinearEquiv.coe_toContinuousLinearEquiv',
    LinearEquiv.ofBijective_apply, ContinuousLinearMap.coe_coe]

/-- The continuous linear map underlying `normalFiberDerivEquiv` is the normal derivative. -/
@[simp]
theorem coe_normalFiberDerivEquiv (f : SmoothEmbedding I J ∞ M N) (hn : (∞ : ℕ∞ω) ≠ 0)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E)
    {Φ : TotalSpace P (fun x ↦ f.NormalSpace x hn) → N} {x : M}
    (hΦ : letI := f.normalSpaceFiberBundle hn hdim
      IsLocalDiffeomorphAt (I.prod 𝓘(ℝ, P)) J ∞ Φ (zeroSection P _ x))
    (hfΦ : Φ ∘ zeroSection P _ =ᶠ[𝓝 x] f) :
    (f.normalFiberDerivEquiv hn hdim hΦ hfΦ : f.NormalSpace x hn →L[ℝ] f.NormalSpace x hn) =
      f.normalFiberDeriv hn hdim Φ x :=
  ContinuousLinearMap.ext (normalFiberDerivEquiv_apply f hn hdim hΦ hfΦ)

/-- Let `Φ` be smooth at every zero vector of the normal bundle and equal to `f` on the zero
section. Then its normal derivative depends smoothly on the base point: the map of total spaces
`⟨x, v⟩ ↦ ⟨x, f.normalFiberDeriv hn hdim Φ x v⟩` is smooth. -/
theorem contMDiff_normalFiberDeriv (f : SmoothEmbedding I J ∞ M N) (hn : (∞ : ℕ∞ω) ≠ 0)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E)
    {Φ : TotalSpace P (fun x ↦ f.NormalSpace x hn) → N}
    (hΦ : letI := f.normalSpaceFiberBundle hn hdim
      ∀ x, ContMDiffAt (I.prod 𝓘(ℝ, P)) J ∞ Φ (zeroSection P _ x))
    (hfΦ : Φ ∘ zeroSection P _ = f) :
    letI := f.normalSpaceFiberBundle hn hdim
    ContMDiff (I.prod 𝓘(ℝ, P)) (I.prod 𝓘(ℝ, P)) ∞
      (fun p : TotalSpace P (fun x ↦ f.NormalSpace x hn) ↦ TotalSpace.mk' P
        (E := fun x ↦ f.NormalSpace x hn) p.proj (f.normalFiberDeriv hn hdim Φ p.proj p.snd)) := by
  let := f.normalSpaceFiberBundle hn hdim
  have := f.normalSpaceVectorBundle hn hdim
  have : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  have : IsManifold J (∞ + 1) N := by simpa using (inferInstance : IsManifold J ∞ N)
  have := f.normalSpaceContMDiffVectorBundle (m := ∞) hn le_rfl hdim
  -- The normal derivative is the normal class of the velocities of the rays.
  have e : (fun p : TotalSpace P (fun x ↦ f.NormalSpace x hn) ↦ TotalSpace.mk' P
      (E := fun x ↦ f.NormalSpace x hn) p.proj (f.normalFiberDeriv hn hdim Φ p.proj p.snd)) =
      f.normalQuotientMap hn ∘ fun p : TotalSpace P (fun x ↦ f.NormalSpace x hn) ↦ (⟨p.proj,
        mfderiv 𝓘(ℝ) J (fun t : ℝ ↦ Φ ⟨p.proj, t • p.snd⟩) 0 (1 : ℝ)⟩ :
          TotalSpace V ((f : M → N) *ᵖ (TangentSpace J))) := by
    funext p
    rw [Function.comp_apply, normalQuotientMap_apply, normalFiberDeriv_apply_eq_mfderiv_smul f hn
      hdim ((hΦ p.proj).mdifferentiableAt (by simp))]
    exact congrArg (TotalSpace.mk p.proj) (f.normalClassL_apply p.proj hn _)
  rw [e]
  exact (f.contMDiff_normalQuotientMap hn le_rfl hdim).comp
    (Bundle.contMDiff_mfderiv_smul_curve (f := ⟨f, f.contMDiff⟩) hΦ hfΦ)

/-- Let `Φ` be a local diffeomorphism at every zero vector of the normal bundle, equal to `f` on
the zero section, such as a tubular neighbourhood of `f`. The smooth diffeomorphism of the total
space of the normal bundle over the identity of `M` that acts on the fibre at `x` by the normal
derivative `normalFiberDerivEquiv` of `Φ` at `x`. Its inverse acts on each fibre by the inverse of
the normal derivative. -/
def normalFiberDerivDiffeomorph (f : SmoothEmbedding I J ∞ M N) (hn : (∞ : ℕ∞ω) ≠ 0)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E)
    {Φ : TotalSpace P (fun x ↦ f.NormalSpace x hn) → N}
    (hΦ : letI := f.normalSpaceFiberBundle hn hdim
      ∀ x, IsLocalDiffeomorphAt (I.prod 𝓘(ℝ, P)) J ∞ Φ (zeroSection P _ x))
    (hfΦ : Φ ∘ zeroSection P _ = f) :
    letI := f.normalSpaceFiberBundle hn hdim
    TotalSpace P (fun x ↦ f.NormalSpace x hn) ≃ₘ^∞⟮I.prod 𝓘(ℝ, P), I.prod 𝓘(ℝ, P)⟯
      TotalSpace P (fun x ↦ f.NormalSpace x hn) :=
  letI := f.normalSpaceFiberBundle hn hdim
  haveI := f.normalSpaceVectorBundle hn hdim
  bundleDiffeomorph (fun x ↦ f.normalFiberDerivEquiv hn hdim (hΦ x) (.of_eq hfΦ))
    ((contMDiff_normalFiberDeriv f hn hdim (fun x ↦ (hΦ x).contMDiffAt) hfΦ).congr fun p ↦
      congrArg (TotalSpace.mk p.proj) (normalFiberDerivEquiv_apply f hn hdim _ _ p.snd))

/-- `normalFiberDerivDiffeomorph` is Tau Ceti's `bundleDiffeomorph` of the automorphisms
`normalFiberDerivEquiv`. -/
theorem normalFiberDerivDiffeomorph_def (f : SmoothEmbedding I J ∞ M N) (hn : (∞ : ℕ∞ω) ≠ 0)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E)
    {Φ : TotalSpace P (fun x ↦ f.NormalSpace x hn) → N}
    (hΦ : letI := f.normalSpaceFiberBundle hn hdim
      ∀ x, IsLocalDiffeomorphAt (I.prod 𝓘(ℝ, P)) J ∞ Φ (zeroSection P _ x))
    (hfΦ : Φ ∘ zeroSection P _ = f) :
    letI := f.normalSpaceFiberBundle hn hdim
    haveI := f.normalSpaceVectorBundle hn hdim
    f.normalFiberDerivDiffeomorph hn hdim hΦ hfΦ =
      bundleDiffeomorph (fun x ↦ f.normalFiberDerivEquiv hn hdim (hΦ x) (.of_eq hfΦ))
        ((contMDiff_normalFiberDeriv f hn hdim (fun x ↦ (hΦ x).contMDiffAt) hfΦ).congr fun p ↦
          congrArg (TotalSpace.mk p.proj) (normalFiberDerivEquiv_apply f hn hdim _ _ p.snd)) :=
  (rfl)

/-- `normalFiberDerivDiffeomorph` applies the normal derivative on each fibre. -/
@[simp]
theorem normalFiberDerivDiffeomorph_apply (f : SmoothEmbedding I J ∞ M N) (hn : (∞ : ℕ∞ω) ≠ 0)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E)
    {Φ : TotalSpace P (fun x ↦ f.NormalSpace x hn) → N}
    (hΦ : letI := f.normalSpaceFiberBundle hn hdim
      ∀ x, IsLocalDiffeomorphAt (I.prod 𝓘(ℝ, P)) J ∞ Φ (zeroSection P _ x))
    (hfΦ : Φ ∘ zeroSection P _ = f) (p : TotalSpace P (fun x ↦ f.NormalSpace x hn)) :
    f.normalFiberDerivDiffeomorph hn hdim hΦ hfΦ p =
      ⟨p.proj, f.normalFiberDeriv hn hdim Φ p.proj p.snd⟩ := by
  let := f.normalSpaceFiberBundle hn hdim
  have := f.normalSpaceVectorBundle hn hdim
  rw [normalFiberDerivDiffeomorph_def, bundleDiffeomorph_apply, normalFiberDerivEquiv_apply]

/-- The inverse of `normalFiberDerivDiffeomorph` applies the inverse of the normal derivative on
each fibre. -/
@[simp]
theorem normalFiberDerivDiffeomorph_symm_apply (f : SmoothEmbedding I J ∞ M N)
    (hn : (∞ : ℕ∞ω) ≠ 0) (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E)
    {Φ : TotalSpace P (fun x ↦ f.NormalSpace x hn) → N}
    (hΦ : letI := f.normalSpaceFiberBundle hn hdim
      ∀ x, IsLocalDiffeomorphAt (I.prod 𝓘(ℝ, P)) J ∞ Φ (zeroSection P _ x))
    (hfΦ : Φ ∘ zeroSection P _ = f) (p : TotalSpace P (fun x ↦ f.NormalSpace x hn)) :
    letI := f.normalSpaceFiberBundle hn hdim
    (f.normalFiberDerivDiffeomorph hn hdim hΦ hfΦ).symm p =
      ⟨p.proj, (f.normalFiberDerivEquiv hn hdim (hΦ p.proj) (.of_eq hfΦ)).symm p.snd⟩ := by
  let := f.normalSpaceFiberBundle hn hdim
  have := f.normalSpaceVectorBundle hn hdim
  rw [normalFiberDerivDiffeomorph_def, bundleDiffeomorph_symm_apply]

/-- `normalFiberDerivDiffeomorph` fixes the zero section. -/
theorem normalFiberDerivDiffeomorph_zeroSection (f : SmoothEmbedding I J ∞ M N)
    (hn : (∞ : ℕ∞ω) ≠ 0) (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E)
    {Φ : TotalSpace P (fun x ↦ f.NormalSpace x hn) → N}
    (hΦ : letI := f.normalSpaceFiberBundle hn hdim
      ∀ x, IsLocalDiffeomorphAt (I.prod 𝓘(ℝ, P)) J ∞ Φ (zeroSection P _ x))
    (hfΦ : Φ ∘ zeroSection P _ = f) (x : M) :
    letI := f.normalSpaceFiberBundle hn hdim
    f.normalFiberDerivDiffeomorph hn hdim hΦ hfΦ (zeroSection P _ x) = zeroSection P _ x := by
  let := f.normalSpaceFiberBundle hn hdim
  have := f.normalSpaceVectorBundle hn hdim
  rw [normalFiberDerivDiffeomorph_def]
  exact bundleDiffeomorph_zeroSection _ _ x

/-- The inverse of `normalFiberDerivDiffeomorph` fixes the zero section. -/
theorem normalFiberDerivDiffeomorph_symm_zeroSection (f : SmoothEmbedding I J ∞ M N)
    (hn : (∞ : ℕ∞ω) ≠ 0) (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E)
    {Φ : TotalSpace P (fun x ↦ f.NormalSpace x hn) → N}
    (hΦ : letI := f.normalSpaceFiberBundle hn hdim
      ∀ x, IsLocalDiffeomorphAt (I.prod 𝓘(ℝ, P)) J ∞ Φ (zeroSection P _ x))
    (hfΦ : Φ ∘ zeroSection P _ = f) (x : M) :
    letI := f.normalSpaceFiberBundle hn hdim
    (f.normalFiberDerivDiffeomorph hn hdim hΦ hfΦ).symm (zeroSection P _ x) =
      zeroSection P _ x := by
  let := f.normalSpaceFiberBundle hn hdim
  have := f.normalSpaceVectorBundle hn hdim
  rw [normalFiberDerivDiffeomorph_def]
  exact bundleDiffeomorph_symm_zeroSection _ _ x

/-- Let `Φ` be differentiable at the zero vector over `x`, and let `Ψ` be a smooth family of
continuous linear automorphisms of the fibres. The normal derivative at `x` of `Φ` precomposed
with the diffeomorphism `TauCeti.bundleDiffeomorph Ψ hΨ` of the total space is the normal
derivative of `Φ` at `x` composed with `Ψ x`. -/
theorem normalFiberDeriv_comp_bundleDiffeomorph (f : SmoothEmbedding I J ∞ M N)
    (hn : (∞ : ℕ∞ω) ≠ 0) (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E)
    {Φ : TotalSpace P (fun x ↦ f.NormalSpace x hn) → N} {x : M}
    (hΦ : letI := f.normalSpaceFiberBundle hn hdim
      MDifferentiableAt (I.prod 𝓘(ℝ, P)) J Φ (zeroSection P _ x))
    (Ψ : ∀ x, f.NormalSpace x hn ≃L[ℝ] f.NormalSpace x hn)
    (hΨ : letI := f.normalSpaceFiberBundle hn hdim
      ContMDiff (I.prod 𝓘(ℝ, P)) (I.prod 𝓘(ℝ, P)) ∞
        (fun p : TotalSpace P (fun x ↦ f.NormalSpace x hn) ↦ TotalSpace.mk' P
          (E := fun x ↦ f.NormalSpace x hn) p.proj (Ψ p.proj p.snd))) :
    letI := f.normalSpaceFiberBundle hn hdim
    haveI := f.normalSpaceVectorBundle hn hdim
    f.normalFiberDeriv hn hdim (Φ ∘ bundleDiffeomorph Ψ hΨ) x =
      (f.normalFiberDeriv hn hdim Φ x).comp (Ψ x : f.NormalSpace x hn →L[ℝ] _) := by
  let := f.normalSpaceFiberBundle hn hdim
  have := f.normalSpaceVectorBundle hn hdim
  have hΦΨ : MDifferentiableAt (I.prod 𝓘(ℝ, P)) J (Φ ∘ bundleDiffeomorph Ψ hΨ)
      (zeroSection P _ x) :=
    MDifferentiableAt.comp_of_eq _ hΦ
      ((bundleDiffeomorph Ψ hΨ).contMDiff.mdifferentiableAt (by simp))
      (bundleDiffeomorph_zeroSection Ψ hΨ x)
  ext v
  rw [ContinuousLinearMap.comp_apply, normalFiberDeriv_apply_eq_mfderiv_smul f hn hdim hΦΨ,
    normalFiberDeriv_apply_eq_mfderiv_smul f hn hdim hΦ]
  have e : (fun t : ℝ ↦ (Φ ∘ bundleDiffeomorph Ψ hΨ) ⟨x, t • v⟩) = fun t ↦ Φ ⟨x, t • Ψ x v⟩ := by
    funext t
    rw [Function.comp_apply, bundleDiffeomorph_apply]
    exact congrArg (fun w ↦ Φ ⟨x, w⟩) ((Ψ x).map_smul t v)
  rw [e, ContinuousLinearEquiv.coe_coe]
  -- The two sides differ only in the base points of the tangent spaces in their implicit
  -- types, which are all `V`.
  rfl

/-- A *normalized tube* of the smooth embedding `f`: a diffeomorphism `Φ` of the total space of
the normal bundle onto an open set `W` of `N` that sends the zero vector over each `x` to `f x`
and whose normal derivative `f.normalFiberDeriv hn hdim` is the identity of the normal space at
every point. By `normalFiberDeriv_eq_id_iff`, the second condition says that in the preferred
trivialization at `x`, the differential of `Φ` at the zero vector on a vertical vector `(0, w)`,
followed by the normal class, is the vector of the fibre with coordinate `w`. -/
structure IsNormalizedTube (f : SmoothEmbedding I J ∞ M N) (hn : (∞ : ℕ∞ω) ≠ 0)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E) {W : TopologicalSpace.Opens N}
    (Φ : letI := f.normalSpaceFiberBundle hn hdim
      TotalSpace P (fun x ↦ f.NormalSpace x hn) ≃ₘ^∞⟮I.prod 𝓘(ℝ, P), J⟯ W) : Prop where
  /-- The tube restricts to `f` on the zero section. -/
  apply_zeroSection (x : M) : letI := f.normalSpaceFiberBundle hn hdim
    (Φ (zeroSection P _ x) : N) = f x
  /-- The normal derivative of the tube is the identity at every point. -/
  normalFiberDeriv_eq_id (x : M) : letI := f.normalSpaceFiberBundle hn hdim
    f.normalFiberDeriv hn hdim (fun p ↦ (Φ p : N)) x = ContinuousLinearMap.id ℝ _

/-- The normal derivative of `Φ` at `x` is the identity exactly when, for each `w : P`, the
differential of `Φ` at the zero vector over `x` sends the vertical vector `(0, w)` of the
preferred chart to a vector whose normal class is the vector of the fibre with coordinate `w` in
the preferred trivialization at `x`. -/
theorem normalFiberDeriv_eq_id_iff (f : SmoothEmbedding I J ∞ M N) (hn : (∞ : ℕ∞ω) ≠ 0)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E)
    (Φ : TotalSpace P (fun x ↦ f.NormalSpace x hn) → N) (x : M) :
    letI := f.normalSpaceFiberBundle hn hdim
    haveI := f.normalSpaceVectorBundle hn hdim
    f.normalFiberDeriv hn hdim Φ x = ContinuousLinearMap.id ℝ _ ↔
      ∀ w : P, f.normalClassL x hn (mfderiv (I.prod 𝓘(ℝ, P)) J Φ (zeroSection P _ x)
        ((0 : E), w)) = (trivializationAt P (fun x ↦ f.NormalSpace x hn) x).symmL ℝ x w := by
  let := f.normalSpaceFiberBundle hn hdim
  have := f.normalSpaceVectorBundle hn hdim
  set e := trivializationAt P (fun x ↦ f.NormalSpace x hn) x
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt P _ x
  -- The normal derivative applied to `v` is the left side at `w = e v`.
  have hD (v : f.NormalSpace x hn) : f.normalFiberDeriv hn hdim Φ x v =
      f.normalClassL x hn (mfderiv (I.prod 𝓘(ℝ, P)) J Φ (zeroSection P _ x)
        ((0 : E), e.continuousLinearMapAt ℝ x v)) := by
    rw [normalFiberDeriv_apply, Bundle.zeroSectionTangentEquiv_symm_apply]
    -- `rw` leaves the projections of the pair `(0, v)` unreduced.
    rfl
  refine ⟨fun h w ↦ ?_, fun h ↦ ContinuousLinearMap.ext fun v ↦ ?_⟩
  · have := hD (e.symmL ℝ x w)
    rwa [h, ContinuousLinearMap.id_apply, e.continuousLinearMapAt_symmL hx, eq_comm] at this
  · rw [hD, h, ContinuousLinearMap.id_apply, e.symmL_continuousLinearMapAt hx]

/-- Let `Φ` be a diffeomorphism of the total space of the normal bundle of `f` onto an open set
`W`, equal to `f` on the zero section, and let `Ψ` be a smooth family of continuous linear
automorphisms of the fibres such that, at each `x`, the normal derivative of `Φ` composed with
`Ψ x` is the identity. Then `Φ` precomposed with the diffeomorphism `TauCeti.bundleDiffeomorph Ψ`
of the total space is a normalized tube. -/
theorem isNormalizedTube_comp_bundleEquiv (f : SmoothEmbedding I J ∞ M N)
    (hn : (∞ : ℕ∞ω) ≠ 0) (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E)
    {W : TopologicalSpace.Opens N}
    (Φ : letI := f.normalSpaceFiberBundle hn hdim
      TotalSpace P (fun x ↦ f.NormalSpace x hn) ≃ₘ^∞⟮I.prod 𝓘(ℝ, P), J⟯ W)
    (hΦ : letI := f.normalSpaceFiberBundle hn hdim
      ∀ x, (Φ (zeroSection P _ x) : N) = f x)
    (Ψ : ∀ x, f.NormalSpace x hn ≃L[ℝ] f.NormalSpace x hn)
    (hΨ : letI := f.normalSpaceFiberBundle hn hdim
      ContMDiff (I.prod 𝓘(ℝ, P)) (I.prod 𝓘(ℝ, P)) ∞
        (fun p : TotalSpace P (fun x ↦ f.NormalSpace x hn) ↦ TotalSpace.mk' P
          (E := fun x ↦ f.NormalSpace x hn) p.proj (Ψ p.proj p.snd)))
    (hΦΨ : letI := f.normalSpaceFiberBundle hn hdim
      ∀ x, (f.normalFiberDeriv hn hdim (fun p ↦ (Φ p : N)) x).comp
        (Ψ x : f.NormalSpace x hn →L[ℝ] _) = ContinuousLinearMap.id ℝ _) :
    letI := f.normalSpaceFiberBundle hn hdim
    haveI := f.normalSpaceVectorBundle hn hdim
    f.IsNormalizedTube hn hdim ((bundleDiffeomorph Ψ hΨ).trans Φ) := by
  let := f.normalSpaceFiberBundle hn hdim
  have := f.normalSpaceVectorBundle hn hdim
  refine ⟨fun x ↦ ?_, fun x ↦ ?_⟩
  · rw [Diffeomorph.coe_trans, Function.comp_apply, bundleDiffeomorph_zeroSection]
    exact hΦ x
  · have hd : MDifferentiableAt (I.prod 𝓘(ℝ, P)) J (fun p ↦ (Φ p : N)) (zeroSection P _ x) :=
      ((isLocalDiffeomorph_subtype_val (I := J) (n := ∞) (U := W) _).mdifferentiableAt
        (by simp)).comp _ (Φ.contMDiff.mdifferentiableAt (by simp))
    rw [← hΦΨ x, ← normalFiberDeriv_comp_bundleDiffeomorph f hn hdim hd Ψ hΨ,
      Diffeomorph.coe_trans]
    -- The two maps differ only in where `Function.comp` and the coercion to `N` are applied.
    rfl

/-- Let `Φ` be a diffeomorphism of the total space of the normal bundle of `f` onto an open set
`W`, equal to `f` on the zero section. Then `Φ` precomposed with the inverse of
`normalFiberDerivDiffeomorph`, which acts on each fibre by the inverse of the normal derivative of
`Φ`, is a normalized tube. -/
theorem isNormalizedTube_normalFiberDerivDiffeomorph_symm_trans (f : SmoothEmbedding I J ∞ M N)
    (hn : (∞ : ℕ∞ω) ≠ 0) (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E)
    {W : TopologicalSpace.Opens N}
    (Φ : letI := f.normalSpaceFiberBundle hn hdim
      TotalSpace P (fun x ↦ f.NormalSpace x hn) ≃ₘ^∞⟮I.prod 𝓘(ℝ, P), J⟯ W)
    (hl : letI := f.normalSpaceFiberBundle hn hdim
      ∀ x, IsLocalDiffeomorphAt (I.prod 𝓘(ℝ, P)) J ∞ (fun p ↦ (Φ p : N)) (zeroSection P _ x))
    (hz : (fun p ↦ (Φ p : N)) ∘ zeroSection P _ = f) :
    letI := f.normalSpaceFiberBundle hn hdim
    f.IsNormalizedTube hn hdim ((f.normalFiberDerivDiffeomorph hn hdim hl hz).symm.trans Φ) := by
  let := f.normalSpaceFiberBundle hn hdim
  have := f.normalSpaceVectorBundle hn hdim
  let Ψ x := (f.normalFiberDerivEquiv hn hdim (hl x) (.of_eq hz)).symm
  have hΨ : ContMDiff (I.prod 𝓘(ℝ, P)) (I.prod 𝓘(ℝ, P)) ∞
      (fun p : TotalSpace P (fun x ↦ f.NormalSpace x hn) ↦ TotalSpace.mk' P
        (E := fun x ↦ f.NormalSpace x hn) p.proj (Ψ p.proj p.snd)) :=
    (f.normalFiberDerivDiffeomorph hn hdim hl hz).symm.contMDiff.congr fun p ↦ by
      rw [normalFiberDerivDiffeomorph_symm_apply]
  have hsymm : (f.normalFiberDerivDiffeomorph hn hdim hl hz).symm = bundleDiffeomorph Ψ hΨ :=
    Diffeomorph.ext fun p ↦ by
      rw [normalFiberDerivDiffeomorph_symm_apply, bundleDiffeomorph_apply]
  rw [hsymm]
  refine f.isNormalizedTube_comp_bundleEquiv hn hdim Φ (fun x ↦ congrFun hz x) Ψ hΨ fun x ↦ ?_
  rw [← coe_normalFiberDerivEquiv f hn hdim (hl x) (.of_eq hz)]
  exact ContinuousLinearEquiv.coe_comp_coe_symm _

/-- **Existence of normalized tubes.** Inside every open set `O` containing the range of a smooth
embedding `f` between boundaryless manifolds, with `N` Hausdorff and second countable, there is a
normalized tube of `f`: a diffeomorphism of the total space of its normal bundle onto an open set
`W ⊆ O`, equal to `f` on the zero section, whose normal derivative is the identity. -/
theorem exists_isNormalizedTube_subset [I.Boundaryless] [J.Boundaryless] [T2Space N]
    [SecondCountableTopology N] (f : SmoothEmbedding I J ∞ M N)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E) {O : Set N} (hO : IsOpen O)
    (hfO : Set.range f ⊆ O) :
    let hn : (∞ : ℕ∞ω) ≠ 0 := by simp
    letI := f.normalSpaceFiberBundle hn hdim
    ∃ W : TopologicalSpace.Opens N, (W : Set N) ⊆ O ∧
      ∃ Φ : TotalSpace P (fun x ↦ f.NormalSpace x hn) ≃ₘ^∞⟮I.prod 𝓘(ℝ, P), J⟯ W,
        f.IsNormalizedTube hn hdim Φ := by
  intro hn
  let := f.normalSpaceFiberBundle hn hdim
  obtain ⟨W, hWO, Φ, hΦ⟩ := f.exists_diffeomorph_normalBundle_subset (P := P) hdim hO hfO
  -- The tube as a map into `N` is a local diffeomorphism.
  have hl (x : M) : IsLocalDiffeomorphAt (I.prod 𝓘(ℝ, P)) J ∞ (fun p ↦ (Φ p : N))
      (zeroSection P _ x) :=
    (Φ.isLocalDiffeomorph _).comp (hg := isLocalDiffeomorph_subtype_val (U := W) _)
  exact ⟨W, hWO, _,
    f.isNormalizedTube_normalFiberDerivDiffeomorph_symm_trans hn hdim Φ hl (funext hΦ)⟩

/-- Let `Φ` be a normalized tube of `f`, `x : M`, and `e` the preferred trivialization of the normal
bundle at `x`. Let `g : P → N` have derivative `A` at `0`, such that the normal class of each
`A w` is the vector of the fibre over `x` with coordinate `w` in `e`. Let `h : P → ν` be
continuous at `0`, send `0` to the zero vector over `x`, and lift `g` through `Φ` near `0`. Then
the fibre coordinate `w ↦ (e (h w)).2` of `h` has derivative the identity at `0`. -/
theorem IsNormalizedTube.hasFDerivAt_trivializationAt_snd {f : SmoothEmbedding I J ∞ M N}
    {hn : (∞ : ℕ∞ω) ≠ 0} {hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E}
    {W : TopologicalSpace.Opens N}
    {Φ : letI := f.normalSpaceFiberBundle hn hdim
      TotalSpace P (fun x ↦ f.NormalSpace x hn) ≃ₘ^∞⟮I.prod 𝓘(ℝ, P), J⟯ W}
    (hΦ : f.IsNormalizedTube hn hdim Φ) {x : M} {g : P → N} {A : P →L[ℝ] V}
    (hg : HasMFDerivAt 𝓘(ℝ, P) J g 0 A)
    (hA : letI := f.normalSpaceFiberBundle hn hdim
      haveI := f.normalSpaceVectorBundle hn hdim
      ∀ w : P, f.normalClassL x hn (A w) =
        (trivializationAt P (fun x ↦ f.NormalSpace x hn) x).symmL ℝ x w)
    {h : P → TotalSpace P (fun x ↦ f.NormalSpace x hn)}
    (hc : letI := f.normalSpaceFiberBundle hn hdim
      ContinuousAt h 0)
    (h0 : h 0 = zeroSection P _ x) (hgh : ∀ᶠ w in 𝓝 0, (Φ (h w) : N) = g w) :
    letI := f.normalSpaceFiberBundle hn hdim
    HasFDerivAt (fun w ↦ (trivializationAt P (fun x ↦ f.NormalSpace x hn) x (h w)).2)
      (ContinuousLinearMap.id ℝ P) 0 := by
  let := f.normalSpaceFiberBundle hn hdim
  have := f.normalSpaceVectorBundle hn hdim
  set e := trivializationAt P (fun x ↦ f.NormalSpace x hn) x
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt P _ x
  set F : TotalSpace P (fun x ↦ f.NormalSpace x hn) → N := fun p ↦ (Φ p : N)
  set p₀ := zeroSection P (fun x ↦ f.NormalSpace x hn) x
  have hl : IsLocalDiffeomorphAt (I.prod 𝓘(ℝ, P)) J ∞ F p₀ :=
    (Φ.isLocalDiffeomorph _).comp (hg := isLocalDiffeomorph_subtype_val (U := W) _)
  have hFh : F ∘ h =ᶠ[𝓝 0] g := hgh
  -- `h` is differentiable at `0`, and its differential `L` followed by the differential `D` of
  -- `F` at `p₀` is `A`.
  have hd : MDifferentiableAt 𝓘(ℝ, P) (I.prod 𝓘(ℝ, P)) h 0 :=
    .of_comp_isLocalDiffeomorph (h0 ▸ hl) (by simp) hc
      (hg.mdifferentiableAt.congr_of_eventuallyEq hFh)
  set D := mfderiv (I.prod 𝓘(ℝ, P)) J F p₀
  set L := mfderiv 𝓘(ℝ, P) (I.prod 𝓘(ℝ, P)) h 0
  have hDL (w : P) : D (L w) = A w := by
    have h1 := mfderiv_comp_apply_of_eq 0 (hl.mdifferentiableAt (by simp)) hd h0 w
    rw [hFh.mfderiv_eq, hg.mfderiv] at h1
    exact h1.symm
  -- The normal class of `D v` is the vector of the fibre with coordinate the second component
  -- of `v`: `D` sends horizontal vectors to tangent vectors of `f`, and is the identity on
  -- vertical vectors.
  have hD (v : TangentSpace (I.prod 𝓘(ℝ, P)) p₀) :
      f.normalClassL x hn (D v) = e.symmL ℝ x v.2 := by
    let a : TangentSpace (I.prod 𝓘(ℝ, P)) p₀ := ((0 : E), v.2)
    let b : TangentSpace (I.prod 𝓘(ℝ, P)) p₀ := (v.1, (0 : P))
    have hv : D v = D a + D b := by
      rw [← D.map_add]
      -- The tangent space at `p₀` is `E × P`, where `v = a + b` holds componentwise.
      exact congrArg D (Prod.ext (zero_add _).symm (add_zero _).symm)
    have ha : f.normalClassL x hn (D a) = e.symmL ℝ x v.2 :=
      (normalFiberDeriv_eq_id_iff f hn hdim F x).1 (hΦ.normalFiberDeriv_eq_id x) v.2
    have hb := Bundle.mfderiv_zeroSectionTangentEquiv_symm_inl (hl.mdifferentiableAt (by simp))
      (g := f) (Filter.Eventually.of_forall hΦ.apply_zeroSection) v.1
    rw [Bundle.zeroSectionTangentEquiv_symm_apply, map_zero] at hb
    have hb' : f.normalClassL x hn (D b) = 0 := by
      -- `hb` is about `((v.1, 0).1, 0)`, which reduces to `b`.
      have : D b = mfderiv I J f x v.1 := hb
      rw [this, normalClassL_apply]
      exact normalClass_mfderiv f x hn _
    -- The two sums live in tangent spaces of `N` at `F p₀` and at `f x`, both `V`.
    calc f.normalClassL x hn (D v) = f.normalClassL x hn (D a + D b) := by rw [hv]
      _ = f.normalClassL x hn (D a) + f.normalClassL x hn (D b) := map_add _ _ _
      _ = e.symmL ℝ x v.2 := by
        rw [ha, hb', add_zero]
  have hL (w : P) : (L w).2 = w := by
    have h1 := congrArg (e.continuousLinearMapAt ℝ x)
      ((hD (L w)).symm.trans ((congrArg _ (hDL w)).trans (hA w)))
    rwa [e.continuousLinearMapAt_symmL hx, e.continuousLinearMapAt_symmL hx] at h1
  -- In the preferred chart at `p₀`, whose second coordinate is that of `e`, `h` has
  -- derivative `L`.
  have hfd := hd.hasMFDerivAt.2
  simp only [writtenInExtChartAt, h0, extChartAt_model_space_eq_id, PartialEquiv.refl_symm,
    PartialEquiv.refl_coe, Function.comp_id, modelWithCornersSelf_coe, Set.range_id,
    hasFDerivWithinAt_univ, id_eq] at hfd
  refine ((hasFDerivAt_snd.comp 0 hfd).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun w ↦ ?_)).congr_fderiv (ContinuousLinearMap.ext fun w ↦ ?_)
  · simp only [Function.comp_apply, FiberBundle.extChartAt, PartialEquiv.coe_trans,
      PartialEquiv.prod_coe, PartialEquiv.refl_coe, id_eq, Trivialization.coe_coe,
      OpenPartialHomeomorph.coe_toPartialEquiv, p₀, zeroSection_proj, e]
  · exact hL w

end TauCeti.SmoothEmbedding

end
