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
import Mathlib.Geometry.Manifold.VectorBundle.Pullback
import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.Quotient
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

## Main definitions

* `TauCeti.SmoothEmbedding.normalFiberDeriv`: the normal derivative of a map out of the normal
  bundle along the zero section, as a continuous linear endomorphism of each fibre.
* `TauCeti.SmoothEmbedding.normalFiberDerivEquiv`: the normal derivative at `x` of a map that is
  a local diffeomorphism at `0_x` and restricts to `f` on the zero section near `x`, as a
  continuous linear automorphism of the fibre at `x`.
* `TauCeti.SmoothEmbedding.normalFiberDerivDiffeomorph`: for a map that is a local
  diffeomorphism at each zero vector and restricts to `f` on the zero section, the diffeomorphism
  of the total space of the normal bundle given on each fibre by the normal derivative.

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
  -- The map `w ↦ ⟨x, L w⟩` into the normal bundle is differentiable: in the preferred
  -- trivialization at `x` its fibre part is a continuous linear map.
  have hm : MDifferentiableAt 𝓘(ℝ, Q) (I.prod 𝓘(ℝ, P))
      (fun w : Q ↦ (⟨x, L w⟩ : TotalSpace P (fun x ↦ f.NormalSpace x hn))) 0 := by
    refine (mdifferentiableAt_totalSpace _ _).2 ⟨mdifferentiableAt_const, ?_⟩
    have e : (fun w : Q ↦ (trivializationAt P (fun x ↦ f.NormalSpace x hn) x ⟨x, L w⟩).2) =
        (trivializationAt P (fun x ↦ f.NormalSpace x hn) x).continuousLinearMapAt ℝ x ∘L L := by
      funext w
      simp [Trivialization.continuousLinearMapAt_apply]
    rw [e]
    exact ContinuousLinearMap.mdifferentiableAt _
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

/-- The continuous linear automorphism `normalFiberDerivEquiv` applies the normal derivative. -/
@[simp]
theorem normalFiberDerivEquiv_apply (f : SmoothEmbedding I J ∞ M N) (hn : (∞ : ℕ∞ω) ≠ 0)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E)
    {Φ : TotalSpace P (fun x ↦ f.NormalSpace x hn) → N} {x : M}
    (hΦ : letI := f.normalSpaceFiberBundle hn hdim
      IsLocalDiffeomorphAt (I.prod 𝓘(ℝ, P)) J ∞ Φ (zeroSection P _ x))
    (hfΦ : Φ ∘ zeroSection P _ =ᶠ[𝓝 x] f) (v : f.NormalSpace x hn) :
    f.normalFiberDerivEquiv hn hdim hΦ hfΦ v = f.normalFiberDeriv hn hdim Φ x v := by
  rw [normalFiberDerivEquiv, LinearEquiv.coe_toContinuousLinearEquiv',
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
  rw [normalFiberDerivDiffeomorph_apply]
  exact congrArg (TotalSpace.mk x) (map_zero _)

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
  rw [normalFiberDerivDiffeomorph_symm_apply]
  exact congrArg (TotalSpace.mk x) (map_zero _)

end TauCeti.SmoothEmbedding

end
