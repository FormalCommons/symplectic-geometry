/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Topology.Compactness.Paracompact
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Topology
public import TauCeti.Topology.VectorBundle.Pullback
import TauCeti.Geometry.Manifold.Immersion.Differential
import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.Basic
import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.NormalSpace.Exact
import SymplecticGeometry.Algebra.Exact.Basic
import TauCeti.Topology.VectorBundle.Splitting
import TauCeti.Topology.FiberBundle.Pullback

/-!
# Splitting the tangent bundle along an embedding

Let `f : M → N` be an embedding of positive regularity into a finite-dimensional manifold
over `𝕜`, and `ν` its normal bundle, with fibres `ν_x = T_{f x} N ⧸ df_x (T_x M)` (Tau Ceti's
`Manifold.IsImmersion.NormalSpace`). This file splits the short exact sequence
`0 → TM → f^* TN → ν → 0` of bundles over `M`.

* A fibrewise linear right inverse `r` of the normal class map, whose map of total spaces is
  continuous, exists when `M` is normal and paracompact and `𝕜` is `ℝ` or `ℂ`:
  `TauCeti.SmoothEmbedding.normalRightInverse`. With the normal bundle given its vector bundle
  structure of rank `dim V - dim E` (Tau Ceti's `TauCeti.SmoothEmbedding.normalSpaceFiberBundle`),
  the normal class map is a continuous, fibrewise surjective section of the Hom bundle from
  `f^* TN` to `ν`, and Tau Ceti's `Continuous.exists_continuous_clm_bundle_rightInverse` gives
  it a continuous right inverse.
* For any fibrewise linear right inverse `r`, the maps `(u, a) ↦ df u + r a` form an isomorphism
  `TM ×ᵇ ν ≃ f^* TN`: `TauCeti.SmoothEmbedding.tangentNormalEquiv`, the inverse of the
  splitting that Mathlib's `Function.Exact.splitSurjectiveEquiv` gives in each fibre. Its map of
  total spaces is continuous when that of `r` is, and so is the inverse, by Tau Ceti's
  `TauCeti.continuous_bundle_symm`.

## Main definitions

* `TauCeti.SmoothEmbedding.normalRightInverse`: a fibrewise right inverse of the normal class
  map, continuous on total spaces.
* `TauCeti.SmoothEmbedding.tangentNormalEquiv`: the isomorphism `TM ×ᵇ ν ≃ f^* TN` given by a
  fibrewise right inverse of the normal class map.

## Main results

* `TauCeti.SmoothEmbedding.normalClass_normalRightInverse`,
  `TauCeti.SmoothEmbedding.continuous_normalRightInverse`.
* `TauCeti.SmoothEmbedding.tangentNormalEquiv_apply`,
  `TauCeti.SmoothEmbedding.continuous_tangentNormalEquiv`,
  `TauCeti.SmoothEmbedding.continuous_tangentNormalEquiv_symm`.

## Implementation notes

Continuity of a section of the Hom bundle is turned into continuity of its map of total spaces,
and back, by Tau Ceti's `TauCeti.continuous_hom_bundle_iff`; the normal class map is a quotient
map from the total space of `f^* TN` onto that of `ν`
(`TauCeti.SmoothEmbedding.isQuotientMap_normalQuotientMap`). The finite dimension of the model
space of `M`, which the vector bundle structure on `ν` needs, comes from the injectivity of the
differential at a point (Tau Ceti's `Manifold.IsImmersion.finiteDimensional_tangentSpace`); over
an empty `M` there is nothing to prove.

## References

* J. Milnor and J. Stasheff, *Characteristic Classes*, Chapter 3, for splitting off a sub-bundle
  by a complement.
* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, the normal bundle before
  Theorem 6.24.
-/

public section

noncomputable section

open Bundle Set Topology Filter
open scoped Manifold ContDiff

namespace TauCeti.SmoothEmbedding

variable {𝕜 E V H G M N : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 V G}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N] {n : ℕ∞ω}

/-! ### The isomorphism given by a right inverse -/

section Equiv

variable (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
  (r : ∀ x, f.isImmersion.NormalSpace x hn →L[𝕜] TangentSpace J (f x))
  (hr : ∀ x a, f.isImmersion.normalClass x hn (r x a) = a)

/-- The isomorphism `T_x M × ν_x ≃ T_{f x} N`, `(u, a) ↦ df u + r a`, given by a fibrewise right
inverse `r` of the normal class map. -/
def tangentNormalEquiv (x : M) :
    (TangentSpace I ×ᵇ fun x ↦ f.isImmersion.NormalSpace x hn) x ≃L[𝕜]
      ((f : M → N) *ᵖ (TangentSpace J)) x :=
  haveI : T2Space (((f : M → N) *ᵖ (TangentSpace J)) x) := inferInstanceAs (T2Space V)
  haveI : FiniteDimensional 𝕜 (((f : M → N) *ᵖ (TangentSpace J)) x) :=
    inferInstanceAs (FiniteDimensional 𝕜 V)
  haveI : T2Space ((TangentSpace I ×ᵇ fun x ↦ f.isImmersion.NormalSpace x hn) x) :=
    inferInstanceAs (T2Space (E × f.isImmersion.NormalSpace x hn))
  ((exact_mfderiv_normalClass f x hn).splitSurjectiveEquiv
      (f.isImmersion.mfderiv_injective hn x) ⟨(r x).toLinearMap, LinearMap.ext (hr x)⟩).val
    |>.toContinuousLinearEquiv.symm

/-- The isomorphism given by a right inverse `r` sends `(u, a)` to `df u + r a`. -/
@[simp]
theorem tangentNormalEquiv_apply (x : M) (p :
    (TangentSpace I ×ᵇ fun x ↦ f.isImmersion.NormalSpace x hn) x) :
    f.tangentNormalEquiv hn r hr x p = mfderiv I J f x p.1 + r x p.2 :=
  (exact_mfderiv_normalClass f x hn).splitSurjectiveEquiv_symm_apply
    (f.isImmersion.mfderiv_injective hn x) ⟨(r x).toLinearMap, LinearMap.ext (hr x)⟩ p

/-- The normal component of the inverse of the isomorphism is the normal class. -/
@[simp]
theorem snd_tangentNormalEquiv_symm_apply (x : M) (v : TangentSpace J (f x)) :
    ((f.tangentNormalEquiv hn r hr x).symm v).2 = f.isImmersion.normalClass x hn v := by
  conv_rhs => rw [← (f.tangentNormalEquiv hn r hr x).apply_symm_apply v]
  rw [tangentNormalEquiv_apply, map_add, Manifold.IsImmersion.normalClass_mfderiv, zero_add, hr]

/-- The tangential component of the inverse of the isomorphism is carried by `df` to
`v - r [v]`. -/
theorem mfderiv_fst_tangentNormalEquiv_symm_apply (x : M)
    (v : TangentSpace J (f x)) :
    mfderiv I J f x ((f.tangentNormalEquiv hn r hr x).symm v).1 =
      v - r x (f.isImmersion.normalClass x hn v) := by
  have h := (f.tangentNormalEquiv hn r hr x).apply_symm_apply v
  rw [tangentNormalEquiv_apply, snd_tangentNormalEquiv_symm_apply] at h
  exact eq_sub_of_add_eq h

variable [IsManifold I 1 M] [IsManifold J 1 N] {P : Type*}

/-- If the map of total spaces of a right inverse `r` is continuous, so is that of the
isomorphism `TM ×ᵇ ν ≃ f^* TN` it gives. -/
theorem continuous_tangentNormalEquiv
    (hrc : Continuous fun p : TotalSpace P (fun x ↦ f.isImmersion.NormalSpace x hn) ↦
      TotalSpace.mk' V (E := (f : M → N) *ᵖ (TangentSpace J)) p.proj (r p.proj p.snd)) :
    Continuous fun p : TotalSpace (E × P) (TangentSpace I ×ᵇ fun x ↦ f.isImmersion.NormalSpace x
        hn) ↦
      TotalSpace.mk' V (E := (f : M → N) *ᵖ (TangentSpace J)) p.proj
        (f.tangentNormalEquiv hn r hr p.proj p.snd) := by
  have hd := (FiberBundle.Prod.isInducing_diag E (TangentSpace I) P
    (fun x ↦ f.isImmersion.NormalSpace x hn)).continuous
  -- The differential, as a map from the total space of `TM` to that of `f^* TN`.
  have hdf : Continuous fun p : TangentBundle I M ↦
      TotalSpace.mk' V (E := (f : M → N) *ᵖ (TangentSpace J)) p.proj
        (mfderiv I J f p.proj p.snd) :=
    Pullback.continuous_iff.2 ⟨FiberBundle.continuous_proj E (TangentSpace I),
      f.contMDiff.continuous_tangentMap (ENat.one_le_iff_ne_zero_withTop.mpr hn)⟩
  have h := (hdf.comp (continuous_fst.comp hd)).add_totalSpace 𝕜 (hrc.comp (continuous_snd.comp hd))
  exact h.congr fun p ↦ (congrArg (TotalSpace.mk p.proj)
    (f.tangentNormalEquiv_apply hn r hr p.proj p.snd)).symm

/-- If the map of total spaces of a right inverse `r` is continuous, so is that of the inverse
of the isomorphism `TM ×ᵇ ν ≃ f^* TN` it gives. -/
theorem continuous_tangentNormalEquiv_symm [FiniteDimensional 𝕜 E] [NormedAddCommGroup P]
    [NormedSpace 𝕜 P] [FiniteDimensional 𝕜 P]
    (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E)
    (hrc : Continuous fun p : TotalSpace P (fun x ↦ f.isImmersion.NormalSpace x hn) ↦
      TotalSpace.mk' V (E := (f : M → N) *ᵖ (TangentSpace J)) p.proj (r p.proj p.snd)) :
    Continuous fun p : TotalSpace V ((f : M → N) *ᵖ (TangentSpace J)) ↦
      TotalSpace.mk' (E × P) (E := TangentSpace I ×ᵇ fun x ↦ f.isImmersion.NormalSpace x hn) p.proj
        ((f.tangentNormalEquiv hn r hr p.proj).symm p.snd) := by
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  exact TauCeti.continuous_bundle_symm _ (f.continuous_tangentNormalEquiv hn r hr hrc)

end Equiv

/-! ### A continuous right inverse of the normal class map -/

section RightInverse

variable [IsManifold I 1 M] [IsManifold J 1 N] (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)

variable [IsRCLikeNormedField 𝕜] [_root_.NormalSpace M] [ParacompactSpace M]

/-- Over a normal paracompact manifold, the normal class map of an embedding over `ℝ` or `ℂ`
has a fibrewise linear right inverse whose composite with the normal class map is continuous on
total spaces. -/
theorem exists_rightInverse_normalClass :
    ∃ r : ∀ x, f.isImmersion.NormalSpace x hn →L[𝕜] TangentSpace J (f x),
      (∀ x a, f.isImmersion.normalClass x hn (r x a) = a) ∧
      Continuous fun v : TotalSpace V ((f : M → N) *ᵖ (TangentSpace J)) ↦
        TotalSpace.mk' V (E := (f : M → N) *ᵖ (TangentSpace J)) v.proj
          (r v.proj (f.isImmersion.normalClass v.proj hn v.snd)) := by
  rcases isEmpty_or_nonempty M with hM | ⟨⟨x₀⟩⟩
  · exact ⟨fun _ ↦ 0, fun x ↦ isEmptyElim x,
      continuous_iff_continuousAt.2 fun v ↦ isEmptyElim v.proj⟩
  -- The differential at `x₀` embeds the model space of `M` in `V`, so it is finite-dimensional
  -- and the normal spaces, of rank `finrank V - finrank E`, form a vector bundle.
  have : FiniteDimensional 𝕜 (TangentSpace J (f x₀)) := inferInstanceAs (FiniteDimensional 𝕜 V)
  have : FiniteDimensional 𝕜 (TangentSpace I x₀) :=
    f.isSmoothEmbedding_toFun.isImmersion.finiteDimensional_tangentSpace x₀ hn
  have : FiniteDimensional 𝕜 E := this
  let := IsRCLikeNormedField.rclike 𝕜
  let P := Fin (Module.finrank 𝕜 V - Module.finrank 𝕜 E) → 𝕜
  have hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E := by simp [P]
  let := f.normalSpaceFiberBundle hn hdim
  have := f.normalSpaceVectorBundle hn hdim
  have hquot := (f.isQuotientMap_normalQuotientMap (K := P) hn).continuous
  -- The normal class map is a continuous section of the Hom bundle from `f^* TN` to `ν`, and
  -- it is fibrewise surjective, so it has a continuous right inverse.
  have hq : Continuous fun x ↦ TotalSpace.mk' (V →L[𝕜] P)
      (E := fun x ↦ ((f : M → N) *ᵖ (TangentSpace J)) x →L[𝕜] f.isImmersion.NormalSpace x hn) x
      (f.isImmersion.normalClassL x hn) :=
    (continuous_hom_bundle_iff (E₁ := (f : M → N) *ᵖ (TangentSpace J)) _).2 <|
      hquot.congr fun v ↦ by
        rw [normalQuotientMap_apply]
        exact congrArg (TotalSpace.mk v.proj)
            (f.isImmersion.normalClassL_apply v.proj hn v.snd).symm
  obtain ⟨r, hr, hqr⟩ := Continuous.exists_continuous_clm_bundle_rightInverse
    (E₁ := (f : M → N) *ᵖ (TangentSpace J)) (E₂ := fun x ↦ f.isImmersion.NormalSpace x hn) hq fun
        x ↦
      .of_surjective_of_finiteDimensional fun w ↦
        (f.isImmersion.normalClass_surjective x hn w).imp fun v hv ↦
            (f.isImmersion.normalClassL_apply x hn v).trans hv
  refine ⟨r, fun x a ↦ ?_, ?_⟩
  · exact (f.isImmersion.normalClassL_apply x hn (r x a)).symm.trans (DFunLike.congr_fun (hqr x) a)
  refine ((continuous_hom_bundle_iff r).1 hr).comp hquot |>.congr fun v ↦ ?_
  rw [Function.comp_apply, normalQuotientMap_apply]
  -- What is left are the projections of a pair, which reduce to its components.
  rfl

/-- A fibrewise linear right inverse of the normal class map `T_{f x} N → ν_x` of an embedding,
over a normal paracompact manifold and over `ℝ` or `ℂ`, whose map of total spaces is
continuous (`TauCeti.SmoothEmbedding.continuous_normalRightInverse`). -/
def normalRightInverse (x : M) : f.isImmersion.NormalSpace x hn →L[𝕜] TangentSpace J (f x) :=
  (f.exists_rightInverse_normalClass hn).choose x

/-- `normalRightInverse` is a right inverse of the normal class map. -/
@[simp]
theorem normalClass_normalRightInverse (x : M) (a : f.isImmersion.NormalSpace x hn) :
    f.isImmersion.normalClass x hn (f.normalRightInverse hn x a) = a :=
  (f.exists_rightInverse_normalClass hn).choose_spec.1 x a

/-- The map of total spaces of `normalRightInverse`, from the normal bundle to `f^* TN`, is
continuous. -/
theorem continuous_normalRightInverse {P : Type*} :
    Continuous fun p : TotalSpace P (fun x ↦ f.isImmersion.NormalSpace x hn) ↦
      TotalSpace.mk' V (E := (f : M → N) *ᵖ (TangentSpace J)) p.proj
        (f.normalRightInverse hn p.proj p.snd) :=
  (f.continuous_normalBundle_iff hn).2 <|
    (f.exists_rightInverse_normalClass hn).choose_spec.2.congr fun v ↦ by
      -- `normalRightInverse` is the chosen right inverse, by definition.
      rw [Function.comp_apply, normalQuotientMap_apply]
      rfl

end RightInverse

end TauCeti.SmoothEmbedding

end
