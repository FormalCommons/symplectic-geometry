/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Lagrangian.SymplecticTangent
public import TauCeti.Geometry.Symplectic.Lagrangian.Embedding.Symplectic.Normal.Bundle
public import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.NormalSpace.ThomPairMap
import TauCeti.Geometry.Symplectic.Lagrangian.Constructions

/-!
# Symplectic tangent images under local symplectomorphisms

A local diffeomorphism `k : M → M₂` that pulls a nondegenerate two-form `σ₂` back to `σ` is a
symplectomorphism on every tangent space. So a differentiable map `f : N → M` has symplectic
tangent images for `σ` exactly when `k ∘ f` has them for `σ₂`
(`TauCeti.SmoothTwoForm.IsNondegenerate.hasSymplecticTangentImages_comp_iff_of_isLocalDiffeomorph`).
This extends Tau Ceti's `hasSymplecticTangentImages_diffeomorph_comp_iff`, for a diffeomorphism
`k`, to local diffeomorphisms such as the inclusion of an open subset or of a piece of a glued
manifold, and follows its proof. Unlike there, `f` must be differentiable: a local diffeomorphism
that is not injective can make a map that is not differentiable smooth.

## Main results

* `TauCeti.SmoothTwoForm.IsNondegenerate.isSymplectomorphism_mfderiv_of_isLocalDiffeomorph`: the
  differential of such a `k` at a point is a linear symplectomorphism.
* `TauCeti.SmoothTwoForm.IsNondegenerate.hasSymplecticTangentImages_comp_iff_of_isLocalDiffeomorph`:
  the transport of symplectic tangent images.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.1
-/

public section

open Manifold
open scoped Manifold ContDiff

namespace TauCeti.SmoothTwoForm.IsNondegenerate

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {E₂ H₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [TopologicalSpace H₂]
  {I₂ : ModelWithCorners ℝ E₂ H₂} {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
  [IsManifold I₂ ∞ M₂]
  {σ : SmoothTwoForm I M} (hσ : σ.IsNondegenerate) {σ₂ : SmoothTwoForm I₂ M₂}
  (hσ₂ : σ₂.IsNondegenerate) {k : M → M₂}

/-- The differential at `y` of a local diffeomorphism `k` pulling `σ₂` back to `σ` is a linear
symplectomorphism from the tangent-space symplectic form of `σ` at `y` to that of `σ₂` at
`k y`. -/
theorem isSymplectomorphism_mfderiv_of_isLocalDiffeomorph (hk : IsLocalDiffeomorph I I₂ ∞ k)
    (hkσ : SmoothForm.mpullback k hk.contMDiff σ₂ = σ) (y : M) :
    SymplecticForm.IsSymplectomorphism (hσ.symplecticFormAt y) (hσ₂.symplecticFormAt (k y))
      (hk.mfderivToContinuousLinearEquiv (by simp) y).toLinearEquiv := by
  rw [SymplecticForm.isSymplectomorphism_iff]
  intro v w
  rw [IsNondegenerate.symplecticFormAt_apply, IsNondegenerate.symplecticFormAt_apply, ← hkσ,
    SmoothForm.eval₂_mpullback, ContinuousLinearEquiv.coe_toLinearEquiv,
    ← ContinuousLinearEquiv.coe_coe, IsLocalDiffeomorph.mfderivToContinuousLinearEquiv_coe]

variable {hσ hσ₂}

/-- **Transport by local symplectomorphisms.** If a local diffeomorphism `k` pulls `σ₂` back to
`σ`, a differentiable map `f` has symplectic tangent images for `σ` exactly when `k ∘ f` has
symplectic tangent images for `σ₂`. -/
theorem hasSymplecticTangentImages_comp_iff_of_isLocalDiffeomorph
    (hk : IsLocalDiffeomorph I I₂ ∞ k) (hkσ : SmoothForm.mpullback k hk.contMDiff σ₂ = σ)
    {f : N → M} (hf : MDifferentiable J I f) :
    hσ₂.HasSymplecticTangentImages J (k ∘ f) ↔ hσ.HasSymplecticTangentImages J f := by
  rw [hasSymplecticTangentImages_iff_forall, hasSymplecticTangentImages_iff_forall]
  refine forall_congr' fun x ↦ ?_
  have he := isSymplectomorphism_mfderiv_of_isLocalDiffeomorph hσ hσ₂ hk hkσ (f x)
  rw [SymplecticForm.isSymplectomorphism_iff_transport_eq] at he
  rw [Function.comp_apply, ← he, mfderiv_comp x ((hk (f x)).mdifferentiableAt (by simp)) (hf x),
    ContinuousLinearMap.toLinearMap_comp, LinearMap.range_comp,
    ← SymplecticForm.isSymplectic_map_transport_iff (e := (hk.mfderivToContinuousLinearEquiv
      (by simp) (f x)).toLinearEquiv)]
  congr!
  ext v
  rw [LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv, ContinuousLinearMap.coe_coe,
    ← ContinuousLinearEquiv.coe_coe, IsLocalDiffeomorph.mfderivToContinuousLinearEquiv_coe]

end TauCeti.SmoothTwoForm.IsNondegenerate


namespace TauCeti.SmoothEmbedding

variable {E V V' H G G' Z X X' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup V'] [NormedSpace ℝ V'] [FiniteDimensional ℝ V']
  [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace G'] {I : ModelWithCorners ℝ E H}
  {J : ModelWithCorners ℝ V G} {J' : ModelWithCorners ℝ V' G'}
  [TopologicalSpace Z] [ChartedSpace H Z] [TopologicalSpace X] [ChartedSpace G X]
  [IsManifold J ∞ X] [TopologicalSpace X'] [ChartedSpace G' X'] [IsManifold J' ∞ X']
  {n m : ℕ∞ω} {σ : SmoothTwoForm J X} {hσ : σ.IsNondegenerate} {σ' : SmoothTwoForm J' X'}
  {hσ' : σ'.IsNondegenerate} {v : X' → X}

/-- **Normal symplectic forms of a commuting triangle.** Let `f' : Z → X'` and `f : Z → X` be
embeddings with symplectic tangent images and `v : X' → X` a map with `v ∘ f' = f`, differentiable
with invertible derivative at each point `f' x`, whose derivative at `f' x` carries `σ` to `σ'`.
Then the identification `normalSpaceEquivOfComp` of the normal spaces of `f'` and `f` at `x`
carries the normal symplectic form of `f'` to that of `f`. -/
theorem symplecticNormalForm_normalSpaceEquivOfComp (f' : SmoothEmbedding I J' n Z X')
    (f : SmoothEmbedding I J m Z X) (hf' : hσ'.HasSymplecticTangentImages I f')
    (hf : hσ.HasSymplecticTangentImages I f) (hn : n ≠ 0) (hm : m ≠ 0)
    (hv : ∀ x, (mfderiv J' J v (f' x)).IsInvertible) (h : v ∘ f' = f) (x : Z)
    (hvx : MDifferentiableAt J' J v (f' x))
    (hvσ : ∀ a b, SmoothBundleForm.eval₂ σ (v (f' x)) (mfderiv J' J v (f' x) a)
      (mfderiv J' J v (f' x) b) = SmoothBundleForm.eval₂ σ' (f' x) a b)
    (a b : f'.isImmersion.NormalSpace x hn) :
    f.symplecticNormalForm hf x hm (f'.normalSpaceEquivOfComp f hn hm hv h x a)
        (f'.normalSpaceEquivOfComp f hn hm hv h x b) =
      f'.symplecticNormalForm hf' x hn a b := by
  rw [normalSpaceEquivOfComp_def, ← ContinuousLinearEquiv.coe_coe,
    normalSpaceEquiv_toContinuousLinearMap]
  exact f'.symplecticNormalForm_normalMap f hf' hf hn hm _ hvx hvσ
    (by rw [mfderiv_id]; exact Function.surjective_id) a b

end TauCeti.SmoothEmbedding

end
