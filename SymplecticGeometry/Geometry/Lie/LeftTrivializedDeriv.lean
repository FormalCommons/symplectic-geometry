/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Lie.InvariantVectorField.Basic
import SymplecticGeometry.Geometry.Manifold.MFDeriv.Constancy

/-!
# Curves in a Lie group with a prescribed left-trivialized derivative

For a real Lie group `G` with Lie algebra `𝔤 = GroupLieAlgebra I G`, a curve `g : ℝ → G` has
left-trivialized derivative `ξ : ℝ → 𝔤` on a set `s` of times if at each `t ∈ s` it has a
derivative within `s` whose translate to the identity, `d(L_{(g t)⁻¹})_{g t} (g' t)`, is `ξ t`:
in matrix notation, `g⁻¹ g' = ξ`. Equivalently, `g' t` is the value at `g t` of the
left-invariant vector field of `ξ t`, so that `g` is an integral curve of the time-dependent
vector field `(t, x) ↦ dL_x (ξ t)`.

## Main definitions

* `SymplecticGeometry.HasLeftTrivializedDerivOn g ξ s`: the curve `g` has left-trivialized
  derivative `ξ` on `s`.

## Main results

* `SymplecticGeometry.hasLeftTrivializedDerivOn_iff`: the condition in terms of Mathlib's
  `mulInvariantVectorField`.
* `SymplecticGeometry.HasLeftTrivializedDerivOn.const_mul`: left translates `t ↦ a * g t` of
  such a curve have the same left-trivialized derivative.
* `SymplecticGeometry.HasLeftTrivializedDerivOn.eqOn`: two curves with the same left-trivialized
  derivative on a preconnected set that agree at one of its points agree on it. Neither
  continuity of `ξ` nor completeness of the model is needed.

## Implementation notes

The derivative is taken within `s`, as in Mathlib's `IsMIntegralCurveOn`; on an open set, and in
particular on `Set.univ`, this is the derivative at each point.

The proof of `const_mul` follows that of Tau Ceti's `IsMIntegralCurveOn.map_of_mfderiv_eq`, with
Tau Ceti's `mfderiv_mul_left_mulInvariantVectorField` for the vector fields.

For uniqueness, at a time `t` both curves are first translated to pass through `1`, as
`φ u = (g t)⁻¹ * g u` and `ψ u = (h t)⁻¹ * h u`; both then have derivative `ξ t` at `t`. By Tau
Ceti's derivatives of multiplication and inversion at the identity (`mfderiv_mul_apply_one`,
`GroupLieAlgebra.mfderiv_inv_one_apply`), `u ↦ φ u * (ψ u)⁻¹` has derivative `ξ t - ξ t = 0`
at `t`, and so has its translate `u ↦ g u * (h u)⁻¹`. A curve whose derivative vanishes on a
preconnected subset of `ℝ` is constant on it (`Convex.apply_eq_of_hasMFDerivWithinAt_zero`).
-/

public section

open Set TauCeti
open scoped Manifold

namespace SymplecticGeometry

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]

/-- A curve `g : ℝ → G` in a Lie group **has left-trivialized derivative** `ξ : ℝ → 𝔤` on a set
`s` of times if, at each `t ∈ s`, it has a derivative `v` within `s` such that
`d(L_{(g t)⁻¹})_{g t} v = ξ t`. -/
def HasLeftTrivializedDerivOn (g : ℝ → G) (ξ : ℝ → GroupLieAlgebra I G) (s : Set ℝ) : Prop :=
  ∀ t ∈ s, ∃ v : TangentSpace I (g t),
    HasMFDerivWithinAt 𝓘(ℝ) I g s t ((1 : ℝ →L[ℝ] ℝ).smulRight v) ∧
      mfderiv I I ((g t)⁻¹ * ·) (g t) v = ξ t

variable {g h : ℝ → G} {ξ : ℝ → GroupLieAlgebra I G} {s : Set ℝ}

/-- The definition of `HasLeftTrivializedDerivOn`. -/
theorem hasLeftTrivializedDerivOn_def :
    HasLeftTrivializedDerivOn g ξ s ↔ ∀ t ∈ s, ∃ v : TangentSpace I (g t),
      HasMFDerivWithinAt 𝓘(ℝ) I g s t ((1 : ℝ →L[ℝ] ℝ).smulRight v) ∧
        mfderiv I I ((g t)⁻¹ * ·) (g t) v = ξ t :=
  Iff.rfl

/-- A curve has left-trivialized derivative `ξ` on `s` if and only if, at each `t ∈ s`, its
derivative within `s` is the value at `g t` of the left-invariant vector field of `ξ t`. -/
theorem hasLeftTrivializedDerivOn_iff [ContMDiffMul I 1 G] :
    HasLeftTrivializedDerivOn g ξ s ↔ ∀ t ∈ s, HasMFDerivWithinAt 𝓘(ℝ) I g s t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (mulInvariantVectorField (ξ t) (g t))) := by
  refine ⟨fun hg t ht ↦ ?_, fun hg t ht ↦
    ⟨_, hg t ht, mfderiv_inv_mul_mulInvariantVectorField _ _⟩⟩
  obtain ⟨v, hgv, hv⟩ := hg t ht
  obtain rfl := (mfderiv_inv_mul_injective (g t)
    ((mfderiv_inv_mul_mulInvariantVectorField _ _).trans hv.symm)).symm
  exact hgv

/-- The condition on a set implies it on every subset. -/
theorem HasLeftTrivializedDerivOn.mono (hg : HasLeftTrivializedDerivOn g ξ s) {s' : Set ℝ}
    (hs' : s' ⊆ s) : HasLeftTrivializedDerivOn g ξ s' := fun t ht ↦
  let ⟨v, hgv, hv⟩ := hg t (hs' ht)
  ⟨v, hgv.mono hs', hv⟩

/-- Left translation preserves the left-trivialized derivative: if `g` has left-trivialized
derivative `ξ` on `s`, so has `t ↦ a * g t`. -/
theorem HasLeftTrivializedDerivOn.const_mul [ContMDiffMul I 1 G]
    (hg : HasLeftTrivializedDerivOn g ξ s) (a : G) :
    HasLeftTrivializedDerivOn (fun t ↦ a * g t) ξ s := by
  rw [hasLeftTrivializedDerivOn_iff] at hg ⊢
  intro t ht
  have hder : (mfderiv I I (a * ·) (g t)).comp
      ((1 : ℝ →L[ℝ] ℝ).smulRight (mulInvariantVectorField (ξ t) (g t))) =
        (1 : ℝ →L[ℝ] ℝ).smulRight (mulInvariantVectorField (ξ t) (a * g t)) := by
    rw [ContinuousLinearMap.smulRight_one_eq_toSpanSingleton,
      ContinuousLinearMap.smulRight_one_eq_toSpanSingleton,
      ContinuousLinearMap.comp_toSpanSingleton, mfderiv_mul_left_mulInvariantVectorField]
  exact (mdifferentiableAt_mul_left.hasMFDerivAt.comp_hasMFDerivWithinAt t (hg t ht)).congr_mfderiv
    hder

/-- Translated to pass through `1` at `t`, a curve with left-trivialized derivative `ξ` has
derivative `ξ t` there. -/
private theorem HasLeftTrivializedDerivOn.hasMFDerivWithinAt_inv_mul [ContMDiffMul I 1 G]
    (hg : HasLeftTrivializedDerivOn g ξ s) {t : ℝ} (ht : t ∈ s) :
    HasMFDerivWithinAt 𝓘(ℝ) I (fun u ↦ (g t)⁻¹ * g u) s t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (ξ t)) := by
  obtain ⟨v, hgv, hv⟩ := hg t ht
  have hder : (mfderiv I I ((g t)⁻¹ * ·) (g t)).comp ((1 : ℝ →L[ℝ] ℝ).smulRight v) =
      (1 : ℝ →L[ℝ] ℝ).smulRight (ξ t) := by
    rw [ContinuousLinearMap.smulRight_one_eq_toSpanSingleton,
      ContinuousLinearMap.smulRight_one_eq_toSpanSingleton,
      ContinuousLinearMap.comp_toSpanSingleton, hv]
    -- The two sides differ only in the tangent space, at `(g t)⁻¹ * g t` or at `1`, that is the
    -- codomain; both are the model space.
    rfl
  exact (mdifferentiableAt_mul_left.hasMFDerivAt.comp_hasMFDerivWithinAt t hgv).congr_mfderiv hder

/-- Two curves through `1` at `t` with the same derivative there: `u ↦ φ u * (ψ u)⁻¹` has zero
derivative at `t`. -/
private theorem hasMFDerivWithinAt_mul_inv_zero [LieGroup I 1 G] {φ ψ : ℝ → G} {t : ℝ}
    {X : GroupLieAlgebra I G}
    (hφ : HasMFDerivWithinAt 𝓘(ℝ) I φ s t ((1 : ℝ →L[ℝ] ℝ).smulRight X))
    (hψ : HasMFDerivWithinAt 𝓘(ℝ) I ψ s t ((1 : ℝ →L[ℝ] ℝ).smulRight X))
    (hφ1 : φ t = 1) (hψ1 : ψ t = 1) :
    HasMFDerivWithinAt 𝓘(ℝ) I (fun u ↦ φ u * (ψ u)⁻¹) s t 0 := by
  have hψi := ((contMDiff_inv I 1).mdifferentiableAt
    one_ne_zero).hasMFDerivAt.comp_hasMFDerivWithinAt t hψ
  have hm := ((contMDiff_mul I 1).mdifferentiableAt
    one_ne_zero).hasMFDerivAt.comp_hasMFDerivWithinAt t (hφ.prodMk hψi)
  refine hm.congr_mfderiv ?_
  -- The derivatives at the identity are stated at `1`; the base points here are only
  -- propositionally equal to it, so generalize them before substituting.
  have key : ∀ x y : G, x = 1 → y = 1 →
      mfderiv (I.prod I) I (fun p : G × G ↦ p.1 * p.2) (x, y⁻¹)
        (X, mfderiv I I (·⁻¹) y X) = 0 := by
    rintro x y rfl rfl
    rw [GroupLieAlgebra.mfderiv_inv_one_apply]
    have h1 : ∀ z : G, z = 1 →
        mfderiv (I.prod I) I (fun p : G × G ↦ p.1 * p.2) (1, z) (X, -X) = 0 := by
      rintro z rfl
      exact (mfderiv_mul_apply_one X (-X)).trans (add_neg_cancel X)
    exact h1 _ inv_one
  ext
  refine (congrArg (mfderiv (I.prod I) I (fun p : G × G ↦ p.1 * p.2) (φ t, (ψ t)⁻¹)) ?_).trans
    (key _ _ hφ1 hψ1)
  exact Prod.ext (one_smul ℝ X)
    (congrArg (mfderiv I I (fun x : G ↦ x⁻¹) (ψ t)) (one_smul ℝ X))

/-- **Uniqueness.** Two curves with the same left-trivialized derivative on a preconnected set
`s` of times that agree at one point of `s` agree on all of `s`. -/
theorem HasLeftTrivializedDerivOn.eqOn [LieGroup I 1 G] (hg : HasLeftTrivializedDerivOn g ξ s)
    (hh : HasLeftTrivializedDerivOn h ξ s) (hs : IsPreconnected s) {t₀ : ℝ} (ht₀ : t₀ ∈ s)
    (h₀ : g t₀ = h t₀) : EqOn g h s := by
  have hk (t : ℝ) (ht : t ∈ s) :
      HasMFDerivWithinAt 𝓘(ℝ) I (fun u ↦ g u * (h u)⁻¹) s t 0 := by
    have hm := hasMFDerivWithinAt_mul_inv_zero (hg.hasMFDerivWithinAt_inv_mul ht)
      (hh.hasMFDerivWithinAt_inv_mul ht) (inv_mul_cancel _) (inv_mul_cancel _)
    have hL := ((contMDiff_mul_left.mul contMDiff_const :
      ContMDiff I I 1 fun x : G ↦ g t * x * (h t)⁻¹).mdifferentiableAt
        one_ne_zero).hasMFDerivAt.comp_hasMFDerivWithinAt t hm
    rw [ContinuousLinearMap.comp_zero] at hL
    convert hL using 1
    · funext u
      simp [mul_assoc]
    -- Both sides are the zero map, into the tangent spaces at the two equal base points.
    · rfl
  intro t ht
  have := hs.convex.apply_eq_of_hasMFDerivWithinAt_zero hk ht ht₀
  rwa [h₀, mul_inv_cancel, mul_inv_eq_one] at this

end SymplecticGeometry

end
