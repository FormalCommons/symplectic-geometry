/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Lie.FundamentalVectorField
public import TauCeti.Geometry.Lie.InvariantVectorField.Basic
public import TauCeti.Geometry.Manifold.MFDeriv.Curve
import SymplecticGeometry.Geometry.Lie.FundamentalVectorField
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

* `SymplecticGeometry.hasLeftTrivializedDerivOn_iff_of_isOpen`,
  `SymplecticGeometry.hasLeftTrivializedDerivOn_univ_iff`: on an open set, the condition with the
  derivative at each point.
* `SymplecticGeometry.hasLeftTrivializedDerivOn_iff`: the condition in terms of Mathlib's
  `mulInvariantVectorField`.
* `SymplecticGeometry.HasLeftTrivializedDerivOn.continuousOn`: such a curve is continuous on `s`.
* `SymplecticGeometry.HasLeftTrivializedDerivOn.mdifferentiableAt`,
  `SymplecticGeometry.HasLeftTrivializedDerivOn.mfderiv_inv_mul_curveVelocity`: at a time of which
  `s` is a neighbourhood, the curve is differentiable, and its velocity translated to the identity
  is `ξ t`.
* `SymplecticGeometry.hasLeftTrivializedDerivOn_mulInvariantExp_smul`: the one-parameter subgroup
  `t ↦ exp (t • v)` has constant left-trivialized derivative `v`.
* `SymplecticGeometry.HasLeftTrivializedDerivOn.const_mul`: left translates `t ↦ a * g t` of
  such a curve have the same left-trivialized derivative.
* `SymplecticGeometry.HasLeftTrivializedDerivOn.const_mul_comp_inv_smul`: the same for a
  derivative `F ((g t)⁻¹ • a⁻¹ • p)` read off along an orbit, which becomes `F ((a * g t)⁻¹ • p)`.
* `SymplecticGeometry.HasLeftTrivializedDerivOn.piecewise`: two such curves on open sets with a
  preconnected intersection, agreeing at one of its points, glue to one on the union.
* `HasMFDerivWithinAt.mul_inv_of_eq_one`: if two maps from a manifold into a Lie group take the
  value `1` at `x` with the same derivative there, then `u ↦ φ u * (ψ u)⁻¹` has zero
  derivative at `x`.
* `SymplecticGeometry.HasLeftTrivializedDerivOn.eqOn`: two curves with the same left-trivialized
  derivative on a preconnected set that agree at one of its points agree on it. Neither
  continuity of `ξ` nor completeness of the model is needed.
* `SymplecticGeometry.HasLeftTrivializedDerivOn.hasMFDerivWithinAt_inv_smul`,
  `SymplecticGeometry.HasLeftTrivializedDerivOn.hasMFDerivWithinAt_inv_smul_of_contMDiffSMul`:
  for an action of `G` on `M` and `p : M`, the orbit curve `t ↦ (g t)⁻¹ • p` has derivative
  `-ξ_M((g t)⁻¹ • p)`: in matrix notation, if `g⁻¹ g' = ξ`, then `y = g⁻¹ p` solves
  `y' = -X_ξ(y)`.

## Implementation notes

The derivative is taken within `s`, as in Mathlib's `IsMIntegralCurveOn`; on an open set, and in
particular on `Set.univ`, this is the derivative at each point.

The gluing lemma `piecewise` adapts the proof of Mathlib's `isMIntegralCurveOn_piecewise` from
intervals to open sets, with `eqOn` in place of the uniqueness of integral curves.

The proof of `const_mul` follows that of Tau Ceti's `IsMIntegralCurveOn.map_of_mfderiv_eq`, with
Tau Ceti's `mfderiv_mul_left_mulInvariantVectorField` for the vector fields; so does the private
step that translates a curve to pass through `1`.

For uniqueness, at a time `t` both curves are first translated to pass through `1`, as
`φ u = (g t)⁻¹ * g u` and `ψ u = (h t)⁻¹ * h u`; both then have derivative `ξ t` at `t`. By Tau
Ceti's derivatives of multiplication and inversion at the identity (`mfderiv_mul_apply_one`,
`GroupLieAlgebra.mfderiv_inv_one_apply`), `u ↦ φ u * (ψ u)⁻¹` has derivative `ξ t - ξ t = 0`
at `t`, and so has its translate `u ↦ g u * (h u)⁻¹`. A curve whose derivative vanishes on a
preconnected subset of `ℝ` is constant on it (`Convex.apply_eq_of_hasMFDerivWithinAt_zero`).

The derivative of the orbit curve is the chain rule along `g`, with the derivative of
`h ↦ h⁻¹ • p` from `TauCeti.mfderiv_inv_smul_apply`.
-/

public section

open Set TauCeti
open scoped Manifold Topology

section MulInv

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E H : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {G : Type*}
  [TopologicalSpace G] [ChartedSpace H G] [Group G] {E' H' : Type*} [NormedAddCommGroup E']
  [NormedSpace 𝕜 E'] [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'} {M : Type*}
  [TopologicalSpace M] [ChartedSpace H' M]

/-- If two maps `φ`, `ψ` into a Lie group take the value `1` at `x` and have the same derivative
within `s` there, then `u ↦ φ u * (ψ u)⁻¹` has zero derivative within `s` at `x`. -/
theorem HasMFDerivWithinAt.mul_inv_of_eq_one [LieGroup I 1 G] {φ ψ : M → G} {s : Set M}
    {x : M} {f' : E' →L[𝕜] E} (hφ : HasMFDerivWithinAt I' I φ s x f')
    (hψ : HasMFDerivWithinAt I' I ψ s x f') (hφ1 : φ x = 1) (hψ1 : ψ x = 1) :
    HasMFDerivWithinAt I' I (fun u ↦ φ u * (ψ u)⁻¹) s x 0 := by
  have hψi := ((contMDiff_inv I 1).mdifferentiableAt
    one_ne_zero).hasMFDerivAt.comp_hasMFDerivWithinAt x hψ
  have hm := ((contMDiff_mul I 1).mdifferentiableAt
    one_ne_zero).hasMFDerivAt.comp_hasMFDerivWithinAt x (hφ.prodMk hψi)
  refine hm.congr_mfderiv ?_
  -- The derivatives at the identity are stated at `1`; the base points here are only
  -- propositionally equal to it, so generalize them before substituting.
  have key : ∀ (X : GroupLieAlgebra I G) (a b : G), a = 1 → b = 1 →
      mfderiv (I.prod I) I (fun p : G × G ↦ p.1 * p.2) (a, b⁻¹)
        (X, mfderiv I I (·⁻¹) b X) = 0 := by
    rintro X a b rfl rfl
    rw [GroupLieAlgebra.mfderiv_inv_one_apply]
    have h1 : ∀ z : G, z = 1 →
        mfderiv (I.prod I) I (fun p : G × G ↦ p.1 * p.2) (1, z) (X, -X) = 0 := by
      rintro z rfl
      exact (mfderiv_mul_apply_one X (-X)).trans (add_neg_cancel X)
    exact h1 _ inv_one
  ext v
  exact key (f' v : GroupLieAlgebra I G) _ _ hφ1 hψ1

end MulInv

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

/-- On an open set of times, the condition takes the derivative at each point instead of the
derivative within the set. -/
theorem hasLeftTrivializedDerivOn_iff_of_isOpen (hs : IsOpen s) :
    HasLeftTrivializedDerivOn g ξ s ↔ ∀ t ∈ s, ∃ v : TangentSpace I (g t),
      HasMFDerivAt 𝓘(ℝ) I g t ((1 : ℝ →L[ℝ] ℝ).smulRight v) ∧
        mfderiv I I ((g t)⁻¹ * ·) (g t) v = ξ t :=
  forall₂_congr fun _ ht ↦ exists_congr fun _ ↦ and_congr_left' ⟨fun h ↦
    h.hasMFDerivAt (hs.mem_nhds ht), HasMFDerivAt.hasMFDerivWithinAt⟩

/-- On all times, the condition takes the derivative at each time. -/
theorem hasLeftTrivializedDerivOn_univ_iff :
    HasLeftTrivializedDerivOn g ξ univ ↔ ∀ t, ∃ v : TangentSpace I (g t),
      HasMFDerivAt 𝓘(ℝ) I g t ((1 : ℝ →L[ℝ] ℝ).smulRight v) ∧
        mfderiv I I ((g t)⁻¹ * ·) (g t) v = ξ t := by
  simp [hasLeftTrivializedDerivOn_iff_of_isOpen isOpen_univ]

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

/-- Left translation of a curve whose left-trivialized derivative is read off along an orbit:
for an action of `G` on `X`, `F : X → 𝔤`, `a : G` and `p : X`, if `g` has left-trivialized
derivative `F ((g t)⁻¹ • a⁻¹ • p)` on `s`, then `t ↦ a * g t` has left-trivialized derivative
`F ((a * g t)⁻¹ • p)` on `s`. -/
theorem HasLeftTrivializedDerivOn.const_mul_comp_inv_smul [ContMDiffMul I 1 G] {X : Type*}
    [MulAction G X] {F : X → GroupLieAlgebra I G} {a : G} {p : X}
    (hg : HasLeftTrivializedDerivOn g (fun t ↦ F ((g t)⁻¹ • a⁻¹ • p)) s) :
    HasLeftTrivializedDerivOn (fun t ↦ a * g t) (fun t ↦ F ((a * g t)⁻¹ • p)) s := by
  simp only [mul_inv_rev, mul_smul]
  exact hg.const_mul a

/-- The one-parameter subgroup `t ↦ exp (t • v)` has the constant left-trivialized derivative
`v` at every time. -/
theorem hasLeftTrivializedDerivOn_mulInvariantExp_smul [CompleteSpace E]
    [LieGroup I (minSmoothness ℝ 3) G] [T2Space G] [BoundarylessManifold I G]
    (v : GroupLieAlgebra I G) :
    HasLeftTrivializedDerivOn (fun t : ℝ ↦ mulInvariantExp (I := I) (t • v)) (fun _ ↦ v) univ :=
  have : LieGroup I 1 G := LieGroup.of_le (n := minSmoothness ℝ 3) (by norm_num)
  hasLeftTrivializedDerivOn_iff.2 fun t _ ↦
    (hasMFDerivAt_mulInvariantExp_smul v t).hasMFDerivWithinAt

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

/-- **Uniqueness.** Two curves with the same left-trivialized derivative on a preconnected set
`s` of times that agree at one point of `s` agree on all of `s`. -/
theorem HasLeftTrivializedDerivOn.eqOn [LieGroup I 1 G] (hg : HasLeftTrivializedDerivOn g ξ s)
    (hh : HasLeftTrivializedDerivOn h ξ s) (hs : IsPreconnected s) {t₀ : ℝ} (ht₀ : t₀ ∈ s)
    (h₀ : g t₀ = h t₀) : EqOn g h s := by
  have hk (t : ℝ) (ht : t ∈ s) :
      HasMFDerivWithinAt 𝓘(ℝ) I (fun u ↦ g u * (h u)⁻¹) s t 0 := by
    have hm := (hg.hasMFDerivWithinAt_inv_mul ht).mul_inv_of_eq_one
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

/-- A curve that agrees on `s` with a curve of left-trivialized derivative `ξ` on `s` has
left-trivialized derivative `ξ` on `s`. -/
theorem HasLeftTrivializedDerivOn.congr (hg : HasLeftTrivializedDerivOn g ξ s) {f : ℝ → G}
    (hfg : EqOn f g s) : HasLeftTrivializedDerivOn f ξ s := by
  intro t ht
  obtain ⟨v, hgv, hv⟩ := hg t ht
  refine ⟨v, (hgv.congr_of_eventuallyEq (eventually_nhdsWithin_of_forall hfg)
    (hfg ht)).congr_mfderiv ?_, by rw [hfg ht]; exact hv⟩
  -- `tangentSpaceCast` between the tangent spaces at the equal points `g t` and `f t` is the
  -- identity of the model space.
  ext
  rfl

/-- A curve with left-trivialized derivative on `s` is continuous on `s`. -/
theorem HasLeftTrivializedDerivOn.continuousOn (hg : HasLeftTrivializedDerivOn g ξ s) :
    ContinuousOn g s := fun t ht ↦
  let ⟨_, hgv, _⟩ := hg t ht
  hgv.continuousWithinAt

/-- At a time `t` of which `s` is a neighbourhood, a curve with left-trivialized derivative on
`s` is differentiable. -/
theorem HasLeftTrivializedDerivOn.mdifferentiableAt (hg : HasLeftTrivializedDerivOn g ξ s)
    {t : ℝ} (hs : s ∈ 𝓝 t) : MDifferentiableAt 𝓘(ℝ) I g t :=
  let ⟨_, hgv, _⟩ := hg t (mem_of_mem_nhds hs)
  (hgv.hasMFDerivAt hs).mdifferentiableAt

/-- At a time `t` of which `s` is a neighbourhood, the velocity `Manifold.curveVelocity I g t` of
a curve with left-trivialized derivative `ξ` on `s`, translated to the identity, is `ξ t`. -/
theorem HasLeftTrivializedDerivOn.mfderiv_inv_mul_curveVelocity
    (hg : HasLeftTrivializedDerivOn g ξ s) {t : ℝ} (hs : s ∈ 𝓝 t) :
    mfderiv I I ((g t)⁻¹ * ·) (g t) (Manifold.curveVelocity I g t) = ξ t := by
  obtain ⟨v, hgv, hv⟩ := hg t (mem_of_mem_nhds hs)
  rw [← Manifold.curveVelocityWithin_of_mem_nhds hs,
    Manifold.curveVelocityWithin_eq_of_hasMFDerivWithinAt hgv (uniqueDiffWithinAt_of_mem_nhds hs),
    hv]

/-- On a union of two open sets, the condition holds if it holds on each of them. -/
theorem HasLeftTrivializedDerivOn.union_of_isOpen {s' : Set ℝ}
    (hg : HasLeftTrivializedDerivOn g ξ s) (hg' : HasLeftTrivializedDerivOn g ξ s')
    (hs : IsOpen s) (hs' : IsOpen s') :
    HasLeftTrivializedDerivOn g ξ (s ∪ s') := by
  rw [hasLeftTrivializedDerivOn_iff_of_isOpen hs] at hg
  rw [hasLeftTrivializedDerivOn_iff_of_isOpen hs'] at hg'
  rw [hasLeftTrivializedDerivOn_iff_of_isOpen (hs.union hs')]
  rintro t (ht | ht)
  exacts [hg t ht, hg' t ht]

/-- **Gluing.** Let `g` and `h` have left-trivialized derivative `ξ` on open sets `s` and `s'`
whose intersection is preconnected, and agree at a point of it. Then the curve equal to `g` on
`s` and to `h` elsewhere has left-trivialized derivative `ξ` on `s ∪ s'`. -/
theorem HasLeftTrivializedDerivOn.piecewise [LieGroup I 1 G] {s' : Set ℝ}
    [∀ t, Decidable (t ∈ s)] (hg : HasLeftTrivializedDerivOn g ξ s)
    (hh : HasLeftTrivializedDerivOn h ξ s') (hs : IsOpen s) (hs' : IsOpen s')
    (hss' : IsPreconnected (s ∩ s')) {t₀ : ℝ} (ht₀ : t₀ ∈ s ∩ s') (h₀ : g t₀ = h t₀) :
    HasLeftTrivializedDerivOn (s.piecewise g h) ξ (s ∪ s') := by
  have hgh := (hg.mono inter_subset_left).eqOn (hh.mono inter_subset_right) hss' ht₀ h₀
  refine (hg.congr (piecewise_eqOn s g h)).union_of_isOpen (hh.congr fun t ht ↦ ?_) hs hs'
  by_cases hts : t ∈ s
  · rw [piecewise_eq_of_mem _ _ _ hts]
    exact hgh ⟨hts, ht⟩
  · exact piecewise_eq_of_notMem _ _ _ hts

section InvSMul

variable {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} {M : Type*} [TopologicalSpace M] [ChartedSpace H' M]
  [MulAction G M] {p : M}

/-- **The orbit curve.** If `g` has left-trivialized derivative `ξ` on `s` and `h ↦ h⁻¹ • p` is
differentiable at `g t`, for `t ∈ s`, then the curve `u ↦ (g u)⁻¹ • p` has derivative within `s`
at `t` equal to `-ξ_M((g t)⁻¹ • p)`, minus the fundamental vector field of `ξ t`. -/
theorem HasLeftTrivializedDerivOn.hasMFDerivWithinAt_inv_smul [LieGroup I 1 G]
    (hg : HasLeftTrivializedDerivOn g ξ s) {t : ℝ} (ht : t ∈ s)
    (hp : MDifferentiableAt I I' (fun h : G ↦ h⁻¹ • p) (g t)) :
    HasMFDerivWithinAt 𝓘(ℝ) I' (fun u ↦ (g u)⁻¹ • p) s t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (-fundamentalVectorField (I := I) (G := G) I' (ξ t) ((g t)⁻¹ • p))) := by
  obtain ⟨v, hgv, hv⟩ := hg t ht
  refine (hp.hasMFDerivAt.comp_hasMFDerivWithinAt t hgv).congr_mfderiv ?_
  rw [ContinuousLinearMap.smulRight_one_eq_toSpanSingleton,
    ContinuousLinearMap.smulRight_one_eq_toSpanSingleton]
  exact (ContinuousLinearMap.comp_toSpanSingleton (R₁ := ℝ)
    (mfderiv I I' (fun h : G ↦ h⁻¹ • p) (g t)) v).trans (by rw [mfderiv_inv_smul_apply, hv])

/-- **The orbit curve, for a smooth action.** If `g` has left-trivialized derivative `ξ` on `s`
and `G` acts smoothly on `M`, then for `t ∈ s` the curve `u ↦ (g u)⁻¹ • p` has derivative within
`s` at `t` equal to `-ξ_M((g t)⁻¹ • p)`. -/
theorem HasLeftTrivializedDerivOn.hasMFDerivWithinAt_inv_smul_of_contMDiffSMul [LieGroup I 1 G]
    [ContMDiffSMul I I' 1 G M] (hg : HasLeftTrivializedDerivOn g ξ s) {t : ℝ} (ht : t ∈ s) :
    HasMFDerivWithinAt 𝓘(ℝ) I' (fun u ↦ (g u)⁻¹ • p) s t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (-fundamentalVectorField (I := I) (G := G) I' (ξ t) ((g t)⁻¹ • p))) :=
  hg.hasMFDerivWithinAt_inv_smul ht <|
    ((ContMDiffSMul.contMDiff_smul_const p).comp (contMDiff_inv I 1)).mdifferentiableAt
      one_ne_zero

end InvSMul

end SymplecticGeometry

end
