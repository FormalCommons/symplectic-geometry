/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Analysis.Calculus.FDeriv.Equiv
import TauCeti.Analysis.Calculus.InverseFunctionTheorem
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompContinuousLinearEquiv
import TauCeti.Analysis.Calculus.IteratedFDeriv.Prod
import TauCeti.Analysis.InnerProductSpace.RangeProjection
import TauCeti.Analysis.Normed.Module.ContinuousInverse
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic

/-!
# Tangent projection charts

Let `e : M → F` be a smooth map from a boundaryless manifold into a real inner product space, with
injective differentials, and let `T` be the range of the differential of `e` at `x : M`. Near `x`,
the orthogonal projection `z ↦ P (e z - e x)` of `e` onto `T` is a chart of `M` with values in
`T`, which presents the image of `e` near `e x` as a graph over its tangent space. For a compact
`M` embedded in a Euclidean space, these are the local graph charts with which Weil builds convex
covers [Weil1952, §1, pp. 120–122].

## Main definitions

* `SymplecticGeometry.tangentProjectionChart`: for a `C^n` map `e` (`1 ≤ n`) with injective
  differential at `x`, a partial diffeomorphism around `x` onto an open subset of `T`, given on
  its source by `z ↦ P (e z - e x)` (`tangentProjectionChart_apply`).

## Main results

* `SymplecticGeometry.exists_uniform_tangentProjectionChart`: for a compact `M` and a smooth
  injective `e`, one radius `r > 0` such that for every `x` such a chart is defined on all `z`
  with `‖e z - e x‖ < r` and reaches the ball of radius `r` in `T`, and one bound for the
  derivatives of order at most `2` of the composite of `e` with the inverses of these charts.

## Implementation notes

The chart at a single point comes from Tau Ceti's inverse function theorem on manifolds,
`TauCeti.isLocalDiffeomorphAt_of_injective_mfderiv`. For the uniform statement, the projection is
read in the extended chart at a point `x₀`, where `e` becomes a map `g` on an open subset of `E`.
The inverse function theorem is applied once, to the map `(w', w) ↦ (w', S (Q w' (g w - g w')))`
of `E × E`, where `Q w'` is the orthogonal projection onto the range of `fderiv ℝ g w'`, which
depends smoothly on `w'` (`ContDiffAt.starProjection_range`), and `S` is a fixed left inverse of
`fderiv ℝ g` at the chart image of `x₀`. Its inverse gives, for all `x` near `x₀` at once, local
inverses of the charts on one ball, with derivative bounds from compactness. Finitely many such
neighbourhoods cover `M`. The chart at a point adapts the argument of Tau Ceti's
`ContDiffOn.exists_openPartialHomeomorph_starProjection`, which builds the same graph chart on an
open subset of `E`: the projection fixes the tangent space, so its differential is an isomorphism
onto it.

## References

* [A. Weil, *Sur les théorèmes de de Rham*][Weil1952], §1, pp. 120–122
-/

public section

open Set Function Filter Topology Metric
open scoped Manifold ContDiff

namespace SymplecticGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {n : WithTop ℕ∞} {e : M → F} {x : M}

/-! ### The chart at a point -/

section Pointwise

variable [IsManifold I n M] [BoundarylessManifold I M]

/-- The orthogonal projection of `e z - e x` onto the range of the differential of `e` at `x` is a
local diffeomorphism at `x`. -/
private theorem isLocalDiffeomorphAt_orthogonalProjectionOnto_sub (hn : 1 ≤ n)
    (he : ContMDiff I 𝓘(ℝ, F) n e) (hx : Injective (mfderiv I 𝓘(ℝ, F) e x)) :
    IsLocalDiffeomorphAt I 𝓘(ℝ, (mvfderiv I e x).range) n
      (fun z ↦ (mvfderiv I e x).range.orthogonalProjectionOnto (e z - e x)) x := by
  have hn0 : n ≠ 0 := by rintro rfl; exact absurd hn (by simp)
  have hx' : Injective (mvfderiv I e x) := fun _ _ h ↦ hx h
  set V := (mvfderiv I e x).range
  have hf : ContMDiff I 𝓘(ℝ, V) n (fun z ↦ V.orthogonalProjectionOnto (e z - e x)) :=
    (V.orthogonalProjectionOnto.contDiff.comp (contDiff_id.sub contDiff_const)).contMDiff.comp he
  refine TauCeti.isLocalDiffeomorphAt_of_injective_mfderiv hf.contMDiffOn isOpen_univ
    (mem_univ x) BoundarylessManifold.isInteriorPoint hn ?_
    (LinearMap.finrank_range_of_inj hx').symm
  -- The differential at `x` is the projection onto `V` after that of `e`, injective since the
  -- projection fixes `V`.
  have hP := ((V.orthogonalProjectionOnto.hasFDerivAt (x := e x)).sub_const
    (V.orthogonalProjectionOnto (e x)))
  simp_rw [← map_sub] at hP
  have hmf : HasMFDerivAt I 𝓘(ℝ, V) (fun z ↦ V.orthogonalProjectionOnto (e z - e x)) x
      (V.orthogonalProjectionOnto ∘L mvfderiv I e x) :=
    hP.hasMFDerivAt.comp x (he.mdifferentiableAt hn0).hasMFDerivAt
  rw [hmf.mfderiv]
  have key : ∀ u, ((V.orthogonalProjectionOnto ∘L mvfderiv I e x) u : F) = mvfderiv I e x u :=
    fun u ↦ congrArg Subtype.val
      (V.orthogonalProjectionOnto_mem_subspace_eq_self ⟨_, LinearMap.mem_range_self _ u⟩)
  intro v w hvw
  exact hx' ((key v).symm.trans ((congrArg Subtype.val hvw).trans (key w)))

/-- A partial diffeomorphism around `x` given by the orthogonal projection of `e z - e x` onto the
range of the differential of `e` at `x`. -/
private theorem exists_partialDiffeomorph_orthogonalProjectionOnto_sub (hn : 1 ≤ n)
    (he : ContMDiff I 𝓘(ℝ, F) n e) (hx : Injective (mfderiv I 𝓘(ℝ, F) e x)) :
    ∃ Φ : PartialDiffeomorph I 𝓘(ℝ, (mvfderiv I e x).range) M (mvfderiv I e x).range n,
      x ∈ Φ.source ∧
        EqOn (fun z ↦ (mvfderiv I e x).range.orthogonalProjectionOnto (e z - e x)) Φ Φ.source := by
  -- `IsLocalDiffeomorphAt` is not exposed; the inverse of its chosen local inverse is the chart.
  set h := isLocalDiffeomorphAt_orthogonalProjectionOnto_sub hn he hx
  refine ⟨h.localInverse.symm, h.localInverse_mem_target, fun z hz ↦ ?_⟩
  have hz' : z ∈ h.localInverse.toPartialEquiv.target := hz
  have hs := h.localInverse.toPartialEquiv.map_target hz'
  calc _ = (fun z ↦ (mvfderiv I e x).range.orthogonalProjectionOnto (e z - e x))
        (h.localInverse (h.localInverse.toPartialEquiv.symm z)) := by
          rw [show h.localInverse (h.localInverse.toPartialEquiv.symm z) = z from
            h.localInverse.toPartialEquiv.right_inv hz']
    _ = _ := h.localInverse_right_inv hs

/-- The **tangent projection chart** of `e : M → F` at `x`: for a `C^n` map `e` (`1 ≤ n`) with
injective differential at `x`, a partial diffeomorphism from a neighbourhood of `x` onto an open
subset of the range `T` of the differential of `e` at `x`, given there by `z ↦ P (e z - e x)`,
where `P` is the orthogonal projection of `F` onto `T` (`tangentProjectionChart_apply`). It
exists by the inverse function theorem, since its differential at `x` is `P` composed with the
differential of `e`, an isomorphism onto `T`. -/
noncomputable def tangentProjectionChart (hn : 1 ≤ n) (he : ContMDiff I 𝓘(ℝ, F) n e) (x : M)
    (hx : Injective (mfderiv I 𝓘(ℝ, F) e x)) :
    PartialDiffeomorph I 𝓘(ℝ, (mvfderiv I e x).range) M (mvfderiv I e x).range n :=
  (exists_partialDiffeomorph_orthogonalProjectionOnto_sub hn he hx).choose

variable {hn : 1 ≤ n} {he : ContMDiff I 𝓘(ℝ, F) n e} {hx : Injective (mfderiv I 𝓘(ℝ, F) e x)}

/-- The source of the tangent projection chart at `x` contains `x`. -/
theorem mem_tangentProjectionChart_source : x ∈ (tangentProjectionChart hn he x hx).source :=
  (exists_partialDiffeomorph_orthogonalProjectionOnto_sub hn he hx).choose_spec.1

/-- On its source, the tangent projection chart at `x` is the orthogonal projection of
`e z - e x` onto the range of the differential of `e` at `x`. -/
theorem tangentProjectionChart_apply {z : M} (hz : z ∈ (tangentProjectionChart hn he x hx).source) :
    tangentProjectionChart hn he x hx z =
      (mvfderiv I e x).range.orthogonalProjectionOnto (e z - e x) :=
  ((exists_partialDiffeomorph_orthogonalProjectionOnto_sub hn he hx).choose_spec.2 hz).symm

/-- The tangent projection chart at `x` sends `x` to `0`. -/
@[simp]
theorem tangentProjectionChart_self : tangentProjectionChart hn he x hx x = 0 := by
  rw [tangentProjectionChart_apply mem_tangentProjectionChart_source, sub_self, map_zero]

end Pointwise

/-! ### Uniform charts on a compact manifold -/

section Coordinates

variable {g : E → F} {U : Set E}

/-- **Tangent projections in coordinates, with a parameter.** Let `g : E → F` be `C^∞` with
injective derivatives on an open set `U ∋ w₀`, and write `Q w'` for the orthogonal projection
onto the range of `fderiv ℝ g w'`. For some `S : F →L[ℝ] E`, the map
`(w', w) ↦ (w', S (Q w' (g w - g w')))` agrees with an open partial homeomorphism `Θ` whose
source contains `(w₀, w₀)` and lies in `U ×ˢ U`, whose inverse is smooth on its target, and on
whose source the derivative of the second component in `w` is injective. -/
private theorem exists_openPartialHomeomorph_tangentProjection (hU : IsOpen U)
    (hg : ContDiffOn ℝ ∞ g U) (hinj : ∀ w ∈ U, Injective (fderiv ℝ g w)) {w₀ : E}
    (hw₀ : w₀ ∈ U) :
    ∃ S : F →L[ℝ] E, ∃ Θ : OpenPartialHomeomorph (E × E) (E × E),
      (∀ p, Θ p = (p.1, S ((fderiv ℝ g p.1).range.starProjection (g p.2 - g p.1)))) ∧
      (w₀, w₀) ∈ Θ.source ∧ Θ.source ⊆ U ×ˢ U ∧ ContDiffOn ℝ ∞ Θ.symm Θ.target ∧
      ∀ q ∈ Θ.source,
        Injective (S ∘L (fderiv ℝ g q.1).range.starProjection ∘L fderiv ℝ g q.2) := by
  set Q : E → F →L[ℝ] F := fun w ↦ (fderiv ℝ g w).range.starProjection
  have hQ : ContDiffOn ℝ ∞ Q U := fun w hw ↦
    (ContDiffAt.starProjection_range ((hg.contDiffAt (hU.mem_nhds hw)).fderiv_right le_rfl)
      (hinj w hw)).contDiffWithinAt
  have hgd : ∀ w ∈ U, HasFDerivAt g (fderiv ℝ g w) w := fun w hw ↦
    ((hg.contDiffAt (hU.mem_nhds hw)).differentiableAt (by simp)).hasFDerivAt
  obtain ⟨S, hSD⟩ :=
    ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional_domain (hinj w₀ hw₀)
  have hQD : ∀ w a, Q w (fderiv ℝ g w a) = fderiv ℝ g w a := fun w a ↦
    Submodule.starProjection_eq_self_iff.2 (LinearMap.mem_range_self _ a)
  -- The map `G (w', w) = (w', Ψ (w', w))` and its derivatives.
  set Ψ : E × E → E := fun p ↦ S (Q p.1 (g p.2 - g p.1))
  set G : E × E → E × E := fun p ↦ (p.1, Ψ p)
  have hG : ContDiffOn ℝ ∞ G (U ×ˢ U) := by
    refine contDiffOn_fst.prodMk (S.contDiff.comp_contDiffOn ?_)
    exact (hQ.comp contDiffOn_fst fun p (hp : p ∈ U ×ˢ U) ↦ hp.1).clm_apply
      ((hg.comp contDiffOn_snd fun p (hp : p ∈ U ×ˢ U) ↦ hp.2).sub
        (hg.comp contDiffOn_fst fun p (hp : p ∈ U ×ˢ U) ↦ hp.1))
  have hGd : ∀ p ∈ U ×ˢ U, HasFDerivAt G (fderiv ℝ G p) p := fun p hp ↦
    ((hG.contDiffAt ((hU.prod hU).mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt
  -- In the second variable, `G` has derivative `inr ∘ S ∘ Q w' ∘ fderiv ℝ g w`.
  have hslice : ∀ p ∈ U ×ˢ U, fderiv ℝ G p ∘L ContinuousLinearMap.inr ℝ E E =
      ContinuousLinearMap.inr ℝ E E ∘L (S ∘L Q p.1 ∘L fderiv ℝ g p.2) := by
    intro p hp
    have hGp : HasFDerivAt G (fderiv ℝ G p) (p.1, p.2) := hGd p hp
    have h₁ := hGp.comp p.2 (hasFDerivAt_prodMk_right p.1 p.2)
    have h₂ : HasFDerivAt (fun w ↦ G (p.1, w))
        (ContinuousLinearMap.inr ℝ E E ∘L (S ∘L Q p.1 ∘L fderiv ℝ g p.2)) p.2 := by
      have := (hasFDerivAt_const p.1 p.2).prodMk
        (((S ∘L Q p.1).hasFDerivAt).comp p.2 ((hgd p.2 hp.2).sub_const (g p.1)))
      convert this using 1
      all_goals ext a <;> simp [G, Ψ]
    exact h₁.unique h₂
  -- In the first variable, `G` is the identity; so its derivative at `(w₀, w₀)` is injective.
  have hfst : ContinuousLinearMap.fst ℝ E E ∘L fderiv ℝ G (w₀, w₀) =
      ContinuousLinearMap.fst ℝ E E :=
    ((hasFDerivAt_fst (𝕜 := ℝ) (p := G (w₀, w₀))).comp (w₀, w₀)
      (hGd (w₀, w₀) ⟨hw₀, hw₀⟩)).unique hasFDerivAt_fst
  have hinj₀ : Injective (fderiv ℝ G (w₀, w₀)) := by
    refine (injective_iff_map_eq_zero _).2 fun ⟨a, b⟩ hab ↦ ?_
    have ha : a = 0 := by
      simpa using (congrArg (fun L ↦ L (a, b)) hfst).symm.trans (congrArg Prod.fst hab)
    subst ha
    have hb := congrArg (fun L ↦ L b) (hslice (w₀, w₀) ⟨hw₀, hw₀⟩)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply] at hb
    rw [hab, hQD, hSD] at hb
    simpa using (congrArg Prod.snd hb).symm
  let L : (E × E) ≃L[ℝ] (E × E) :=
    (LinearEquiv.ofInjectiveEndo (fderiv ℝ G (w₀, w₀) : E × E →ₗ[ℝ] E × E)
      hinj₀).toContinuousLinearEquiv
  obtain ⟨Θ, hΘ, hp₀Θ, hΘU, hΘsymm⟩ := TauCeti.ContDiffOn.exists_openPartialHomeomorph hG
    (hU.prod hU) ⟨hw₀, hw₀⟩ (by simp) (e := L) (ContinuousLinearMap.ext fun _ ↦ rfl)
  refine ⟨S, Θ, fun p ↦ congrFun hΘ p, hp₀Θ, hΘU, hΘsymm, fun q hq a b hab ↦ ?_⟩
  -- On the source of `Θ` the derivative of `G` is invertible, and so is its slice.
  have hq' := hΘU hq
  have hΘd : DifferentiableAt ℝ Θ q := hΘ ▸ (hGd q hq').differentiableAt
  have hΘsd : DifferentiableAt ℝ Θ.symm (Θ q) :=
    (hΘsymm.contDiffAt (Θ.open_target.mem_nhds (Θ.map_source hq))).differentiableAt (by simp)
  obtain ⟨Li, hLi⟩ := Θ.isInvertible_fderiv hq hΘd hΘsd
  rw [hΘ] at hLi
  have h₁ := congrArg (fun L ↦ L a) (hslice q hq')
  have h₂ := congrArg (fun L ↦ L b) (hslice q hq')
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply] at h₁ h₂
  have h : (Li : E × E →L[ℝ] E × E) (0, a) = (Li : E × E →L[ℝ] E × E) (0, b) := by
    rw [hLi, h₁, h₂]
    exact congrArg (Prod.mk 0) hab
  simpa using Li.injective h

/-- **Tangent projections in coordinates, uniformly.** In the setting of
`exists_openPartialHomeomorph_tangentProjection`, for `w'` near `w₀` the maps
`Ψ w' : w ↦ S (Q w' (g w - g w'))` are inverted on one ball around `w₀` by maps `h w'`, the image
of that ball under each contains one ball around `0`, and the derivatives of order at most `2` of
`g ∘ h w'` are bounded there uniformly in `w'`. -/
private theorem exists_uniform_inverse (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U)
    (hinj : ∀ w ∈ U, Injective (fderiv ℝ g w)) {w₀ : E} (hw₀ : w₀ ∈ U) :
    ∃ S : F →L[ℝ] E, ∃ ε > 0, ∃ η > 0, ∃ C : ℝ, ∃ h : E → E → E, η ≤ ε ∧ ball w₀ ε ⊆ U ∧
      ∀ w' ∈ ball w₀ η,
        (∀ w ∈ ball w₀ ε,
          Injective (S ∘L (fderiv ℝ g w').range.starProjection ∘L fderiv ℝ g w) ∧
          h w' (S ((fderiv ℝ g w').range.starProjection (g w - g w'))) = w ∧
          ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (g ∘ h w')
            (S ((fderiv ℝ g w').range.starProjection (g w - g w')))‖ ≤ C) ∧
        ∀ v ∈ ball (0 : E) η, ∃ w ∈ ball w₀ ε,
          S ((fderiv ℝ g w').range.starProjection (g w - g w')) = v := by
  obtain ⟨S, Θ, hΘG, hp₀Θ, hΘU, hΘsymm, hinjS⟩ :=
    exists_openPartialHomeomorph_tangentProjection hU hg hinj hw₀
  set Q : E → F →L[ℝ] F := fun w ↦ (fderiv ℝ g w).range.starProjection
  set p₀ : E × E := (w₀, w₀)
  -- A closed ball around `(w₀, w₀)` in the source of `Θ`.
  obtain ⟨ε, hε, hεΘ⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (Θ.open_source.mem_nhds hp₀Θ)
  have hball : ∀ w' ∈ ball w₀ ε, ∀ w ∈ ball w₀ ε, (w', w) ∈ ball p₀ ε := fun w' hw' w hw ↦
    ball_prod_same w₀ w₀ ε ▸ ⟨hw', hw⟩
  have hsrc : ∀ w' ∈ ball w₀ ε, ∀ w ∈ ball w₀ ε, (w', w) ∈ Θ.source := fun w' hw' w hw ↦
    hεΘ (ball_subset_closedBall (hball w' hw' w hw))
  have hεU : ball w₀ ε ⊆ U := fun w hw ↦ (hΘU (hsrc w hw w hw)).2
  -- `k = g ∘ snd ∘ Θ⁻¹` is smooth on the target, with bounded derivatives on a compact set.
  set k : E × E → F := fun q ↦ g (Θ.symm q).2
  have hk : ContDiffOn ℝ ∞ k Θ.target :=
    hg.comp (contDiff_snd.comp_contDiffOn hΘsymm) fun q hq ↦ (hΘU (Θ.map_target hq)).2
  have hKt : Θ '' closedBall p₀ ε ⊆ Θ.target :=
    image_subset_iff.2 fun q hq ↦ Θ.map_source (hεΘ hq)
  have hKc : IsCompact (Θ '' closedBall p₀ ε) :=
    (isCompact_closedBall p₀ ε).image_of_continuousOn (Θ.continuousOn.mono hεΘ)
  have hbd : ∀ j : ℕ, ∃ C, ∀ q ∈ Θ '' closedBall p₀ ε, ‖iteratedFDeriv ℝ j k q‖ ≤ C :=
    fun j ↦ hKc.exists_bound_of_continuousOn fun q hq ↦
      ((hk.contDiffAt (Θ.open_target.mem_nhds (hKt hq))).continuousAt_iteratedFDeriv
        (by exact_mod_cast le_top)).continuousWithinAt
  choose Cf hCf using hbd
  -- The image of the open ball contains a product of balls around `Θ (w₀, w₀) = (w₀, 0)`.
  have hopen : IsOpen (Θ '' ball p₀ ε) :=
    Θ.isOpen_image_of_subset_source isOpen_ball (ball_subset_closedBall.trans hεΘ)
  have hΘp₀ : Θ p₀ = (w₀, 0) := by simp [hΘG, p₀]
  obtain ⟨η, hη, hηsub⟩ := Metric.isOpen_iff.1 hopen _ ⟨p₀, mem_ball_self hε, hΘp₀⟩
  refine ⟨S, ε, hε, min η ε, lt_min hη hε, max (Cf 0) (max (Cf 1) (Cf 2)),
    fun w' v ↦ (Θ.symm (w', v)).2, min_le_right _ _, hεU, fun w' hw' ↦ ⟨fun w hw ↦ ?_, ?_⟩⟩
  · have hw'ε : w' ∈ ball w₀ ε := ball_subset_ball (min_le_right _ _) hw'
    have hq := hsrc w' hw'ε w hw
    have hΘq : Θ (w', w) = (w', S (Q w' (g w - g w'))) := hΘG _
    refine ⟨hinjS (w', w) hq, ?_, fun j hj ↦ ?_⟩
    · simpa [hΘq] using congrArg Prod.snd (Θ.left_inv hq)
    · have hmem : (w', S (Q w' (g w - g w'))) ∈ Θ '' closedBall p₀ ε :=
        ⟨(w', w), ball_subset_closedBall (hball w' hw'ε w hw), hΘq⟩
      have hkat : ContDiffAt ℝ ∞ k (w', S (Q w' (g w - g w'))) :=
        hk.contDiffAt (Θ.open_target.mem_nhds (hKt hmem))
      refine (hkat.norm_iteratedFDeriv_prod_right_le j (by exact_mod_cast le_top)).trans
        ((hCf j _ hmem).trans ?_)
      interval_cases j <;> simp
  · intro v hv
    have hmem : (w', v) ∈ ball (w₀, (0 : E)) η := by
      rw [← ball_prod_same]
      exact ⟨ball_subset_ball (min_le_left _ _) hw', ball_subset_ball (min_le_left _ _) hv⟩
    obtain ⟨q, hq, hqv⟩ := hηsub hmem
    rw [hΘG] at hqv
    obtain ⟨hq₁, hq₂⟩ := Prod.mk.inj hqv
    rw [← ball_prod_same] at hq
    exact ⟨q.2, hq.2, hq₁ ▸ hq₂⟩

end Coordinates

section Uniform

variable [IsManifold I ∞ M] [BoundarylessManifold I M]

/-- **The chart at a point near `x₀`.** Read in the extended chart at `x₀`, where `e` becomes `g`,
the coordinate data of `exists_uniform_inverse` at `w' = extChartAt I x₀ x` give a tangent
projection chart at `x` whose source is the preimage of the ball of radius `ε`, whose target
contains a ball of radius `η / (‖S‖ + 1)`, and whose inverse has derivatives bounded in terms of
`S` and `C`. -/
private theorem exists_partialDiffeomorph_of_uniformInverse (he : ContMDiff I 𝓘(ℝ, F) ∞ e)
    (hinj : ∀ x, Injective (mfderiv I 𝓘(ℝ, F) e x)) {x₀ x : M} {g : E → F}
    (hgdef : g = e ∘ (extChartAt I x₀).symm) {S : F →L[ℝ] E} {ε η C : ℝ} {h : E → E → E}
    (hη : 0 < η) (hεU : ball (extChartAt I x₀ x₀) ε ⊆ interior (extChartAt I x₀).target)
    (hx : x ∈ (extChartAt I x₀).source)
    (hxε : extChartAt I x₀ x ∈ ball (extChartAt I x₀ x₀) ε)
    (hmain : ∀ w ∈ ball (extChartAt I x₀ x₀) ε,
      Injective (S ∘L (fderiv ℝ g (extChartAt I x₀ x)).range.starProjection ∘L fderiv ℝ g w) ∧
      h (extChartAt I x₀ x) (S ((fderiv ℝ g (extChartAt I x₀ x)).range.starProjection
        (g w - g (extChartAt I x₀ x)))) = w ∧
      ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (g ∘ h (extChartAt I x₀ x))
        (S ((fderiv ℝ g (extChartAt I x₀ x)).range.starProjection
          (g w - g (extChartAt I x₀ x))))‖ ≤ C)
    (hsurj : ∀ v ∈ ball (0 : E) η, ∃ w ∈ ball (extChartAt I x₀ x₀) ε,
      S ((fderiv ℝ g (extChartAt I x₀ x)).range.starProjection
        (g w - g (extChartAt I x₀ x))) = v) :
    ∃ Φ : PartialDiffeomorph I 𝓘(ℝ, (mvfderiv I e x).range) M (mvfderiv I e x).range ∞,
      (∀ z ∈ Φ.source, Φ z = (mvfderiv I e x).range.orthogonalProjectionOnto (e z - e x)) ∧
      Φ.source = (extChartAt I x₀).source ∩ extChartAt I x₀ ⁻¹' ball (extChartAt I x₀ x₀) ε ∧
      ball 0 (η / (‖S‖ + 1)) ⊆ Φ.target ∧
      ∀ u ∈ Φ.target, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (e ∘ Φ.symm) u‖ ≤ (‖S‖ + 1) ^ 2 * max C 0 := by
  set c := extChartAt I x₀
  set w₀ := c x₀
  set w' := c x
  set s := c.source ∩ c ⁻¹' ball w₀ ε
  have hs : IsOpen s :=
    (continuousOn_extChartAt x₀).isOpen_inter_preimage (isOpen_extChartAt_source x₀) isOpen_ball
  have hg : ContDiffOn ℝ ∞ g (interior c.target) := hgdef ▸
    (contMDiffOn_iff_contDiffOn.mp (he.comp_contMDiffOn (contMDiffOn_extChartAt_symm x₀))).mono
      interior_subset
  have hgd : ∀ z ∈ s, DifferentiableAt ℝ g (c z) := fun z hz ↦
    (hg.contDiffAt (isOpen_interior.mem_nhds (hεU hz.2))).differentiableAt (by simp)
  have hgx : ∀ z ∈ c.source, g (c z) = e z := fun z hz ↦ by
    rw [hgdef, comp_apply, c.left_inv hz]
  -- In the chart, the differential of `e` at `z ∈ s` is `fderiv ℝ g (c z)` after that of `c`.
  have hD : ∀ z ∈ s, ∀ v, mvfderiv I e z v = fderiv ℝ g (c z) (mfderiv I 𝓘(ℝ, E) c z v) := by
    intro z hz v
    -- `mvfderiv I e z v` is `mfderiv I 𝓘(ℝ, F) e z v`, read in `F`.
    change mfderiv I 𝓘(ℝ, F) e z v = _
    rw [TauCeti.mfderiv_eq_fderiv_comp_mfderiv_extChartAt hz.1 (hgdef ▸ hgd z hz), hgdef]
    rfl
  -- The range `V` of the differential of `e` at `x`, and the orthogonal projection onto it.
  set V := (mvfderiv I e x).range
  set Q' := (fderiv ℝ g w').range.starProjection
  have hxs : x ∈ s := ⟨hx, hxε⟩
  have hV : V = (fderiv ℝ g w').range := by
    obtain ⟨Lc, hLc⟩ := isInvertible_mfderiv_extChartAt hx
    ext u
    simp only [V, LinearMap.mem_range, ContinuousLinearMap.coe_coe, hD x hxs]
    refine ⟨fun ⟨v, hv⟩ ↦ ⟨_, hv⟩, fun ⟨a, ha⟩ ↦ ⟨Lc.symm a, ?_⟩⟩
    rw [← ha, ← hLc]
    exact congrArg _ (Lc.apply_symm_apply a)
  -- The subspaces agree by `hV`; the projection instances are propositions.
  have hVQ : V.starProjection = Q' := by
    congr 1
  have hPV : ∀ y, (V.orthogonalProjectionOnto y : F) = Q' y := fun y ↦ by
    rw [← V.starProjection_apply, hVQ]
  have hQD : ∀ a, Q' (fderiv ℝ g w' a) = fderiv ℝ g w' a := fun a ↦
    Submodule.starProjection_eq_self_iff.2 (LinearMap.mem_range_self _ a)
  -- `S` restricts to an isomorphism `T` from `V` onto `E`.
  have hSinj : Injective (S ∘L V.subtypeL) := by
    rintro ⟨u₁, hu₁⟩ ⟨u₂, hu₂⟩ h12
    rw [hV] at hu₁ hu₂
    obtain ⟨a₁, rfl⟩ := hu₁
    obtain ⟨a₂, rfl⟩ := hu₂
    have h := (hmain w' hxε).1 (a₁ := a₁) (a₂ := a₂) (by simpa [hQD] using h12)
    subst h
    rfl
  have hdim : Module.finrank ℝ V = Module.finrank ℝ E :=
    LinearMap.finrank_range_of_inj fun _ _ h ↦ hinj x h
  let T : V ≃L[ℝ] E :=
    (LinearMap.linearEquivOfInjective (S ∘L V.subtypeL : V →ₗ[ℝ] E) hSinj hdim)
      |>.toContinuousLinearEquiv
  have hT : ∀ u : V, T u = S u := fun u ↦ rfl
  have hTn : ∀ u : V, ‖T u‖ ≤ (‖S‖ + 1) * ‖u‖ := fun u ↦ by
    rw [hT]
    calc ‖S u‖ ≤ ‖S‖ * ‖u‖ := S.le_opNorm _
      _ ≤ (‖S‖ + 1) * ‖u‖ := by gcongr; linarith
  -- The chart `φ`, read through `T`, is the map `Ψ w'` of the coordinate data.
  set φ : M → V := fun z ↦ V.orthogonalProjectionOnto (e z - e x)
  have hkey : ∀ z ∈ c.source, T (φ z) = S (Q' (g (c z) - g w')) := fun z hz ↦ by
    rw [hT, hgx z hz, hgx x hx]
    exact congrArg S (hPV _)
  have hinjOn : InjOn φ s := fun z₁ hz₁ z₂ hz₂ h12 ↦ by
    have h' := congrArg T h12
    rw [hkey z₁ hz₁.1, hkey z₂ hz₂.1] at h'
    have h'' := congrArg (h w') h'
    rw [(hmain _ hz₁.2).2.1, (hmain _ hz₂.2).2.1] at h''
    exact c.injOn hz₁.1 hz₂.1 h''
  have hφ : ContMDiff I 𝓘(ℝ, V) ∞ φ :=
    (V.orthogonalProjectionOnto.contDiff.comp (contDiff_id.sub contDiff_const)).contMDiff.comp he
  have hloc : IsLocalDiffeomorphOn I 𝓘(ℝ, V) ∞ φ s := by
    rw [isLocalDiffeomorphOn_iff]
    rintro ⟨z, hz⟩
    refine TauCeti.isLocalDiffeomorphAt_of_injective_mfderiv hφ.contMDiffOn isOpen_univ
      (mem_univ z) BoundarylessManifold.isInteriorPoint (by simp) ?_ hdim.symm
    -- The differential of `φ` at `z` is the projection onto `V` after that of `e`.
    have hP := ((V.orthogonalProjectionOnto.hasFDerivAt (x := e z)).sub_const
      (V.orthogonalProjectionOnto (e x)))
    simp_rw [← map_sub] at hP
    have hmf : HasMFDerivAt I 𝓘(ℝ, V) φ z (V.orthogonalProjectionOnto ∘L mvfderiv I e z) :=
      hP.hasMFDerivAt.comp z (he.mdifferentiableAt (by simp)).hasMFDerivAt
    rw [hmf.mfderiv]
    obtain ⟨Lc, hLc⟩ := isInvertible_mfderiv_extChartAt hz.1
    intro a b hab
    have hPa : ∀ a', ((V.orthogonalProjectionOnto ∘L mvfderiv I e z) a' : F) =
        Q' (fderiv ℝ g (c z) (mfderiv I 𝓘(ℝ, E) c z a')) := fun a' ↦ by
      rw [← hPV, ← hD z hz]
      rfl
    have h' : S (Q' (fderiv ℝ g (c z) (mfderiv I 𝓘(ℝ, E) c z a))) =
        S (Q' (fderiv ℝ g (c z) (mfderiv I 𝓘(ℝ, E) c z b))) := by
      rw [← hPa, ← hPa]
      exact congrArg (fun y : V ↦ S y) hab
    have h'' := (hmain (c z) hz.2).1 (a₁ := mfderiv I 𝓘(ℝ, E) c z a)
      (a₂ := mfderiv I 𝓘(ℝ, E) c z b) h'
    rw [← hLc] at h''
    exact Lc.injective h''
  -- The chart is `φ` on `s`, as a partial diffeomorphism onto its image.
  have : Nonempty M := ⟨x⟩
  set Φ := hloc.partialDiffeomorphOfInjOn hs hinjOn
  have hΦ : ∀ z, Φ z = φ z := fun z ↦
    congrFun (IsLocalDiffeomorphOn.coe_partialDiffeomorphOfInjOn hloc hs hinjOn) z
  have hΦt : Φ.target = φ '' s :=
    IsLocalDiffeomorphOn.partialDiffeomorphOfInjOn_target hloc hs hinjOn
  have hΦsymm : ∀ y, Φ.symm y = invFunOn φ s y :=
    IsLocalDiffeomorphOn.partialDiffeomorphOfInjOn_symm_apply hloc hs hinjOn
  refine ⟨Φ, fun z _ ↦ hΦ z, IsLocalDiffeomorphOn.partialDiffeomorphOfInjOn_source hloc hs hinjOn,
    fun u hu ↦ hΦt ▸ ?_, hΦt ▸ ?_⟩
  · -- The target contains a ball around `0`: its points come from `hsurj`.
    have hTu : T u ∈ ball (0 : E) η := by
      rw [mem_ball_zero_iff]
      calc ‖T u‖ ≤ (‖S‖ + 1) * ‖u‖ := hTn u
        _ < (‖S‖ + 1) * (η / (‖S‖ + 1)) := by gcongr; exact mem_ball_zero_iff.1 hu
        _ = η := by field_simp
    obtain ⟨w, hw, hwu⟩ := hsurj (T u) hTu
    have hwt : w ∈ c.target := interior_subset (hεU hw)
    refine ⟨c.symm w, ⟨c.map_target hwt, ?_⟩, T.injective ?_⟩
    · rw [mem_preimage, c.right_inv hwt]
      exact hw
    · rw [hkey _ (c.map_target hwt), c.right_inv hwt, hwu]
  · -- On the target, `e ∘ Φ⁻¹ = (g ∘ h w') ∘ T`, whose derivatives `hmain` bounds.
    rintro _ ⟨z₀, hz₀, rfl⟩ j hj
    have heq : EqOn (e ∘ Φ.symm) ((g ∘ h w') ∘ T) (φ '' s) := by
      rintro _ ⟨z, hz, rfl⟩
      simp only [comp_apply]
      rw [hkey z hz.1, (hmain _ hz.2).2.1, hgx z hz.1, hΦsymm]
      exact congrArg e (hinjOn.leftInvOn_invFunOn hz)
    have hmem : φ z₀ ∈ φ '' s := ⟨z₀, hz₀, rfl⟩
    rw [((heq.eventuallyEq_of_mem ((hΦt ▸ Φ.open_target).mem_nhds hmem)).iteratedFDeriv ℝ
      j).eq_of_nhds]
    refine (T.norm_iteratedFDeriv_comp_right_le _ _ j).trans ?_
    rw [hkey z₀ hz₀.1]
    have hTn' : ‖(T : V →L[ℝ] E)‖ ≤ ‖S‖ + 1 :=
      ContinuousLinearMap.opNorm_le_bound _ (by positivity) hTn
    exact mul_le_mul ((pow_le_pow_left₀ (norm_nonneg _) hTn' j).trans
      (pow_le_pow_right₀ (by linarith [norm_nonneg S]) hj))
      (((hmain _ hz₀.2).2.2 j hj).trans (le_max_left _ _)) (norm_nonneg _) (by positivity)

/-- **Tangent projection charts near a point.** Near each point `x₀`, the charts of
`exists_uniform_tangentProjectionChart` exist with constants uniform in `x`. -/
private theorem exists_uniform_tangentProjectionChart_nhds [CompactSpace M]
    (he : ContMDiff I 𝓘(ℝ, F) ∞ e) (hinj : ∀ x, Injective (mfderiv I 𝓘(ℝ, F) e x))
    (he' : Injective e) (x₀ : M) :
    ∃ W ∈ 𝓝 x₀, ∃ r > 0, ∃ C : ℝ, ∀ x ∈ W,
      ∃ Φ : PartialDiffeomorph I 𝓘(ℝ, (mvfderiv I e x).range) M (mvfderiv I e x).range ∞,
        (∀ z ∈ Φ.source, Φ z = (mvfderiv I e x).range.orthogonalProjectionOnto (e z - e x)) ∧
        {z | dist (e z) (e x) < r} ⊆ Φ.source ∧ ball 0 r ⊆ Φ.target ∧
        ∀ u ∈ Φ.target, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (e ∘ Φ.symm) u‖ ≤ C := by
  -- Work in the extended chart `c` at `x₀`, where `e` reads as `g`.
  set c := extChartAt I x₀
  set g : E → F := e ∘ c.symm with hgdef
  have hw₀ : c x₀ ∈ interior c.target :=
    ModelWithCorners.isInteriorPoint_iff.mp (BoundarylessManifold.isInteriorPoint (x := x₀))
  have hg : ContDiffOn ℝ ∞ g (interior c.target) :=
    (contMDiffOn_iff_contDiffOn.mp (he.comp_contMDiffOn (contMDiffOn_extChartAt_symm x₀))).mono
      interior_subset
  have hinjg : ∀ w ∈ interior c.target, Injective (fderiv ℝ g w) := fun w hw ↦ by
    have hw' := interior_subset hw
    have h := TauCeti.fderiv_comp_extChartAt_symm_injective (c.map_target hw')
      (by rw [c.right_inv hw']
          exact (hg.contDiffAt (isOpen_interior.mem_nhds hw)).differentiableAt (by simp))
      (hinj _)
    rwa [c.right_inv hw'] at h
  obtain ⟨S, ε, hε, η, hη, C, h, hηε, hεU, hmain⟩ :=
    exists_uniform_inverse isOpen_interior hg hinjg hw₀
  have hcont : ContinuousOn c c.source := continuousOn_extChartAt x₀
  have hsrc : IsOpen c.source := isOpen_extChartAt_source x₀
  set s := c.source ∩ c ⁻¹' ball (c x₀) ε
  have hs : IsOpen s := hcont.isOpen_inter_preimage hsrc isOpen_ball
  have hx₀s : x₀ ∈ s := ⟨mem_extChartAt_source x₀, mem_ball_self hε⟩
  -- Points whose images are close to that of a point near `x₀` lie in `s`.
  obtain ⟨W, hW, r, hr, hWr⟩ :
      ∃ W ∈ 𝓝 x₀, ∃ r > 0, ∀ x ∈ W, ∀ z, dist (e z) (e x) < r → z ∈ s := by
    have hK : IsCompact (e '' sᶜ) := hs.isClosed_compl.isCompact.image he.continuous
    have hnot : e x₀ ∉ e '' sᶜ := fun ⟨z, hz, hze⟩ ↦ hz (he' hze ▸ hx₀s)
    obtain ⟨δ, hδ, hδK⟩ := Metric.isOpen_iff.1 hK.isClosed.isOpen_compl _ hnot
    refine ⟨e ⁻¹' ball (e x₀) (δ / 2), he.continuous.continuousAt.preimage_mem_nhds
      (ball_mem_nhds _ (half_pos hδ)), δ / 2, half_pos hδ, fun x hx z hz ↦ ?_⟩
    by_contra hzs
    refine hδK ?_ ⟨z, hzs, rfl⟩
    rw [mem_preimage, mem_ball] at hx
    rw [mem_ball]
    linarith [dist_triangle (e z) (e x) (e x₀)]
  have hρ : 0 < η / (‖S‖ + 1) := div_pos hη (by positivity)
  refine ⟨W ∩ (c.source ∩ c ⁻¹' ball (c x₀) η),
    inter_mem hW ((hcont.isOpen_inter_preimage hsrc isOpen_ball).mem_nhds
      ⟨mem_extChartAt_source x₀, mem_ball_self hη⟩),
    min r (η / (‖S‖ + 1)), lt_min hr hρ, (‖S‖ + 1) ^ 2 * max C 0, fun x ⟨hxW, hxc, hxη⟩ ↦ ?_⟩
  obtain ⟨hmain', hsurj⟩ := hmain (c x) hxη
  obtain ⟨Φ, h₁, h₂, h₃, h₄⟩ := exists_partialDiffeomorph_of_uniformInverse he hinj hgdef hη
    hεU hxc (ball_subset_ball hηε hxη) hmain' hsurj
  exact ⟨Φ, h₁, fun z hz ↦ h₂ ▸ hWr x hxW z (lt_of_lt_of_le hz (min_le_left _ _)),
    (ball_subset_ball (min_le_right _ _)).trans h₃, h₄⟩

/-- **Uniform tangent projection charts.** Let `e : M → F` be a smooth injective map with injective
differentials from a compact boundaryless manifold into a real inner product space. There are
`r > 0` and `C` such that, for every `x : M`, some partial diffeomorphism `Φ` from `M` onto an open
subset of the range `T` of the differential of `e` at `x`

* is given on its source by `z ↦ P (e z - e x)`, for `P` the orthogonal projection onto `T`, as
  `tangentProjectionChart` is;
* has a source containing every `z` with `‖e z - e x‖ < r`, and a target containing the ball of
  radius `r` around `0`;
* has an inverse whose composite with `e` has iterated derivatives of order at most `2` bounded
  by `C` on the target. -/
theorem exists_uniform_tangentProjectionChart [CompactSpace M]
    (he : ContMDiff I 𝓘(ℝ, F) ∞ e) (hinj : ∀ x, Injective (mfderiv I 𝓘(ℝ, F) e x))
    (he' : Injective e) :
    ∃ r > 0, ∃ C : ℝ, ∀ x : M,
      ∃ Φ : PartialDiffeomorph I 𝓘(ℝ, (mvfderiv I e x).range) M (mvfderiv I e x).range ∞,
        (∀ z ∈ Φ.source, Φ z = (mvfderiv I e x).range.orthogonalProjectionOnto (e z - e x)) ∧
        {z | dist (e z) (e x) < r} ⊆ Φ.source ∧ ball 0 r ⊆ Φ.target ∧
        ∀ u ∈ Φ.target, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (e ∘ Φ.symm) u‖ ≤ C := by
  rcases isEmpty_or_nonempty M with hM | ⟨⟨x₀⟩⟩
  · exact ⟨1, one_pos, 0, fun x ↦ isEmptyElim x⟩
  choose W hW r hr C hC using exists_uniform_tangentProjectionChart_nhds he hinj he'
  obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover W fun x _ ↦ hW x
  have htne : t.Nonempty := by
    obtain ⟨i, hi, -⟩ := mem_iUnion₂.1 (ht (mem_univ x₀))
    exact ⟨i, hi⟩
  refine ⟨t.inf' htne r, (Finset.lt_inf'_iff htne).2 fun i _ ↦ hr i, t.sup' htne C, fun x ↦ ?_⟩
  obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.1 (ht (mem_univ x))
  obtain ⟨Φ, h₁, h₂, h₃, h₄⟩ := hC i x hxi
  have hri : t.inf' htne r ≤ r i := Finset.inf'_le _ hi
  exact ⟨Φ, h₁, fun z hz ↦ h₂ (lt_of_lt_of_le hz hri), (ball_subset_ball hri).trans h₃,
    fun u hu j hj ↦ (h₄ u hu j hj).trans (Finset.le_sup' C hi)⟩

end Uniform

end SymplecticGeometry

end
