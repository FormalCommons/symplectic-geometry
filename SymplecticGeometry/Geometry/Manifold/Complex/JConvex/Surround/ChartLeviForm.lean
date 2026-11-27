/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.Complex.LeviForm
public import SymplecticGeometry.Geometry.Manifold.Complex.JConvex.Surround.Chart

import SymplecticGeometry.Analysis.Complex.LeviForm.CompSymm
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv

/-!
# Margins carried to the manifold by the chart along a disc

Let `Φ` be a chart along an attached disc as `SymplecticGeometry.exists_modelChart` gives it,
holomorphic to order `N` along the core (`SymplecticGeometry.IsHolomorphicToOrderAlongCore`):
near every point `p₀` of the core `ι₀ (ℝᵏ)` of the model space `ℂᵏ × ℂᵐ`, its reading `e` in the
chart of `M` at `Φ p₀` has `‖∂̄e p‖ ≤ C √(t p) ^ N` and `‖D(∂̄e) p‖ ≤ C √(t p) ^ (N - 1)`, where
`t p = (shape p).2`. This file shows that such a chart carries strict plurisubharmonicity with a
margin to `M`: on the handles `{t ≤ γ², s ≤ (1 + γ)²}` with `γ` small, a function `u` whose Levi
form is at least `c γ ^ N₀ max ‖D²u‖ ‖Du‖ ‖v‖²` has `u ∘ Φ⁻¹` strictly plurisubharmonic on `M`,
as soon as `N₀ + 2 ≤ N`.

The handles shrink to the compact disc `ι₀ (closedBall 0 1)` as `γ → 0`
(`SymplecticGeometry.iInter_setOf_shape_le_eq`), so for small `γ` they lie in finitely many
of the neighbourhoods where the bounds hold, which gives uniform constants there. The comparison
of Levi forms through a chart that is not holomorphic, `TauCeti.le_re_leviForm_comp_symm` of
`SymplecticGeometry/Analysis/Complex/LeviForm/CompSymm.lean`, then bounds the loss by a constant
times `γ ^ (N₀ + 1) max ‖D²u‖ ‖Du‖ ‖v‖²`, which is at most half the margin for small `γ`. Strict
plurisubharmonicity on `M` is read in the chart at `Φ p₀` by Tau Ceti's
`TauCeti.isManifoldStrictlyPlurisubharmonicAt_iff_of_mem_maximalAtlas`.

## Main results

* `SymplecticGeometry.isManifoldStrictlyPlurisubharmonicAt_comp_modelChart_symm`: the margin
  carried to `M` by the chart.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  the bound (8.1) and Theorem 4.2 (iv): a function that is `J`-convex with a margin stays
  `J`-convex for an almost complex structure close enough to the standard one.
-/

public section

open Filter Manifold Metric Set Topology TauCeti
open scoped ContDiff

namespace SymplecticGeometry

variable {k m : ℕ}

section Chart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

/-- The uniform constants of the proof of
`isManifoldStrictlyPlurisubharmonicAt_comp_modelChart_symm`: on a handle of some width
`γ₁ ∈ (0, 1)`, every point lies in the source of `Φ` followed by some chart of `M`, that composite
and its inverse are `C²` there, their first derivatives and the second derivative of the
composite are bounded by one `K`, and the bounds on `∂̄` hold with one constant `C ≥ 0`. -/
private theorem exists_uniform_bounds_modelChart {N : ℕ} [IsManifold 𝓘(ℝ, E) ∞ M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m))
      𝓘(ℝ, E) (EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) M ∞)
    (hΦ : IsHolomorphicToOrderAlongCore N Φ) :
    ∃ γ₁ ∈ Ioo (0 : ℝ) 1, ∃ K C : ℝ, 0 ≤ C ∧ ∀ p, (shape p).2 ≤ γ₁ ^ 2 →
      (shape p).1 ≤ (1 + γ₁) ^ 2 → ∃ y : M,
        p ∈ (Φ.toOpenPartialHomeomorph.trans (chartAt E y)).source ∧
        ContDiffAt ℝ 2 (Φ.toOpenPartialHomeomorph.trans (chartAt E y)) p ∧
        ContDiffAt ℝ 2 (Φ.toOpenPartialHomeomorph.trans (chartAt E y)).symm
          (Φ.toOpenPartialHomeomorph.trans (chartAt E y) p) ∧
        ‖fderiv ℝ (Φ.toOpenPartialHomeomorph.trans (chartAt E y)) p‖ ≤ K ∧
        ‖fderiv ℝ (Φ.toOpenPartialHomeomorph.trans (chartAt E y)).symm
          (Φ.toOpenPartialHomeomorph.trans (chartAt E y) p)‖ ≤ K ∧
        ‖fderiv ℝ (fderiv ℝ (Φ.toOpenPartialHomeomorph.trans (chartAt E y))) p‖ ≤ K ∧
        ‖conjWirtingerDeriv (Φ.toOpenPartialHomeomorph.trans (chartAt E y)) p‖ ≤
          C * √(shape p).2 ^ N ∧
        ‖fderiv ℝ (conjWirtingerDeriv (Φ.toOpenPartialHomeomorph.trans (chartAt E y))) p‖ ≤
          C * √(shape p).2 ^ (N - 1) := by
  set V := EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)
  set e : V → OpenPartialHomeomorph V E :=
    fun x ↦ Φ.toOpenPartialHomeomorph.trans (chartAt E (Φ x))
  -- The composites `e x` and their inverses are smooth, and `e x` is the reading of `Φ` at `x`.
  have hsm (x : V) : ContDiffOn ℝ ∞ (e x) (e x).source ∧
      ContDiffOn ℝ ∞ (e x).symm (e x).target := by
    have h := Φ.toOpenPartialHomeomorph.symm.contDiffOn_symm_trans_and_symm_of_contMDiffOn
      (ψ₂ := chartAt E (Φ x)) Φ.symm.contMDiffOn Φ.contMDiffOn contMDiffOn_chart
      contMDiffOn_chart_symm
    rwa [OpenPartialHomeomorph.symm_symm] at h
  have hw (x : V) : writtenInExtChartAt 𝓘(ℝ, V) 𝓘(ℝ, E) x Φ = e x := by
    simp [e]
  -- The neighbourhoods of the bounds, and closed balls inside them.
  choose! U hU hUs hUc C hC using (isHolomorphicToOrderAlongCore_def N Φ).1 hΦ
  have hball : ∀ x ∈ range (modelDisc k m), ∃ r > 0, closedBall x r ⊆ U x := fun x hx ↦
    nhds_basis_closedBall.mem_iff.1 (hU x hx)
  choose! r hr hrU using hball
  -- Finitely many balls cover the compact disc `ι₀ (closedBall 0 1)`.
  set K := modelDisc k m '' closedBall 0 1
  have hK : IsCompact K := (isCompact_closedBall 0 1).image (modelDisc k m).continuous
  have hKr : K ⊆ range (modelDisc k m) := image_subset_range _ _
  obtain ⟨t, htK, hKt⟩ := hK.elim_nhds_subcover (fun x ↦ ball x (r x))
    fun x hx ↦ ball_mem_nhds x (hr x (hKr hx))
  have hsub : ∀ x ∈ t, closedBall x (r x) ⊆ (e x).source := fun x hx q hq ↦ by
    have := hrU x (hKr (htK x hx)) hq
    rw [OpenPartialHomeomorph.trans_source, Φ.toOpenPartialHomeomorph_source,
      PartialDiffeomorph.toFun'_toOpenPartialHomeomorph]
    exact ⟨hUs x (hKr (htK x hx)) this, hUc x (hKr (htK x hx)) this⟩
  -- Bounds on the derivatives of the charts on the closed balls.
  have hbd : ∀ x ∈ t, ∃ B, ∀ q ∈ closedBall x (r x),
      ‖(fderiv ℝ (e x) q, fderiv ℝ (e x).symm (e x q), fderiv ℝ (fderiv ℝ (e x)) q)‖ ≤ B := by
    intro x hx
    have hs := (hsm x).1
    have h1 := hs.continuousOn_fderiv_of_isOpen (e x).open_source (by simp)
    have h2 := (hs.fderiv_of_isOpen (e x).open_source (m := 1)
      (by simp)).continuousOn_fderiv_of_isOpen (e x).open_source le_rfl
    have h3 := ((hsm x).2.continuousOn_fderiv_of_isOpen
      (e x).open_target (by simp)).comp (e x).continuousOn_toFun fun _ hq ↦ (e x).map_source hq
    exact (isCompact_closedBall x (r x)).exists_bound_of_continuousOn
      ((h1.prodMk (h3.prodMk h2)).mono (hsub x hx))
  choose! B hB using hbd
  -- The handles lie in the union of the balls for small `γ`.
  have : Nonempty (Ioo (0 : ℝ) 1) := ⟨⟨1 / 2, by norm_num, by norm_num⟩⟩
  obtain ⟨⟨γ₁, hγ₁⟩, hγ₁W⟩ := exists_subset_nhds_of_isCompact'
    (V := fun γ : Ioo (0 : ℝ) 1 ↦ {p : V | (shape p).2 ≤ (γ : ℝ) ^ 2 ∧
      (shape p).1 ≤ (1 + (γ : ℝ)) ^ 2})
    (fun a b ↦ ⟨⟨min a b, lt_min a.property.1 b.property.1,
        (min_le_left _ _).trans_lt a.property.2⟩,
      setOf_shape_le_subset_setOf_shape_le (le_min a.property.1.le b.property.1.le)
        (min_le_left _ _),
      setOf_shape_le_subset_setOf_shape_le (le_min a.property.1.le b.property.1.le)
        (min_le_right _ _)⟩)
    (fun _ ↦ isCompact_setOf_shape_le _ _) (fun _ ↦ (isCompact_setOf_shape_le _ _).isClosed)
    (U := ⋃ x ∈ t, ball x (r x))
    (mem_nhdsSet_iff_forall.2 fun p hp ↦ (isOpen_biUnion fun x _ ↦ isOpen_ball).mem_nhds
      (hKt (iInter_setOf_shape_le_eq.subset hp)))
  -- The constants are sums over the finitely many balls.
  have hle {f : V → ℝ} {x : V} (hx : x ∈ t) : f x ≤ ∑ x ∈ t, |f x| :=
    (le_abs_self _).trans (Finset.single_le_sum (f := fun x ↦ |f x|) (fun _ _ ↦ abs_nonneg _) hx)
  refine ⟨γ₁, hγ₁, ∑ x ∈ t, |B x|, ∑ x ∈ t, |C x|, Finset.sum_nonneg fun _ _ ↦ abs_nonneg _,
    fun p ht hs ↦ ?_⟩
  obtain ⟨x, hx, hpx⟩ := mem_iUnion₂.1 (hγ₁W ⟨ht, hs⟩)
  have hpx := ball_subset_closedBall hpx
  have hB' := hB x hx p hpx
  rw [Prod.norm_def, Prod.norm_def, max_le_iff, max_le_iff] at hB'
  have hCe := hC x (hKr (htK x hx)) p (hrU x (hKr (htK x hx)) hpx)
  rw [hw] at hCe
  have hpS := hsub x hx hpx
  exact ⟨Φ x, hpS,
    ((hsm x).1.contDiffAt ((e x).open_source.mem_nhds hpS)).of_le (by simp),
    ((hsm x).2.contDiffAt ((e x).open_target.mem_nhds ((e x).map_source hpS))).of_le (by simp),
    hB'.1.trans (hle hx), hB'.2.1.trans (hle hx),
    hB'.2.2.trans (hle hx), hCe.1.trans (by gcongr; exact hle hx),
    hCe.2.trans (by gcongr; exact hle hx)⟩

/-- **Margins carried to the manifold by the chart along a disc.** Let `Φ` be a smooth partial
diffeomorphism from the model space `ℂᵏ × ℂᵐ` to the complex manifold `M` that is holomorphic to
order `N` along the core (`IsHolomorphicToOrderAlongCore`), as
`SymplecticGeometry.exists_modelChart` gives it. Let `c > 0` and `N₀ + 2 ≤ N`. Then there is
`γ₀ ∈ (0, 1]` such that, for `0 < γ < γ₀`, the handle `{p | t p ≤ γ² ∧ s p ≤ (1 + γ)²}` lies in
the source of `Φ`, and for every `C²` function `u` on the model space that is strictly
plurisubharmonic at each point `p` of the handle, with
`c γ ^ N₀ max ‖D²u p‖ ‖Du p‖ ‖v‖² ≤ Re L(u)(p)(v, v)` for all `v`, the function `u ∘ Φ⁻¹` is
strictly plurisubharmonic at `Φ p` for every `p` in the handle. Here `(s, t) = shape p`. -/
theorem isManifoldStrictlyPlurisubharmonicAt_comp_modelChart_symm [IsManifold 𝓘(ℂ, E) 2 M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {N : ℕ}
    (Φ : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m))
      𝓘(ℝ, E) (EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) M ∞)
    (hΦ : IsHolomorphicToOrderAlongCore N Φ)
    {c : ℝ} (hc : 0 < c) {N₀ : ℕ} (hN : N₀ + 2 ≤ N) :
    ∃ γ₀ ∈ Ioc (0 : ℝ) 1, ∀ γ ∈ Ioo 0 γ₀,
      {p | (shape p).2 ≤ γ ^ 2 ∧ (shape p).1 ≤ (1 + γ) ^ 2} ⊆ Φ.source ∧
      ∀ u : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m) → ℝ, ContDiff ℝ 2 u →
        (∀ p, (shape p).2 ≤ γ ^ 2 → (shape p).1 ≤ (1 + γ) ^ 2 →
          IsStrictlyPlurisubharmonicAt u p ∧
          ∀ v, c * γ ^ N₀ * max ‖fderiv ℝ (fderiv ℝ u) p‖ ‖fderiv ℝ u p‖ * ‖v‖ ^ 2 ≤
            (leviForm u p v v).re) →
        ∀ p, (shape p).2 ≤ γ ^ 2 → (shape p).1 ≤ (1 + γ) ^ 2 →
          IsManifoldStrictlyPlurisubharmonicAt E (u ∘ Φ.symm) (Φ p) := by
  obtain ⟨γ₁, hγ₁, K, Cc, hCc, hcov⟩ := exists_uniform_bounds_modelChart Φ hΦ
  obtain ⟨C₀, hC₀⟩ := le_re_leviForm_comp_symm
    (V := EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) (W := E) K
  set C₀' := max C₀ 0
  have hden : 0 < 2 * (3 * C₀' * Cc + 1) := by positivity
  refine ⟨min γ₁ (c / (2 * (3 * C₀' * Cc + 1))), ⟨lt_min hγ₁.1 (div_pos hc hden),
    (min_le_left _ _).trans hγ₁.2.le⟩, fun γ hγ ↦ ?_⟩
  have hγγ₁ : γ ≤ γ₁ := hγ.2.le.trans (min_le_left _ _)
  have hγ1 : γ ≤ 1 := hγγ₁.trans hγ₁.2.le
  have hcov' (p) (ht : (shape p).2 ≤ γ ^ 2) (hs : (shape p).1 ≤ (1 + γ) ^ 2) :=
    hcov p (setOf_shape_le_subset_setOf_shape_le hγ.1.le hγγ₁ ⟨ht, hs⟩).1
      (setOf_shape_le_subset_setOf_shape_le hγ.1.le hγγ₁ ⟨ht, hs⟩).2
  have hmem {y : M} {p} (hp : p ∈ (Φ.toOpenPartialHomeomorph.trans (chartAt E y)).source) :
      p ∈ Φ.source ∧ Φ p ∈ (chartAt E y).source := by
    simpa only [OpenPartialHomeomorph.trans_source, Φ.toOpenPartialHomeomorph_source,
      PartialDiffeomorph.toFun'_toOpenPartialHomeomorph, mem_inter_iff, mem_preimage] using hp
  refine ⟨fun p hp ↦ ?_, fun u hu hmargin p ht hs ↦ ?_⟩
  · obtain ⟨y, hpS, -⟩ := hcov' p hp.1 hp.2
    exact (hmem hpS).1
  obtain ⟨y, hpS, hcd, hcds, hK₁, hK₂, hK₃, ha, hb⟩ := hcov' p ht hs
  set e := Φ.toOpenPartialHomeomorph.trans (chartAt E y)
  have hΦp : Φ p ∈ Φ.target := Φ.map_source (hmem hpS).1
  -- `u ∘ Φ⁻¹` is `C²` at `Φ p`, and its Levi form is read in the chart at `y`.
  have hu' : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 (u ∘ Φ.symm) (Φ p) :=
    hu.contMDiff.contMDiffAt.comp _
      ((Φ.symm.contMDiffOn.contMDiffAt (Φ.open_target.mem_nhds hΦp)).of_le (by simp))
  rw [isManifoldStrictlyPlurisubharmonicAt_iff_of_mem_maximalAtlas
    (IsManifold.chart_mem_maximalAtlas y) (x := Φ p) (hmem hpS).2 hu']
  have hsymm : (u ∘ Φ.symm) ∘ (chartAt E y).symm = u ∘ e.symm := by
    rw [OpenPartialHomeomorph.coe_trans_symm, Φ.coe_toOpenPartialHomeomorph_symm,
      Function.comp_assoc]
  rw [hsymm, ← PartialDiffeomorph.toFun'_toOpenPartialHomeomorph Φ,
    ← OpenPartialHomeomorph.trans_apply, isStrictlyPlurisubharmonicAt_iff]
  intro w hw
  -- Write `w = De_p v` with `v ≠ 0`.
  set v := fderiv ℝ e.symm (e p) w
  have hvw : fderiv ℝ e p v = w := e.fderiv_apply_fderiv_symm_apply_of_mem_source hpS
    (hcd.differentiableAt (by norm_num)) (hcds.differentiableAt (by norm_num)) w
  have hv : v ≠ 0 := fun h ↦ hw (by rw [← hvw, h, map_zero])
  obtain ⟨hpsh, hm⟩ := hmargin p ht hs
  have hcomp := hC₀ e p hpS hcd hcds hK₁ hK₂ hK₃ u hu.contDiffAt v
  rw [hvw] at hcomp
  -- The bounds on `∂̄` at `p`, in terms of `γ`.
  have hsq : √(shape p).2 ≤ γ := by
    rw [← Real.sqrt_sq hγ.1.le]
    exact Real.sqrt_le_sqrt ht
  have hpow (n : ℕ) (hn : N₀ + 1 ≤ n) : Cc * √(shape p).2 ^ n ≤ Cc * γ ^ (N₀ + 1) :=
    calc Cc * √(shape p).2 ^ n ≤ Cc * γ ^ n := by gcongr
      _ ≤ Cc * γ ^ (N₀ + 1) := mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hγ.1.le hγ1 hn) hCc
  replace ha := ha.trans (hpow N (by omega))
  replace hb := hb.trans (hpow (N - 1) (by omega))
  set a := ‖conjWirtingerDeriv e p‖
  set b := ‖fderiv ℝ (conjWirtingerDeriv e) p‖
  set d₂ := ‖fderiv ℝ (fderiv ℝ u) p‖
  set d₁ := ‖fderiv ℝ u p‖
  set D := max d₂ d₁
  have hL := isStrictlyPlurisubharmonicAt_iff.1 hpsh v hv
  have hmv := hm v
  have hg : 0 ≤ Cc * γ ^ (N₀ + 1) := mul_nonneg hCc (pow_nonneg hγ.1.le _)
  have hd₂ : 0 ≤ d₂ := norm_nonneg (fderiv ℝ (fderiv ℝ u) p)
  have hd₁ : 0 ≤ d₁ := norm_nonneg (fderiv ℝ u p)
  have hX : a * d₂ + (a + b) * d₁ ≤ 3 * Cc * γ ^ (N₀ + 1) * D := by
    nlinarith [mul_le_mul ha (le_max_left d₂ d₁) hd₂ hg,
      mul_le_mul (add_le_add ha hb) (le_max_right d₂ d₁) hd₁ (add_nonneg hg hg)]
  have hγc : 3 * C₀' * Cc * γ ≤ c / 2 := by
    have : γ ≤ c / (2 * (3 * C₀' * Cc + 1)) := hγ.2.le.trans (min_le_right _ _)
    rw [le_div_iff₀ hden] at this
    nlinarith [hγ.1, mul_nonneg (le_max_right C₀ 0) hCc]
  have hX0 : 0 ≤ a * d₂ + (a + b) * d₁ := by positivity
  have hbound : C₀ * (a * d₂ + (a + b) * d₁) ≤ (c / 2) * γ ^ N₀ * D :=
    calc C₀ * (a * d₂ + (a + b) * d₁) ≤ C₀' * (a * d₂ + (a + b) * d₁) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hX0
      _ ≤ C₀' * (3 * Cc * γ ^ (N₀ + 1) * D) := mul_le_mul_of_nonneg_left hX (le_max_right _ _)
      _ = (3 * C₀' * Cc * γ) * (γ ^ N₀ * D) := by ring
      _ ≤ (c / 2) * (γ ^ N₀ * D) :=
          mul_le_mul_of_nonneg_right hγc (mul_nonneg (pow_nonneg hγ.1.le _)
            (hd₁.trans (le_max_right d₂ d₁)))
      _ = (c / 2) * γ ^ N₀ * D := by ring
  have := mul_le_mul_of_nonneg_right hbound (sq_nonneg ‖v‖)
  linarith

end Chart

end SymplecticGeometry

end
