/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.AsymptoticallyHolomorphic.RescaledChart
import TauCeti.Analysis.Normed.Module.CoveringNumber

/-!
# Separated sets for the rescaled distance

The estimates of Donaldson's construction sum Gaussian bounds `exp (-c d_k(x, y) ^ 2)` over a set
`S` of centres whose points are pairwise at rescaled distance `d_k = √(2π k) · d_{g_J}` at least
some `r₀ > 0`. Such sums are bounded uniformly in `k` once the number of points of `S` in a
`d_k`-ball of radius `r` grows at most polynomially in `r`, uniformly in `k`. This file proves
the local half of that count: inside one rescaled unitary chart, where `d_k` is comparable with
the norm of `StdSpace ι` (`RescaledUnitaryCharts.rescaledEDist_symm_mem_Icc` and
`RescaledUnitaryCharts.rescaledEDist_symm_symm_le`), the points of `S` in a `d_k`-ball of radius
`r` are sent by the chart to a separated set in a ball of radius `√2 * r`, whose size the
volume bound `TauCeti.card_le_of_le_dist_of_subset_closedBall` controls.

## Main results

* `SymplecticGeometry.RescaledUnitaryCharts.card_filter_rescaledEDist_le`: if the distinct points
  of `S` are at `d_k` at least `r₀ > 0`, then for every `y` and every `0 ≤ r` with
  `r < ρ₁ * √k / √2`, `ρ₁` a comparison radius for `D.chart k y`, at most
  `(1 + 2 √3 r / r₀) ^ dim` points of `S` are at `d_k` at most `r` from `y`.
* `SymplecticGeometry.RescaledUnitaryCharts.card_filter_rescaledDist_le`: the same for the real
  rescaled distance, on a preconnected manifold.

## References

* [S. K. Donaldson, *Symplectic submanifolds and almost-complex geometry*][Donaldson1996].
* [D. Auroux, *A remark about Donaldson's construction of symplectic submanifolds*][Auroux2002].
-/

public section

open scoped Manifold ContDiff
open Bundle Metric Module TauCeti

namespace SymplecticGeometry

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {ι : Type*} [Fintype ι]
  {P : M → Type*} [TopologicalSpace (TotalSpace Circle P)] [∀ x, TopologicalSpace (P x)]
  [FiberBundle Circle P] [ContMDiffFiberBundle ∞ Circle P I (𝓡 1)]

namespace RescaledUnitaryCharts

variable {σ : SmoothTwoForm I M} {J : SmoothAlmostComplexStructure I M}
  {α : SmoothForm (I.prod (𝓡 1)) (ManifoldTotalSpace Circle P) ℝ 1} {k₀ : ℕ} {ρ₀ : ℝ}
  (D : RescaledUnitaryCharts P σ J α ι k₀ ρ₀)
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- **Points of a separated set in a small `d_k`-ball.** Let `M` be Hausdorff, with a Riemannian
metric whose inner product is `⟪u, w⟫ = σ(u, J w)`, let `k ≥ k₀`, let `y` be a point, and let
`ρ₁ ≤ ρ₀` be a comparison radius for `D.chart k y` (`IsComparisonRadius`). Let `S` be a finite
set whose distinct points are at rescaled distance `d_k = √(2π k) · d_{g_J}` at least `r₀ > 0`.
Then for `0 ≤ r < ρ₁ * √k / √2`, at most `(1 + 2 √3 r / r₀) ^ dim` points of `S` are at `d_k`
at most `r` from `y`, where `dim` is the real dimension of `StdSpace ι`. -/
theorem card_filter_rescaledEDist_le [T2Space M]
    (hg : ∀ (x : M) (u w : TangentSpace I x), inner ℝ u w = σ.eval₂ x u (J x w))
    {ρ₁ : ℝ} (hρ₁₀ : ρ₁ ≤ ρ₀)
    {k : ℕ} (hk : k₀ ≤ k) (y : M) (hcmp : D.IsComparisonRadius k y ρ₁)
    {r₀ r : ℝ} (hr₀ : 0 < r₀) (hr : 0 ≤ r) (hrρ : r < (√2)⁻¹ * (ρ₁ * √k)) {S : Finset M}
    (hS : ∀ x ∈ S, ∀ x' ∈ S, x ≠ x' → ENNReal.ofReal r₀ ≤ rescaledEDist I k x x') :
    ((S.filter fun x ↦ rescaledEDist I k x y ≤ ENNReal.ofReal r).card : ℝ) ≤
      (1 + 2 * √3 * r / r₀) ^ finrank ℝ (StdSpace ι) := by
  set φ := D.chart k y with hφ
  set T := S.filter fun x ↦ rescaledEDist I k x y ≤ ENNReal.ofReal r
  have hmem (x : M) (hx : x ∈ T) : x ∈ φ.source ∧ ‖φ x‖ ≤ √2 * r :=
    D.mem_source_and_norm_le_of_rescaledEDist_le hg hρ₁₀ hk y hcmp hr hrρ
      (Finset.mem_filter.1 hx).2
  have hball (x : M) (hx : x ∈ T) : φ x ∈ ball (0 : StdSpace ι) (ρ₁ * √k) :=
    mem_ball_zero_iff.2 ((hmem x hx).2.trans_lt (by
      rwa [← lt_inv_mul_iff₀ (by positivity : (0 : ℝ) < √2)]))
  have hinj : Set.InjOn φ T := fun x hx x' hx' h ↦ by
    rw [← φ.left_inv (hmem x hx).1, h, φ.left_inv (hmem x' hx').1]
  -- The images are separated at norm distance `r₀ / √(3 / 2)`, by the two-point upper bound.
  have hδ : 0 < r₀ / √(3 / 2) := by positivity
  have hsep : ∀ a ∈ T.image φ, ∀ b ∈ T.image φ, a ≠ b → r₀ / √(3 / 2) ≤ dist a b := by
    simp only [Finset.mem_image]
    rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩ hne
    have h := D.rescaledEDist_symm_symm_le hg hρ₁₀ hk y hcmp (hball x hx) (hball x' hx')
    rw [← hφ, PartialDiffeomorph.symm_toPartialEquiv, φ.left_inv (hmem x hx).1,
      φ.left_inv (hmem x' hx').1] at h
    have h := (hS x (Finset.mem_filter.1 hx).1 x' (Finset.mem_filter.1 hx').1
      fun h ↦ hne (h ▸ rfl)).trans h
    rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
    rw [dist_eq_norm, div_le_iff₀ (by positivity), mul_comm]
    exact h
  have hsub : (T.image φ : Set (StdSpace ι)) ⊆ closedBall 0 (√2 * r) := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 ha
    exact mem_closedBall_zero_iff.2 (hmem x hx).2
  have h := card_le_of_le_dist_of_subset_closedBall (x := 0) (by positivity) hδ hsep hsub
  rw [Finset.card_image_of_injOn hinj] at h
  convert h using 3
  have h32 : √2 * √(3 / 2) = √3 := by
    rw [← Real.sqrt_mul zero_le_two]
    norm_num
  rw [div_div_eq_mul_div, ← h32]
  ring

/-- **Points of a separated set in a small `d_k`-ball, for the real distance.** The statement of
`card_filter_rescaledEDist_le` for the real rescaled distance `rescaledDist`, on a preconnected
manifold: if the distinct points of `S` are at `rescaledDist I k` at least `r₀ > 0`, then for
`0 ≤ r < ρ₁ * √k / √2` at most `(1 + 2 √3 r / r₀) ^ dim` points of `S` are at `rescaledDist I k`
at most `r` from `y`. -/
theorem card_filter_rescaledDist_le [T2Space M] [PreconnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (hg : ∀ (x : M) (u w : TangentSpace I x), inner ℝ u w = σ.eval₂ x u (J x w))
    {ρ₁ : ℝ} (hρ₁₀ : ρ₁ ≤ ρ₀)
    {k : ℕ} (hk : k₀ ≤ k) (y : M) (hcmp : D.IsComparisonRadius k y ρ₁)
    {r₀ r : ℝ} (hr₀ : 0 < r₀) (hr : 0 ≤ r) (hrρ : r < (√2)⁻¹ * (ρ₁ * √k)) {S : Finset M}
    (hS : ∀ x ∈ S, ∀ x' ∈ S, x ≠ x' → r₀ ≤ rescaledDist I k x x') :
    ((S.filter fun x ↦ rescaledDist I k x y ≤ r).card : ℝ) ≤
      (1 + 2 * √3 * r / r₀) ^ finrank ℝ (StdSpace ι) := by
  have h := D.card_filter_rescaledEDist_le hg hρ₁₀ hk y hcmp hr₀ hr hrρ (S := S)
    fun x hx x' hx' hne ↦ by
      rw [← ofReal_rescaledDist]
      exact ENNReal.ofReal_le_ofReal (hS x hx x' hx' hne)
  convert h using 4 with x
  rw [← ofReal_rescaledDist, ENNReal.ofReal_le_ofReal_iff hr]

end RescaledUnitaryCharts

end SymplecticGeometry

end
