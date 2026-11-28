/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.AsymptoticallyHolomorphic.RescaledChart
import SymplecticGeometry.Combinatorics.SimpleGraph.GreedyColoring
import TauCeti.Analysis.Normed.Module.CoveringNumber

/-!
# Separated sets for the rescaled distance

The estimates of Donaldson's construction sum Gaussian bounds `exp (-c d_k(x, y) ^ 2)` over a set
`S` of centres whose points are pairwise at rescaled distance `d_k = √(2π k) · d_{g_J}` at least
some `r₀ > 0`. Such sums are bounded uniformly in `k` once the number of points of `S` in a
`d_k`-ball of radius `r` grows at most polynomially in `r`, uniformly in `k`. This file proves
that count, first locally: inside one rescaled unitary chart, where `d_k` is comparable with
the norm of `StdSpace ι` (`RescaledUnitaryCharts.rescaledEDist_symm_mem_Icc` and
`RescaledUnitaryCharts.rescaledEDist_symm_symm_le`), the points of `S` in a `d_k`-ball of radius
`r` are sent by the chart to a separated set in a ball of radius `√2 * r`, whose size the
volume bound `TauCeti.card_le_of_le_dist_of_subset_closedBall` controls.

It then makes the count global on a compact manifold. The images of small balls under the
charts for one fixed power `k₁` cover `M`, and finitely many of them suffice. Since
`√k₁ * d_k = √k * d_{k₁}` (`SymplecticGeometry.sqrt_mul_rescaledEDist`), each of them has
`d_k`-radius a small multiple of `√k` about its centre, so by the local count it holds
`O((1 + √k) ^ dim)` points of `S`. This bounds the size of `S`, and with it the number of points
of `S` in a `d_k`-ball of radius `r` once `r` is a fixed multiple of `√k`; smaller balls are
covered by the local count. Each count is proved for the extended distance `rescaledEDist`, and
then deduced for the real one `rescaledDist` on a preconnected manifold.

Finally it builds the net of centres. Since the size of a separated set is bounded for each `k`,
a separated set that cannot be enlarged exists; every point is then at `d_k` less than `r₀` from
one of its points, so lies in the image of a closed unit ball of the chart at that point
(`RescaledUnitaryCharts.exists_norm_lt_symm_eq_of_rescaledEDist_lt`), once `√2 * r₀ ≤ 1`. The
colouring is the greedy one of `Finset.exists_coloring_le_of_card_le_mul_pow`, fed by the count.

## Main results

* `SymplecticGeometry.RescaledUnitaryCharts.card_filter_rescaledEDist_le`: if the distinct points
  of `S` are at `d_k` at least `r₀ > 0`, then for every `y` and every `0 ≤ r` with
  `r < ρ₁ * √k / √2`, `ρ₁` a comparison radius for `D.chart k y`, at most
  `(1 + 2 √3 r / r₀) ^ dim` points of `S` are at `d_k` at most `r` from `y`.
* `SymplecticGeometry.RescaledUnitaryCharts.card_filter_rescaledDist_le`: the same for the real
  rescaled distance, on a preconnected manifold.
* `SymplecticGeometry.RescaledUnitaryCharts.exists_forall_card_le_of_le_rescaledEDist`: on a
  compact manifold, a `d_k`-separated set with separation `r₀` has at most `C * (1 + √k) ^ dim`
  points, with `C` independent of `k`; `exists_forall_card_le_of_le_rescaledDist` is the same
  for the real rescaled distance, on a compact preconnected manifold.
* `SymplecticGeometry.RescaledUnitaryCharts.exists_forall_card_filter_rescaledEDist_le`: on a
  compact manifold, at most `C * (1 + r) ^ dim` of its points lie in a `d_k`-ball of radius `r`,
  with `C` independent of `k`, of the ball and of `r`; `exists_forall_card_filter_rescaledDist_le`
  is the same for the real rescaled distance, on a compact preconnected manifold.
* `SymplecticGeometry.RescaledUnitaryCharts.exists_separated_chart_cover_coloring`: for all
  `k ≥ max k₀ 1`, a finite `r₀`-separated set of centres whose closed unit balls in the charts
  `D.chart k x` cover `M`, with the counting bound above and, for every `R ≥ 1`, a colouring by
  `O(R ^ dim)` colours of which each colour class is `R`-separated; `r₀` and the constant do not
  depend on `k` or `R`.

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

include D in
/-- **The size of a separated set, uniformly in `k`.** Let `M` be compact and Hausdorff, with a
Riemannian metric whose inner product is `⟪u, w⟫ = σ(u, J w)`, and let the rescaled unitary
charts have radius `ρ₀ > 0`. For every `r₀ > 0` there is a constant `C` such that for every
`k ≥ max k₀ 1`, every finite set `S` whose distinct points are at rescaled extended distance
`d_k = √(2π k) · d_{g_J}` at least `r₀` has at most `C * (1 + √k) ^ dim` points, where `dim` is
the real dimension of `StdSpace ι`. -/
theorem exists_forall_card_le_of_le_rescaledEDist [CompactSpace M] [T2Space M]
    (hg : ∀ (x : M) (u w : TangentSpace I x), inner ℝ u w = σ.eval₂ x u (J x w))
    (hρ₀ : 0 < ρ₀) {r₀ : ℝ} (hr₀ : 0 < r₀) :
    ∃ C, ∀ {k : ℕ}, max k₀ 1 ≤ k → ∀ S : Finset M,
      (∀ x ∈ S, ∀ x' ∈ S, x ≠ x' → ENNReal.ofReal r₀ ≤ rescaledEDist I k x x') →
        (S.card : ℝ) ≤ C * (1 + √k) ^ finrank ℝ (StdSpace ι) := by
  classical
  obtain ⟨ρ₁, hρ₁, hρ₁₀, hcmp⟩ := D.exists_forall_isComparisonRadius hρ₀
  set n := finrank ℝ (StdSpace ι)
  set k₁ := max k₀ 1
  have hk₁ : k₀ ≤ k₁ := le_max_left _ _
  have hk₁0 : 0 < √(k₁ : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast (le_max_right k₀ 1))
  -- A cover of `M`, independent of `k`, by images of small balls under the charts for `k₁`.
  obtain ⟨ε, rfl⟩ : ∃ ε, ρ₁ = 4 * ε := ⟨ρ₁ / 4, by ring⟩
  have hε : 0 < ε := by linarith
  have hεB : ball (0 : StdSpace ι) (ε * √k₁) ⊆ ball 0 (4 * ε * √k₁) :=
    ball_subset_ball (by gcongr; linarith)
  set U : M → Set M := fun x ↦ (D.chart k₁ x).symm '' ball 0 (ε * √k₁)
  have hU (x : M) : U x ∈ nhds x := by
    refine IsOpen.mem_nhds ?_ ⟨0, mem_ball_self (by positivity), D.chart_symm_zero hk₁ x⟩
    have h := (D.chart k₁ x).symm.toOpenPartialHomeomorph.isOpen_image_of_subset_source
      (isOpen_ball (x := (0 : StdSpace ι)) (ε := ε * √k₁)) <|
        hεB.trans ((ball_subset_ball (by gcongr)).trans (D.ball_subset_target hk₁ x))
    simpa [U] using h
  obtain ⟨t, ht⟩ := CompactSpace.elim_nhds_subcover U hU
  obtain ⟨a, ha, ha_def⟩ : ∃ a, 0 ≤ a ∧ a = 2 * √3 * (√(3 / 2) * ε) / r₀ :=
    ⟨_, by positivity, rfl⟩
  refine ⟨t.card * (1 + a) ^ n, fun {k} hk S hS ↦ ?_⟩
  have hk₀ : k₀ ≤ k := (le_max_left _ _).trans hk
  have hk0 : 0 < √(k : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast (le_max_right k₀ 1).trans hk)
  -- The points of `S` in `U x` are at `d_k` at most `√(3 / 2) * ε * √k` from `x`.
  have hcount (x : M) : ((S.filter (· ∈ U x)).card : ℝ) ≤ (1 + a) ^ n * (1 + √k) ^ n := by
    have hsub : S.filter (· ∈ U x) ⊆
        S.filter fun y ↦ rescaledEDist I k y x ≤ ENNReal.ofReal (√(3 / 2) * ε * √k) := by
      intro y hy
      rw [Finset.mem_filter] at hy ⊢
      refine ⟨hy.1, ?_⟩
      obtain ⟨z, hz, rfl⟩ := hy.2
      have h₁ := D.rescaledEDist_symm_le hg hρ₁₀ hk₁ x (hcmp hk₁ x) (hεB hz)
      have h := sqrt_mul_rescaledEDist (I := I) k k₁ x ((D.chart k₁ x).symm z)
      rw [rescaledEDist_comm, ← ENNReal.mul_le_mul_iff_right
        (ENNReal.ofReal_pos.2 hk₁0).ne' ENNReal.ofReal_ne_top, h,
        ← ENNReal.ofReal_mul hk₁0.le]
      calc ENNReal.ofReal √k * rescaledEDist I k₁ x ((D.chart k₁ x).symm z)
          ≤ ENNReal.ofReal √k * ENNReal.ofReal (√(3 / 2) * (ε * √k₁)) := by
            gcongr
            exact h₁.trans (ENNReal.ofReal_le_ofReal (by
              gcongr; exact (mem_ball_zero_iff.1 hz).le))
        _ = ENNReal.ofReal (√k₁ * (√(3 / 2) * ε * √k)) := by
            rw [← ENNReal.ofReal_mul hk0.le]
            ring_nf
    refine (Nat.cast_le.2 (Finset.card_le_card hsub)).trans ?_
    refine (D.card_filter_rescaledEDist_le hg hρ₁₀ hk₀ x (hcmp hk₀ x) hr₀ (by positivity) ?_
      hS).trans ?_
    · rw [lt_inv_mul_iff₀ (by positivity)]
      have h32 : √2 * √(3 / 2) < 2 := by
        rw [← Real.sqrt_mul zero_le_two, show (2 : ℝ) * (3 / 2) = 3 by norm_num,
          Real.sqrt_lt' two_pos]
        norm_num
      nlinarith [mul_lt_mul_of_pos_right h32 (mul_pos hε hk0)]
    · rw [← mul_pow]
      gcongr
      calc 1 + 2 * √3 * (√(3 / 2) * ε * √k) / r₀ = 1 + a * √k := by rw [ha_def]; ring
        _ ≤ (1 + a) * (1 + √k) := by nlinarith [mul_nonneg ha hk0.le]
  -- Summing over the cover.
  have hS : S ⊆ t.biUnion fun x ↦ S.filter (· ∈ U x) := by
    intro y hy
    have hyU : y ∈ ⋃ x ∈ t, U x := ht ▸ Set.mem_univ y
    obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 hyU
    exact Finset.mem_biUnion.2 ⟨x, hx, Finset.mem_filter.2 ⟨hy, hyx⟩⟩
  calc (S.card : ℝ) ≤ ∑ x ∈ t, ((S.filter (· ∈ U x)).card : ℝ) := by
        exact_mod_cast (Finset.card_le_card hS).trans Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ t, (1 + a) ^ n * (1 + √k) ^ n := Finset.sum_le_sum fun x _ ↦ hcount x
    _ = t.card * (1 + a) ^ n * (1 + √k) ^ n := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_assoc]

include D in
/-- **The size of a separated set, uniformly in `k`, for the real distance.** The statement of
`exists_forall_card_le_of_le_rescaledEDist` for the real rescaled distance `rescaledDist`, on a
compact, Hausdorff, preconnected manifold: for every `r₀ > 0` there is `C` such that for every
`k ≥ max k₀ 1`, a finite set whose distinct points are at `rescaledDist I k` at least `r₀` has at
most `C * (1 + √k) ^ dim` points. -/
theorem exists_forall_card_le_of_le_rescaledDist [CompactSpace M] [T2Space M]
    [PreconnectedSpace M] [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (hg : ∀ (x : M) (u w : TangentSpace I x), inner ℝ u w = σ.eval₂ x u (J x w))
    (hρ₀ : 0 < ρ₀) {r₀ : ℝ} (hr₀ : 0 < r₀) :
    ∃ C, ∀ {k : ℕ}, max k₀ 1 ≤ k → ∀ S : Finset M,
      (∀ x ∈ S, ∀ x' ∈ S, x ≠ x' → r₀ ≤ rescaledDist I k x x') →
        (S.card : ℝ) ≤ C * (1 + √k) ^ finrank ℝ (StdSpace ι) := by
  obtain ⟨C, hC⟩ := D.exists_forall_card_le_of_le_rescaledEDist hg hρ₀ hr₀
  refine ⟨C, fun hk S hS ↦ hC hk S fun x hx x' hx' hne ↦ ?_⟩
  rw [← ofReal_rescaledDist]
  exact ENNReal.ofReal_le_ofReal (hS x hx x' hx' hne)

include D in
/-- **Points of a separated set in a `d_k`-ball, uniformly in `k`.** Let `M` be compact and
Hausdorff, with a Riemannian metric whose inner product is `⟪u, w⟫ = σ(u, J w)`, and let the
rescaled unitary charts have radius `ρ₀ > 0`. For every `r₀ > 0` there is a constant `C` such
that for every `k ≥ max k₀ 1`, every finite set `S` whose distinct points are at rescaled
extended distance `d_k = √(2π k) · d_{g_J}` at least `r₀`, every point `y` and every `r ≥ 0`:
at most `C * (1 + r) ^ dim` points of `S` are at `d_k` at most `r` from `y`, where `dim` is the
real dimension of `StdSpace ι`. -/
theorem exists_forall_card_filter_rescaledEDist_le [CompactSpace M] [T2Space M]
    (hg : ∀ (x : M) (u w : TangentSpace I x), inner ℝ u w = σ.eval₂ x u (J x w))
    (hρ₀ : 0 < ρ₀) {r₀ : ℝ} (hr₀ : 0 < r₀) :
    ∃ C, ∀ {k : ℕ}, max k₀ 1 ≤ k → ∀ S : Finset M,
      (∀ x ∈ S, ∀ x' ∈ S, x ≠ x' → ENNReal.ofReal r₀ ≤ rescaledEDist I k x x') →
        ∀ (y : M) {r : ℝ}, 0 ≤ r →
          ((S.filter fun x ↦ rescaledEDist I k x y ≤ ENNReal.ofReal r).card : ℝ) ≤
            C * (1 + r) ^ finrank ℝ (StdSpace ι) := by
  obtain ⟨ρ₁, hρ₁, hρ₁₀, hcmp⟩ := D.exists_forall_isComparisonRadius hρ₀
  obtain ⟨A, hA⟩ := D.exists_forall_card_le_of_le_rescaledEDist hg hρ₀ hr₀
  set n := finrank ℝ (StdSpace ι)
  set b := 2 * √3 / r₀
  set c := √2 / ρ₁
  refine ⟨(1 + b) ^ n + max A 0 * (1 + c) ^ n, fun {k} hk S hS y r hr ↦ ?_⟩
  have hk₀ : k₀ ≤ k := (le_max_left _ _).trans hk
  have hb : 0 ≤ b := by positivity
  have hc : 0 ≤ c := by positivity
  rcases lt_or_ge r ((√2)⁻¹ * (ρ₁ * √k)) with hrρ | hrρ
  · -- A small ball: the local count in the chart centred at `y`.
    refine (D.card_filter_rescaledEDist_le hg hρ₁₀ hk₀ y (hcmp hk₀ y) hr₀ hr hrρ hS).trans ?_
    calc (1 + 2 * √3 * r / r₀) ^ n ≤ ((1 + b) * (1 + r)) ^ n := by
          gcongr
          calc 1 + 2 * √3 * r / r₀ = 1 + b * r := by ring
            _ ≤ (1 + b) * (1 + r) := by nlinarith [mul_nonneg hb hr]
      _ = (1 + b) ^ n * (1 + r) ^ n := mul_pow _ _ _
      _ ≤ ((1 + b) ^ n + max A 0 * (1 + c) ^ n) * (1 + r) ^ n := by
          gcongr
          exact le_add_of_nonneg_right (by positivity)
  · -- A large ball: `√k` is at most `c * r`, and the total count applies.
    have hkr : √k ≤ c * r := by
      rw [inv_mul_le_iff₀ (by positivity), mul_comm] at hrρ
      rw [div_mul_eq_mul_div, le_div_iff₀ hρ₁]
      linarith
    calc ((S.filter fun x ↦ rescaledEDist I k x y ≤ ENNReal.ofReal r).card : ℝ) ≤ S.card := by
          exact_mod_cast Finset.card_filter_le _ _
      _ ≤ A * (1 + √k) ^ n := hA hk S hS
      _ ≤ max A 0 * ((1 + c) * (1 + r)) ^ n := by
          gcongr
          · exact le_max_left _ _
          · nlinarith [mul_nonneg hc hr]
      _ = max A 0 * (1 + c) ^ n * (1 + r) ^ n := by rw [mul_pow, mul_assoc]
      _ ≤ ((1 + b) ^ n + max A 0 * (1 + c) ^ n) * (1 + r) ^ n := by
          gcongr
          exact le_add_of_nonneg_left (by positivity)

include D in
/-- **Points of a separated set in a `d_k`-ball, uniformly in `k`, for the real distance.** The
statement of `exists_forall_card_filter_rescaledEDist_le` for the real rescaled distance
`rescaledDist`, on a compact, Hausdorff, preconnected manifold: for every `r₀ > 0` there is `C`
such that for every `k ≥ max k₀ 1`, every finite set `S` whose distinct points are at
`rescaledDist I k` at least `r₀`, every `y` and every `r ≥ 0`, at most `C * (1 + r) ^ dim`
points of `S` are at `rescaledDist I k` at most `r` from `y`. -/
theorem exists_forall_card_filter_rescaledDist_le [CompactSpace M] [T2Space M]
    [PreconnectedSpace M] [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (hg : ∀ (x : M) (u w : TangentSpace I x), inner ℝ u w = σ.eval₂ x u (J x w))
    (hρ₀ : 0 < ρ₀) {r₀ : ℝ} (hr₀ : 0 < r₀) :
    ∃ C, ∀ {k : ℕ}, max k₀ 1 ≤ k → ∀ S : Finset M,
      (∀ x ∈ S, ∀ x' ∈ S, x ≠ x' → r₀ ≤ rescaledDist I k x x') → ∀ (y : M) {r : ℝ}, 0 ≤ r →
        ((S.filter fun x ↦ rescaledDist I k x y ≤ r).card : ℝ) ≤
          C * (1 + r) ^ finrank ℝ (StdSpace ι) := by
  obtain ⟨C, hC⟩ := D.exists_forall_card_filter_rescaledEDist_le hg hρ₀ hr₀
  refine ⟨C, fun hk S hS y r hr ↦ ?_⟩
  have h := hC hk S (fun x hx x' hx' hne ↦ by
    rw [← ofReal_rescaledDist]
    exact ENNReal.ofReal_le_ofReal (hS x hx x' hx' hne)) y hr
  convert h using 4 with x
  rw [← ofReal_rescaledDist, ENNReal.ofReal_le_ofReal_iff hr]

include D in
/-- **A coloured separated net of rescaled unit balls.** Let `M` be compact, Hausdorff and
preconnected, with a Riemannian metric whose inner product is `⟪u, w⟫ = σ(u, J w)`, and let the
rescaled unitary charts have radius `ρ₀ > 0`. There are `r₀ > 0` and `C` such that for every
`k ≥ max k₀ 1` there is a finite set `S` of centres with:

* its distinct points at rescaled distance `rescaledDist I k` at least `r₀`;
* every point of `M` of the form `(D.chart k x).symm z` with `x ∈ S` and `‖z‖ ≤ 1`;
* for every `y` and `r ≥ 0`, at most `C * (1 + r) ^ dim` points of `S` at rescaled distance at
  most `r` from `y`;
* for every `R ≥ 1`, a colouring `c : M → Fin N` with `N ≤ C * R ^ dim` colours in which
  distinct points of `S` of the same colour are at rescaled distance at least `R`.

Here `dim` is the real dimension of `StdSpace ι`, and `r₀`, `C` depend neither on `k` nor on
`R`. -/
theorem exists_separated_chart_cover_coloring [CompactSpace M] [T2Space M]
    [PreconnectedSpace M] [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (hg : ∀ (x : M) (u w : TangentSpace I x), inner ℝ u w = σ.eval₂ x u (J x w))
    (hρ₀ : 0 < ρ₀) :
    ∃ r₀ > 0, ∃ C, ∀ {k : ℕ}, max k₀ 1 ≤ k → ∃ S : Finset M,
      (∀ x ∈ S, ∀ x' ∈ S, x ≠ x' → r₀ ≤ rescaledDist I k x x') ∧
      (∀ y : M, ∃ x ∈ S, ∃ z ∈ closedBall (0 : StdSpace ι) 1, (D.chart k x).symm z = y) ∧
      (∀ (y : M) {r : ℝ}, 0 ≤ r →
        ((S.filter fun x ↦ rescaledDist I k x y ≤ r).card : ℝ) ≤
          C * (1 + r) ^ finrank ℝ (StdSpace ι)) ∧
      ∀ {R : ℝ}, 1 ≤ R → ∃ N : ℕ, (N : ℝ) ≤ C * R ^ finrank ℝ (StdSpace ι) ∧
        ∃ c : M → Fin N, ∀ x ∈ S, ∀ x' ∈ S, x ≠ x' → c x = c x' → R ≤ rescaledDist I k x x' := by
  classical
  obtain ⟨ρ₁, hρ₁, hρ₁₀, hcmp⟩ := D.exists_forall_isComparisonRadius hρ₀
  set n := finrank ℝ (StdSpace ι)
  have h2 : (0 : ℝ) < √2 := by positivity
  set r₀ := (√2)⁻¹ * min 1 ρ₁ with hr₀_def
  have hr₀ : 0 < r₀ := by positivity
  have hr₀1 : √2 * r₀ ≤ 1 := by
    rw [hr₀_def, mul_inv_cancel_left₀ h2.ne']
    exact min_le_left _ _
  obtain ⟨A, hA⟩ := D.exists_forall_card_le_of_le_rescaledDist hg hρ₀ hr₀
  obtain ⟨B, hB⟩ := D.exists_forall_card_filter_rescaledDist_le hg hρ₀ hr₀
  set B' := max B 0
  refine ⟨r₀, hr₀, 2 ^ n * B' + 1, fun {k} hk ↦ ?_⟩
  have hk₀ : k₀ ≤ k := (le_max_left _ _).trans hk
  have hk1 : 1 ≤ √(k : ℝ) :=
    Real.one_le_sqrt.2 (by exact_mod_cast (le_max_right k₀ 1).trans hk)
  have hr₀ρ : r₀ ≤ (√2)⁻¹ * (ρ₁ * √k) := by
    rw [hr₀_def]
    gcongr
    exact (min_le_right _ _).trans (le_mul_of_one_le_right hρ₁.le hk1)
  set Sep : Finset M → Prop := fun S ↦ ∀ x ∈ S, ∀ x' ∈ S, x ≠ x' → r₀ ≤ rescaledDist I k x x'
  -- A maximal separated set exists, since the separated sets have bounded size.
  obtain ⟨S, hS, hmax⟩ : ∃ S, Sep S ∧ ∀ y : M, ∃ x ∈ S, rescaledDist I k x y < r₀ := by
    by_contra! h
    have hn (m : ℕ) : ∃ S, Sep S ∧ S.card = m := by
      induction m with
      | zero => exact ⟨∅, by simp [Sep], rfl⟩
      | succ m ih =>
        obtain ⟨S, hS, rfl⟩ := ih
        obtain ⟨y, hy⟩ := h S hS
        have hyS : y ∉ S := fun hyS ↦ by
          have := hy y hyS
          rw [rescaledDist_self] at this
          exact hr₀.not_ge this
        refine ⟨insert y S, ?_, Finset.card_insert_of_notMem hyS⟩
        simp only [Sep, Finset.mem_insert]
        rintro x (rfl | hx) x' (rfl | hx') hne
        · exact absurd rfl hne
        · exact rescaledDist_comm (I := I) k x x' ▸ hy x' hx'
        · exact hy x hx
        · exact hS x hx x' hx' hne
    obtain ⟨S, hS, hcard⟩ := hn (⌊A * (1 + √k) ^ n⌋₊ + 1)
    have h := hA hk S hS
    rw [hcard] at h
    push_cast at h
    linarith [Nat.lt_floor_add_one (A * (1 + √(k : ℝ)) ^ n)]
  have hcount (y : M) {r : ℝ} (hr : 0 ≤ r) :
      ((S.filter fun x ↦ rescaledDist I k x y ≤ r).card : ℝ) ≤ B' * (1 + r) ^ n :=
    (hB hk S hS y hr).trans (by gcongr; exact le_max_left _ _)
  refine ⟨S, hS, fun y ↦ ?_, fun y r hr ↦ (hcount y hr).trans ?_, fun {R} hR ↦ ?_⟩
  · -- The cover, from maximality and the comparison of `d_k` with the chart norm.
    obtain ⟨x, hx, hxy⟩ := hmax y
    rw [← ENNReal.ofReal_lt_ofReal_iff hr₀, ofReal_rescaledDist] at hxy
    obtain ⟨z, hz, rfl⟩ :=
      D.exists_norm_lt_symm_eq_of_rescaledEDist_lt hg hρ₁₀ hk₀ x (hcmp hk₀ x) hr₀ρ hxy
    exact ⟨x, hx, z, mem_closedBall_zero_iff.2 (hz.le.trans hr₀1), rfl⟩
  · gcongr
    have h1 : B' ≤ 2 ^ n * B' :=
      le_mul_of_one_le_left (le_max_right B 0) (one_le_pow₀ one_le_two)
    linarith
  · -- The colouring, by the greedy colouring of the graph of nearby centres.
    exact Finset.exists_coloring_le_of_card_le_mul_pow (rescaledDist_comm (I := I) k) S
      (le_max_right B 0) (fun y _ r hr ↦ hcount y hr) hR

end RescaledUnitaryCharts

end SymplecticGeometry

end
