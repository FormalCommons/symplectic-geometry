/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.AsymptoticallyHolomorphic.ChartSection
import SymplecticGeometry.Analysis.SpecialFunctions.Gaussian.Basic

/-!
# Peak sections

Let `D` be rescaled unitary charts for `J` and a connection on the powers `PowerBundle P k` of a
line bundle, so that `D.chart k x` is a Darboux chart centred at `x` for `2π k σ`, with
derivative at the centre complex linear, rescaled by `√(2π k)`, and `D.frame k x`
a frame in which the connection is the model one. The **peak section**
`D.peakSection k x` is the section of `PowerBundle P k` extended by zero
(`SymplecticGeometry.RescaledUnitaryCharts.sectionOfReading`) from the cut-off Gaussian
`SymplecticGeometry.peakFunction k`, `χ (‖z‖ / k ^ (1 / 6)) * exp (-‖z‖ ^ 2 / 4)`, in the chart at
`x`, and `D.peakSection_mul k x j` the one extended by zero from `z_j` times it,
`SymplecticGeometry.peakFunction_mul k j`.

The cut-off Gaussians are smooth, supported in the closed ball of radius `2 * k ^ (1 / 6)`, which
for large `k` lies in any ball of radius `ε * √k`, have Gaussian jet bounds uniform in `k`, and
their model `∂̄` has such bounds with a factor `k ^ (-1 / 2)`
(`SymplecticGeometry.exists_jetNormAt_peakFunction_le`,
`SymplecticGeometry.exists_jetNormAt_modelDbar_peakFunction_le` and their versions for
`peakFunction_mul`). The estimates for sections extended by zero from such families, in
`ChartSection.lean`, then give the estimates of the peak sections in terms of the rescaled
distance `d_k(x, y) = √(2π k) · d_g(x, y)`: the lower bound `exp (-1 / 4)` near the centre, the
Gaussian decay of the jet norms and of the `∂̄` jet norms, with a factor `k ^ (-1 / 2)` for the
latter, and that peak sections at any sequence of centres are asymptotically holomorphic.

## Main definitions

* `SymplecticGeometry.RescaledUnitaryCharts.peakSection`: the peak section at `x`.
* `SymplecticGeometry.RescaledUnitaryCharts.peakSection_mul`: the peak section at `x` times the
  `j`-th complex coordinate of the chart.

## Main results

* `SymplecticGeometry.RescaledUnitaryCharts.exists_le_norm_peakSection`: the lower bound near
  the centre.
* `SymplecticGeometry.RescaledUnitaryCharts.exists_jetNorm_peakSection_le`,
  `SymplecticGeometry.RescaledUnitaryCharts.exists_dbarJetNorm_peakSection_le` and their
  versions for `peakSection_mul`: the Gaussian decay of the jet norms and of the `∂̄` jet norms.
* `SymplecticGeometry.RescaledUnitaryCharts.isAsymptoticallyHolomorphic_peakSection`,
  `SymplecticGeometry.RescaledUnitaryCharts.isAsymptoticallyHolomorphic_peakSection_mul`: peak
  sections at a sequence of centres are asymptotically holomorphic.
* `SymplecticGeometry.RescaledUnitaryCharts.exists_peakSection_estimates`: all of these together.

## References

* [S. K. Donaldson, *Symplectic submanifolds and almost-complex geometry*][Donaldson1996].
* [D. Auroux, *A remark about Donaldson's construction of symplectic submanifolds*][Auroux2002],
  Lemmas 1–2 and the proof of Proposition 2.
-/

public section

open scoped Manifold ContDiff
open TauCeti Metric Bundle

namespace SymplecticGeometry

namespace RescaledUnitaryCharts

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {ι : Type*} [Fintype ι]
  {P : M → Type*} [TopologicalSpace (TotalSpace Circle P)] [∀ x, TopologicalSpace (P x)]
  [FiberBundle Circle P] [∀ x, MulAction Circleᵐᵒᵖ (P x)] [PrincipalBundle Circle P]
  [ContMDiffFiberBundle ∞ Circle P I (𝓡 1)]
  {σ : SmoothTwoForm I M} {J : SmoothAlmostComplexStructure I M}
  {α : SmoothForm (I.prod (𝓡 1)) (ManifoldTotalSpace Circle P) ℝ 1} {k₀ : ℕ} {ρ₀ : ℝ}
  (D : RescaledUnitaryCharts P σ J α ι k₀ ρ₀)

/-! ### The peak sections -/

/-- The **peak section** at `x`: the section of `PowerBundle P k` extended by zero from the
cut-off Gaussian `χ (‖z‖ / k ^ (1 / 6)) * exp (-‖z‖ ^ 2 / 4)` in the chart `D.chart k x`. -/
noncomputable def peakSection (k : ℕ) (x : M) : Π y, PowerBundle P k y :=
  D.sectionOfReading k x (peakFunction k)

theorem peakSection_def (k : ℕ) (x : M) :
    D.peakSection k x = D.sectionOfReading k x (peakFunction k) :=
  (rfl)

/-- The peak section at `x` times the `j`-th complex coordinate: the section of `PowerBundle P k`
extended by zero from `z_j` times the cut-off Gaussian in the chart `D.chart k x`. -/
noncomputable def peakSection_mul (k : ℕ) (x : M) (j : ι) : Π y, PowerBundle P k y :=
  D.sectionOfReading k x (peakFunction_mul k j)

theorem peakSection_mul_def (k : ℕ) (x : M) (j : ι) :
    D.peakSection_mul k x j = D.sectionOfReading k x (peakFunction_mul k j) :=
  (rfl)

/-- For `k₀ ≤ k`, the reading of the peak section at `x` in the chart at `x` is the cut-off
Gaussian on the ball of radius `ρ₀ * √k`. -/
theorem reading_peakSection {k : ℕ} (hk : k₀ ≤ k) (x : M) :
    Set.EqOn (D.reading k x (D.peakSection k x)) (peakFunction k) (ball 0 (ρ₀ * √k)) :=
  D.reading_sectionOfReading hk x _

/-- For `k₀ ≤ k`, the reading of `D.peakSection_mul k x j` in the chart at `x` is `z_j` times the
cut-off Gaussian on the ball of radius `ρ₀ * √k`. -/
theorem reading_peakSection_mul {k : ℕ} (hk : k₀ ≤ k) (x : M) (j : ι) :
    Set.EqOn (D.reading k x (D.peakSection_mul k x j)) (peakFunction_mul k j)
      (ball 0 (ρ₀ * √k)) :=
  D.reading_sectionOfReading hk x _

/-! ### The estimates -/

section RiemannianEDist

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- **Lower bound of the peak sections near the centre.** Let `M` be Hausdorff, with a
Riemannian metric whose inner product is `⟪u, w⟫ = σ(u, J w)`, and let `ρ₀ > 0`. There is
`R > 0` such that for large `k`, all points `x`, and all `y` at rescaled distance
`√(2π k) · d_g(x, y)` less than `R` from `x`, the peak section at `x` has norm at least
`exp (-1 / 4)` at `y`. -/
theorem exists_le_norm_peakSection [T2Space M]
    (hg : ∀ (x : M) (u w : TangentSpace I x), inner ℝ u w = σ.eval₂ x u (J x w))
    (hρ₀ : 0 < ρ₀) :
    ∃ R > 0, ∀ᶠ k : ℕ in Filter.atTop, ∀ x y : M,
      rescaledEDist I k x y < ENNReal.ofReal R →
        Real.exp (-1 / 4) ≤ ‖D.peakSection k x y‖ :=
  D.exists_le_norm_sectionOfReading hg hρ₀ <| by
    filter_upwards [Filter.eventually_ge_atTop 1] with k hk z hz
    exact exp_neg_one_div_four_le_norm_peakFunction hk hz.le

/-- **Gaussian decay of the peak sections.** Let `M` be a Hausdorff boundaryless manifold, let
`σ` be compatible with `J`, let `M` carry a Riemannian metric whose inner product is
`⟪u, w⟫ = σ(u, J w)`, let `α` be a connection form and `ρ₀ > 0`. For every order `r` there are
`C`, `N` and `c > 0` such that for large `k` and all points `x` and `y`, the `r`-jet norm at `y`
of the peak section at `x` is at most `C * (1 + d) ^ N * exp (-c * d ^ 2)`, for `d` the rescaled
distance `√(2π k) · d_g(x, y)`. -/
theorem exists_jetNorm_peakSection_le [T2Space M] [I.Boundaryless]
    (hg : ∀ (x : M) (u w : TangentSpace I x), inner ℝ u w = σ.eval₂ x u (J x w))
    (hJ : σ.Compatible J) (hα : IsCircleConnectionForm α) (hρ₀ : 0 < ρ₀) (r : ℕ) :
    ∃ C : ℝ, ∃ N : ℕ, ∃ c > 0, ∀ᶠ k : ℕ in Filter.atTop, ∀ x y : M,
      D.jetNorm k r (D.peakSection k x) y ≤
        C * (1 + rescaledDist I k x y) ^ N *
          Real.exp (-c * rescaledDist I k x y ^ 2) :=
  let ⟨A, N, c, hc, h⟩ := exists_jetNormAt_peakFunction_le (E := StdSpace ι) r
  D.exists_jetNorm_sectionOfReading_le hg hJ hα hρ₀ r
    (.of_forall fun k ↦ contDiff_peakFunction k)
    (fun _ hε ↦ eventually_tsupport_peakFunction_subset_ball hε)
    ⟨A, N, c, hc, .of_forall h⟩

/-- **Gaussian decay of `∂̄` of the peak sections.** Under the hypotheses of
`SymplecticGeometry.RescaledUnitaryCharts.exists_jetNorm_peakSection_le`, for every order `r`
there are `C`, `N` and `c > 0` such that for large `k` and all points `x` and `y`, the `r`-jet
norm at `y` of `∂̄` of the peak section at `x` is at most
`C * k ^ (-1 / 2) * (1 + d) ^ N * exp (-c * d ^ 2)`, for `d` the rescaled distance
`√(2π k) · d_g(x, y)`. -/
theorem exists_dbarJetNorm_peakSection_le [T2Space M] [I.Boundaryless]
    (hg : ∀ (x : M) (u w : TangentSpace I x), inner ℝ u w = σ.eval₂ x u (J x w))
    (hJ : σ.Compatible J) (hα : IsCircleConnectionForm α) (hρ₀ : 0 < ρ₀) (r : ℕ) :
    ∃ C : ℝ, ∃ N : ℕ, ∃ c > 0, ∀ᶠ k : ℕ in Filter.atTop, ∀ x y : M,
      D.dbarJetNorm k r (D.peakSection k x) y ≤
        C * (k : ℝ) ^ (-1 / 2 : ℝ) * (1 + rescaledDist I k x y) ^ N *
          Real.exp (-c * rescaledDist I k x y ^ 2) :=
  let ⟨A, N, c, hc, h⟩ := exists_jetNormAt_peakFunction_le (E := StdSpace ι) (r + 1)
  let ⟨A', N', c', hc', h'⟩ := exists_jetNormAt_modelDbar_peakFunction_le (ι := ι) r
  D.exists_dbarJetNorm_sectionOfReading_le hg hJ hα hρ₀ r
    (.of_forall fun k ↦ contDiff_peakFunction k)
    (fun _ hε ↦ eventually_tsupport_peakFunction_subset_ball hε)
    ⟨A, N, c, hc, .of_forall h⟩
    ⟨A', N', c', hc', Filter.eventually_ge_atTop 1 |>.mono fun k hk ↦ h' k hk⟩

/-- **Gaussian decay of the peak sections times a coordinate.** Under the hypotheses of
`SymplecticGeometry.RescaledUnitaryCharts.exists_jetNorm_peakSection_le`, for every order `r`
there are `C`, `N` and `c > 0` such that for large `k`, every `j` and all points `x` and `y`, the
`r`-jet norm at `y` of `D.peakSection_mul k x j` is at most `C * (1 + d) ^ N * exp (-c * d ^ 2)`,
for `d` the rescaled distance `√(2π k) · d_g(x, y)`. -/
theorem exists_jetNorm_peakSection_mul_le [T2Space M] [I.Boundaryless]
    (hg : ∀ (x : M) (u w : TangentSpace I x), inner ℝ u w = σ.eval₂ x u (J x w))
    (hJ : σ.Compatible J) (hα : IsCircleConnectionForm α) (hρ₀ : 0 < ρ₀) (r : ℕ) (j : ι) :
    ∃ C : ℝ, ∃ N : ℕ, ∃ c > 0, ∀ᶠ k : ℕ in Filter.atTop, ∀ x y : M,
      D.jetNorm k r (D.peakSection_mul k x j) y ≤
        C * (1 + rescaledDist I k x y) ^ N *
          Real.exp (-c * rescaledDist I k x y ^ 2) :=
  let ⟨A, N, c, hc, h⟩ := exists_jetNormAt_peakFunction_mul_le (ι := ι) r
  D.exists_jetNorm_sectionOfReading_le hg hJ hα hρ₀ r
    (.of_forall fun k ↦ contDiff_peakFunction_mul k j)
    (fun _ hε ↦ (eventually_tsupport_peakFunction_mul_subset_ball hε).mono fun _ h ↦ h j)
    ⟨A, N, c, hc, .of_forall fun k ↦ h k j⟩

/-- **Gaussian decay of `∂̄` of the peak sections times a coordinate.** Under the hypotheses of
`SymplecticGeometry.RescaledUnitaryCharts.exists_jetNorm_peakSection_le`, for every order `r`
there are `C`, `N` and `c > 0` such that for large `k`, every `j` and all points `x` and `y`, the
`r`-jet norm at `y` of `∂̄` of `D.peakSection_mul k x j` is at most
`C * k ^ (-1 / 2) * (1 + d) ^ N * exp (-c * d ^ 2)`, for `d` the rescaled distance
`√(2π k) · d_g(x, y)`. -/
theorem exists_dbarJetNorm_peakSection_mul_le [T2Space M] [I.Boundaryless]
    (hg : ∀ (x : M) (u w : TangentSpace I x), inner ℝ u w = σ.eval₂ x u (J x w))
    (hJ : σ.Compatible J) (hα : IsCircleConnectionForm α) (hρ₀ : 0 < ρ₀) (r : ℕ) (j : ι) :
    ∃ C : ℝ, ∃ N : ℕ, ∃ c > 0, ∀ᶠ k : ℕ in Filter.atTop, ∀ x y : M,
      D.dbarJetNorm k r (D.peakSection_mul k x j) y ≤
        C * (k : ℝ) ^ (-1 / 2 : ℝ) * (1 + rescaledDist I k x y) ^ N *
          Real.exp (-c * rescaledDist I k x y ^ 2) :=
  let ⟨A, N, c, hc, h⟩ := exists_jetNormAt_peakFunction_mul_le (ι := ι) (r + 1)
  let ⟨A', N', c', hc', h'⟩ := exists_jetNormAt_modelDbar_peakFunction_mul_le (ι := ι) r
  D.exists_dbarJetNorm_sectionOfReading_le hg hJ hα hρ₀ r
    (.of_forall fun k ↦ contDiff_peakFunction_mul k j)
    (fun _ hε ↦ (eventually_tsupport_peakFunction_mul_subset_ball hε).mono fun _ h ↦ h j)
    ⟨A, N, c, hc, .of_forall fun k ↦ h k j⟩
    ⟨A', N', c', hc', Filter.eventually_ge_atTop 1 |>.mono fun k hk ↦ h' k hk j⟩

/-- **Peak sections are asymptotically holomorphic.** Under the hypotheses of
`SymplecticGeometry.RescaledUnitaryCharts.exists_jetNorm_peakSection_le`, for every sequence of
centres `x k`, the peak sections `D.peakSection k (x k)` form an asymptotically holomorphic
sequence. -/
theorem isAsymptoticallyHolomorphic_peakSection [T2Space M] [I.Boundaryless]
    (hg : ∀ (x : M) (u w : TangentSpace I x), inner ℝ u w = σ.eval₂ x u (J x w))
    (hJ : σ.Compatible J) (hα : IsCircleConnectionForm α) (hρ₀ : 0 < ρ₀) (x : ℕ → M) :
    D.IsAsymptoticallyHolomorphic fun k ↦ D.peakSection k (x k) :=
  D.isAsymptoticallyHolomorphic_sectionOfReading hg hJ hα hρ₀
    (.of_forall fun k ↦ contDiff_peakFunction k)
    (fun _ hε ↦ eventually_tsupport_peakFunction_subset_ball hε)
    (fun r ↦ let ⟨A, N, c, hc, h⟩ := exists_jetNormAt_peakFunction_le (E := StdSpace ι) r
      ⟨A, N, c, hc, .of_forall h⟩)
    (fun r ↦ let ⟨A, N, c, hc, h⟩ := exists_jetNormAt_modelDbar_peakFunction_le (ι := ι) r
      ⟨A, N, c, hc, Filter.eventually_ge_atTop 1 |>.mono fun k hk ↦ h k hk⟩) x

/-- **Peak sections times a coordinate are asymptotically holomorphic.** Under the hypotheses of
`SymplecticGeometry.RescaledUnitaryCharts.exists_jetNorm_peakSection_le`, for every sequence of
centres `x k` and every `j`, the sections `D.peakSection_mul k (x k) j` form an asymptotically
holomorphic sequence. -/
theorem isAsymptoticallyHolomorphic_peakSection_mul [T2Space M] [I.Boundaryless]
    (hg : ∀ (x : M) (u w : TangentSpace I x), inner ℝ u w = σ.eval₂ x u (J x w))
    (hJ : σ.Compatible J) (hα : IsCircleConnectionForm α) (hρ₀ : 0 < ρ₀) (x : ℕ → M) (j : ι) :
    D.IsAsymptoticallyHolomorphic fun k ↦ D.peakSection_mul k (x k) j :=
  D.isAsymptoticallyHolomorphic_sectionOfReading hg hJ hα hρ₀
    (.of_forall fun k ↦ contDiff_peakFunction_mul k j)
    (fun _ hε ↦ (eventually_tsupport_peakFunction_mul_subset_ball hε).mono fun _ h ↦ h j)
    (fun r ↦ let ⟨A, N, c, hc, h⟩ := exists_jetNormAt_peakFunction_mul_le (ι := ι) r
      ⟨A, N, c, hc, .of_forall fun k ↦ h k j⟩)
    (fun r ↦ let ⟨A, N, c, hc, h⟩ := exists_jetNormAt_modelDbar_peakFunction_mul_le (ι := ι) r
      ⟨A, N, c, hc, Filter.eventually_ge_atTop 1 |>.mono fun k hk ↦ h k hk j⟩) x

/-- **Asymptotically holomorphic peak sections.** Let `M` be a Hausdorff boundaryless manifold,
let `σ` be compatible with `J`, let `M` carry the Riemannian metric `⟪u, w⟫ = σ(u, J w)`, let
`α` be a connection form, and let `D` be rescaled unitary charts of radius `ρ₀ > 0` (on a compact
manifold of dimension `2 * card ι`, for `α` of curvature `-2π σ`, they exist by
`SymplecticGeometry.exists_rescaledUnitaryCharts`). Write
`d = √(2π k) · d_g(x, y)` for the rescaled distance. Then the peak sections `D.peakSection k x`
and `D.peakSection_mul k x j` satisfy:
* for some `R > 0` and large `k`, `‖D.peakSection k x y‖ ≥ exp (-1 / 4)` whenever `d < R`;
* for every order `r` there are `C`, `N` and `c > 0` such that for large `k` and all `x`, `y`,
  the `r`-jet norm at `y` of `D.peakSection k x` is at most `C * (1 + d) ^ N * exp (-c * d ^ 2)`
  and that of its `∂̄` is at most `C * k ^ (-1 / 2) * (1 + d) ^ N * exp (-c * d ^ 2)`;
* the same holds for `D.peakSection_mul k x j`, for every `j`;
* for every sequence of centres `x k`, the sequences `D.peakSection k (x k)` and
  `D.peakSection_mul k (x k) j` are asymptotically holomorphic.

Milestone: *Asymptotically holomorphic peak sections*. -/
theorem exists_peakSection_estimates [T2Space M] [I.Boundaryless]
    (hg : ∀ (x : M) (u w : TangentSpace I x), inner ℝ u w = σ.eval₂ x u (J x w))
    (hJ : σ.Compatible J) (hα : IsCircleConnectionForm α) (hρ₀ : 0 < ρ₀) :
    (∃ R > 0, ∀ᶠ k : ℕ in Filter.atTop, ∀ x y : M,
      rescaledEDist I k x y < ENNReal.ofReal R →
        Real.exp (-1 / 4) ≤ ‖D.peakSection k x y‖) ∧
    (∀ r : ℕ, ∃ C : ℝ, ∃ N : ℕ, ∃ c > 0, ∀ᶠ k : ℕ in Filter.atTop, ∀ x y : M,
      D.jetNorm k r (D.peakSection k x) y ≤
          C * (1 + rescaledDist I k x y) ^ N *
            Real.exp (-c * rescaledDist I k x y ^ 2) ∧
        D.dbarJetNorm k r (D.peakSection k x) y ≤
          C * (k : ℝ) ^ (-1 / 2 : ℝ) * (1 + rescaledDist I k x y) ^ N *
            Real.exp (-c * rescaledDist I k x y ^ 2)) ∧
    (∀ (r : ℕ) (j : ι), ∃ C : ℝ, ∃ N : ℕ, ∃ c > 0, ∀ᶠ k : ℕ in Filter.atTop, ∀ x y : M,
      D.jetNorm k r (D.peakSection_mul k x j) y ≤
          C * (1 + rescaledDist I k x y) ^ N *
            Real.exp (-c * rescaledDist I k x y ^ 2) ∧
        D.dbarJetNorm k r (D.peakSection_mul k x j) y ≤
          C * (k : ℝ) ^ (-1 / 2 : ℝ) * (1 + rescaledDist I k x y) ^ N *
            Real.exp (-c * rescaledDist I k x y ^ 2)) ∧
    ∀ x : ℕ → M, D.IsAsymptoticallyHolomorphic (fun k ↦ D.peakSection k (x k)) ∧
      ∀ j : ι, D.IsAsymptoticallyHolomorphic fun k ↦ D.peakSection_mul k (x k) j := by
  refine ⟨D.exists_le_norm_peakSection hg hρ₀, fun r ↦ ?_, fun r j ↦ ?_, fun x ↦
    ⟨D.isAsymptoticallyHolomorphic_peakSection hg hJ hα hρ₀ x,
      D.isAsymptoticallyHolomorphic_peakSection_mul hg hJ hα hρ₀ x⟩⟩
  · obtain ⟨C₁, N₁, c₁, hc₁, h₁⟩ := D.exists_jetNorm_peakSection_le hg hJ hα hρ₀ r
    obtain ⟨C₂, N₂, c₂, hc₂, h₂⟩ := D.exists_dbarJetNorm_peakSection_le hg hJ hα hρ₀ r
    obtain ⟨C, -, N, c, hc, h⟩ := Real.exists_le_one_add_pow_mul_exp_neg_mul_sq_and_le
      (l := Filter.atTop) (w := fun k : ℕ ↦ (k : ℝ) ^ (-1 / 2 : ℝ))
      (F := fun k (p : M × M) ↦ D.jetNorm k r (D.peakSection k p.1) p.2)
      (G := fun k p ↦ D.dbarJetNorm k r (D.peakSection k p.1) p.2)
      (d := fun k p ↦ rescaledDist I k p.1 p.2) (fun k p ↦ rescaledDist_nonneg I k p.1 p.2)
      (fun _ ↦ by positivity)
      ⟨C₁, N₁, c₁, hc₁, h₁.mono fun _ h p ↦ h p.1 p.2⟩
      ⟨C₂, N₂, c₂, hc₂, h₂.mono fun _ h p ↦ h p.1 p.2⟩
    exact ⟨C, N, c, hc, h.mono fun _ h x y ↦ h (x, y)⟩
  · obtain ⟨C₁, N₁, c₁, hc₁, h₁⟩ := D.exists_jetNorm_peakSection_mul_le hg hJ hα hρ₀ r j
    obtain ⟨C₂, N₂, c₂, hc₂, h₂⟩ := D.exists_dbarJetNorm_peakSection_mul_le hg hJ hα hρ₀ r j
    obtain ⟨C, -, N, c, hc, h⟩ := Real.exists_le_one_add_pow_mul_exp_neg_mul_sq_and_le
      (l := Filter.atTop) (w := fun k : ℕ ↦ (k : ℝ) ^ (-1 / 2 : ℝ))
      (F := fun k (p : M × M) ↦ D.jetNorm k r (D.peakSection_mul k p.1 j) p.2)
      (G := fun k p ↦ D.dbarJetNorm k r (D.peakSection_mul k p.1 j) p.2)
      (d := fun k p ↦ rescaledDist I k p.1 p.2) (fun k p ↦ rescaledDist_nonneg I k p.1 p.2)
      (fun _ ↦ by positivity)
      ⟨C₁, N₁, c₁, hc₁, h₁.mono fun _ h p ↦ h p.1 p.2⟩
      ⟨C₂, N₂, c₂, hc₂, h₂.mono fun _ h p ↦ h p.1 p.2⟩
    exact ⟨C, N, c, hc, h.mono fun _ h x y ↦ h (x, y)⟩

end RiemannianEDist

end RescaledUnitaryCharts

end SymplecticGeometry

end
