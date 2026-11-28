/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.AsymptoticallyHolomorphic.ChartSection
import SymplecticGeometry.Analysis.SpecialFunctions.Gaussian.Basic
import TauCeti.Analysis.Calculus.ContDiff.Differentiable

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
* `SymplecticGeometry.RescaledUnitaryCharts.affinePeakSection`: the combination
  `w₀ • peakSection k x + Σ_j w_j • peakSection_mul k x j`, additive and homogeneous in
  `w = (w₀, w₁, …, wₙ)`.

## Main results

* `SymplecticGeometry.RescaledUnitaryCharts.reading_affinePeakSection`: the reading of
  `affinePeakSection k x w` in the chart at `x` is `(w₀ + Σ_j w_j z_j)` times the cut-off
  Gaussian; and
  `SymplecticGeometry.RescaledUnitaryCharts.reading_sub_affinePeakSection_eventuallyEq`: near
  the points where the cut-off is `1`, the reading of `s - affinePeakSection k x w` is the quotient
  of the reading of `s` by the cut-off Gaussian, minus `w₀ + Σ_j w_j z_j`, times the Gaussian.
* `SymplecticGeometry.RescaledUnitaryCharts.exists_le_norm_peakSection`: the lower bound near
  the centre.
* `SymplecticGeometry.RescaledUnitaryCharts.exists_jetNorm_peakSection_le`,
  `SymplecticGeometry.RescaledUnitaryCharts.exists_dbarJetNorm_peakSection_le` and their
  versions for `peakSection_mul`: the Gaussian decay of the jet norms and of the `∂̄` jet norms.
* `SymplecticGeometry.RescaledUnitaryCharts.exists_jetNorm_affinePeakSection_le`,
  `SymplecticGeometry.RescaledUnitaryCharts.exists_dbarJetNorm_affinePeakSection_le`: the same
  Gaussian decay for `affinePeakSection k x w`, with constants uniform in `w` and a factor `‖w‖`.
  They combine the bounds for the `n + 1` peak sections with
  `Real.exists_forall_le_one_add_pow_mul_exp_neg_mul_sq`, through
  `SymplecticGeometry.RescaledUnitaryCharts.affinePeakSection_eq_sum` and the triangle
  inequalities `SymplecticGeometry.RescaledUnitaryCharts.jetNorm_sum_le` and
  `SymplecticGeometry.RescaledUnitaryCharts.dbarJetNorm_sum_le`.
* `SymplecticGeometry.RescaledUnitaryCharts.exists_jetNorm_sum_affinePeakSection_le`: for a sum
  `∑ x ∈ S, affinePeakSection k x (w x)` over a finite set `S` of centres that has at most
  `C₀ * (1 + ρ) ^ m` points at rescaled distance at most `ρ` from `y`, with `‖w x‖ ≤ δ`, the jet
  norm at `y` is at most `C * δ`, that of `∂̄` at most `C * δ * k ^ (-1 / 2)`, and the part over
  the centres at rescaled distance at least `R` has jet norm at most `C * δ * exp (-c * R ^ 2)`.
  The proof bounds the jet norms of the sum over any finite set by the sum of the previous
  estimates
  (`SymplecticGeometry.RescaledUnitaryCharts.exists_jetNorm_sum_affinePeakSection_le_mul_sum` and
  its `∂̄` version), and bounds these Gaussian sums with
  `SymplecticGeometry.exists_sum_one_add_rescaledDist_pow_mul_exp_le`. For large `k` the readings
  of such sums are smooth
  (`RescaledUnitaryCharts.eventually_contDiffAt_reading_and_dbarReading_sum_affinePeakSection`).
* `SymplecticGeometry.RescaledUnitaryCharts.isAsymptoticallyHolomorphic_peakSection`,
  `SymplecticGeometry.RescaledUnitaryCharts.isAsymptoticallyHolomorphic_peakSection_mul`: peak
  sections at a sequence of centres are asymptotically holomorphic.
* `SymplecticGeometry.RescaledUnitaryCharts.exists_peakSection_estimates`: all of these together.
* `SymplecticGeometry.RescaledUnitaryCharts.isAsymptoticallyHolomorphic_sum_affinePeakSection`:
  sums of `affinePeakSection` over sets of centres with the counting bound above, with bounded
  coefficients, are asymptotically holomorphic.

## References

* [S. K. Donaldson, *Symplectic submanifolds and almost-complex geometry*][Donaldson1996].
* [D. Auroux, *A remark about Donaldson's construction of symplectic submanifolds*][Auroux2002],
  Lemmas 1–2 and the proof of Proposition 2.
-/

public section

open scoped Manifold ContDiff Topology
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

/-! ### Affine combinations of peak sections -/

/-- The **affine combination of peak sections** at `x` with coefficients
`w = (w₀, w₁, …, wₙ)`, indexed by `Option ι` with `w₀ = w none`:
`w₀ • D.peakSection k x + Σ_j w_j • D.peakSection_mul k x j`. -/
noncomputable def affinePeakSection (k : ℕ) (x : M) (w : EuclideanSpace ℂ (Option ι)) :
    Π y, PowerBundle P k y :=
  w none • D.peakSection k x + ∑ j, w (some j) • D.peakSection_mul k x j

theorem affinePeakSection_def (k : ℕ) (x : M) (w : EuclideanSpace ℂ (Option ι)) :
    D.affinePeakSection k x w =
      w none • D.peakSection k x + ∑ j, w (some j) • D.peakSection_mul k x j :=
  (rfl)

/-- The affine combination with zero coefficients is the zero section. -/
@[simp]
theorem affinePeakSection_zero (k : ℕ) (x : M) :
    D.affinePeakSection k x (0 : EuclideanSpace ℂ (Option ι)) = 0 := by
  simp [affinePeakSection_def]

/-- The affine combination of peak sections is additive in its coefficients. -/
theorem affinePeakSection_add (k : ℕ) (x : M) (w w' : EuclideanSpace ℂ (Option ι)) :
    D.affinePeakSection k x (w + w') =
      D.affinePeakSection k x w + D.affinePeakSection k x w' := by
  simp only [affinePeakSection_def, PiLp.add_apply, add_smul, Finset.sum_add_distrib]
  abel

/-- The affine combination of peak sections is homogeneous in its coefficients. -/
theorem affinePeakSection_smul (k : ℕ) (x : M) (c : ℂ) (w : EuclideanSpace ℂ (Option ι)) :
    D.affinePeakSection k x (c • w) = c • D.affinePeakSection k x w := by
  simp only [affinePeakSection_def, PiLp.smul_apply, smul_eq_mul, mul_smul, smul_add,
    Finset.smul_sum]

/-- The affine combination of peak sections as a sum over `Option ι`: the coefficient `w none`
multiplies the peak section and `w (some j)` the peak section times the `j`-th coordinate. -/
theorem affinePeakSection_eq_sum (k : ℕ) (x : M) (w : EuclideanSpace ℂ (Option ι)) :
    D.affinePeakSection k x w =
      ∑ j : Option ι, w j • j.elim (D.peakSection k x) (D.peakSection_mul k x) := by
  simp [affinePeakSection_def, Fintype.sum_option]

/-- For `k₀ ≤ k`, the reading of `D.affinePeakSection k x w` in the chart at `x` is
`(w₀ + Σ_j w_j z_j)` times the cut-off Gaussian on the ball of radius `ρ₀ * √k`, for
`z_j = (complexToRealEuclidean ι).symm z j`. -/
theorem reading_affinePeakSection {k : ℕ} (hk : k₀ ≤ k) (x : M)
    (w : EuclideanSpace ℂ (Option ι)) :
    Set.EqOn (D.reading k x (D.affinePeakSection k x w))
      (fun z ↦ (w none + ∑ j, w (some j) * (complexToRealEuclidean ι).symm z j) *
        peakFunction k z) (ball 0 (ρ₀ * √k)) := by
  intro z hz
  simp only [affinePeakSection_def, reading_add, reading_smul, reading_sum, Pi.add_apply,
    Pi.smul_apply, Finset.sum_apply, smul_eq_mul, D.reading_peakSection hk x hz,
    D.reading_peakSection_mul hk x _ hz, peakFunction_mul_def, add_mul, Finset.sum_mul]
  congr 1
  exact Finset.sum_congr rfl fun j _ ↦ by ring

/-- **The reading of a section corrected by peak sections.** For `k₀ ≤ k` and `z` in the balls of
radii `ρ₀ * √k` and `k ^ (1 / 6)`, near `z` the reading of `s - D.affinePeakSection k x w` in the
chart at `x` is `q - w₀ - Σ_j w_j z_j` times the Gaussian `exp (-‖·‖ ^ 2 / 4)`, for `q` the
quotient of the reading of `s` by the cut-off Gaussian `peakFunction k`. -/
theorem reading_sub_affinePeakSection_eventuallyEq {k : ℕ} (hk : k₀ ≤ k) (x : M)
    (s : Π y, PowerBundle P k y) (w : EuclideanSpace ℂ (Option ι)) {z : StdSpace ι}
    (hzρ : ‖z‖ < ρ₀ * √k) (hz6 : ‖z‖ < (k : ℝ) ^ (1 / 6 : ℝ)) :
    D.reading k x (s - D.affinePeakSection k x w) =ᶠ[𝓝 z]
      fun y ↦ (D.reading k x s y / peakFunction k y - w none -
        ∑ j, w (some j) * (complexToRealEuclidean ι).symm y j) * Real.exp (-‖y‖ ^ 2 / 4) := by
  have hzU : z ∈ ball (0 : StdSpace ι) (min (ρ₀ * √k) ((k : ℝ) ^ (1 / 6 : ℝ))) :=
    mem_ball_zero_iff.2 (lt_min hzρ hz6)
  filter_upwards [isOpen_ball.mem_nhds hzU] with y hy
  have hy₁ : y ∈ ball (0 : StdSpace ι) (ρ₀ * √k) := ball_subset_ball (min_le_left _ _) hy
  have hy₂ : y ∈ ball (0 : StdSpace ι) ((k : ℝ) ^ (1 / 6 : ℝ)) :=
    ball_subset_ball (min_le_right _ _) hy
  have hp : peakFunction k y = (Real.exp (-‖y‖ ^ 2 / 4) : ℂ) := peakFunction_eqOn_ball k hy₂
  rw [reading_sub, Pi.sub_apply, D.reading_affinePeakSection hk x w hy₁]
  simp only [hp]
  field_simp
  ring

/-! ### Smoothness of the readings -/

/-- On a Hausdorff boundaryless manifold with `ρ₀ > 0`, for large `k`, at every point `y`, the
reading and the `∂̄` reading in the chart at `y` of the peak section at every `x` are smooth at
`0`. -/
theorem eventually_contDiffAt_reading_and_dbarReading_peakSection [T2Space M] [I.Boundaryless]
    (hρ₀ : 0 < ρ₀) :
    ∀ᶠ k : ℕ in Filter.atTop, ∀ x y : M,
      ContDiffAt ℝ ∞ (D.reading k y (D.peakSection k x)) 0 ∧
        ContDiffAt ℝ ∞ (D.dbarReading k y (D.peakSection k x)) 0 := by
  filter_upwards [Filter.eventually_ge_atTop k₀,
    eventually_tsupport_peakFunction_subset_ball (E := StdSpace ι) hρ₀]
    with k hk hf x y
  exact D.contDiffAt_reading_and_dbarReading_sectionOfReading hk x hf
    (contDiff_peakFunction k).contDiffOn y

/-- On a Hausdorff boundaryless manifold with `ρ₀ > 0`, for large `k`, at every point `y`, the
reading and the `∂̄` reading in the chart at `y` of `D.peakSection_mul k x j` are smooth at `0`,
for every `x` and `j`. -/
theorem eventually_contDiffAt_reading_and_dbarReading_peakSection_mul [T2Space M]
    [I.Boundaryless] (hρ₀ : 0 < ρ₀) :
    ∀ᶠ k : ℕ in Filter.atTop, ∀ (x y : M) (j : ι),
      ContDiffAt ℝ ∞ (D.reading k y (D.peakSection_mul k x j)) 0 ∧
        ContDiffAt ℝ ∞ (D.dbarReading k y (D.peakSection_mul k x j)) 0 := by
  filter_upwards [Filter.eventually_ge_atTop k₀,
    eventually_tsupport_peakFunction_mul_subset_ball (ι := ι) hρ₀] with k hk hf x y j
  exact D.contDiffAt_reading_and_dbarReading_sectionOfReading hk x (hf j)
    (contDiff_peakFunction_mul k j).contDiffOn y

/-- On a Hausdorff boundaryless manifold with `ρ₀ > 0`, for large `k`, at every point `y`, the
reading and the `∂̄` reading in the chart at `y` of `D.affinePeakSection k x w` are smooth at `0`,
for every centre `x` and all coefficients `w`. -/
theorem eventually_contDiffAt_reading_and_dbarReading_affinePeakSection [T2Space M]
    [I.Boundaryless] (hρ₀ : 0 < ρ₀) :
    ∀ᶠ k : ℕ in Filter.atTop, ∀ (x y : M) (w : EuclideanSpace ℂ (Option ι)),
      ContDiffAt ℝ ∞ (D.reading k y (D.affinePeakSection k x w)) 0 ∧
        ContDiffAt ℝ ∞ (D.dbarReading k y (D.affinePeakSection k x w)) 0 := by
  filter_upwards [D.eventually_contDiffAt_reading_and_dbarReading_peakSection hρ₀,
    D.eventually_contDiffAt_reading_and_dbarReading_peakSection_mul hρ₀] with k h₀ h₁ x y w
  rw [affinePeakSection_eq_sum]
  refine D.contDiffAt_reading_and_dbarReading_sum fun j _ ↦
    D.contDiffAt_reading_and_dbarReading_const_smul ?_ (w j)
  cases j
  exacts [h₀ x y, h₁ x y _]

/-- On a Hausdorff boundaryless manifold with `ρ₀ > 0`, for large `k`, at every point `y`, the
reading and the `∂̄` reading in the chart at `y` of a finite sum of affine combinations of peak
sections `∑ x ∈ S, D.affinePeakSection k x (w x)` are smooth at `0`. -/
theorem eventually_contDiffAt_reading_and_dbarReading_sum_affinePeakSection [T2Space M]
    [I.Boundaryless] (hρ₀ : 0 < ρ₀) :
    ∀ᶠ k : ℕ in Filter.atTop, ∀ (S : Finset M) (w : M → EuclideanSpace ℂ (Option ι)) (y : M),
      ContDiffAt ℝ ∞ (D.reading k y (∑ x ∈ S, D.affinePeakSection k x (w x))) 0 ∧
        ContDiffAt ℝ ∞ (D.dbarReading k y (∑ x ∈ S, D.affinePeakSection k x (w x))) 0 := by
  filter_upwards [D.eventually_contDiffAt_reading_and_dbarReading_affinePeakSection hρ₀]
    with k h S w y
  exact D.contDiffAt_reading_and_dbarReading_sum fun x _ ↦ h x y (w x)

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

/-- **Gaussian decay of the affine combinations of peak sections, linear in the coefficients.**
Under the hypotheses of `SymplecticGeometry.RescaledUnitaryCharts.exists_jetNorm_peakSection_le`,
for every order `r` there are `C`, `N` and `c > 0` such that for large `k`, all points `x` and
`y` and all coefficients `w`, the `r`-jet norm at `y` of `D.affinePeakSection k x w` is at most
`C * ‖w‖ * (1 + d) ^ N * exp (-c * d ^ 2)`, for `d` the rescaled distance
`√(2π k) · d_g(x, y)`. -/
theorem exists_jetNorm_affinePeakSection_le [T2Space M] [I.Boundaryless]
    (hg : ∀ (x : M) (u w : TangentSpace I x), inner ℝ u w = σ.eval₂ x u (J x w))
    (hJ : σ.Compatible J) (hα : IsCircleConnectionForm α) (hρ₀ : 0 < ρ₀) (r : ℕ) :
    ∃ C : ℝ, ∃ N : ℕ, ∃ c > 0, ∀ᶠ k : ℕ in Filter.atTop,
      ∀ (x y : M) (w : EuclideanSpace ℂ (Option ι)),
        D.jetNorm k r (D.affinePeakSection k x w) y ≤
          C * ‖w‖ * (1 + rescaledDist I k x y) ^ N *
            Real.exp (-c * rescaledDist I k x y ^ 2) := by
  have hb : ∀ j : Option ι, ∃ C : ℝ, ∃ N : ℕ, ∃ c > 0, ∀ᶠ k : ℕ in Filter.atTop, ∀ p : M × M,
      D.jetNorm k r (j.elim (D.peakSection k p.1) (D.peakSection_mul k p.1)) p.2 ≤
        C * 1 * (1 + rescaledDist I k p.1 p.2) ^ N *
          Real.exp (-c * rescaledDist I k p.1 p.2 ^ 2) := by
    rintro (_ | j)
    · obtain ⟨C, N, c, hc, h⟩ := D.exists_jetNorm_peakSection_le hg hJ hα hρ₀ r
      exact ⟨C, N, c, hc, h.mono fun k h p ↦ by simpa using h p.1 p.2⟩
    · obtain ⟨C, N, c, hc, h⟩ := D.exists_jetNorm_peakSection_mul_le hg hJ hα hρ₀ r j
      exact ⟨C, N, c, hc, h.mono fun k h p ↦ by simpa using h p.1 p.2⟩
  obtain ⟨C, -, N, c, hc, h⟩ := Real.exists_forall_le_one_add_pow_mul_exp_neg_mul_sq
    (w := fun _ _ ↦ 1) (fun k (p : M × M) ↦ rescaledDist_nonneg I k p.1 p.2)
    (fun _ _ ↦ zero_le_one) hb
  refine ⟨C * Fintype.card (Option ι), N, c, hc, ?_⟩
  filter_upwards [h, D.eventually_contDiffAt_reading_and_dbarReading_peakSection hρ₀,
    D.eventually_contDiffAt_reading_and_dbarReading_peakSection_mul hρ₀] with k h h₀ h₁ x y w
  set W := (1 + rescaledDist I k x y) ^ N * Real.exp (-c * rescaledDist I k x y ^ 2)
  have hs : ∀ j : Option ι,
      ContDiffAt ℝ ∞ (D.reading k y (j.elim (D.peakSection k x) (D.peakSection_mul k x))) 0
    | none => (h₀ x y).1
    | some j => (h₁ x y j).1
  rw [affinePeakSection_eq_sum]
  refine (D.jetNorm_sum_le fun j _ ↦ ?_).trans ?_
  · rw [reading_smul]
    exact ((hs j).of_le (m := r) (by simp)).const_smul (w j)
  · calc ∑ j : Option ι, D.jetNorm k r
            (w j • j.elim (D.peakSection k x) (D.peakSection_mul k x)) y
        ≤ ∑ _j : Option ι, ‖w‖ * (C * W) := by
          refine Finset.sum_le_sum fun j _ ↦ ?_
          rw [jetNorm_smul]
          exact mul_le_mul (PiLp.norm_apply_le w j) ((h j (x, y)).trans_eq (by ring))
            (D.jetNorm_nonneg _ _ _ _) (norm_nonneg _)
      _ = C * Fintype.card (Option ι) * ‖w‖ * W := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ring
      _ = _ := by simp only [W]; ring

/-- **Gaussian decay of `∂̄` of the affine combinations of peak sections, linear in the
coefficients.** Under the hypotheses of
`SymplecticGeometry.RescaledUnitaryCharts.exists_jetNorm_peakSection_le`, for every order `r`
there are `C`, `N` and `c > 0` such that for large `k`, all points `x` and `y` and all
coefficients `w`, the `r`-jet norm at `y` of `∂̄` of `D.affinePeakSection k x w` is at most
`C * ‖w‖ * k ^ (-1 / 2) * (1 + d) ^ N * exp (-c * d ^ 2)`, for `d` the rescaled distance
`√(2π k) · d_g(x, y)`. -/
theorem exists_dbarJetNorm_affinePeakSection_le [T2Space M] [I.Boundaryless]
    (hg : ∀ (x : M) (u w : TangentSpace I x), inner ℝ u w = σ.eval₂ x u (J x w))
    (hJ : σ.Compatible J) (hα : IsCircleConnectionForm α) (hρ₀ : 0 < ρ₀) (r : ℕ) :
    ∃ C : ℝ, ∃ N : ℕ, ∃ c > 0, ∀ᶠ k : ℕ in Filter.atTop,
      ∀ (x y : M) (w : EuclideanSpace ℂ (Option ι)),
        D.dbarJetNorm k r (D.affinePeakSection k x w) y ≤
          C * ‖w‖ * (k : ℝ) ^ (-1 / 2 : ℝ) * (1 + rescaledDist I k x y) ^ N *
            Real.exp (-c * rescaledDist I k x y ^ 2) := by
  have hb : ∀ j : Option ι, ∃ C : ℝ, ∃ N : ℕ, ∃ c > 0, ∀ᶠ k : ℕ in Filter.atTop, ∀ p : M × M,
      D.dbarJetNorm k r (j.elim (D.peakSection k p.1) (D.peakSection_mul k p.1)) p.2 ≤
        C * (k : ℝ) ^ (-1 / 2 : ℝ) * (1 + rescaledDist I k p.1 p.2) ^ N *
          Real.exp (-c * rescaledDist I k p.1 p.2 ^ 2) := by
    rintro (_ | j)
    · obtain ⟨C, N, c, hc, h⟩ := D.exists_dbarJetNorm_peakSection_le hg hJ hα hρ₀ r
      exact ⟨C, N, c, hc, h.mono fun k h p ↦ by simpa using h p.1 p.2⟩
    · obtain ⟨C, N, c, hc, h⟩ := D.exists_dbarJetNorm_peakSection_mul_le hg hJ hα hρ₀ r j
      exact ⟨C, N, c, hc, h.mono fun k h p ↦ by simpa using h p.1 p.2⟩
  obtain ⟨C, -, N, c, hc, h⟩ := Real.exists_forall_le_one_add_pow_mul_exp_neg_mul_sq
    (w := fun _ (k : ℕ) ↦ (k : ℝ) ^ (-1 / 2 : ℝ))
    (fun k (p : M × M) ↦ rescaledDist_nonneg I k p.1 p.2) (fun _ _ ↦ by positivity) hb
  refine ⟨C * Fintype.card (Option ι), N, c, hc, ?_⟩
  filter_upwards [h, D.eventually_contDiffAt_reading_and_dbarReading_peakSection hρ₀,
    D.eventually_contDiffAt_reading_and_dbarReading_peakSection_mul hρ₀] with k h h₀ h₁ x y w
  set W := (1 + rescaledDist I k x y) ^ N * Real.exp (-c * rescaledDist I k x y ^ 2)
  have hs : ∀ j : Option ι,
      ContDiffAt ℝ ∞ (D.reading k y (j.elim (D.peakSection k x) (D.peakSection_mul k x))) 0 ∧
        ContDiffAt ℝ ∞
          (D.dbarReading k y (j.elim (D.peakSection k x) (D.peakSection_mul k x))) 0
    | none => h₀ x y
    | some j => h₁ x y j
  rw [affinePeakSection_eq_sum]
  refine (D.dbarJetNorm_sum_le (fun j _ ↦ ?_) (fun j _ ↦ ?_)).trans ?_
  · rw [reading_smul]
    exact ((hs j).1.eventually_differentiableAt (by exact_mod_cast le_top)).mono
      fun z hz ↦ hz.const_smul _
  · rw [funext (D.dbarReading_smul k y (w j) _)]
    exact ((hs j).2.of_le (m := r) (by simp)).const_smul (w j)
  · calc ∑ j : Option ι, D.dbarJetNorm k r
            (w j • j.elim (D.peakSection k x) (D.peakSection_mul k x)) y
        ≤ ∑ _j : Option ι, ‖w‖ * (C * (k : ℝ) ^ (-1 / 2 : ℝ) * W) := by
          refine Finset.sum_le_sum fun j _ ↦ ?_
          rw [dbarJetNorm_smul]
          exact mul_le_mul (PiLp.norm_apply_le w j) ((h j (x, y)).trans_eq (by ring))
            (D.dbarJetNorm_nonneg _ _ _ _) (norm_nonneg _)
      _ = C * Fintype.card (Option ι) * ‖w‖ * (k : ℝ) ^ (-1 / 2 : ℝ) * W := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ring
      _ = _ := by simp only [W]; ring

/-- **Jet norms of sums of affine combinations of peak sections.** Under the hypotheses of
`SymplecticGeometry.RescaledUnitaryCharts.exists_jetNorm_peakSection_le`, for every order `r`
there are `C ≥ 0`, `N` and `c > 0` such that for large `k`, every point `y`, every finite set `S`
of centres and all coefficients `w` with `‖w x‖ ≤ δ` on `S`, the `r`-jet norm at `y` of
`∑ x ∈ S, affinePeakSection k x (w x)` is at most `C * δ` times the sum over `S` of
`(1 + d) ^ N * exp (-c * d ^ 2)`, with `d = rescaledDist I k x y`. -/
theorem exists_jetNorm_sum_affinePeakSection_le_mul_sum [T2Space M] [I.Boundaryless]
    (hg : ∀ (x : M) (u w : TangentSpace I x), inner ℝ u w = σ.eval₂ x u (J x w))
    (hJ : σ.Compatible J) (hα : IsCircleConnectionForm α) (hρ₀ : 0 < ρ₀) (r : ℕ) :
    ∃ C ≥ (0 : ℝ), ∃ N : ℕ, ∃ c > 0, ∀ᶠ k : ℕ in Filter.atTop, ∀ (y : M) (S : Finset M) (δ : ℝ)
      (w : M → EuclideanSpace ℂ (Option ι)), (∀ x ∈ S, ‖w x‖ ≤ δ) →
        D.jetNorm k r (∑ x ∈ S, D.affinePeakSection k x (w x)) y ≤
          C * δ * ∑ x ∈ S, (1 + rescaledDist I k x y) ^ N *
            Real.exp (-c * rescaledDist I k x y ^ 2) := by
  obtain ⟨C, N, c, hc, h⟩ := D.exists_jetNorm_affinePeakSection_le hg hJ hα hρ₀ r
  refine ⟨max C 0, le_max_right _ _, N, c, hc, ?_⟩
  filter_upwards [h, D.eventually_contDiffAt_reading_and_dbarReading_affinePeakSection hρ₀]
    with k h hs y S δ w hw
  refine (D.jetNorm_sum_le fun x _ ↦ (hs x y (w x)).1.of_le (by exact_mod_cast le_top)).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun x hx ↦ (h x y (w x)).trans ?_
  have := rescaledDist_nonneg I k x y
  rw [mul_assoc _ ((1 + _) ^ _)]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  exact (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)).trans
    (mul_le_mul_of_nonneg_left (hw x hx) (le_max_right _ _))

/-- **`∂̄` jet norms of sums of affine combinations of peak sections.** Under the hypotheses of
`SymplecticGeometry.RescaledUnitaryCharts.exists_jetNorm_peakSection_le`, for every order `r`
there are `C ≥ 0`, `N` and `c > 0` such that for large `k`, every point `y`, every finite set `S`
of centres and all coefficients `w` with `‖w x‖ ≤ δ` on `S`, the `r`-jet norm at `y` of the `∂̄`
of `∑ x ∈ S, affinePeakSection k x (w x)` is at most `C * δ * k ^ (-1 / 2)` times the sum over
`S` of `(1 + d) ^ N * exp (-c * d ^ 2)`, with `d = rescaledDist I k x y`. -/
theorem exists_dbarJetNorm_sum_affinePeakSection_le_mul_sum [T2Space M] [I.Boundaryless]
    (hg : ∀ (x : M) (u w : TangentSpace I x), inner ℝ u w = σ.eval₂ x u (J x w))
    (hJ : σ.Compatible J) (hα : IsCircleConnectionForm α) (hρ₀ : 0 < ρ₀) (r : ℕ) :
    ∃ C ≥ (0 : ℝ), ∃ N : ℕ, ∃ c > 0, ∀ᶠ k : ℕ in Filter.atTop, ∀ (y : M) (S : Finset M) (δ : ℝ)
      (w : M → EuclideanSpace ℂ (Option ι)), (∀ x ∈ S, ‖w x‖ ≤ δ) →
        D.dbarJetNorm k r (∑ x ∈ S, D.affinePeakSection k x (w x)) y ≤
          C * δ * (k : ℝ) ^ (-1 / 2 : ℝ) * ∑ x ∈ S, (1 + rescaledDist I k x y) ^ N *
            Real.exp (-c * rescaledDist I k x y ^ 2) := by
  obtain ⟨C, N, c, hc, h⟩ := D.exists_dbarJetNorm_affinePeakSection_le hg hJ hα hρ₀ r
  refine ⟨max C 0, le_max_right _ _, N, c, hc, ?_⟩
  filter_upwards [h, D.eventually_contDiffAt_reading_and_dbarReading_affinePeakSection hρ₀]
    with k h hs y S δ w hw
  have hdiff : ∀ x ∈ S, ∀ᶠ z in 𝓝 0,
      DifferentiableAt ℝ (D.reading k y (D.affinePeakSection k x (w x))) z := fun x _ ↦
    (hs x y (w x)).1.eventually_differentiableAt (by exact_mod_cast le_top)
  refine (D.dbarJetNorm_sum_le hdiff fun x _ ↦
    (hs x y (w x)).2.of_le (by exact_mod_cast le_top)).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun x hx ↦ (h x y (w x)).trans ?_
  have := rescaledDist_nonneg I k x y
  rw [mul_assoc _ ((1 + _) ^ _)]
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (by positivity))
    (by positivity)
  exact (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)).trans
    (mul_le_mul_of_nonneg_left (hw x hx) (le_max_right _ _))

/-- **Sums of affine combinations of peak sections over a set of polynomial counting.** Under the
hypotheses of `SymplecticGeometry.RescaledUnitaryCharts.exists_jetNorm_peakSection_le`, for every
counting constant `C₀`, exponent `m` and order `r` there are `C` and `c > 0` such that for large
`k` the following holds. Let `y` be a point and `S` a finite set of centres such that for every
`ρ ≥ 0` at most `C₀ * (1 + ρ) ^ m` of them lie at rescaled distance at most `ρ` from `y`, and let
`w x` be coefficients of norm at most `δ` on `S`. Then for
`t = ∑ x ∈ S, affinePeakSection k x (w x)`:
* the `r`-jet norm of `t` at `y` is at most `C * δ`;
* the `r`-jet norm of `∂̄ t` at `y` is at most `C * δ * k ^ (-1 / 2)`;
* for every `R ≥ 0`, the `r`-jet norm at `y` of the part of the sum over the centres at rescaled
  distance at least `R` from `y` is at most `C * δ * exp (-c * R ^ 2)`. -/
theorem exists_jetNorm_sum_affinePeakSection_le [T2Space M] [I.Boundaryless]
    (hg : ∀ (x : M) (u w : TangentSpace I x), inner ℝ u w = σ.eval₂ x u (J x w))
    (hJ : σ.Compatible J) (hα : IsCircleConnectionForm α) (hρ₀ : 0 < ρ₀) (C₀ : ℝ) (m r : ℕ) :
    ∃ C : ℝ, ∃ c > 0, ∀ᶠ k : ℕ in Filter.atTop, ∀ (y : M) (S : Finset M),
      (∀ ρ : ℝ, 0 ≤ ρ → ((S.filter fun x ↦ rescaledDist I k x y ≤ ρ).card : ℝ) ≤
        C₀ * (1 + ρ) ^ m) →
      ∀ (δ : ℝ) (w : M → EuclideanSpace ℂ (Option ι)), 0 ≤ δ → (∀ x ∈ S, ‖w x‖ ≤ δ) →
        D.jetNorm k r (∑ x ∈ S, D.affinePeakSection k x (w x)) y ≤ C * δ ∧
        D.dbarJetNorm k r (∑ x ∈ S, D.affinePeakSection k x (w x)) y ≤
          C * δ * (k : ℝ) ^ (-1 / 2 : ℝ) ∧
        ∀ R : ℝ, 0 ≤ R →
          D.jetNorm k r (∑ x ∈ S with R ≤ rescaledDist I k x y,
            D.affinePeakSection k x (w x)) y ≤ C * δ * Real.exp (-c * R ^ 2) := by
  obtain ⟨C₁, hC₁, N₁, c₁, hc₁, h₁⟩ :=
    D.exists_jetNorm_sum_affinePeakSection_le_mul_sum hg hJ hα hρ₀ r
  obtain ⟨C₂, hC₂, N₂, c₂, hc₂, h₂⟩ :=
    D.exists_dbarJetNorm_sum_affinePeakSection_le_mul_sum hg hJ hα hρ₀ r
  obtain ⟨K₁, hK₁⟩ := exists_sum_one_add_rescaledDist_pow_mul_exp_le (M := M) I C₀ m N₁ hc₁
  obtain ⟨K₂, hK₂⟩ := exists_sum_one_add_rescaledDist_pow_mul_exp_le (M := M) I C₀ m N₂ hc₂
  refine ⟨max (C₁ * K₁) (C₂ * K₂), c₁ / 2, half_pos hc₁, ?_⟩
  filter_upwards [h₁, h₂] with k h₁ h₂ y S hS δ w hδ hw
  obtain ⟨e₁, e₃⟩ := hK₁ k y S hS
  refine ⟨?_, ?_, fun R hR ↦ ?_⟩
  · calc _ ≤ C₁ * δ * K₁ := (h₁ y S δ w hw).trans (by gcongr)
      _ = C₁ * K₁ * δ := by ring
      _ ≤ _ := by gcongr; exact le_max_left _ _
  · calc _ ≤ C₂ * δ * (k : ℝ) ^ (-1 / 2 : ℝ) * K₂ :=
          (h₂ y S δ w hw).trans (by gcongr; exact (hK₂ k y S hS).1)
      _ = C₂ * K₂ * δ * (k : ℝ) ^ (-1 / 2 : ℝ) := by ring
      _ ≤ _ := by gcongr; exact le_max_right _ _
  · calc _ ≤ C₁ * δ * (K₁ * Real.exp (-(c₁ / 2) * R ^ 2)) :=
          (h₁ y _ δ w fun x hx ↦ hw x (Finset.mem_filter.1 hx).1).trans (by gcongr; exact e₃ R hR)
      _ = C₁ * K₁ * δ * Real.exp (-(c₁ / 2) * R ^ 2) := by ring
      _ ≤ _ := by gcongr; exact le_max_left _ _

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

/-- **Sums of peak sections are asymptotically holomorphic.** Let `M` be Hausdorff and
boundaryless, with a metric whose inner product is `⟪u, w⟫ = σ(u, J w)`. For finite sets `S k`
of centres with at most `C₀ * (1 + ρ) ^ m` points at rescaled distance at most `ρ` from any
point, and coefficients `w k x` of norm at most `δ` on `S k`, both for large `k`, the sequence of
sections
`Σ_{x ∈ S k} D.affinePeakSection k x (w k x)` is asymptotically holomorphic. -/
theorem isAsymptoticallyHolomorphic_sum_affinePeakSection [T2Space M] [I.Boundaryless]
    (hg : ∀ (x : M) (u w : TangentSpace I x), inner ℝ u w = σ.eval₂ x u (J x w))
    (hJ : σ.Compatible J) (hα : IsCircleConnectionForm α) (hρ₀ : 0 < ρ₀) {C₀ δ : ℝ} {m : ℕ}
    (S : ℕ → Finset M) (w : ℕ → M → EuclideanSpace ℂ (Option ι)) (hδ : 0 ≤ δ)
    (hS : ∀ᶠ k in Filter.atTop, ∀ (y : M) (ρ : ℝ), 0 ≤ ρ →
      (((S k).filter fun x ↦ rescaledDist I k x y ≤ ρ).card : ℝ) ≤ C₀ * (1 + ρ) ^ m)
    (hw : ∀ᶠ k in Filter.atTop, ∀ x ∈ S k, ‖w k x‖ ≤ δ) :
    D.IsAsymptoticallyHolomorphic fun k ↦ ∑ x ∈ S k, D.affinePeakSection k x (w k x) := by
  refine (D.isAsymptoticallyHolomorphic_def _).2
    ⟨(D.eventually_contDiffAt_reading_and_dbarReading_sum_affinePeakSection hρ₀).mono
      fun k h x ↦ h (S k) (w k) x, fun r ↦ ?_⟩
  obtain ⟨C, _, -, hsum⟩ := D.exists_jetNorm_sum_affinePeakSection_le hg hJ hα hρ₀ C₀ m r
  refine ⟨C * δ, ?_⟩
  filter_upwards [hsum, hS, hw] with k hk hSk hwk x
  obtain ⟨h1, h2, -⟩ := hk x (S k) (hSk x) δ (w k) hδ hwk
  exact ⟨h1, h2⟩

end RiemannianEDist

end RescaledUnitaryCharts

end SymplecticGeometry

end
