/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Topology
public import Mathlib.Geometry.Manifold.MFDeriv.Defs
import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Differential
import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Evaluation
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Geometry.Manifold.MFDeriv.Basic

/-!
# Maps close to an injective immersion are injective

Let `M` be a compact boundaryless manifold modelled on a finite-dimensional real space and `N` a
Hausdorff manifold. If a `C^n` map `g : M → N`, with `1 ≤ n`, is injective and has injective
differential at every point, then every map close enough to `g` in Tau Ceti's weak Whitney
topology is injective (`ContMDiffMap.eventually_injective`).

The proof has a local and a global step.

* Near a point `x₀` where the differential of `g` is injective, the chart derivative `A` of `g`
  at `x₀` satisfies `‖v‖ ≤ K * ‖A v‖`. If the chart derivative of a map stays within
  `(2 * K)⁻¹` of `A` on a ball, then by the mean value inequality the map minus `A` is
  `(2 * K)⁻¹`-Lipschitz there, so the map is injective on the ball. Chart derivatives are
  jointly continuous in the map and the point, so one ball serves all maps near `g`
  (`ContMDiffMap.exists_mem_nhds_eventually_injOn`).
* Off the diagonal, `g x ≠ g y`, and evaluation is jointly continuous, so nearby maps still
  separate nearby pairs. Compactness of `M × M`
  (`IsCompact.eventually_forall_of_forall_eventually`) glues the two estimates.

This is the openness of injective immersions of a compact manifold in the `C^1` topology, as in
M. Hirsch, *Differential Topology*, Chapter 2, §1.

## References

* [M. W. Hirsch, *Differential Topology*][Hirsch1976], Chapter 2, §1
-/

public section

open Set Filter Topology Function
open scoped Manifold TauCeti.ManifoldWeakWhitney

namespace ContMDiffMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {n : WithTop ℕ∞}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I n M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J n N]

/-- If a `C^n` map `g`, with `1 ≤ n`, has injective differential at `x₀`, then there is a
neighbourhood `U` of `x₀` on which every map close enough to `g` in the weak Whitney topology is
injective. -/
theorem exists_mem_nhds_eventually_injOn (hn : 1 ≤ n) {g : C^n⟮I, M; J, N⟯} {x₀ : M}
    (hg : Injective (mfderiv I J g x₀)) :
    ∃ U ∈ 𝓝 x₀, ∀ᶠ f : C^n⟮I, M; J, N⟯ in 𝓝 g, InjOn f U := by
  set φ := extChartAt I x₀
  set ψ := extChartAt J (g x₀)
  have hn0 : n ≠ 0 := (zero_lt_one.trans_le hn).ne'
  have hw₀ : φ x₀ ∈ φ.target := mem_extChartAt_target x₀
  have hφo : IsOpen φ.target := isOpen_extChartAt_target x₀
  have hgw₀ : g (φ.symm (φ x₀)) ∈ ψ.source := by
    rw [extChartAt_to_inv]
    exact mem_extChartAt_source (g x₀)
  -- The chart derivative of `g` at `x₀` is its differential, which is bounded below.
  set A := fderivWithin ℝ (ψ ∘ g ∘ φ.symm) φ.target (φ x₀)
  have hA : Injective A := by
    have h := (g.contMDiff.mdifferentiableAt (x := x₀) hn0).mfderiv_abuse
    rw [I.range_eq_univ, fderivWithin_univ, writtenInExtChartAt] at h
    rw [show A = _ from fderivWithin_of_isOpen hφo hw₀, ← h]
    exact hg
  obtain ⟨K, hK0, hK⟩ :=
    (A : E →ₗ[ℝ] F).exists_antilipschitzWith (LinearMap.ker_eq_bot.mpr hA)
  have hKA (v : E) : ‖v‖ ≤ K * ‖A v‖ := A.bound_of_antilipschitz hK v
  have hc : (0 : ℝ) < (2 * (K : ℝ))⁻¹ := by positivity
  -- Nearby maps at nearby chart points stay in the target chart, with derivatives near `A`.
  have hev : ∀ᶠ p : C^n⟮I, M; J, N⟯ × E in 𝓝 g ×ˢ 𝓝 (φ x₀),
      p.1 (φ.symm p.2) ∈ ψ.source ∧ p.2 ∈ φ.target ∧
        fderivWithin ℝ (ψ ∘ p.1 ∘ φ.symm) φ.target p.2 ∈ Metric.ball A (2 * (K : ℝ))⁻¹ := by
    rw [← hφo.nhdsWithin_eq hw₀]
    filter_upwards [eventually_mem_extChartAt_source hw₀ hgw₀,
      prod_mem_prod univ_mem self_mem_nhdsWithin,
      (TauCeti.tendsto_fderivWithin_extChartAt hn hw₀ hgw₀).eventually
        (Metric.ball_mem_nhds A hc)] with p h₁ h₂ h₃
    exact ⟨h₁, h₂.2, h₃⟩
  obtain ⟨P, hP, Q, hQ, hPQ⟩ := eventually_prod_iff.mp hev
  obtain ⟨r, hr, hrQ⟩ := Metric.eventually_nhds_iff_ball.mp hQ
  refine ⟨φ.source ∩ φ ⁻¹' Metric.ball (φ x₀) r,
    inter_mem (extChartAt_source_mem_nhds x₀)
      ((continuousAt_extChartAt x₀).preimage_mem_nhds (Metric.ball_mem_nhds _ hr)), ?_⟩
  filter_upwards [hP] with f hf a ha b hb hab
  have hfs (w) (hw : w ∈ Metric.ball (φ x₀) r) := (hPQ hf (hrQ w hw)).1
  have hft (w) (hw : w ∈ Metric.ball (φ x₀) r) := (hPQ hf (hrQ w hw)).2.1
  have hfd (w) (hw : w ∈ Metric.ball (φ x₀) r) := (hPQ hf (hrQ w hw)).2.2
  -- On the ball, the chart representative of `f` minus `A` is `(2 * K)⁻¹`-Lipschitz.
  have hD (w) (hw : w ∈ Metric.ball (φ x₀) r) : DifferentiableAt ℝ (ψ ∘ f ∘ φ.symm) w :=
    ((f.contDiffWithinAt_extChartAt (hft w hw) (hfs w hw)).contDiffAt
      (hφo.mem_nhds (hft w hw))).differentiableAt hn0
  have hB (w) (hw : w ∈ Metric.ball (φ x₀) r) :
      ‖fderiv ℝ (ψ ∘ f ∘ φ.symm) w - A‖ ≤ (2 * (K : ℝ))⁻¹ := by
    rw [← fderivWithin_of_isOpen hφo (hft w hw), ← dist_eq_norm]
    exact (Metric.mem_ball.mp (hfd w hw)).le
  have hmv := (convex_ball (φ x₀) r).norm_image_sub_le_of_norm_fderiv_le' hD hB ha.2 hb.2
  have hfab : (ψ ∘ f ∘ φ.symm) (φ b) = (ψ ∘ f ∘ φ.symm) (φ a) := by
    simp only [Function.comp_apply, φ.left_inv ha.1, φ.left_inv hb.1, hab]
  rw [hfab, sub_self, zero_sub, norm_neg] at hmv
  have hle := (hKA (φ b - φ a)).trans (mul_le_mul_of_nonneg_left hmv K.coe_nonneg)
  have hK0' : (K : ℝ) ≠ 0 := (NNReal.coe_pos.mpr hK0).ne'
  have h0 : ‖φ b - φ a‖ = 0 := by
    have : (K : ℝ) * ((2 * (K : ℝ))⁻¹ * ‖φ b - φ a‖) = ‖φ b - φ a‖ / 2 := by
      field_simp [hK0']
    linarith [norm_nonneg (φ b - φ a)]
  exact φ.injOn ha.1 hb.1 (sub_eq_zero.mp (norm_eq_zero.mp h0)).symm

/-- On a compact boundaryless manifold modelled on a finite-dimensional real space, maps close
enough, in the weak Whitney topology, to an injective `C^n` map `g`, with `1 ≤ n`, whose
differential is injective at every point, are injective. -/
theorem eventually_injective [CompactSpace M] [T2Space N] (hn : 1 ≤ n) {g : C^n⟮I, M; J, N⟯}
    (hg : Injective g) (hg' : ∀ x, Injective (mfderiv I J g x)) :
    ∀ᶠ f : C^n⟮I, M; J, N⟯ in 𝓝 g, Injective f := by
  have key : ∀ q ∈ (univ : Set (M × M)), ∀ᶠ z : C^n⟮I, M; J, N⟯ × (M × M) in 𝓝 (g, q),
      z.1 z.2.1 = z.1 z.2.2 → z.2.1 = z.2.2 := by
    rintro ⟨x, y⟩ -
    rcases eq_or_ne x y with rfl | hxy
    · obtain ⟨U, hU, hfU⟩ := exists_mem_nhds_eventually_injOn hn (hg' x)
      rw [nhds_prod_eq]
      filter_upwards [prod_mem_prod hfU (prod_mem_nhds hU hU)] with z hz
      exact fun h ↦ hz.1 hz.2.1 hz.2.2 h
    · have he (i : M × M → M) (hi : Continuous i) :
          Continuous fun z : C^n⟮I, M; J, N⟯ × (M × M) ↦ z.1 (i z.2) :=
        continuous_eval_manifoldWeakWhitney.comp (continuous_fst.prodMk (hi.comp continuous_snd))
      filter_upwards [((he _ continuous_fst).continuousAt.ne_iff_eventually_ne
        (he _ continuous_snd).continuousAt).mp (hg.ne hxy)] with z hz h
      exact absurd h hz
  filter_upwards [isCompact_univ.eventually_forall_of_forall_eventually
    (P := fun (f : C^n⟮I, M; J, N⟯) (q : M × M) ↦ f q.1 = f q.2 → q.1 = q.2) key] with f hf a b hab
  exact hf (a, b) trivial hab

end ContMDiffMap

end
