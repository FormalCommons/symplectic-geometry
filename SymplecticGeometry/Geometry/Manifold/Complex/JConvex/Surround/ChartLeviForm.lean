/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.Complex.LeviForm
public import TauCeti.Analysis.Complex.Wirtinger.Basic
public import SymplecticGeometry.Geometry.Manifold.Complex.JConvex.Surround.Shape

import SymplecticGeometry.Analysis.Complex.LeviForm.CompSymm
import SymplecticGeometry.Geometry.Manifold.MFDeriv.Chart
import TauCeti.Analysis.Calculus.FDeriv.Equiv

/-!
# Margins carried to the manifold by the chart along a disc

Let `Φ` be a chart along an attached disc as `SymplecticGeometry.exists_modelChart` gives it:
near every point `p₀` of the core `ι₀ (ℝᵏ)` of the model space `ℂᵏ × ℂᵐ`, its reading `e` in the
chart of `M` at `Φ p₀` has `‖∂̄e p‖ ≤ C √(t p) ^ N` and `‖D(∂̄e) p‖ ≤ C √(t p) ^ (N - 1)`, where
`t p = (shape p).2`. This file shows that such a chart carries strict plurisubharmonicity with a
margin to `M`: on the handles `{t ≤ γ², s ≤ (1 + γ)²}` with `γ` small, a function `u` whose Levi
form is at least `c γ ^ N₀ max ‖D²u‖ ‖Du‖ ‖v‖²` has `u ∘ Φ⁻¹` strictly plurisubharmonic on `M`,
as soon as `N₀ + 2 ≤ N`.

The handles shrink to the compact disc `ι₀ (closedBall 0 1)` as `γ → 0`
(`SymplecticGeometry.iInter_setOf_shape_le_subset`), so for small `γ` they lie in finitely many
of the neighbourhoods where the bounds hold, which gives uniform constants there. Tau Ceti's
comparison of Levi forms through a chart that is not holomorphic,
`TauCeti.le_re_leviForm_comp_symm`, then bounds the loss by a constant times `γ ^ (N₀ + 1)` times
`max ‖D²u‖ ‖Du‖ ‖v‖²`, which is at most half the margin for small `γ`. Strict
plurisubharmonicity on `M` is read in the chart at `Φ p₀` by Tau Ceti's
`TauCeti.isManifoldStrictlyPlurisubharmonicAt_iff_of_mem_maximalAtlas`.

## Main results

* `SymplecticGeometry.isCompact_setOf_shape_le`: the sets `{t ≤ a, s ≤ b}` are compact.
* `SymplecticGeometry.iInter_setOf_shape_le_subset`: the handles `{t ≤ γ², s ≤ (1 + γ)²}`,
  `0 < γ < 1`, meet in the model disc `ι₀ (closedBall 0 1)`.
* `SymplecticGeometry.isManifoldStrictlyPlurisubharmonicAt_comp_modelChart_symm`: the margin
  carried to `M` by the chart.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  (8.1) in the proof of Theorem 8.5 and Theorem 4.2 (iv): a function on the model handle that is
  `J`-convex with a margin stays `J`-convex for a structure close to the standard one.
-/

public section

open Filter Manifold Metric Set Topology TauCeti
open scoped ContDiff

namespace SymplecticGeometry

variable {k m : ℕ}

section Handle

/-- The squared norm of a point of `ℂᵏ` is the sum of the squares of the real and imaginary
parts of its coordinates. -/
private theorem norm_sq_eq_sum_re_sq_add_im_sq (z : EuclideanSpace ℂ (Fin k)) :
    ‖z‖ ^ 2 = ∑ j, ((z j).re ^ 2 + (z j).im ^ 2) := by
  rw [EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

/-- The sets `{p | t p ≤ a ∧ s p ≤ b}` of the shape coordinates `(s, t) = shape p` are compact. -/
theorem isCompact_setOf_shape_le (a b : ℝ) :
    IsCompact {p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m) |
      (shape p).2 ≤ a ∧ (shape p).1 ≤ b} := by
  have hc := (contDiff_shape (k := k) (m := m) (n := 0)).continuous
  refine Metric.isCompact_of_isClosed_isBounded
    ((isClosed_le (continuous_snd.comp hc) continuous_const).inter
      (isClosed_le (continuous_fst.comp hc) continuous_const))
    ((isBounded_closedBall (x := 0) (r := √(|a| + |b|))).subset fun p hp ↦ ?_)
  obtain ⟨ha, hb⟩ := hp
  have hs := shape_fst_nonneg p
  have ht := shape_snd_nonneg p
  rw [shape_fst] at hs hb
  rw [shape_snd] at ht ha
  rw [mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff]
  constructor <;> refine Real.le_sqrt_of_sq_le ?_
  · rw [norm_sq_eq_sum_re_sq_add_im_sq, Finset.sum_add_distrib]
    have : 0 ≤ ∑ j, (p.1 j).im ^ 2 := by positivity
    have : 0 ≤ ‖p.2‖ ^ 2 := by positivity
    linarith [le_abs_self a, le_abs_self b]
  · have : 0 ≤ ∑ j, (p.1 j).im ^ 2 := by positivity
    linarith [le_abs_self a, le_abs_self b, abs_nonneg a, abs_nonneg b]

/-- The handles `{p | t p ≤ γ ^ 2 ∧ s p ≤ (1 + γ) ^ 2}` for `0 < γ < 1` meet in the model disc
`ι₀ (closedBall 0 1)`. -/
theorem iInter_setOf_shape_le_subset :
    ⋂ γ : Ioo (0 : ℝ) 1, {p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m) |
      (shape p).2 ≤ (γ : ℝ) ^ 2 ∧ (shape p).1 ≤ (1 + (γ : ℝ)) ^ 2} ⊆
      modelDisc k m '' closedBall 0 1 := by
  intro p hp
  simp only [mem_iInter, mem_ofPred_eq, Subtype.forall, mem_Ioo] at hp
  have ht : (shape p).2 ≤ 0 := by
    refine le_of_forall_pos_lt_add fun ε hε ↦ ?_
    obtain ⟨γ, hγ0, hγ1, hγε⟩ : ∃ γ : ℝ, 0 < γ ∧ γ < 1 ∧ γ ^ 2 < ε :=
      ⟨min (1 / 2) (√ε / 2), by positivity, by
        exact (min_le_left _ _).trans_lt (by norm_num), by
        have h1 : min (1 / 2) (√ε / 2) ≤ √ε / 2 := min_le_right _ _
        calc min (1 / 2) (√ε / 2) ^ 2 ≤ (√ε / 2) ^ 2 := by gcongr
          _ = ε / 4 := by rw [div_pow, Real.sq_sqrt hε.le]; ring
          _ < ε := by linarith⟩
    linarith [(hp γ ⟨hγ0, hγ1⟩).1]
  have hs : (shape p).1 ≤ 1 := by
    refine le_of_forall_pos_lt_add fun ε hε ↦ ?_
    set γ := min (1 / 2) (ε / 4)
    have hγ0 : 0 < γ := by positivity
    have hγ1 : γ ≤ 1 / 2 := min_le_left _ _
    have hγε : γ ≤ ε / 4 := min_le_right _ _
    have := (hp γ ⟨hγ0, by linarith⟩).2
    nlinarith
  rw [shape_snd] at ht
  have him : ∀ j, (p.1 j).im = 0 := fun j ↦ by
    have : (p.1 j).im ^ 2 ≤ ∑ i, (p.1 i).im ^ 2 :=
      Finset.single_le_sum (f := fun i ↦ (p.1 i).im ^ 2) (fun _ _ ↦ by positivity)
        (Finset.mem_univ j)
    have : 0 ≤ ‖p.2‖ ^ 2 := by positivity
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (by nlinarith [sq_nonneg (p.1 j).im])
  have h2 : p.2 = 0 := by
    have : 0 ≤ ∑ i, (p.1 i).im ^ 2 := by positivity
    exact norm_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1
      (le_antisymm (by linarith) (by positivity)))
  refine ⟨WithLp.toLp 2 fun j ↦ (p.1 j).re, ?_, ?_⟩
  · rw [mem_closedBall, dist_zero_right]
    refine (sq_le_one_iff₀ (norm_nonneg _)).1 ?_
    rw [EuclideanSpace.norm_sq_eq]
    simpa [shape_fst] using hs
  · ext j
    · simp only [modelDisc_apply_fst_apply]
      exact Complex.ext (by simp) (by simp [him j])
    · simp [h2]

end Handle
section Chart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

/-- The reading of a map from the model space in the chart of `M` at the image of `x` is the
composite of the partial homeomorphism and that chart. -/
private theorem writtenInExtChartAt_eq_coe_trans
    (Φ : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m))
      𝓘(ℝ, E) (EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) M ∞)
    (x : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) :
    writtenInExtChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) 𝓘(ℝ, E) x Φ =
      ⇑(Φ.toOpenPartialHomeomorph.trans (chartAt E (Φ x))) := by
  rw [writtenInExtChartAt_model_space_left, OpenPartialHomeomorph.coe_trans, extChartAt_coe,
    modelWithCornersSelf_coe, Function.id_comp, PartialDiffeomorph.toFun'_toOpenPartialHomeomorph]

/-- The composite of a partial diffeomorphism from the model space with a chart of `M` is smooth
on its source, and so is its inverse on its target. -/
private theorem contDiffOn_trans_chartAt [IsManifold 𝓘(ℝ, E) ∞ M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m))
      𝓘(ℝ, E) (EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) M ∞) (y : M) :
    ContDiffOn ℝ ∞ (Φ.toOpenPartialHomeomorph.trans (chartAt E y))
        (Φ.toOpenPartialHomeomorph.trans (chartAt E y)).source ∧
      ContDiffOn ℝ ∞ (Φ.toOpenPartialHomeomorph.trans (chartAt E y)).symm
        (Φ.toOpenPartialHomeomorph.trans (chartAt E y)).target := by
  constructor
  · refine contMDiffOn_iff_contDiffOn.1 ?_
    rw [OpenPartialHomeomorph.coe_trans, OpenPartialHomeomorph.trans_source]
    exact (contMDiffOn_chart (I := 𝓘(ℝ, E))).comp (Φ.contMDiffOn.mono inter_subset_left)
      fun _ hp ↦ hp.2
  · refine contMDiffOn_iff_contDiffOn.1 ?_
    rw [OpenPartialHomeomorph.coe_trans_symm, OpenPartialHomeomorph.trans_target]
    exact Φ.symm.contMDiffOn.comp ((contMDiffOn_chart_symm (I := 𝓘(ℝ, E))).mono
      inter_subset_left) fun _ hz ↦ hz.2

/-- **Margins carried to the manifold by the chart along a disc.** Let `Φ` be a smooth partial
diffeomorphism from the model space `ℂᵏ × ℂᵐ` to the complex manifold `M` that is holomorphic to
order `N` along the core, as `SymplecticGeometry.exists_modelChart` gives it: every point `p₀` of
the core has a neighbourhood `U` in the source of `Φ`, mapped into the source of the chart at
`Φ p₀`, and a constant `C` with `‖∂̄e p‖ ≤ C √(t p) ^ N` and `‖D(∂̄e) p‖ ≤ C √(t p) ^ (N - 1)` on
`U`, for the reading `e` of `Φ` in that chart. Let `c > 0` and `N₀ + 2 ≤ N`. Then there is
`γ₀ ∈ (0, 1]` such that, for `0 < γ < γ₀`, the handle `{p | t p ≤ γ² ∧ s p ≤ (1 + γ)²}` lies in
the source of `Φ`, and for every `C²` function `u` on the model space that is strictly
plurisubharmonic at each point `p` of the handle, with
`c γ ^ N₀ max ‖D²u p‖ ‖Du p‖ ‖v‖² ≤ Re L(u)(p)(v, v)` for all `v`, the function `u ∘ Φ⁻¹` is
strictly plurisubharmonic at `Φ p` for every `p` in the handle. Here `(s, t) = shape p`. -/
theorem isManifoldStrictlyPlurisubharmonicAt_comp_modelChart_symm [IsManifold 𝓘(ℂ, E) 2 M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {N : ℕ}
    (Φ : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m))
      𝓘(ℝ, E) (EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) M ∞)
    (hΦ : ∀ p₀ ∈ range (modelDisc k m), ∃ U ∈ 𝓝 p₀,
      U ⊆ Φ.source ∧ U ⊆ Φ ⁻¹' (chartAt E (Φ p₀)).source ∧ ∃ C, ∀ p ∈ U,
        ‖conjWirtingerDeriv (writtenInExtChartAt
          𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) 𝓘(ℝ, E) p₀ Φ) p‖ ≤
          C * √(shape p).2 ^ N ∧
        ‖fderiv ℝ (conjWirtingerDeriv (writtenInExtChartAt
          𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) 𝓘(ℝ, E) p₀ Φ)) p‖ ≤
          C * √(shape p).2 ^ (N - 1))
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
  set V := EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)
  set e : V → OpenPartialHomeomorph V E :=
    fun x ↦ Φ.toOpenPartialHomeomorph.trans (chartAt E (Φ x))
  -- The neighbourhoods of the bounds, and closed balls inside them.
  choose! U hU hUs hUc C hC using hΦ
  have hball : ∀ x ∈ range (modelDisc k m), ∃ r > 0, closedBall x r ⊆ U x := fun x hx ↦
    nhds_basis_closedBall.mem_iff.1 (hU x hx)
  choose! r hr hrU using hball
  -- Finitely many balls cover the compact disc `ι₀ (closedBall 0 1)`.
  set K := modelDisc k m '' closedBall 0 1
  have hK : IsCompact K := (isCompact_closedBall 0 1).image (modelDisc k m).continuous
  have hKr : K ⊆ range (modelDisc k m) := image_subset_range _ _
  obtain ⟨t, htK, hKt⟩ := hK.elim_nhds_subcover (fun x ↦ ball x (r x))
    fun x hx ↦ ball_mem_nhds x (hr x (hKr hx))
  -- Uniform bounds on the derivatives of the charts on the closed balls.
  have hbd : ∀ x ∈ t, ∃ B, ∀ q ∈ closedBall x (r x),
      ‖(fderiv ℝ (e x) q, fderiv ℝ (e x).symm (e x q), fderiv ℝ (fderiv ℝ (e x)) q)‖ ≤ B := by
    intro x hx
    have hsub : closedBall x (r x) ⊆ (e x).source := fun q hq ↦ by
      have := hrU x (hKr (htK x hx)) hq
      exact ⟨hUs x (hKr (htK x hx)) this, hUc x (hKr (htK x hx)) this⟩
    obtain ⟨hs, hss⟩ := contDiffOn_trans_chartAt Φ (Φ x)
    have h1 := hs.continuousOn_fderiv_of_isOpen (e x).open_source (by simp)
    have h2 := (hs.fderiv_of_isOpen (e x).open_source (m := 1)
      (by simp)).continuousOn_fderiv_of_isOpen
      (e x).open_source le_rfl
    have h3 := (hss.continuousOn_fderiv_of_isOpen (e x).open_target (by simp)).comp
      (e x).continuousOn_toFun fun _ hq ↦ (e x).map_source hq
    exact (isCompact_closedBall x (r x)).exists_bound_of_continuousOn
      (((h1.prodMk (h3.prodMk h2))).mono hsub)
  choose! B hB using hbd
  set Kb := ∑ x ∈ t, |B x|
  set Cc := ∑ x ∈ t, |C x|
  have hBK : ∀ x ∈ t, B x ≤ Kb := fun x hx ↦
    (le_abs_self _).trans (Finset.single_le_sum (f := fun x ↦ |B x|) (fun _ _ ↦ abs_nonneg _) hx)
  have hCC : ∀ x ∈ t, C x ≤ Cc := fun x hx ↦
    (le_abs_self _).trans (Finset.single_le_sum (f := fun x ↦ |C x|) (fun _ _ ↦ abs_nonneg _) hx)
  have hCc : 0 ≤ Cc := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  obtain ⟨C₀, hC₀⟩ := le_re_leviForm_comp_symm (V := V) (W := E) Kb
  -- The handles lie in the union of the balls for small `γ`.
  have hmono : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → {p : V | (shape p).2 ≤ a ^ 2 ∧
      (shape p).1 ≤ (1 + a) ^ 2} ⊆ {p : V | (shape p).2 ≤ b ^ 2 ∧ (shape p).1 ≤ (1 + b) ^ 2} :=
    fun ha hab p hp ↦ ⟨hp.1.trans (by gcongr), hp.2.trans (by gcongr)⟩
  have : Nonempty (Ioo (0 : ℝ) 1) := ⟨⟨1 / 2, by norm_num, by norm_num⟩⟩
  obtain ⟨⟨γ₁, hγ₁⟩, hγ₁W⟩ := exists_subset_nhds_of_isCompact'
    (V := fun γ : Ioo (0 : ℝ) 1 ↦ {p : V | (shape p).2 ≤ (γ : ℝ) ^ 2 ∧
      (shape p).1 ≤ (1 + (γ : ℝ)) ^ 2})
    (fun a b ↦ ⟨⟨min a b, lt_min a.property.1 b.property.1,
        (min_le_left _ _).trans_lt a.property.2⟩,
      hmono (le_min a.property.1.le b.property.1.le) (min_le_left _ _),
      hmono (le_min a.property.1.le b.property.1.le) (min_le_right _ _)⟩)
    (fun _ ↦ isCompact_setOf_shape_le _ _) (fun _ ↦ (isCompact_setOf_shape_le _ _).isClosed)
    (U := ⋃ x ∈ t, ball x (r x))
    (mem_nhdsSet_iff_forall.2 fun p hp ↦ (isOpen_biUnion fun x _ ↦ isOpen_ball).mem_nhds
      (hKt (iInter_setOf_shape_le_subset hp)))
  set C₀' := max C₀ 0
  set γ₀ := min γ₁ (c / (2 * (3 * C₀' * Cc + 1)))
  have hden : 0 < 2 * (3 * C₀' * Cc + 1) := by positivity
  have hγ₀ : 0 < γ₀ := lt_min hγ₁.1 (div_pos hc hden)
  refine ⟨γ₀, ⟨hγ₀, (min_le_left _ _).trans hγ₁.2.le⟩, fun γ hγ ↦ ?_⟩
  have hγγ₁ : γ ≤ γ₁ := hγ.2.le.trans (min_le_left _ _)
  have hγ1 : γ ≤ 1 := hγγ₁.trans hγ₁.2.le
  -- Each point of the handle lies in one of the balls.
  have hcov : ∀ p : V, (shape p).2 ≤ γ ^ 2 → (shape p).1 ≤ (1 + γ) ^ 2 →
      ∃ x ∈ t, p ∈ closedBall x (r x) := fun p ht hs ↦ by
    have := hγ₁W ⟨ht.trans (by gcongr; exact hγ.1.le),
      hs.trans (by gcongr; linarith [hγ.1])⟩
    obtain ⟨x, hx, hpx⟩ := mem_iUnion₂.1 this
    exact ⟨x, hx, ball_subset_closedBall hpx⟩
  refine ⟨fun p hp ↦ ?_, fun u hu hmargin p ht hs ↦ ?_⟩
  · obtain ⟨x, hx, hpx⟩ := hcov p hp.1 hp.2
    exact hUs x (hKr (htK x hx)) (hrU x (hKr (htK x hx)) hpx)
  obtain ⟨x, hx, hpx⟩ := hcov p ht hs
  have hxr := hKr (htK x hx)
  have hpU := hrU x hxr hpx
  have hpS : p ∈ (e x).source := ⟨hUs x hxr hpU, hUc x hxr hpU⟩
  obtain ⟨hs₁, hs₂⟩ := contDiffOn_trans_chartAt Φ (Φ x)
  have hcd : ContDiffAt ℝ 2 (e x) p :=
    (hs₁.contDiffAt ((e x).open_source.mem_nhds hpS)).of_le (by simp)
  have hcds : ContDiffAt ℝ 2 (e x).symm (e x p) :=
    (hs₂.contDiffAt ((e x).open_target.mem_nhds ((e x).map_source hpS))).of_le
    (by simp)
  have hΦp : Φ p ∈ Φ.target := Φ.toOpenPartialHomeomorph.map_source hpS.1
  -- `u ∘ Φ⁻¹` is `C²` at `Φ p`.
  have hu' : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 (u ∘ Φ.symm) (Φ p) :=
    hu.contMDiff.contMDiffAt.comp _
      ((Φ.symm.contMDiffOn.contMDiffAt (Φ.open_target.mem_nhds hΦp)).of_le (by simp))
  rw [isManifoldStrictlyPlurisubharmonicAt_iff_of_mem_maximalAtlas
    (IsManifold.chart_mem_maximalAtlas (Φ x)) (x := Φ p) hpS.2 hu']
  -- The inverse of `Φ.toOpenPartialHomeomorph` is `Φ.symm`, by definition.
  have hsymm : (u ∘ Φ.symm) ∘ (chartAt E (Φ x)).symm = u ∘ (e x).symm := rfl
  have hex : chartAt E (Φ x) (Φ p) = e x p := rfl
  rw [hsymm, hex]
  rw [isStrictlyPlurisubharmonicAt_iff]
  intro w hw
  set v := fderiv ℝ (e x).symm (e x p) w
  have hdx : DifferentiableAt ℝ (e x) p := hcd.differentiableAt (by norm_num)
  have hdsx : DifferentiableAt ℝ (e x).symm (e x p) := hcds.differentiableAt (by norm_num)
  have hvw : fderiv ℝ (e x) p v = w :=
    (e x).fderiv_apply_fderiv_symm_apply_of_mem_source hpS hdx hdsx w
  have hv : v ≠ 0 := fun h ↦ hw (by rw [← hvw, h, map_zero])
  obtain ⟨hpsh, hm⟩ := hmargin p ht hs
  have hB' := hB x hx p hpx
  rw [Prod.norm_def, Prod.norm_def, max_le_iff, max_le_iff] at hB'
  have hcomp := hC₀ (e x) p hpS hcd hcds (hB'.1.trans (hBK x hx)) (hB'.2.1.trans (hBK x hx))
    (hB'.2.2.trans (hBK x hx)) u hu.contDiffAt v
  rw [hvw] at hcomp
  -- The bounds on `∂̄` at `p`, in terms of `γ`.
  have hCe := hC x hxr p hpU
  rw [writtenInExtChartAt_eq_coe_trans] at hCe
  have hsq : √(shape p).2 ≤ γ := by
    rw [← Real.sqrt_sq hγ.1.le]
    exact Real.sqrt_le_sqrt ht
  have hpow : ∀ n, N₀ + 1 ≤ n → C x * √(shape p).2 ^ n ≤ Cc * γ ^ (N₀ + 1) := fun n hn ↦
    calc C x * √(shape p).2 ^ n ≤ Cc * √(shape p).2 ^ n := by gcongr; exact hCC x hx
      _ ≤ Cc * γ ^ n := by gcongr
      _ ≤ Cc * γ ^ (N₀ + 1) := mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hγ.1.le hγ1 hn) hCc
  have ha := hCe.1.trans (hpow N (by omega))
  have hb := hCe.2.trans (hpow (N - 1) (by omega))
  set a := ‖conjWirtingerDeriv (e x) p‖
  set b := ‖fderiv ℝ (conjWirtingerDeriv (e x)) p‖
  set d₂ := ‖fderiv ℝ (fderiv ℝ u) p‖
  set d₁ := ‖fderiv ℝ u p‖
  set D := max d₂ d₁
  have hL := isStrictlyPlurisubharmonicAt_iff.1 hpsh v hv
  have hmv := hm v
  have hg : 0 ≤ Cc * γ ^ (N₀ + 1) := mul_nonneg hCc (pow_nonneg hγ.1.le _)
  have hX : a * d₂ + (a + b) * d₁ ≤ 3 * Cc * γ ^ (N₀ + 1) * D := by
    have h2 : d₂ ≤ D := le_max_left _ _
    have h1 : d₁ ≤ D := le_max_right _ _
    have hd₂ : 0 ≤ d₂ := norm_nonneg (fderiv ℝ (fderiv ℝ u) p)
    have hd₁ : 0 ≤ d₁ := norm_nonneg (fderiv ℝ u p)
    nlinarith [mul_le_mul ha h2 hd₂ hg, mul_le_mul (add_le_add ha hb) h1 hd₁ (add_nonneg hg hg)]
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
            ((norm_nonneg (fderiv ℝ u p)).trans (le_max_right d₂ d₁)))
      _ = (c / 2) * γ ^ N₀ * D := by ring
  have := mul_le_mul_of_nonneg_right hbound (sq_nonneg ‖v‖)
  linarith

end Chart

end SymplecticGeometry

end
