/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Immersion
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import TauCeti.Geometry.Manifold.Morse.Hessian
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import SymplecticGeometry.Analysis.Calculus.SliceLowerBound
import SymplecticGeometry.Geometry.Manifold.Immersion.Chart
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompContinuousLinearEquiv
import TauCeti.Geometry.Manifold.Immersion.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic

/-!
# The squared distance to an immersed submanifold in a chart

Let `ι : N → M` be a `C^n` immersion at `y`, `n ≥ 2`, of a boundaryless manifold into a manifold
`M` modelled on a real normed space `E`, with finite-dimensional complement. Let `ρ : M → ℝ` be
`C²` at `ι y`, nonnegative near `ι y`, zero on the image of `ι` near `ι y`, and with critical
Hessian at `ι y` positive on every tangent vector off the tangent image of `ι`. Then, in any
chart `e` of the `C²` maximal atlas of `M` at `ι y`, the squared distance from `z` to the image
`e '' (e.source ∩ range ι)` is at most `C * ρ (e.symm z)` for `z` near `e (ι y)`
(`Manifold.IsImmersionAtOfComplement.exists_eventually_infDist_sq_le_mul` and
`Manifold.IsImmersionAt.exists_eventually_infDist_sq_le_mul`).

The proof reads `ρ` in the normal-form chart `ψ` of the immersion, through `L = h.equiv`, as a
function `g` on `E' × F` for which the image of `ι` contains the slice `{(a, 0)}` near the base
point. There `g` is nonnegative and vanishes on the slice, so it is critical along it, and its
Hessian in the directions `(0, w)` is the critical Hessian of `ρ` on the vector that `ψ` and `L`
send to `(0, w)` (Tau Ceti's `TauCeti.criticalHessian_apply_eq_of_mem_maximalAtlas` and
`TauCeti.fderiv_fderiv_comp_right_apply_apply`), which is off the tangent image of `ι`
(`Manifold.IsImmersionAtOfComplement.snd_equiv_symm_mfderiv_extend_eq_zero_iff`). So
`ContDiffAt.exists_pos_eventually_mul_norm_snd_sq_le_sub` gives `c ‖b‖² ≤ g (a, b)`. The point
with coordinates `(a, 0)` lies on the image of `ι`, and the transition map to `e` is `C¹`, hence
Lipschitz near the base point, so the distance in `e` to the image is at most a multiple of `‖b‖`.

Only the points of the image over the slice are used, so `ι` need not be an embedding: for a
`C^n` embedding `h`, apply the second statement to `h.isImmersion.isImmersionAt y`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Springer GTM 218 (2013),
  Chapter 4 (the rank theorem) and Chapter 5 (slice charts).
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §2, for the Hessian at a critical point.
-/

public section

open Set Function Filter Manifold Topology TauCeti
open scoped ContDiff Manifold

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {n : WithTop ℕ∞} {ι : N → M} {y : N} {ρ : M → ℝ}

namespace Manifold.IsImmersionAtOfComplement

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- **The squared distance to an immersed submanifold in a chart.** Let `ι` be a `C^n` immersion
at `y`, `n ≥ 2`, of a boundaryless manifold, with finite-dimensional complement `F`, and let
`ρ` be `C²` at `ι y`, nonnegative near `ι y` and zero on the image of `ι` near `ι y`, with
critical Hessian at `ι y` positive on every vector off the tangent image of `ι`. Then for every
chart `e` of the `C²` maximal atlas whose source contains `ι y` there is `C` such that the
squared distance from `z` to `e '' (e.source ∩ range ι)` is at most `C * ρ (e.symm z)` for every
`z` near `e (ι y)`. -/
theorem exists_eventually_infDist_sq_le_mul (h : IsImmersionAtOfComplement F I' 𝓘(ℝ, E) n ι y)
    (hn : 2 ≤ n) (hρ : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 ρ (ι y)) (hρ0 : ∀ᶠ x in 𝓝 (ι y), 0 ≤ ρ x)
    (hρι : ∀ᶠ x in 𝓝 (ι y), x ∈ range ι → ρ x = 0)
    (hpos : ∀ v ∉ LinearMap.range (mfderiv I' 𝓘(ℝ, E) ι y).toLinearMap,
      0 < criticalHessian 𝓘(ℝ, E) ρ (ι y) v v)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 2 M)
    (hy : ι y ∈ e.source) :
    ∃ C, ∀ᶠ z in 𝓝 (e (ι y)),
      Metric.infDist z (e '' (e.source ∩ range ι)) ^ 2 ≤ C * ρ (e.symm z) := by
  set ψ := h.codChart.extend 𝓘(ℝ, E)
  set L := h.equiv
  have hψ : h.codChart ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 2 M :=
    IsManifold.maximalAtlas_subset_of_le hn h.codChart_mem_maximalAtlas
  have hyψ : ι y ∈ h.codChart.source := h.mem_codChart_source
  -- The function `ρ` and the chart `e`, read in the normal-form coordinates.
  set g : E' × F → ℝ := (ρ ∘ ψ.symm) ∘ L
  set a₀ := h.domChart.extend I' y
  have hu₀ : L.symm (ψ (ι y)) = (a₀, 0) := h.equiv_symm_codChart_extend_apply h.mem_domChart_source
  have hLu₀ : L (a₀, 0) = ψ (ι y) := by rw [← hu₀, ContinuousLinearEquiv.apply_symm_apply]
  have hψsymm : ψ.symm (ψ (ι y)) = ι y := h.codChart.extend_left_inv hyψ
  have hcontψ : ContinuousAt ψ.symm (ψ (ι y)) := h.codChart.continuousAt_extend_symm hyψ
  have hΦ : Tendsto (fun u ↦ ψ.symm (L u)) (𝓝 (a₀, 0)) (𝓝 (ι y)) := by
    have hL : Tendsto L (𝓝 (a₀, 0)) (𝓝 (ψ (ι y))) := hLu₀ ▸ L.continuous.tendsto _
    have := hcontψ.tendsto.comp hL
    rwa [hψsymm] at this
  -- Points of the slice near `a₀` lie on the image of `ι`.
  have hslice : ∀ᶠ a in 𝓝 a₀, ψ.symm (L (a, 0)) ∈ range ι := by
    have hmem : (h.domChart.extend I').target ∈ 𝓝 a₀ :=
      (h.domChart.isOpen_extend_target).mem_nhds ((h.domChart.extend I').map_source
        (by rw [h.domChart.extend_source]; exact h.mem_domChart_source))
    filter_upwards [hmem] with a ha
    exact ⟨_, (h.mem_codChart_source_and_extend_eq ha).2.2.1.symm⟩
  have hmk : Tendsto (fun a : E' ↦ ((a, 0) : E' × F)) (𝓝 a₀) (𝓝 (a₀, 0)) :=
    (continuous_id.prodMk continuous_const).tendsto a₀
  -- `g` is nonnegative near `(a₀, 0)` and vanishes on the slice, so it is critical there.
  have hg0 : ∀ᶠ u in 𝓝 ((a₀, 0) : E' × F), 0 ≤ g u := hΦ.eventually hρ0
  have hgslice : ∀ᶠ a in 𝓝 a₀, g (a, 0) = 0 :=
    (hmk.eventually (hΦ.eventually hρι)).and hslice |>.mono fun _ ha ↦ ha.1 ha.2
  have hcrit : ∀ᶠ a in 𝓝 a₀, fderiv ℝ g (a, 0) = 0 := by
    filter_upwards [hgslice, hmk.eventually (eventually_eventually_nhds.2 hg0)] with a ha ha'
    exact IsLocalMin.fderiv_eq_zero (ha'.mono fun u hu ↦ ha ▸ hu)
  -- The coordinate expression of `ρ` in `ψ`, and the critical point of `ρ` at `ι y`.
  have hf₀ : ContDiffAt ℝ 2 (ρ ∘ ψ.symm) (ψ (ι y)) :=
    (contMDiffAt_iff_contDiffAt_comp_extend_symm hψ hyψ).1 hρ
  have hg : ContDiffAt ℝ 2 g (a₀, 0) := by
    rw [← hLu₀] at hf₀
    exact hf₀.comp (a₀, 0) L.contDiff.contDiffAt
  have hρy : ρ (ι y) = 0 := hρι.self_of_nhds (mem_range_self y)
  have hcritρ : mvfderiv 𝓘(ℝ, E) ρ (ι y) = 0 := by
    rw [mvfderiv_eq_zero_iff_fderiv_comp_extend_symm_eq_zero
      (IsManifold.maximalAtlas_subset_of_le (by norm_num) hψ) hyψ]
    refine IsLocalMin.fderiv_eq_zero ?_
    have := hcontψ.tendsto.eventually (hψsymm ▸ hρ0)
    exact this.mono fun u hu ↦
      (by rw [hψsymm, hρy]; exact hu : ρ (ψ.symm (ψ (ι y))) ≤ ρ (ψ.symm u))
  -- The Hessian of `g` is positive on the fibre directions.
  have hpos' (w : F) (hw : w ≠ 0) : 0 < fderiv ℝ (fderiv ℝ g) (a₀, 0) (0, w) (0, w) := by
    obtain ⟨D, hD⟩ := isInvertible_mvfderiv_extend
      (IsManifold.maximalAtlas_subset_of_le (by norm_num) hψ) hyψ
    set v : TangentSpace 𝓘(ℝ, E) (ι y) := D.symm (L (0, w))
    have hv : mvfderiv 𝓘(ℝ, E) ψ (ι y) v = L (0, w) := by
      rw [← hD, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
    have hvr : v ∉ LinearMap.range (mfderiv I' 𝓘(ℝ, E) ι y).toLinearMap := by
      rw [← h.snd_equiv_symm_mfderiv_extend_eq_zero_iff
        (ENat.one_le_iff_ne_zero_withTop.1 (one_le_two.trans hn)) h.mem_domChart_source]
      -- `mvfderiv` of a map into `E` is `mfderiv` read in `E`.
      change (L.symm (mvfderiv 𝓘(ℝ, E) ψ (ι y) v)).2 ≠ 0
      rwa [hv, ContinuousLinearEquiv.symm_apply_apply]
    have := hpos v hvr
    rwa [criticalHessian_apply_eq_of_mem_maximalAtlas hψ hyψ hρ hcritρ, hv, ← hLu₀,
      ← L.fderiv_fderiv_comp_right_apply_apply] at this
  obtain ⟨c, hc, hcb⟩ := hg.exists_pos_eventually_mul_norm_snd_sq_le_sub hcrit
    fun w hw ↦ hpos' w hw
  have hgu₀ : g (a₀, 0) = 0 := by simp [g, hLu₀, hψsymm, hρy]
  -- The transition map to `e` is Lipschitz near `(a₀, 0)`.
  set T : E' × F → E := (e.extend 𝓘(ℝ, E) ∘ ψ.symm) ∘ L
  have hT : ContDiffAt ℝ 1 T (a₀, 0) := by
    have := (contMDiffAt_iff_contDiffAt_comp_extend_symm hψ hyψ).1 (e.contMDiffAt_extend he hy)
    rw [← hLu₀] at this
    exact (this.of_le one_le_two).comp (a₀, 0) L.contDiff.contDiffAt
  obtain ⟨K, t, ht, hK⟩ := hT.exists_lipschitzOnWith
  -- Near the base point, the slice point over `u` lies on the image of `ι` in the source of `e`.
  have hgood : ∀ᶠ u in 𝓝 ((a₀, 0) : E' × F), u ∈ t ∧ (u.1, 0) ∈ t ∧
      ψ.symm (L (u.1, 0)) ∈ e.source ∩ range ι ∧ c * ‖u.2‖ ^ 2 ≤ g u := by
    have hfst : Tendsto (fun u : E' × F ↦ ((u.1, 0) : E' × F)) (𝓝 (a₀, 0)) (𝓝 (a₀, 0)) :=
      ((continuous_fst.prodMk continuous_const).tendsto ((a₀, 0) : E' × F))
    have hsl : ∀ᶠ a in 𝓝 a₀, ψ.symm (L (a, 0)) ∈ e.source ∩ range ι :=
      (hmk.eventually (hΦ.eventually (e.open_source.mem_nhds hy))).and hslice
    filter_upwards [ht, hfst.eventually ht, (continuous_fst.tendsto ((a₀, 0) : E' × F)).eventually
      hsl, hcb] with u h1 h2 h3 h4
    exact ⟨h1, h2, h3, by rwa [hgu₀, sub_zero] at h4⟩
  -- The normal-form coordinates of a point of the chart `e`.
  set Θ : E → E' × F := fun z ↦ L.symm (ψ (e.symm z))
  have heψ : e.symm (e (ι y)) = ι y := e.left_inv hy
  have hΘ : Tendsto Θ (𝓝 (e (ι y))) (𝓝 (a₀, 0)) := by
    have h1 := (e.continuousAt_symm (e.map_source hy)).tendsto
    rw [heψ] at h1
    have h2 := (h.codChart.continuousAt_extend (I := 𝓘(ℝ, E)) hyψ).tendsto.comp h1
    have := (L.symm.continuous.tendsto _).comp h2
    rwa [← hu₀]
  refine ⟨K ^ 2 / c, ?_⟩
  have hsrc : ∀ᶠ z in 𝓝 (e (ι y)), e.symm z ∈ h.codChart.source := by
    have := (e.continuousAt_symm (e.map_source hy)).tendsto
    rw [heψ] at this
    exact this.eventually (h.codChart.open_source.mem_nhds hyψ)
  filter_upwards [hΘ.eventually hgood, hsrc, e.open_target.mem_nhds (e.map_source hy)] with z
    ⟨h1, h2, h3, h4⟩ hz hzt
  have hΦz : ψ.symm (L (Θ z)) = e.symm z := by
    simp only [Θ, ContinuousLinearEquiv.apply_symm_apply]
    exact h.codChart.extend_left_inv hz
  have hTz : T (Θ z) = z := by
    simp only [T, comp_apply, hΦz, OpenPartialHomeomorph.extend_coe, modelWithCornersSelf_coe,
      id_eq, e.right_inv hzt]
  have hgz : g (Θ z) = ρ (e.symm z) := by simp only [g, comp_apply, hΦz]
  -- The distance to the image is at most `K ‖(Θ z).2‖`.
  have hdist : Metric.infDist z (e '' (e.source ∩ range ι)) ≤ K * ‖(Θ z).2‖ := by
    refine (Metric.infDist_le_dist_of_mem (mem_image_of_mem e h3)).trans ?_
    have hTs : e (ψ.symm (L ((Θ z).1, 0))) = T ((Θ z).1, 0) := by
      simp only [T, comp_apply, OpenPartialHomeomorph.extend_coe, modelWithCornersSelf_coe, id_eq]
    have hle := hK.dist_le_mul _ h1 _ h2
    rw [hTz] at hle
    rw [hTs]
    refine hle.trans (le_of_eq ?_)
    rw [Prod.dist_eq, dist_self, dist_eq_norm, sub_zero, max_eq_right (norm_nonneg _)]
  calc Metric.infDist z (e '' (e.source ∩ range ι)) ^ 2 ≤ (K * ‖(Θ z).2‖) ^ 2 :=
        pow_le_pow_left₀ Metric.infDist_nonneg hdist 2
    _ = K ^ 2 / c * (c * ‖(Θ z).2‖ ^ 2) := by field_simp
    _ ≤ K ^ 2 / c * ρ (e.symm z) := by rw [← hgz]; gcongr

end Manifold.IsImmersionAtOfComplement

namespace Manifold.IsImmersionAt

/-- **The squared distance to an immersed submanifold in a chart.** Let `ι` be a `C^n` immersion
at `y`, `n ≥ 2`, of a boundaryless manifold into a manifold with finite-dimensional model `E`,
and let `ρ` be `C²` at `ι y`, nonnegative near `ι y` and zero on the image of `ι` near `ι y`,
with critical Hessian at `ι y` positive on every vector off the tangent image of `ι`. Then for
every chart `e` of the `C²` maximal atlas whose source contains `ι y` there is `C` such that the
squared distance from `z` to `e '' (e.source ∩ range ι)` is at most `C * ρ (e.symm z)` for every
`z` near `e (ι y)`. -/
theorem exists_eventually_infDist_sq_le_mul [FiniteDimensional ℝ E]
    (h : IsImmersionAt I' 𝓘(ℝ, E) n ι y) (hn : 2 ≤ n)
    (hρ : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 ρ (ι y)) (hρ0 : ∀ᶠ x in 𝓝 (ι y), 0 ≤ ρ x)
    (hρι : ∀ᶠ x in 𝓝 (ι y), x ∈ range ι → ρ x = 0)
    (hpos : ∀ v ∉ LinearMap.range (mfderiv I' 𝓘(ℝ, E) ι y).toLinearMap,
      0 < criticalHessian 𝓘(ℝ, E) ρ (ι y) v v)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 2 M)
    (hy : ι y ∈ e.source) :
    ∃ C, ∀ᶠ z in 𝓝 (e (ι y)),
      Metric.infDist z (e '' (e.source ∩ range ι)) ^ 2 ≤ C * ρ (e.symm z) := by
  have h' := h.isImmersionAtOfComplement_complement
  -- The complement embeds linearly into `E`, so it is finite-dimensional.
  have : FiniteDimensional ℝ h.complement :=
    Module.Finite.of_injective
      ((h'.equiv : E' × h.complement →L[ℝ] E).comp (ContinuousLinearMap.inr ℝ E' _)).toLinearMap
      (h'.equiv.injective.comp (Prod.mk_right_injective (0 : E')))
  exact h'.exists_eventually_infDist_sq_le_mul hn hρ hρ0 hρι hpos he hy

end Manifold.IsImmersionAt

end
