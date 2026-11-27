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
import SymplecticGeometry.Analysis.Calculus.FDeriv.FirstOrderVanishing
import SymplecticGeometry.Analysis.Calculus.SliceLowerBound
import SymplecticGeometry.Geometry.Manifold.Immersion.Chart
import SymplecticGeometry.Geometry.Manifold.Immersion.Complement
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompContinuousLinearEquiv
import TauCeti.Geometry.Manifold.ContMDiff.Atlas
import TauCeti.Geometry.Manifold.Immersion.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The squared distance to an immersed submanifold in a chart

Let `ι : N → M` be a `C^n` immersion at `y`, `n ≥ 2`, of a boundaryless manifold into a manifold
`M` modelled on a real normed space `E`, with finite-dimensional complement. Let `ρ : M → ℝ` be
`C²` at `ι y` and nonnegative near `ι y`, with `ρ ∘ ι` zero near `y` and with critical Hessian
at `ι y` positive on every tangent vector off the tangent image of `ι`. Then, in any chart `e`
of the `C¹` maximal atlas of `M` at `ι y`, the squared distance from `z` to the image
`e '' (e.source ∩ range ι)` is at most `C * ρ (e.symm z)` for `z` near `e (ι y)`
(`Manifold.IsImmersionAtOfComplement.exists_eventually_infDist_sq_le_mul` and
`Manifold.IsImmersionAt.exists_eventually_infDist_sq_le_mul`).

The proof reads `ρ` in the normal-form chart `ψ` of the immersion, through `L = h.equiv`, as a
function `g` on `E' × F`. Near the base point `(a₀, 0)`, the point with coordinates `(a, 0)` is
`ι (φ.symm a)`, `φ` being the domain chart, so `g` is nonnegative and vanishes on the slice
`{(a, 0)}`; hence it is critical along it, and `ρ` is critical at `ι y`
(`IsLocalMin.mem_criticalPoints`). The Hessian of `g` in the directions `(0, w)` is the critical
Hessian of `ρ` on the vector that `ψ` and `L` send to `(0, w)` (Tau Ceti's
`TauCeti.criticalHessian_apply_eq_of_mem_maximalAtlas` and
`ContinuousLinearEquiv.fderiv_fderiv_comp_right_apply_apply`), which is off the tangent image of
`ι` (`Manifold.IsImmersionAtOfComplement.snd_equiv_symm_mfderiv_extend_eq_zero_iff`). So
`ContDiffAt.exists_pos_eventually_mul_norm_snd_sq_le_sub` gives `c ‖b‖² ≤ g (a, b)`. The point
with coordinates `(a, 0)` lies on the image of `ι`, and the transition map to `e` is `C¹`, hence
Lipschitz near the base point, so the distance in `e` to the image is at most a multiple of `‖b‖`.

Only the points of the image over the slice are used, so `ι` need not be an embedding: for a
`C^n` embedding `h`, apply the second statement to `h.isImmersion.isImmersionAt y`.

The same subset `e '' (e.source ∩ range ι)` controls a function `D : M → ℝ` that is `C²` near
`ι y` and vanishes to first order on the image of `ι` near `ι y`, when `ι` is a topological
embedding and `E` is finite-dimensional: in a chart of the `C²` maximal atlas, `D` is at most a
multiple of the squared distance to it, and its derivative at most a multiple of the distance
(`Topology.IsEmbedding.exists_eventually_abs_comp_symm_le_mul_infDist_sq`, from
`IsCompact.exists_eventually_norm_le_mul_infDist_sq_and_norm_fderiv_le_mul_infDist`). Here the
embedding matters: the points of that subset near `e (ι y)` are images of points near `y`.

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
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {n : WithTop ℕ∞} {ι : N → M} {y : N} {ρ : M → ℝ}

namespace Manifold.IsImmersionAtOfComplement

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Let `φ` be the domain chart of `h` and `a₀ = φ y`. For `a` near `a₀`, the point with
normal-form coordinates `(a, 0)` is `ι (φ.symm a)`, and `φ.symm a` tends to `y` as `a` tends to
`a₀`. -/
private theorem eventually_extend_symm_equiv_eq [I'.Boundaryless]
    (h : IsImmersionAtOfComplement F I' 𝓘(ℝ, E) n ι y) :
    (∀ᶠ a in 𝓝 (h.domChart.extend I' y), (h.codChart.extend 𝓘(ℝ, E)).symm (h.equiv (a, 0)) =
      ι ((h.domChart.extend I').symm a)) ∧
    Tendsto (h.domChart.extend I').symm (𝓝 (h.domChart.extend I' y)) (𝓝 y) := by
  have hy : y ∈ (h.domChart.extend I').source := by
    rw [h.domChart.extend_source]; exact h.mem_domChart_source
  refine ⟨?_, ?_⟩
  · filter_upwards [(h.domChart.isOpen_extend_target (I := I')).mem_nhds
      ((h.domChart.extend I').map_source hy)] with a ha
    exact (h.mem_codChart_source_and_extend_eq ha).2.2.1
  · have := (h.domChart.continuousAt_extend_symm (I := I') h.mem_domChart_source).tendsto
    rwa [(h.domChart.extend I').left_inv hy] at this

/-- **The normal Hessian in normal-form coordinates.** If `ρ` is `C²` and critical at `ι y`, with
critical Hessian positive off the tangent image of `ι`, then its coordinate expression in the
normal-form chart of `ι` has positive second derivative at `(φ y, 0)`, `φ` being the domain chart,
in every direction `(0, w)` with `w ≠ 0`. -/
private theorem fderiv_fderiv_apply_inr_pos (h : IsImmersionAtOfComplement F I' 𝓘(ℝ, E) n ι y)
    (hn : 2 ≤ n) (hρ : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 ρ (ι y))
    (hcrit : mvfderiv 𝓘(ℝ, E) ρ (ι y) = 0)
    (hpos : ∀ v ∉ LinearMap.range (mfderiv I' 𝓘(ℝ, E) ι y).toLinearMap,
      0 < criticalHessian 𝓘(ℝ, E) ρ (ι y) v v) {w : F} (hw : w ≠ 0) :
    0 < fderiv ℝ (fderiv ℝ ((ρ ∘ (h.codChart.extend 𝓘(ℝ, E)).symm) ∘ h.equiv))
      (h.domChart.extend I' y, 0) (0, w) (0, w) := by
  set ψ := h.codChart.extend 𝓘(ℝ, E)
  set L := h.equiv
  have hψ : h.codChart ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 2 M :=
    IsManifold.maximalAtlas_subset_of_le hn h.codChart_mem_maximalAtlas
  obtain ⟨D, hD⟩ := isInvertible_mvfderiv_extend
    (IsManifold.maximalAtlas_subset_of_le (by norm_num) hψ) h.mem_codChart_source
  set v : TangentSpace 𝓘(ℝ, E) (ι y) := D.symm (L (0, w))
  have hv : mvfderiv 𝓘(ℝ, E) ψ (ι y) v = L (0, w) := by
    rw [← hD, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
  have hvr : v ∉ LinearMap.range (mfderiv I' 𝓘(ℝ, E) ι y).toLinearMap := by
    rw [← h.snd_equiv_symm_mfderiv_extend_eq_zero_iff
      (ENat.one_le_iff_ne_zero_withTop.1 (one_le_two.trans hn)) h.mem_domChart_source]
    rwa [← mvfderiv_apply_eq_mfderiv_apply, hv, ContinuousLinearEquiv.symm_apply_apply]
  have := hpos v hvr
  rwa [criticalHessian_apply_eq_of_mem_maximalAtlas hψ h.mem_codChart_source hρ hcrit, hv,
    ← h.equiv_domChart_extend_apply h.mem_domChart_source,
    ← L.fderiv_fderiv_comp_right_apply_apply] at this

/-- For a chart `e` at `ι y`, the normal-form coordinates of the point `e.symm z` tend to
`(φ y, 0)` as `z` tends to `e (ι y)`, `φ` being the domain chart, and for `z` near `e (ι y)` the
normal-form chart sends them back to `e.symm z`. -/
private theorem tendsto_equiv_symm_extend_symm (h : IsImmersionAtOfComplement F I' 𝓘(ℝ, E) n ι y)
    {e : OpenPartialHomeomorph M E} (hy : ι y ∈ e.source) :
    Tendsto (fun z ↦ h.equiv.symm (h.codChart.extend 𝓘(ℝ, E) (e.symm z))) (𝓝 (e (ι y)))
      (𝓝 (h.domChart.extend I' y, 0)) ∧
    ∀ᶠ z in 𝓝 (e (ι y)), (h.codChart.extend 𝓘(ℝ, E)).symm
      (h.equiv (h.equiv.symm (h.codChart.extend 𝓘(ℝ, E) (e.symm z)))) = e.symm z := by
  have he := (e.continuousAt_symm (e.map_source hy)).tendsto
  rw [e.left_inv hy] at he
  refine ⟨?_, ?_⟩
  · have := (h.equiv.symm.continuous.tendsto _).comp
      ((h.codChart.continuousAt_extend (I := 𝓘(ℝ, E)) h.mem_codChart_source).tendsto.comp he)
    rwa [← h.equiv_symm_codChart_extend_apply h.mem_domChart_source]
  · filter_upwards [he.eventually (h.codChart.open_source.mem_nhds h.mem_codChart_source)] with z hz
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact h.codChart.extend_left_inv hz

/-- **The distance to the image in a chart is at most a multiple of the normal coordinate.**
For a chart `e` of the `C¹` maximal atlas at `ι y`, there is `K` such that, for `z` near
`e (ι y)`, the distance from `z` to `e '' (e.source ∩ range ι)` is at most `K` times the norm of
the normal coordinate of `e.symm z` in the normal-form chart of `ι`. -/
private theorem exists_eventually_infDist_le_mul_norm_snd [I'.Boundaryless]
    (h : IsImmersionAtOfComplement F I' 𝓘(ℝ, E) n ι y) (hn : 1 ≤ n)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 1 M)
    (hy : ι y ∈ e.source) :
    ∃ K, ∀ᶠ z in 𝓝 (e (ι y)), Metric.infDist z (e '' (e.source ∩ range ι)) ≤
      K * ‖(h.equiv.symm (h.codChart.extend 𝓘(ℝ, E) (e.symm z))).2‖ := by
  obtain ⟨hslice, hφ⟩ := h.eventually_extend_symm_equiv_eq
  obtain ⟨hΘ, hΘeq⟩ := h.tendsto_equiv_symm_extend_symm hy
  have hLu₀ := h.equiv_domChart_extend_apply h.mem_domChart_source
  set ψ := h.codChart.extend 𝓘(ℝ, E)
  set L := h.equiv
  set a₀ := h.domChart.extend I' y
  set Θ : E → E' × F := fun z ↦ L.symm (ψ (e.symm z))
  have hψ : h.codChart ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 1 M :=
    IsManifold.maximalAtlas_subset_of_le hn h.codChart_mem_maximalAtlas
  have hyψ : ι y ∈ h.codChart.source := h.mem_codChart_source
  -- The transition map from the normal-form coordinates to `e` is Lipschitz near `(a₀, 0)`.
  set T : E' × F → E := (e.extend 𝓘(ℝ, E) ∘ ψ.symm) ∘ L
  have hT : ContDiffAt ℝ 1 T (a₀, 0) := by
    have : ContDiffAt ℝ 1 (e.extend 𝓘(ℝ, E) ∘ ψ.symm) (ψ (ι y)) :=
      (e.contMDiffAt_extend he hy).contDiffAt_comp_symm_of_mem_maximalAtlas hψ hyψ
    rw [← hLu₀] at this
    exact this.comp (a₀, 0) L.contDiff.contDiffAt
  obtain ⟨K, t, ht, hK⟩ := hT.exists_lipschitzOnWith
  -- Near `(a₀, 0)`, the slice point over `u` lies on the image of `ι` in the source of `e`.
  have hmk : Tendsto (fun a : E' ↦ ((a, 0) : E' × F)) (𝓝 a₀) (𝓝 (a₀, 0)) :=
    (continuous_id.prodMk continuous_const).tendsto a₀
  have hΦ : Tendsto (fun a : E' ↦ ψ.symm (L (a, 0))) (𝓝 a₀) (𝓝 (ι y)) := by
    have h1 := (h.codChart.continuousAt_extend_symm (I := 𝓘(ℝ, E)) hyψ).tendsto
    rw [h.codChart.extend_left_inv hyψ, ← hLu₀] at h1
    exact h1.comp ((L.continuous.tendsto _).comp hmk)
  have hsl : ∀ᶠ a in 𝓝 a₀, ψ.symm (L (a, 0)) ∈ e.source ∩ range ι := by
    filter_upwards [hΦ.eventually (e.open_source.mem_nhds hy), hslice] with a h1 h2
    exact ⟨h1, _, h2.symm⟩
  have hfst : Tendsto (fun u : E' × F ↦ ((u.1, 0) : E' × F)) (𝓝 (a₀, 0)) (𝓝 (a₀, 0)) :=
    (continuous_fst.prodMk continuous_const).tendsto ((a₀, 0) : E' × F)
  have hgood : ∀ᶠ u in 𝓝 ((a₀, 0) : E' × F), u ∈ t ∧ (u.1, 0) ∈ t ∧
      ψ.symm (L (u.1, 0)) ∈ e.source ∩ range ι := by
    filter_upwards [ht, hfst.eventually ht,
      (continuous_fst.tendsto ((a₀, 0) : E' × F)).eventually hsl] with u h1 h2 h3
    exact ⟨h1, h2, h3⟩
  refine ⟨K, ?_⟩
  filter_upwards [hΘ.eventually hgood, hΘeq, e.open_target.mem_nhds (e.map_source hy)] with z
    ⟨h1, h2, h3⟩ hz hzt
  have hTz : T (Θ z) = z := by
    simp only [T, comp_apply, OpenPartialHomeomorph.extend_coe, modelWithCornersSelf_coe, id_eq]
    rw [hz, e.right_inv hzt]
  have hTs : e (ψ.symm (L ((Θ z).1, 0))) = T ((Θ z).1, 0) := by
    simp only [T, comp_apply, OpenPartialHomeomorph.extend_coe, modelWithCornersSelf_coe, id_eq]
  refine (Metric.infDist_le_dist_of_mem (mem_image_of_mem e h3)).trans ?_
  have hle := hK.dist_le_mul _ h1 _ h2
  rw [hTz] at hle
  rw [hTs]
  refine hle.trans (le_of_eq ?_)
  rw [Prod.dist_eq, dist_self, dist_eq_norm, sub_zero, max_eq_right (norm_nonneg _)]

variable [FiniteDimensional ℝ F]

/-- **The squared distance to an immersed submanifold in a chart.** Let `ι` be a `C^n` immersion
at `y`, `n ≥ 2`, of a boundaryless manifold, with finite-dimensional complement `F`, and let
`ρ` be `C²` at `ι y`, nonnegative near `ι y`, with `ρ ∘ ι` zero near `y`, and with critical
Hessian at `ι y` positive on every vector off the tangent image of `ι`. Then for every chart `e`
of the `C¹` maximal atlas whose source contains `ι y` there is `C` such that the squared distance
from `z` to `e '' (e.source ∩ range ι)` is at most `C * ρ (e.symm z)` for every `z` near
`e (ι y)`. -/
theorem exists_eventually_infDist_sq_le_mul [I'.Boundaryless]
    (h : IsImmersionAtOfComplement F I' 𝓘(ℝ, E) n ι y)
    (hn : 2 ≤ n) (hρ : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 ρ (ι y)) (hρ0 : ∀ᶠ x in 𝓝 (ι y), 0 ≤ ρ x)
    (hρι : ∀ᶠ y' in 𝓝 y, ρ (ι y') = 0)
    (hpos : ∀ v ∉ LinearMap.range (mfderiv I' 𝓘(ℝ, E) ι y).toLinearMap,
      0 < criticalHessian 𝓘(ℝ, E) ρ (ι y) v v)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 1 M)
    (hy : ι y ∈ e.source) :
    ∃ C, ∀ᶠ z in 𝓝 (e (ι y)),
      Metric.infDist z (e '' (e.source ∩ range ι)) ^ 2 ≤ C * ρ (e.symm z) := by
  obtain ⟨hslice, hφ⟩ := h.eventually_extend_symm_equiv_eq
  obtain ⟨hΘ, hΘeq⟩ := h.tendsto_equiv_symm_extend_symm hy
  obtain ⟨K, hK⟩ := h.exists_eventually_infDist_le_mul_norm_snd (one_le_two.trans hn) he hy
  have hLu₀ := h.equiv_domChart_extend_apply h.mem_domChart_source
  set ψ := h.codChart.extend 𝓘(ℝ, E)
  set L := h.equiv
  have hψ : h.codChart ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 2 M :=
    IsManifold.maximalAtlas_subset_of_le hn h.codChart_mem_maximalAtlas
  have hyψ : ι y ∈ h.codChart.source := h.mem_codChart_source
  -- `ρ` read in the normal-form coordinates, around the base point `(a₀, 0)`.
  set g : E' × F → ℝ := (ρ ∘ ψ.symm) ∘ L
  set a₀ := h.domChart.extend I' y
  have hψsymm : ψ.symm (ψ (ι y)) = ι y := h.codChart.extend_left_inv hyψ
  have hΦ : Tendsto (fun u ↦ ψ.symm (L u)) (𝓝 (a₀, 0)) (𝓝 (ι y)) := by
    have := (h.codChart.continuousAt_extend_symm hyψ).tendsto.comp
      (hLu₀ ▸ L.continuous.tendsto (a₀, 0))
    rwa [hψsymm] at this
  -- `g` is nonnegative near `(a₀, 0)` and vanishes on the slice, so it is critical along it.
  have hg0 : ∀ᶠ u in 𝓝 ((a₀, 0) : E' × F), 0 ≤ g u := hΦ.eventually hρ0
  have hmk : Tendsto (fun a : E' ↦ ((a, 0) : E' × F)) (𝓝 a₀) (𝓝 (a₀, 0)) :=
    (continuous_id.prodMk continuous_const).tendsto a₀
  have hcrit : ∀ᶠ a in 𝓝 a₀, fderiv ℝ g (a, 0) = 0 := by
    filter_upwards [hslice, hφ.eventually hρι, hmk.eventually (eventually_eventually_nhds.2 hg0)]
      with a ha hρa ha'
    have hga : g (a, 0) = 0 := by simp only [g, comp_apply, ha, hρa]
    exact IsLocalMin.fderiv_eq_zero (ha'.mono fun u hu ↦ hga ▸ hu)
  have hg : ContDiffAt ℝ 2 g (a₀, 0) := by
    have hf₀ : ContDiffAt ℝ 2 (ρ ∘ ψ.symm) (ψ (ι y)) :=
      hρ.contDiffAt_comp_symm_of_mem_maximalAtlas hψ hyψ
    rw [← hLu₀] at hf₀
    exact hf₀.comp (a₀, 0) L.contDiff.contDiffAt
  have hρy : ρ (ι y) = 0 := hρι.self_of_nhds
  have hcritρ : mvfderiv 𝓘(ℝ, E) ρ (ι y) = 0 :=
    mem_criticalPoints.1 <| IsLocalMin.mem_criticalPoints (hρ0.mono fun x hx ↦ hρy ▸ hx)
      BoundarylessManifold.isInteriorPoint
  obtain ⟨c, hc, hcb⟩ := hg.exists_pos_eventually_mul_norm_snd_sq_le_sub hcrit
    fun w hw ↦ h.fderiv_fderiv_apply_inr_pos hn hρ hcritρ hpos hw
  have hgu₀ : g (a₀, 0) = 0 := by simp [g, hLu₀, hψsymm, hρy]
  -- Combine with the bound of the distance by the normal coordinate.
  refine ⟨K ^ 2 / c, ?_⟩
  filter_upwards [hK, hΘ.eventually hcb, hΘeq] with z hdist hgz hz
  rw [hgu₀, sub_zero] at hgz
  simp only [g, comp_apply, hz] at hgz
  calc Metric.infDist z (e '' (e.source ∩ range ι)) ^ 2
      ≤ (K * ‖(L.symm (ψ (e.symm z))).2‖) ^ 2 := pow_le_pow_left₀ Metric.infDist_nonneg hdist 2
    _ = K ^ 2 / c * (c * ‖(L.symm (ψ (e.symm z))).2‖ ^ 2) := by field_simp
    _ ≤ K ^ 2 / c * ρ (e.symm z) := by gcongr

end Manifold.IsImmersionAtOfComplement

namespace Manifold.IsImmersionAt

/-- **The squared distance to an immersed submanifold in a chart.** Let `ι` be a `C^n` immersion
at `y`, `n ≥ 2`, of a boundaryless manifold into a manifold with finite-dimensional model `E`,
and let `ρ` be `C²` at `ι y`, nonnegative near `ι y`, with `ρ ∘ ι` zero near `y`, and with
critical Hessian at `ι y` positive on every vector off the tangent image of `ι`. Then for every
chart `e` of the `C¹` maximal atlas whose source contains `ι y` there is `C` such that the
squared distance from `z` to `e '' (e.source ∩ range ι)` is at most `C * ρ (e.symm z)` for every
`z` near `e (ι y)`. -/
theorem exists_eventually_infDist_sq_le_mul [I'.Boundaryless] [FiniteDimensional ℝ E]
    (h : IsImmersionAt I' 𝓘(ℝ, E) n ι y) (hn : 2 ≤ n)
    (hρ : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 ρ (ι y)) (hρ0 : ∀ᶠ x in 𝓝 (ι y), 0 ≤ ρ x)
    (hρι : ∀ᶠ y' in 𝓝 y, ρ (ι y') = 0)
    (hpos : ∀ v ∉ LinearMap.range (mfderiv I' 𝓘(ℝ, E) ι y).toLinearMap,
      0 < criticalHessian 𝓘(ℝ, E) ρ (ι y) v v)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 1 M)
    (hy : ι y ∈ e.source) :
    ∃ C, ∀ᶠ z in 𝓝 (e (ι y)),
      Metric.infDist z (e '' (e.source ∩ range ι)) ^ 2 ≤ C * ρ (e.symm z) :=
  have := h.finiteDimensional_complement
  h.isImmersionAtOfComplement_complement.exists_eventually_infDist_sq_le_mul hn hρ hρ0 hρι hpos
    he hy

end Manifold.IsImmersionAt

namespace Topology.IsEmbedding

/-- **A function vanishing to first order along an embedded subset, in a chart.** Let `ι` be a
topological embedding into a manifold modelled on a finite-dimensional real normed space `E`, and
let `D : M → ℝ` be `C²` near `ι y`, with `D (ι y') = 0` and `mvfderiv 𝓘(ℝ, E) D (ι y') = 0` for
`y'` near `y`. Then for every chart `e` of the `C²` maximal atlas whose source contains `ι y`
there is `A` such that, for `z` near `e (ι y)` and `Z = e '' (e.source ∩ range ι)`,
`|D (e.symm z)| ≤ A * infDist z Z ^ 2` and `‖fderiv ℝ (D ∘ e.symm) z‖ ≤ A * infDist z Z`. -/
theorem exists_eventually_abs_comp_symm_le_mul_infDist_sq [FiniteDimensional ℝ E] {D : M → ℝ}
    (h : IsEmbedding ι) (hD : ∀ᶠ x in 𝓝 (ι y), ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 D x)
    (hDι : ∀ᶠ y' in 𝓝 y, D (ι y') = 0 ∧ mvfderiv 𝓘(ℝ, E) D (ι y') = 0)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 2 M)
    (hy : ι y ∈ e.source) :
    ∃ A, ∀ᶠ z in 𝓝 (e (ι y)),
      |D (e.symm z)| ≤ A * Metric.infDist z (e '' (e.source ∩ range ι)) ^ 2 ∧
      ‖fderiv ℝ (D ∘ e.symm) z‖ ≤ A * Metric.infDist z (e '' (e.source ∩ range ι)) := by
  have he1 : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 1 M :=
    IsManifold.maximalAtlas_subset_of_le (by norm_num) he
  have hsymm : D ∘ (e.extend 𝓘(ℝ, E)).symm = D ∘ e.symm := by simp
  have hext : ∀ x, e.extend 𝓘(ℝ, E) x = e x := fun x ↦ by simp
  set Z := e '' (e.source ∩ range ι)
  -- An open set `U ∋ e (ι y)` on which `D ∘ e.symm` is `C²`, and whose points in `Z` are images
  -- of points where `D` vanishes to first order: here `ι` being an embedding matters.
  obtain ⟨O', hO', hO'W⟩ : ∃ O' ∈ 𝓝 (ι y), ι ⁻¹' O' ⊆
      {y' | D (ι y') = 0 ∧ mvfderiv 𝓘(ℝ, E) D (ι y') = 0} := by
    rw [h.isInducing.nhds_eq_comap] at hDι
    exact hDι
  obtain ⟨O, hOsub, hOo, hyO⟩ := mem_nhds_iff.1 (inter_mem hD hO')
  set U := e.target ∩ e.symm ⁻¹' O
  have hz₀U : e (ι y) ∈ U := ⟨e.map_source hy, by simpa [e.left_inv hy] using hyO⟩
  have hgU : ContDiffOn ℝ 2 (D ∘ e.symm) U :=
    ContMDiffOn.contDiffOn_comp_symm_of_mem_maximalAtlas
      (fun x hx ↦ (hOsub hx).1.contMDiffWithinAt) he
  have hZU : ∀ z ∈ Z ∩ U, ∃ y', e.symm z = ι y' ∧ ι y' ∈ e.source ∧ z = e (ι y') ∧
      D (ι y') = 0 ∧ mvfderiv 𝓘(ℝ, E) D (ι y') = 0 := by
    rintro z ⟨⟨x, ⟨hxs, y', rfl⟩, rfl⟩, -, hzO⟩
    rw [mem_preimage, e.left_inv hxs] at hzO
    exact ⟨y', e.left_inv hxs, hxs, rfl, hO'W (hOsub hzO).2⟩
  obtain ⟨A, hA⟩ :=
    IsCompact.exists_eventually_norm_le_mul_infDist_sq_and_norm_fderiv_le_mul_infDist
      (K := {e (ι y)}) (Z := Z) (U := U) isCompact_singleton
      (singleton_subset_iff.2 (mem_image_of_mem e ⟨hy, mem_range_self y⟩))
      (e.isOpen_inter_preimage_symm hOo) (singleton_subset_iff.2 hz₀U) hgU
      (fun z hz ↦ by
        obtain ⟨y', hzy, -, -, hD0, -⟩ := hZU z hz
        simp [hzy, hD0])
      (fun z hz ↦ by
        obtain ⟨y', -, hys, rfl, -, hD1⟩ := hZU z hz
        have := (mvfderiv_eq_zero_iff_fderiv_comp_extend_symm_eq_zero he1 hys).1 hD1
        rwa [hsymm, hext] at this)
  rw [nhdsSet_singleton] at hA
  exact ⟨A, hA.mono fun z hz ↦ ⟨by simpa using hz.1, hz.2⟩⟩

end Topology.IsEmbedding

end
