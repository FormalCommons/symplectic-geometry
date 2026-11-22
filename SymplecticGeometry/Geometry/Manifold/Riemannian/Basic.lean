/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Topology.Order.Compact

/-!
# Uniform bounds for the differential of a `C¹` map on a compact set

Let `f` be a `C¹` map from an open subset `U` of a finite-dimensional real normed space `F` to a
manifold `M` whose tangent spaces carry a continuous Riemannian metric. On a compact `K ⊆ U`, the
differential of `f` is bounded for the Riemannian norm, and if it is injective at every point of
`K`, it is bounded below there.

Both bounds come from the joint continuity of `(z, ξ) ↦ ‖df_z ξ‖`
(Tau Ceti's `ContMDiffOn.continuousOn_norm_mfderiv_apply`) on the compact set `K × S`, `S` the
unit sphere of `F`, together with Mathlib's passage from unit vectors to all vectors
(`ContinuousLinearMap.opNorm_le_of_unit_norm`, `antilipschitz_of_bound_of_norm_one`).

## Main results

* `ContMDiffOn.exists_norm_mfderiv_le_mul_norm`: the differential of a `C¹` map is bounded on a
  compact subset of its open domain.
* `ContMDiffOn.exists_pos_mul_norm_le_norm_mfderiv`: where the differential is injective on a
  compact set, it is bounded below there.
-/

public section

open Bundle Set
open scoped ContDiff Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {f : F → M} {U K : Set F} {n : ℕ∞ω}

namespace ContMDiffOn

/-- The differential of a `C¹` map from an open subset `U` of a finite-dimensional real normed
space to a manifold with a continuous Riemannian metric is bounded on a compact `K ⊆ U`:
`‖df_y v‖ ≤ C * ‖v‖` for every `y ∈ K` and every `v`. -/
theorem exists_norm_mfderiv_le_mul_norm (hf : ContMDiffOn 𝓘(ℝ, F) I n f U) (hn : 1 ≤ n)
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C, ∀ y ∈ K, ∀ v : F, ‖mfderiv 𝓘(ℝ, F) I f y v‖ ≤ C * ‖v‖ := by
  obtain ⟨C, hC⟩ := (hK.prod (isCompact_sphere (0 : F) 1)).exists_bound_of_continuousOn
    ((hf.continuousOn_norm_mfderiv_apply hn hU).mono (prod_mono hKU (subset_univ _)))
  refine ⟨max C 0, fun y hy v ↦ ?_⟩
  let L : F →L[ℝ] TangentSpace I (f y) := mfderiv 𝓘(ℝ, F) I f y
  refine L.le_of_opNorm_le (L.opNorm_le_of_unit_norm (le_max_right _ _) fun u hu ↦ ?_) v
  have := hC (y, u) (mk_mem_prod hy (mem_sphere_zero_iff_norm.2 hu))
  exact (le_abs_self _).trans (this.trans (le_max_left _ _))

/-- If a `C¹` map from an open subset `U` of a finite-dimensional real normed space to a manifold
with a continuous Riemannian metric has injective differentials on a compact `K ⊆ U`, they are
uniformly bounded below there: `c * ‖v‖ ≤ ‖df_y v‖` for some `0 < c`, every `y ∈ K` and every
`v`. -/
theorem exists_pos_mul_norm_le_norm_mfderiv (hf : ContMDiffOn 𝓘(ℝ, F) I n f U) (hn : 1 ≤ n)
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hinj : ∀ y ∈ K, Function.Injective (mfderiv 𝓘(ℝ, F) I f y)) :
    ∃ c, 0 < c ∧ ∀ y ∈ K, ∀ v : F, c * ‖v‖ ≤ ‖mfderiv 𝓘(ℝ, F) I f y v‖ := by
  -- A uniform lower bound `c` on unit vectors gives the bound on all vectors.
  suffices ∃ c, 0 < c ∧ ∀ y ∈ K, ∀ u : F, ‖u‖ = 1 → c ≤ ‖mfderiv 𝓘(ℝ, F) I f y u‖ by
    obtain ⟨c, hc, hcK⟩ := this
    refine ⟨c, hc, fun y hy v ↦ ?_⟩
    let L : F →L[ℝ] TangentSpace I (f y) := mfderiv 𝓘(ℝ, F) I f y
    have hL : AntilipschitzWith (Real.toNNReal c⁻¹) L :=
      antilipschitz_of_bound_of_norm_one (𝕜 := ℝ) L fun u hu ↦ by
        rw [Real.coe_toNNReal _ (inv_nonneg.2 hc.le), ← div_eq_inv_mul, one_le_div hc]
        exact hcK y hy u hu
    have := hL.le_mul_norm (map_zero L) v
    rwa [Real.coe_toNNReal _ (inv_nonneg.2 hc.le), ← div_eq_inv_mul, le_div_iff₀ hc,
      mul_comm] at this
  rcases (K ×ˢ Metric.sphere (0 : F) 1).eq_empty_or_nonempty with he | hne
  · exact ⟨1, one_pos, fun y hy u hu ↦
      (he.subset (mk_mem_prod hy (mem_sphere_zero_iff_norm.2 hu))).elim⟩
  obtain ⟨⟨y₀, u₀⟩, ⟨hy₀, hu₀⟩, hmin⟩ := (hK.prod (isCompact_sphere (0 : F) 1)).exists_isMinOn
    hne ((hf.continuousOn_norm_mfderiv_apply hn hU).mono (prod_mono hKU (subset_univ _)))
  have hu₀' : u₀ ≠ 0 := ne_zero_of_mem_unit_sphere ⟨u₀, hu₀⟩
  refine ⟨‖mfderiv 𝓘(ℝ, F) I f y₀ u₀‖, norm_pos_iff.2 fun h ↦ hu₀' ?_, fun y hy u hu ↦
    hmin (mk_mem_prod hy (mem_sphere_zero_iff_norm.2 hu))⟩
  exact (injective_iff_map_eq_zero
    (mfderiv 𝓘(ℝ, F) I f y₀ : F →L[ℝ] TangentSpace I (f y₀))).1 (hinj y₀ hy₀) u₀ h

end ContMDiffOn

end
