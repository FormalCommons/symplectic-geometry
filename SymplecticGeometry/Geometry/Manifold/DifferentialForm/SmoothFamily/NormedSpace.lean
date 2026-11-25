/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.MetricSpace.Thickening
import TauCeti.Topology.Algebra.Module.BilinearForm

/-!
# Smooth families of forms on a normed space

On a normed space `E`, with its model structure `𝓘(ℝ, E)`, every tangent space is `E`, so the
values of a `k`-form on `E` all lie in the one normed space `E [⋀^Fin k]→L[ℝ] F`. For a smooth
family `α : N → SmoothForm 𝓘(ℝ, E) E F k` over a manifold `N`, this file shows that the value
`(α t) x` is jointly continuous in `(t, x)`, and draws the consequences over compact sets
`K ⊆ N` and `S ⊆ E`: the values are bounded on `K × S`, and, for two-forms, nondegeneracy on
`K × S` survives every perturbation of the value that is small enough, with one bound for all
of `K × S`.

## Main results

* `SymplecticGeometry.IsSmoothFamily.continuous_val`: the value `(α t) x` of a smooth family of
  forms on a normed space is a continuous function of `(t, x)`.
* `SymplecticGeometry.IsSmoothFamily.exists_norm_val_le`: it is bounded on `K × S`, for compact
  `K` and `S`.
* `SymplecticGeometry.IsSmoothFamily.exists_pos_forall_nondegenerate`: if the two-forms `τ t`
  are nondegenerate at every point of `S` for every `t ∈ K`, then there is `r > 0` such that
  every two-form `σ` with `‖σ x - τ t x‖ < r`, for some `t ∈ K` and `x ∈ S`, is nondegenerate
  at `x`.

The last one combines the openness of nondegenerate alternating maps (Tau Ceti's
`TauCeti.isOpen_setOf_nondegenerate`) with Mathlib's `IsCompact.exists_thickening_subset_open`,
applied to the compact image of `K × S`.

`SymplecticGeometry.IsSmoothFamily.continuous_apply_one` (`SmoothFamily/Basic.lean`) is the
special case of one-forms on `ℝ`, evaluated on the unit vector.
-/

public section

open Set TauCeti
open scoped Manifold

namespace SymplecticGeometry.IsSmoothFamily

variable {E EN HN N F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
  [TopologicalSpace N] [ChartedSpace HN N] {J : ModelWithCorners ℝ EN HN} [IsManifold J 1 N]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ} {α : N → SmoothForm 𝓘(ℝ, E) E F k}

/-- **Joint continuity of a smooth family.** For a smooth family `α` of `k`-forms on a normed
space `E`, the value `(α t) x`, an element of `E [⋀^Fin k]→L[ℝ] F`, depends continuously on
`(t, x)`. -/
theorem continuous_val (h : IsSmoothFamily J α) :
    Continuous (Y := E [⋀^Fin k]→L[ℝ] F) fun p : N × E ↦ (α p.1).val p.2 := by
  refine continuous_iff_continuousAt.2 fun p₀ ↦ ?_
  have hc := (Bundle.contMDiffAt_totalSpace_iff.mp (isSmoothFamily_iff_contMDiff.mp h p₀)).2
  simp only [FiberBundle.trivializationAt_continuousAlternatingMap_apply_snd,
    TangentBundle.symmL_model_space] at hc
  refine hc.continuousAt.congr (Filter.Eventually.of_forall fun p ↦ ?_)
  ext v
  -- The trivialization at `p₀` is `1 : E →L[ℝ] TangentSpace 𝓘(ℝ, E) p.2`, whose target is `E`
  -- only definitionally, so `ContinuousLinearMap.one_apply` does not apply (as in
  -- `SymplecticGeometry.IsSmoothFamily.continuous_apply_one`).
  exact (ContinuousAlternatingMap.compContinuousLinearMap_apply _ _ _).trans rfl

/-- **Bounds on compact sets.** The values of a smooth family `α` of forms on a normed space
`E` are bounded in norm on `K × S`, for compact sets `K` of parameters and `S` of points. -/
theorem exists_norm_val_le (h : IsSmoothFamily J α) {K : Set N} {S : Set E} (hK : IsCompact K)
    (hS : IsCompact S) :
    ∃ C, ∀ t ∈ K, ∀ x ∈ S, ‖(show E [⋀^Fin k]→L[ℝ] F from (α t).val x)‖ ≤ C := by
  obtain ⟨C, hC⟩ := (hK.prod hS).exists_bound_of_continuousOn h.continuous_val.continuousOn
  exact ⟨C, fun t ht x hx ↦ hC (t, x) ⟨ht, hx⟩⟩

/-- **Uniform nondegeneracy on compact sets.** Let `τ` be a smooth family of two-forms on a
finite-dimensional normed space `E`, nondegenerate at every point of a compact set `S` for every
parameter in a compact set `K`. Then there is `r > 0` such that every two-form `σ` on `E` with
`‖σ x - τ t x‖ < r` for some `t ∈ K` and `x ∈ S` is nondegenerate at `x`. -/
theorem exists_pos_forall_nondegenerate [FiniteDimensional ℝ E]
    {τ : N → SmoothTwoForm 𝓘(ℝ, E) E} (h : IsSmoothFamily J τ) {K : Set N} {S : Set E}
    (hK : IsCompact K) (hS : IsCompact S)
    (hτ : ∀ t ∈ K, ∀ x ∈ S, ((τ t).bilinFormAt x).Nondegenerate) :
    ∃ r > 0, ∀ t ∈ K, ∀ x ∈ S, ∀ σ : SmoothTwoForm 𝓘(ℝ, E) E,
      ‖(show E [⋀^Fin 2]→L[ℝ] ℝ from σ.val x - (τ t).val x)‖ < r →
        (σ.bilinFormAt x).Nondegenerate := by
  -- The bilinear form of a two-form at `x` is that of its value at `x`.
  have hB (σ : SmoothTwoForm 𝓘(ℝ, E) E) (x : E) : σ.bilinFormAt x =
      MultilinearMap.toBilinMap (show E [⋀^Fin 2]→L[ℝ] ℝ from σ.val x).toMultilinearMap := by
    ext v w
    rw [SmoothForm.bilinFormAt_apply, SmoothBundleForm.eval₂_apply]
    exact (MultilinearMap.toBilinMap_apply _ v w).symm
  have hU : IsOpen {A : E [⋀^Fin 2]→L[ℝ] ℝ |
      (MultilinearMap.toBilinMap A.toMultilinearMap).Nondegenerate} :=
    TauCeti.isOpen_setOf_nondegenerate fun v w ↦ by
      simpa using continuous_eval_const ![v, w]
  obtain ⟨r, hr, hrU⟩ := ((hK.prod hS).image h.continuous_val).exists_thickening_subset_open hU
    (by
      rintro _ ⟨p, hp, rfl⟩
      have := hτ p.1 hp.1 p.2 hp.2
      rwa [hB] at this)
  refine ⟨r, hr, fun t ht x hx σ hσ ↦ ?_⟩
  have := hrU (Metric.mem_thickening_iff.2 ⟨_, mem_image_of_mem _ (mk_mem_prod ht hx),
    (dist_eq_norm _ _).trans_lt hσ⟩)
  rwa [hB]

end SymplecticGeometry.IsSmoothFamily

end
