/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.MetricSpace.Thickening
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Smooth
import SymplecticGeometry.Topology.Algebra.Module.BilinearForm

/-!
# Smooth families of forms on a normed space

On a normed space `E`, with its model structure `𝓘(ℝ, E)`, every tangent space is `E`, so the
values of a `k`-form on `E` all lie in the one normed space `E [⋀^Fin k]→L[ℝ] F`. For a smooth
family `α : N → SmoothForm 𝓘(ℝ, E) E F k` over a manifold `N`, the value `(α t) x` is jointly
continuous in `(t, x)` (`SymplecticGeometry.IsSmoothFamily.continuous_val`, in
`SmoothFamily/Basic.lean`). This file draws the consequences over compact sets `K ⊆ N` and
`S ⊆ E`: the values are bounded on `K × S`, and, for two-forms, nondegeneracy on `K × S`
survives every perturbation of the value that is small enough, with one bound for all of
`K × S`.

## Main results

* `SymplecticGeometry.IsSmoothFamily.exists_norm_val_le`: the value of a smooth family of forms
  on a normed space is bounded on `K × S`, for compact `K` and `S`.
* `SymplecticGeometry.IsSmoothFamily.exists_pos_forall_nondegenerate`: if the two-forms `τ t`
  are nondegenerate at every point of `S` for every `t ∈ K`, then there is `r > 0` such that
  every two-form `σ` with `‖σ x - τ t x‖ < r`, for some `t ∈ K` and `x ∈ S`, is nondegenerate
  at `x`.

The last one combines the openness of nondegenerate alternating maps
(`ContinuousAlternatingMap.isOpen_setOf_nondegenerate_toBilinMap`) with
Mathlib's `IsCompact.exists_thickening_subset_open`, applied to the compact image of `K × S`.
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

/-- **Bounds on compact sets.** The values of a smooth family `α` of forms on a normed space
`E` are bounded in norm on `K × S`, for compact sets `K` of parameters and `S` of points. -/
theorem exists_norm_val_le (h : IsSmoothFamily J α) {K : Set N} {S : Set E} (hK : IsCompact K)
    (hS : IsCompact S) :
    ∃ C, ∀ t ∈ K, ∀ x ∈ S, @norm (E [⋀^Fin k]→L[ℝ] F) _ ((α t).val x) ≤ C := by
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
      @norm (E [⋀^Fin 2]→L[ℝ] ℝ) _ (σ.val x - (τ t).val x) < r →
        (σ.bilinFormAt x).Nondegenerate := by
  obtain ⟨r, hr, hrU⟩ := ((hK.prod hS).image h.continuous_val).exists_thickening_subset_open
    ContinuousAlternatingMap.isOpen_setOf_nondegenerate_toBilinMap (by
      rintro _ ⟨p, hp, rfl⟩
      have := hτ p.1 hp.1 p.2 hp.2
      rwa [SmoothForm.bilinFormAt_def] at this)
  refine ⟨r, hr, fun t ht x hx σ hσ ↦ ?_⟩
  have := hrU (Metric.mem_thickening_iff.2 ⟨_, mem_image_of_mem _ (mk_mem_prod ht hx),
    (dist_eq_norm _ _).trans_lt hσ⟩)
  rwa [SmoothForm.bilinFormAt_def]

end SymplecticGeometry.IsSmoothFamily

end
