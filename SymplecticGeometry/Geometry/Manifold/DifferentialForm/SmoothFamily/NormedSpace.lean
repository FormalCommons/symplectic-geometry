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
`K × S`. The latter needs only the joint continuity, so it is stated first for families of
two-forms over any topological space whose values are jointly continuous on `K × S`.

## Main results

* `SymplecticGeometry.IsSmoothFamily.exists_norm_val_le`: the value of a smooth family of forms
  on a normed space is bounded on `K × S`, for compact `K` and `S`.
* `SymplecticGeometry.exists_pos_forall_nondegenerate_of_continuousOn`: if the values of the
  two-forms `τ t` are jointly continuous on `K × S` and nondegenerate at every point of `S` for
  every `t ∈ K`, then there is `r > 0` such that every two-form `σ` with
  `‖σ x - τ t x‖ < r`, for some `t ∈ K` and `x ∈ S`, is nondegenerate at `x`.
* `SymplecticGeometry.exists_pos_forall_nondegenerate_sub_smul_of_continuousOn`: the same `r`
  works along segments: `τ t - s • η` is nondegenerate at `x ∈ S` for `t ∈ K`, `s ∈ [0, 1]`
  and every two-form `η` with `‖η x‖ < r`.
* `SymplecticGeometry.IsSmoothFamily.exists_pos_forall_nondegenerate` and
  `SymplecticGeometry.IsSmoothFamily.exists_pos_forall_nondegenerate_sub_smul`: the two
  previous results for a smooth family over a manifold.

`exists_pos_forall_nondegenerate_of_continuousOn` combines the openness of nondegenerate
alternating maps (`ContinuousAlternatingMap.isOpen_setOfPred_nondegenerate_toBilinMap`) with
Mathlib's `IsCompact.exists_thickening_subset_open`, applied to the compact image of `K × S`.
-/

public section

open Set TauCeti
open scoped Manifold

namespace SymplecticGeometry

variable {E EN HN N F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
  [TopologicalSpace N] [ChartedSpace HN N] {J : ModelWithCorners ℝ EN HN} [IsManifold J 1 N]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ} {α : N → SmoothForm 𝓘(ℝ, E) E F k}

section ContinuousOn

variable [FiniteDimensional ℝ E] {Λ : Type*} [TopologicalSpace Λ]
  {τ : Λ → SmoothTwoForm 𝓘(ℝ, E) E} {K : Set Λ} {S : Set E}

/-- **Uniform nondegeneracy on compact sets, for continuous families.** Let `τ` be a family of
two-forms on a finite-dimensional normed space `E`, over a topological space `Λ`, whose value
`(τ t).val x` is jointly continuous in `(t, x)` on `K × S`, for compact sets `K ⊆ Λ` and
`S ⊆ E`, and nondegenerate at every `x ∈ S` for every `t ∈ K`. Then there is `r > 0` such that
every two-form `σ` on `E` with `‖σ x - τ t x‖ < r` for some `t ∈ K` and `x ∈ S` is
nondegenerate at `x`. -/
theorem exists_pos_forall_nondegenerate_of_continuousOn
    (h : ContinuousOn (Y := E [⋀^Fin 2]→L[ℝ] ℝ) (fun p : Λ × E ↦ (τ p.1).val p.2) (K ×ˢ S))
    (hK : IsCompact K) (hS : IsCompact S)
    (hτ : ∀ t ∈ K, ∀ x ∈ S, ((τ t).bilinFormAt x).Nondegenerate) :
    ∃ r > 0, ∀ t ∈ K, ∀ x ∈ S, ∀ σ : SmoothTwoForm 𝓘(ℝ, E) E,
      @norm (E [⋀^Fin 2]→L[ℝ] ℝ) _ (σ.val x - (τ t).val x) < r →
        (σ.bilinFormAt x).Nondegenerate := by
  obtain ⟨r, hr, hrU⟩ := ((hK.prod hS).image_of_continuousOn h).exists_thickening_subset_open
    ContinuousAlternatingMap.isOpen_setOfPred_nondegenerate_toBilinMap (by
      rintro _ ⟨p, hp, rfl⟩
      have := hτ p.1 hp.1 p.2 hp.2
      rwa [SmoothForm.bilinFormAt_def] at this)
  refine ⟨r, hr, fun t ht x hx σ hσ ↦ ?_⟩
  have := hrU (Metric.mem_thickening_iff.2 ⟨_, mem_image_of_mem _ (mk_mem_prod ht hx),
    (dist_eq_norm _ _).trans_lt hσ⟩)
  rwa [SmoothForm.bilinFormAt_def]

/-- **Uniform nondegeneracy along segments, for continuous families.** Let `τ` be a family of
two-forms on a finite-dimensional normed space `E`, over a topological space `Λ`, whose value
`(τ t).val x` is jointly continuous in `(t, x)` on `K × S`, for compact sets `K ⊆ Λ` and
`S ⊆ E`, and nondegenerate at every `x ∈ S` for every `t ∈ K`. Then there is `r > 0` such that
for every two-form `η` on `E` with `‖η x‖ < r` at a point `x ∈ S`, the two-forms `τ t - s • η`
with `t ∈ K` and `s ∈ [0, 1]` are nondegenerate at `x`. -/
theorem exists_pos_forall_nondegenerate_sub_smul_of_continuousOn
    (h : ContinuousOn (Y := E [⋀^Fin 2]→L[ℝ] ℝ) (fun p : Λ × E ↦ (τ p.1).val p.2) (K ×ˢ S))
    (hK : IsCompact K) (hS : IsCompact S)
    (hτ : ∀ t ∈ K, ∀ x ∈ S, ((τ t).bilinFormAt x).Nondegenerate) :
    ∃ r > 0, ∀ t ∈ K, ∀ x ∈ S, ∀ η : SmoothTwoForm 𝓘(ℝ, E) E,
      @norm (E [⋀^Fin 2]→L[ℝ] ℝ) _ (η.val x) < r → ∀ s ∈ Icc (0 : ℝ) 1,
        ((τ t - s • η).bilinFormAt x).Nondegenerate := by
  obtain ⟨r, hr, H⟩ := exists_pos_forall_nondegenerate_of_continuousOn h hK hS hτ
  refine ⟨r, hr, fun t ht x hx η hη s hs ↦ H t ht x hx _ ?_⟩
  -- The value of `τ t - s • η` at `x` differs from that of `τ t` by `s` times that of `η`.
  have key (a b : E [⋀^Fin 2]→L[ℝ] ℝ) : ‖a - s • b - a‖ ≤ ‖b‖ := by
    rw [sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
    exact mul_le_of_le_one_left (norm_nonneg _) hs.2
  simp only [SmoothBundleForm.sub_apply, SmoothBundleForm.smul_apply]
  -- The values of forms on `E` are alternating maps on `E` itself, so `key` applies to them.
  exact (key _ _).trans_lt hη

end ContinuousOn

namespace IsSmoothFamily

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
        (σ.bilinFormAt x).Nondegenerate :=
  exists_pos_forall_nondegenerate_of_continuousOn h.continuous_val.continuousOn hK hS hτ

/-- **Uniform nondegeneracy along segments.** Let `τ` be a smooth family of two-forms on a
finite-dimensional normed space `E`, nondegenerate at every point of a compact set `S` for every
parameter in a compact set `K`. Then there is `r > 0` such that for every two-form `η` on `E`
with `‖η x‖ < r` at a point `x ∈ S`, the two-forms `τ t - s • η` with `t ∈ K` and `s ∈ [0, 1]`
are nondegenerate at `x`. -/
theorem exists_pos_forall_nondegenerate_sub_smul [FiniteDimensional ℝ E]
    {τ : N → SmoothTwoForm 𝓘(ℝ, E) E} (h : IsSmoothFamily J τ) {K : Set N} {S : Set E}
    (hK : IsCompact K) (hS : IsCompact S)
    (hτ : ∀ t ∈ K, ∀ x ∈ S, ((τ t).bilinFormAt x).Nondegenerate) :
    ∃ r > 0, ∀ t ∈ K, ∀ x ∈ S, ∀ η : SmoothTwoForm 𝓘(ℝ, E) E,
      @norm (E [⋀^Fin 2]→L[ℝ] ℝ) _ (η.val x) < r → ∀ s ∈ Icc (0 : ℝ) 1,
        ((τ t - s • η).bilinFormAt x).Nondegenerate :=
  exists_pos_forall_nondegenerate_sub_smul_of_continuousOn h.continuous_val.continuousOn
    hK hS hτ

end IsSmoothFamily

end SymplecticGeometry

end
