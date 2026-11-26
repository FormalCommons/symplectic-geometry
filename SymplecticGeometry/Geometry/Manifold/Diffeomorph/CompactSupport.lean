/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Geometry.Manifold.Diffeomorph
import TauCeti.Geometry.Manifold.Diffeomorph.NormedSpace

/-!
# Diffeomorphisms of a normed space that are the identity off a compact set

A `C¹` self-map `g` of a real normed space `E` that is the identity off a compact set `C` has a
bounded derivative: `g - id` has compact support, so its derivative is bounded, and the derivative
of `g` is that of `g - id` plus the identity. For a diffeomorphism `Φ` of `E` that is the
identity off `C`, its inverse is the identity off the compact set `Φ '' C`, so both `Φ` and
`Φ.symm` have bounded derivatives, and by the mean value inequality `Φ` is Lipschitz.

## Main results

* `ContDiff.exists_norm_fderiv_le_of_forall_notMem_eq_self`: a `C¹` self-map of `E` that is the
  identity off a compact set has bounded derivative.
* `Diffeomorph.symm_apply_eq_self_of_notMem_image`: if `Φ` is the identity off `C`, then `Φ.symm`
  is the identity off `Φ '' C`.
* `Diffeomorph.exists_lipschitzWith_and_norm_fderiv_symm_le`: such a diffeomorphism is
  `L`-Lipschitz and its inverse has derivative of norm at most `L`, for one constant `L ≥ 1`.

The bound on the derivative follows the proof of Mathlib's
`ContDiff.lipschitzWith_of_hasCompactSupport`, applied to `g - id`.
-/

public section

open Set
open scoped Manifold NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : WithTop ℕ∞}

/-- A `C^n` self-map, `n ≠ 0`, of a real normed space that is the identity off a compact set has
bounded derivative. -/
theorem ContDiff.exists_norm_fderiv_le_of_forall_notMem_eq_self {g : E → E} (hg : ContDiff ℝ n g)
    (hn : n ≠ 0) {C : Set E} (hC : IsCompact C) (hgC : ∀ x ∉ C, g x = x) :
    ∃ M : ℝ≥0, ∀ x, ‖fderiv ℝ g x‖ ≤ M := by
  have hs : HasCompactSupport (g - id) :=
    HasCompactSupport.intro hC fun x hx ↦ by simp [hgC x hx]
  have hd : ContDiff ℝ n (g - id) := hg.sub contDiff_id
  obtain ⟨M, hM⟩ := (hs.fderiv ℝ).exists_bound_of_continuous (hd.continuous_fderiv hn)
  refine ⟨M.toNNReal + 1, fun x ↦ ?_⟩
  have hgx : fderiv ℝ g x = fderiv ℝ (g - id) x + ContinuousLinearMap.id ℝ E := by
    rw [fderiv_sub ((hg.differentiable hn) x) differentiableAt_id, fderiv_id, sub_add_cancel]
  rw [hgx, NNReal.coe_add, NNReal.coe_one]
  calc ‖fderiv ℝ (g - id) x + ContinuousLinearMap.id ℝ E‖
      ≤ ‖fderiv ℝ (g - id) x‖ + ‖ContinuousLinearMap.id ℝ E‖ := norm_add_le _ _
    _ ≤ M.toNNReal + 1 :=
      add_le_add ((hM x).trans (Real.le_coe_toNNReal M)) ContinuousLinearMap.norm_id_le

namespace Diffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {F H M : Type*} [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners 𝕜 F H}

/-- If a diffeomorphism `Φ` is the identity off `C`, its inverse is the identity off `Φ '' C`. -/
theorem symm_apply_eq_self_of_notMem_image (Φ : M ≃ₘ^n⟮I, I⟯ M) {C : Set M}
    (hΦ : ∀ x ∉ C, Φ x = x) {y : M} (hy : y ∉ Φ '' C) : Φ.symm y = y := by
  by_cases h : Φ.symm y ∈ C
  · exact absurd ⟨_, h, Φ.apply_symm_apply y⟩ hy
  · have := hΦ _ h
    rw [Φ.apply_symm_apply] at this
    exact this.symm

/-- A `C^n` diffeomorphism `Φ`, `n ≠ 0`, of a real normed space that is the identity off a compact
set is `L`-Lipschitz, and the derivative of its inverse has norm at most `L` everywhere, for one
constant `L ≥ 1`. -/
theorem exists_lipschitzWith_and_norm_fderiv_symm_le (Φ : E ≃ₘ^n⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ E)
    (hn : n ≠ 0) {C : Set E} (hC : IsCompact C) (hΦ : ∀ x ∉ C, Φ x = x) :
    ∃ L : ℝ≥0, 1 ≤ L ∧ LipschitzWith L Φ ∧ ∀ y, ‖fderiv ℝ Φ.symm y‖ ≤ L := by
  obtain ⟨M₁, hM₁⟩ := Φ.contDiff.exists_norm_fderiv_le_of_forall_notMem_eq_self hn hC hΦ
  obtain ⟨M₂, hM₂⟩ := Φ.symm.contDiff.exists_norm_fderiv_le_of_forall_notMem_eq_self hn
    (hC.image Φ.continuous) fun y hy ↦ Φ.symm_apply_eq_self_of_notMem_image hΦ hy
  refine ⟨max (max M₁ M₂) 1, le_max_right _ _, ?_, fun y ↦ ?_⟩
  · refine lipschitzWith_of_nnNorm_fderiv_le (Φ.differentiable hn) fun x ↦ ?_
    rw [← NNReal.coe_le_coe, coe_nnNorm]
    exact (hM₁ x).trans (by simp)
  · exact (hM₂ y).trans (by simp)

end Diffeomorph

end
