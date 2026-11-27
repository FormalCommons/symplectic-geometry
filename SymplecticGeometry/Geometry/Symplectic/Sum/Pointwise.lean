/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.Graph
import TauCeti.Geometry.Symplectic.Manifold.Opens
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Opens
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.Smooth

/-!
# Nondegenerate forms that follow a homotopy outside a ball

This file holds the one-chart step of the pointwise obstruction to symplectic connected sums
[McDuffSalamon2017, Lemma 7.2.2]: a nondegenerate two-form `η` near a ball is joined, through a
homotopy `β` of nondegenerate forms on the complement of a smaller ball ending at `η`, to the
start `β 0` of the homotopy far out. The form is `η` near the ball and, on the complement, the
slice `SymplecticGeometry.IsSmoothFamily.sliceAlong` of `β` along a cut-off function of the
point.

## Main results

* `SymplecticGeometry.exists_isNondegenerate_eq_sliceAlong`: on a manifold covered by open sets
  `W` and `V`, for a nondegenerate form `η`, a smooth family `β` of two-forms on `V`,
  nondegenerate for `t ∈ [0, 1]`, with `β 1` the restriction of `η`, and a smooth
  `χ : V → [0, 1]` equal to `1` on `W`, there is a nondegenerate form equal to `η` on `W` whose
  restriction to `V` is the slice of `β` along `χ`.
* `SymplecticGeometry.exists_isNondegenerate_eq_of_lt_norm`: on a real normed space
  with smooth bump functions, such as a finite-dimensional one, with `0 ≤ ρ < R`,
  `V` containing `{w | ρ < ‖w‖}` and `β` as above, there is a nondegenerate form equal
  to `η` near the closed ball of radius `ρ` and to `β 0` where `R < ‖w‖`. The
  cut-off is a `ContDiffBump` between two radii in `(ρ, R)`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §7.2
  (Lemma 7.2.2).
-/

public section

noncomputable section

open Set Filter TopologicalSpace Metric TauCeti
open scoped Manifold ContDiff Topology

namespace SymplecticGeometry

section Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Let `M` be covered by an open set `W` and an open set `V`. Take a nondegenerate
two-form `η` on `M`, and let `β` be a smooth family of two-forms on `V` over `ℝ`,
nondegenerate for `t ∈ [0, 1]`, with `β 1` the restriction of `η` to `V`. For a smooth
`χ : V → [0, 1]` equal to `1` at the points of `W`, there is a nondegenerate two-form on `M` that
is `η` on `W` and whose restriction to `V` is the slice of `β` along `χ`. -/
theorem exists_isNondegenerate_eq_sliceAlong {V : Opens M} {W : Set M} (hW : IsOpen W)
    (hWV : W ∪ V = univ) {η : SmoothTwoForm I M} (hη : η.IsNondegenerate)
    {β : ℝ → SmoothTwoForm I V} (hβ : IsSmoothFamily 𝓘(ℝ, ℝ) β)
    (hβ₁ : β 1 = SmoothForm.mpullback Subtype.val contMDiff_subtypeVal η)
    (hβnd : ∀ t ∈ Icc (0 : ℝ) 1, (β t).IsNondegenerate) {χ : V → ℝ}
    (hχ : ContMDiff I 𝓘(ℝ, ℝ) ∞ χ) (hχI : ∀ x, χ x ∈ Icc (0 : ℝ) 1)
    (hχW : ∀ x : V, (x : M) ∈ W → χ x = 1) :
    ∃ τ : SmoothTwoForm I M, τ.IsNondegenerate ∧ (∀ x ∈ W, τ.val x = η.val x) ∧
      SmoothForm.mpullback Subtype.val contMDiff_subtypeVal τ = hβ.sliceAlong χ hχ := by
  classical
  set σ := hβ.sliceAlong χ hχ
  -- On `V ∩ W` the slice is `β 1`, the restriction of `η`.
  have hσ : ∀ x : V, (x : M) ∈ W → σ.val x = η.val x := fun x hx ↦ by
    rw [IsSmoothFamily.sliceAlong_val, hχW x hx, hβ₁, SmoothForm.coe_mpullback,
      mpullback_subtype_val_apply]
  let γ : RoughForm I M ℝ 2 := fun y ↦ if hy : y ∈ V then σ.val ⟨y, hy⟩ else η.val y
  have hγW : ∀ y ∈ W, γ y = η.val y := fun y hyW ↦ by
    by_cases hy : y ∈ V
    · exact (dite_eq_left hy).trans (hσ ⟨y, hy⟩ hyW)
    · exact dite_eq_right hy
  have hγV : mpullback I I (Subtype.val : V → M) γ = σ.val :=
    funext fun x ↦ (mpullback_subtype_val_apply γ x).trans (dite_eq_left x.property)
  have hγ : IsSmoothForm I ∞ γ := by
    rw [isSmoothForm_def]
    intro y
    by_cases hy : y ∈ V
    · exact (contMDiffAt_mpullback_subtype_val_iff γ ⟨y, hy⟩).1 (hγV ▸ σ.contMDiff ⟨y, hy⟩)
    · have hyW : y ∈ W := (hWV.symm.subset (mem_univ y)).resolve_right hy
      refine (η.contMDiff y).congr_of_eventuallyEq ?_
      filter_upwards [hW.mem_nhds hyW] with z hz
      rw [hγW z hz]
  let τ : SmoothTwoForm I M := ⟨γ, hγ.mem_smoothBundleForms⟩
  have hτV : SmoothForm.mpullback Subtype.val contMDiff_subtypeVal τ = σ :=
    (SmoothForm.mpullback_eq_iff _).2 hγV
  have hnd : ∀ y, (τ.bilinFormAt y).Nondegenerate := fun y ↦ by
    by_cases hy : y ∈ V
    · have hσnd : SmoothTwoForm.IsNondegenerate σ := hβ.isNondegenerate_sliceAlong hχ hχI hβnd
      exact (SmoothTwoForm.nondegenerate_bilinFormAt_mpullback_subtype_val_iff ⟨y, hy⟩).1
        (hτV ▸ hσnd.nondegenerate_bilinFormAt ⟨y, hy⟩)
    · have hyW : y ∈ W := (hWV.symm.subset (mem_univ y)).resolve_right hy
      have : τ.bilinFormAt y = η.bilinFormAt y := LinearMap.ext₂ fun v w ↦ by
        rw [SmoothForm.bilinFormAt_apply, SmoothForm.bilinFormAt_apply,
          SmoothBundleForm.eval₂_apply, SmoothBundleForm.eval₂_apply]
        exact congrArg (fun a ↦ a ![v, w]) (hγW y hyW)
      exact this ▸ hη.nondegenerate_bilinFormAt y
  exact ⟨τ, SmoothTwoForm.isNondegenerate_iff_forall_ker_bilinFormAt_eq_bot.2 fun y ↦
    (hnd y).ker_eq_bot, hγW, hτV⟩

end Manifold

section BumpFunction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [HasContDiffBump E]

/-- Let `0 ≤ ρ < R` and let `V` be an open set in a real normed space `E` with smooth bump
functions (`HasContDiffBump E`, as for every finite-dimensional `E`) that contains every `w`
with `ρ < ‖w‖`. Let `η` be a nondegenerate two-form on `E`, and
`β` a smooth family of two-forms on `V` over `ℝ`, nondegenerate for `t ∈ [0, 1]`, with `β 1` the
restriction of `η` to `V`. Then there is a nondegenerate two-form on `E` equal to `η` near the
closed ball of radius `ρ` and whose restriction to `V` is `β 0` at the points with
`R < ‖w‖`. -/
theorem exists_isNondegenerate_eq_of_lt_norm {ρ R : ℝ} (hρ : 0 ≤ ρ) (hρR : ρ < R)
    {V : Opens E} (hV : ∀ w, ρ < ‖w‖ → w ∈ V) {η : SmoothTwoForm 𝓘(ℝ, E) E}
    (hη : η.IsNondegenerate) {β : ℝ → SmoothTwoForm 𝓘(ℝ, E) V}
    (hβ : IsSmoothFamily 𝓘(ℝ, ℝ) β)
    (hβ₁ : β 1 = SmoothForm.mpullback Subtype.val contMDiff_subtypeVal η)
    (hβnd : ∀ t ∈ Icc (0 : ℝ) 1, (β t).IsNondegenerate) :
    ∃ τ : SmoothTwoForm 𝓘(ℝ, E) E, τ.IsNondegenerate ∧
      (∀ᶠ x in 𝓝ˢ (closedBall (0 : E) ρ), τ.val x = η.val x) ∧
      ∀ x : V, R < ‖(x : E)‖ →
        (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal τ).val x = (β 0).val x := by
  -- A bump function equal to `1` within `(2ρ + R) / 3` and `0` from `R` on.
  let f : ContDiffBump (0 : E) :=
    ⟨(2 * ρ + R) / 3, R, by linarith, by linarith⟩
  have hχ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (fun x : V ↦ f x) :=
    f.contDiff.contMDiff.comp contMDiff_subtypeVal
  have hball : IsOpen (ball (0 : E) ((2 * ρ + R) / 3)) := isOpen_ball
  obtain ⟨τ, hτ, hτW, hτV⟩ := exists_isNondegenerate_eq_sliceAlong hball
    (eq_univ_of_forall fun w ↦ by
      by_cases hw : ‖w‖ < (2 * ρ + R) / 3
      · exact Or.inl (mem_ball_zero_iff.2 hw)
      · exact Or.inr (hV w (by linarith [not_lt.1 hw])))
    hη hβ hβ₁ hβnd hχ (fun x ↦ ⟨f.nonneg, f.le_one⟩)
    (fun x hx ↦ f.one_of_mem_closedBall (ball_subset_closedBall hx))
  refine ⟨τ, hτ, ?_, fun x hx ↦ ?_⟩
  · refine eventually_of_mem (hball.mem_nhdsSet.2 (closedBall_subset_ball ?_)) hτW
    linarith
  · have h0 : f x = 0 := f.zero_of_le_dist (by rw [dist_zero_right]; exact hx.le)
    rw [hτV, IsSmoothFamily.sliceAlong_val]
    simp only [h0]

end BumpFunction

end SymplecticGeometry

end
