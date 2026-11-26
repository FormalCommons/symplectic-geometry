/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.Riemannian.Distance
import TauCeti.Geometry.Manifold.Riemannian.MetricBridge

/-!
# Distances in a chart bounded by the Riemannian distance

Let `M` be a Hausdorff manifold whose tangent spaces carry a Riemannian metric, and
`φ : PartialDiffeomorph I 𝓘(ℝ, F) M F n`, `n ≥ 1`, a chart into a proper real normed space `F`.
If the ball `B` of radius `R` about `φ x` lies in the target of `φ`, and the differential of `φ`
stretches Riemannian norms by at most `C ≠ 0` at every point of the source whose image lies in `B`,
then for every `z ∈ B`, `‖z - φ x‖ ≤ C · d(x, φ⁻¹ z)`, `d` the Riemannian distance.

The proof bounds the length of each `C¹` path `γ` from `x` to `φ⁻¹ z`. As long as `γ` stays in
the preimage `W` of `B`, Tau Ceti's `TauCeti.Manifold.enorm_sub_le_mul_pathELength` bounds the
displacement of `φ ∘ γ` by `C` times the length of `γ`. If that length were less than
`‖z - φ x‖ / C`, then `γ` could not leave `W`: before the first time `τ` at which it would, it
stays in the image under `φ⁻¹` of a closed ball of radius `r < R`, a compact set, so closed, and
so does `γ τ`, which then lies in `W`. So the whole path stays in `W`, and its endpoint gives the
bound.

## Main results

* `PartialDiffeomorph.ofReal_norm_sub_le_mul_riemannianEDist`: the lower bound for the
  Riemannian distance by distances in the chart.
-/

public section

open Bundle Metric Set
open scoped ENNReal NNReal Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ∞ω}

namespace PartialDiffeomorph

/-- **Chart distances are bounded by the Riemannian distance.** Let `φ` be a `C¹` partial
diffeomorphism from a Hausdorff manifold `M` with a Riemannian metric to a proper real normed
space `F`, and `x` a point of its source. If the ball of radius `R` about `φ x` lies in the
target of `φ`, and the differential of `φ` stretches tangent vectors by at most `C ≠ 0` at the
points of the source whose image lies in that ball, then every `z` in the ball satisfies
`‖z - φ x‖ ≤ C · d(x, φ⁻¹ z)`, for `d` the Riemannian extended distance. -/
theorem ofReal_norm_sub_le_mul_riemannianEDist [T2Space M] [ProperSpace F]
    (φ : PartialDiffeomorph I 𝓘(ℝ, F) M F n) (hn : 1 ≤ n) {x : M} (hx : x ∈ φ.source) {R : ℝ}
    (hR : ball (φ x) R ⊆ φ.target) {C : ℝ≥0} (hC0 : C ≠ 0)
    (hC : ∀ y ∈ φ.source, φ y ∈ ball (φ x) R → ∀ v : TangentSpace I y,
      ‖mvfderiv I φ y v‖ ≤ C * ‖v‖)
    {z : F} (hz : z ∈ ball (φ x) R) :
    ENNReal.ofReal ‖z - φ x‖ ≤ C * Manifold.riemannianEDist I x (φ.symm z) := by
  -- The points of the source whose image lies in the ball.
  set W := φ.source ∩ φ ⁻¹' ball (φ x) R
  have hW : IsOpen W :=
    φ.contMDiffOn.continuousOn.isOpen_inter_preimage φ.open_source isOpen_ball
  have hxW : x ∈ W := ⟨hx, mem_ball_self ((dist_nonneg).trans_lt hz)⟩
  have hφ1 : CMDiff[φ.source] 1 φ := φ.contMDiffOn.of_le hn
  have hCe : ∀ y ∈ W, ∀ v : TangentSpace I y, ‖mvfderiv I φ y v‖ₑ ≤ C * ‖v‖ₑ := by
    intro y hy v
    rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_coe_nnreal,
      ← ENNReal.ofReal_mul (NNReal.coe_nonneg C)]
    exact ENNReal.ofReal_le_ofReal (hC y hy.1 hy.2 v)
  -- Along a path that stays in `W` up to time `t`, `φ ∘ γ` moves by at most `C` times the
  -- length of the path.
  have hbound : ∀ γ : ℝ → M, γ 0 = x → CMDiff[Icc 0 1] 1 γ → ∀ t ∈ Icc (0 : ℝ) 1,
      (∀ u ∈ Icc 0 t, γ u ∈ W) → ‖φ (γ t) - φ x‖ₑ ≤ C * Manifold.pathELength I γ 0 1 := by
    intro γ hγ0 hγ t ht hγW
    have hγt : CMDiff[Icc 0 t] 1 γ := hγ.mono (Icc_subset_Icc le_rfl ht.2)
    have h := TauCeti.Manifold.enorm_sub_le_mul_pathELength (f := φ) ht.1
      (hγt.mdifferentiableOn one_ne_zero) (hφ1.comp hγt fun u hu ↦ (hγW u hu).1)
      (fun u hu ↦ φ.mdifferentiableAt (zero_lt_one.trans_le hn).ne' (hγW u hu).1)
      -- `mvfderiv` and `mfderiv` into `F` agree, and so do the norms on `F` and on its tangent
      -- spaces, up to definitional unfolding.
      fun u hu ↦ hCe _ (hγW u hu) _
    rw [hγ0] at h
    exact h.trans (by gcongr; exact ht.2)
  -- Every path from `x` to `φ.symm z` has length at least `‖z - φ x‖ / C`.
  have key : ∀ γ : ℝ → M, γ 0 = x → γ 1 = φ.symm z → CMDiff[Icc 0 1] 1 γ →
      ENNReal.ofReal ‖z - φ x‖ ≤ C * Manifold.pathELength I γ 0 1 := by
    intro γ hγ0 hγ1 hγ
    have hz1 : φ (γ 1) = z := by
      rw [hγ1, PartialDiffeomorph.symm_toPartialEquiv, φ.right_inv (hR hz)]
    by_contra hlt
    rw [not_le] at hlt
    set r := (C * Manifold.pathELength I γ 0 1).toReal
    have hr : C * Manifold.pathELength I γ 0 1 = ENNReal.ofReal r :=
      (ENNReal.ofReal_toReal (hlt.trans ENNReal.ofReal_lt_top).ne).symm
    have hrR : r < R := by
      rw [hr] at hlt
      exact ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg).1 hlt).trans
        (mem_ball_iff_norm.1 hz)
    -- The image `K` under `φ.symm` of the closed ball of radius `r` is compact, so closed, and
    -- it lies in `W`.
    have hKball : closedBall (φ x) r ⊆ ball (φ x) R := closedBall_subset_ball hrR
    set K := φ.toPartialEquiv.symm '' closedBall (φ x) r
    have hK : IsClosed K := ((isCompact_closedBall (φ x) r).image_of_continuousOn
      (φ.contMDiffOn_invFun.continuousOn.mono (hKball.trans hR))).isClosed
    have hKW : K ⊆ W := by
      rintro _ ⟨w, hw, rfl⟩
      have hwt := hR (hKball hw)
      exact ⟨φ.map_target hwt, by rw [mem_preimage, φ.right_inv hwt]; exact hKball hw⟩
    -- A path that stays in `W` up to time `t` lies in `K` at time `t`.
    have hstay : ∀ t ∈ Icc (0 : ℝ) 1, (∀ u ∈ Icc 0 t, γ u ∈ W) → γ t ∈ K := by
      intro t ht hγW
      refine ⟨φ (γ t), ?_, φ.left_inv (hγW t ⟨ht.1, le_rfl⟩).1⟩
      rw [mem_closedBall_iff_norm, ← ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg,
        ofReal_norm, ← hr]
      exact hbound γ hγ0 hγ t ht hγW
    -- So `γ` never leaves `W`: at the first time `τ` it would, `γ τ` lies in the closure of
    -- `γ '' Ico 0 τ`, inside the closed set `K ⊆ W`.
    have hall : ∀ u ∈ Icc (0 : ℝ) 1, γ u ∈ W := by
      by_contra hne
      push Not at hne
      set S := Icc (0 : ℝ) 1 ∩ γ ⁻¹' Wᶜ
      have hS : IsClosed S :=
        hγ.continuousOn.preimage_isClosed_of_isClosed isClosed_Icc hW.isClosed_compl
      have hSne : S.Nonempty := let ⟨u, hu, hu'⟩ := hne; ⟨u, hu, hu'⟩
      have hbdd : BddBelow S := ⟨0, fun t ht ↦ ht.1.1⟩
      set τ := sInf S
      have hτ : τ ∈ S := hS.csInf_mem hSne hbdd
      have hbefore : ∀ u ∈ Icc (0 : ℝ) 1, u < τ → γ u ∈ W := fun u hu huτ ↦
        by_contra fun h ↦ (csInf_le hbdd ⟨hu, h⟩).not_gt huτ
      have hτ0 : 0 < τ := lt_of_le_of_ne hτ.1.1 fun h ↦ hτ.2 (by rw [← h, hγ0]; exact hxW)
      have hsub : γ '' Ico 0 τ ⊆ K := by
        rintro _ ⟨t, ht, rfl⟩
        have ht1 : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.le.trans hτ.1.2⟩
        exact hstay t ht1 fun u hu ↦ hbefore u ⟨hu.1, hu.2.trans ht1.2⟩ (hu.2.trans_lt ht.2)
      have hcl : τ ∈ closure (Ico 0 τ) := by
        rw [closure_Ico hτ0.ne]
        exact ⟨hτ.1.1, le_rfl⟩
      have hγτ := ((hγ.continuousOn τ hτ.1).mono
        (Ico_subset_Icc_self.trans (Icc_subset_Icc le_rfl hτ.1.2))).mem_closure_image hcl
      exact hτ.2 (hKW (hK.closure_subset_iff.2 hsub hγτ))
    have h1 := hbound γ hγ0 hγ 1 ⟨zero_le_one, le_rfl⟩ fun u hu ↦ hall u ⟨hu.1, hu.2⟩
    rw [hz1, ← ofReal_norm] at h1
    exact hlt.not_ge h1
  have hC0' : (C : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.2 hC0
  calc ENNReal.ofReal ‖z - φ x‖ = C * (ENNReal.ofReal ‖z - φ x‖ / C) :=
        (ENNReal.mul_div_cancel hC0' ENNReal.coe_ne_top).symm
    _ ≤ C * Manifold.riemannianEDist I x (φ.symm z) := by
        gcongr
        exact TauCeti.Manifold.le_riemannianEDist_of_forall_le_pathELength fun γ h0 h1 hγ ↦
          ENNReal.div_le_of_le_mul' (key γ h0 h1 hγ)

end PartialDiffeomorph
