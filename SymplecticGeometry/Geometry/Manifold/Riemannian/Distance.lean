/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Curve

/-!
# The mean value inequality for the Riemannian distance

For a map `f` from a real normed space `F` to a manifold `M` whose tangent spaces carry a
Riemannian metric, `C¹` at the points of the segment from `a` to `b`, the Riemannian extended
distance from `f a` to `f b` is at most any bound `C` on the norms of `df_z (b - a)` for `z` on
the segment: it is at most the length of the image of the segment under `f`.

The proof adapts Tau Ceti's `IsRiemannianManifold.edist_le_of_norm_mfderiv_le`, which states the
same bound for the distance of a Riemannian manifold with a given extended metric equal to its
Riemannian one; here no metric structure on `M` is assumed, and the conclusion is stated for
Mathlib's `Manifold.riemannianEDist`.

## Main results

* `Manifold.riemannianEDist_le_of_norm_mfderiv_le`: the mean value inequality for
  `Manifold.riemannianEDist`.
-/

public section

open Bundle Set
open scoped Manifold

namespace Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **The mean value inequality for the Riemannian distance.** Let `f` be a map from a real
normed space to a manifold with a Riemannian metric, `C¹` at every point of the segment from `a`
to `b`. If its differential at the points of that segment sends `b - a` to vectors of norm at
most `C`, then the Riemannian extended distance from `f a` to `f b` is at most `C`. -/
theorem riemannianEDist_le_of_norm_mfderiv_le {f : F → M} {a b : F} {C : ℝ}
    (hf : ∀ z ∈ segment ℝ a b, ContMDiffAt 𝓘(ℝ, F) I 1 f z)
    (hC : ∀ z ∈ segment ℝ a b, ‖mfderiv 𝓘(ℝ, F) I f z (b - a)‖ ≤ C) :
    riemannianEDist I (f a) (f b) ≤ ENNReal.ofReal C := by
  let c : ℝ → F := fun τ ↦ a + τ • (b - a)
  have hcseg : MapsTo c (Icc 0 1) (segment ℝ a b) := fun τ hτ ↦ by
    rw [segment_eq_image']
    exact ⟨τ, hτ, rfl⟩
  have hcderiv : ∀ τ, HasDerivAt c (b - a) τ := fun τ ↦
    (((hasDerivAt_id' τ).smul_const (b - a)).const_add a).congr_deriv (one_smul ℝ _)
  have hc : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, F) 1 c := by
    rw [contMDiff_iff_contDiff]
    exact contDiff_const.add (contDiff_id.smul contDiff_const)
  have hsmooth : CMDiff[Icc 0 1] 1 (f ∘ c) := fun τ hτ ↦
    (hf _ (hcseg hτ)).comp_contMDiffWithinAt τ hc.contMDiffAt.contMDiffWithinAt
  calc
    riemannianEDist I (f a) (f b) ≤ pathELength I (f ∘ c) 0 1 :=
      riemannianEDist_le_pathELength hsmooth (by simp [c]) (by simp [c]) zero_le_one
    _ = ∫⁻ τ in Ioo 0 1, ‖mfderiv 𝓘(ℝ, ℝ) I (f ∘ c) τ (1 : ℝ)‖ₑ :=
      pathELength_eq_lintegral_mfderiv_Ioo
    _ ≤ ∫⁻ _ in Ioo (0 : ℝ) 1, ENNReal.ofReal C := by
      refine MeasureTheory.setLIntegral_mono' measurableSet_Ioo fun τ hτ ↦ ?_
      have hτ' : c τ ∈ segment ℝ a b := hcseg (Ioo_subset_Icc_self hτ)
      rw [← TauCeti.Manifold.curveVelocity_apply,
        ((hf _ hτ').mdifferentiableAt one_ne_zero).curveVelocity_comp_mfderiv (hcderiv τ),
        ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hC _ hτ')
    _ = ENNReal.ofReal C := by simp

end Manifold

end
