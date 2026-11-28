/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Blowup.Area
public import TauCeti.Geometry.Manifold.SmoothSingular.TopForm
public import SymplecticGeometry.LinearAlgebra.Complex.Finrank
import TauCeti.Geometry.Manifold.Complex.Integration
import SymplecticGeometry.Analysis.Complex.Euclidean.Space
import SymplecticGeometry.Geometry.Manifold.SmoothSingular.Integral

/-!
# The integral of the blowup form over a simplex of a fibre, in the model

Let `h` be a profile of the blowup of weight `l` with collar `ε` (`IsBlowupProfile l ε h`), and
`σ = ω̃_{l,ε} - π^* ω₀` the difference of the blowup form `profileForm n l ε h` of the model
blowup `BlowupModel n` of `ℂⁿ⁺¹` and the pull-back of `ω₀` by the blowdown `π`. For `v ≠ 0`, the
map `t ↦ curveLift (· • v) t` parametrizes the fibre over `[v]` of the tautological line.

This file integrates `σ` over the image under that map of a smooth singular `2`-simplex `τ` of
`ℂ` which is positively oriented for the complex orientation of `ℂ` and whose image contains every
`t` with `curveLift (· • v) t` in `L(l + ε) = closedNbhd n (l + ε)`: the integral is `-π l²`.

* `SymplecticGeometry.BlowupModel.integral_curveLift_smul_profileForm_sub`: `∫_τ σ = -π l²`.
  Off `L(l + ε)` the form `σ` vanishes (`profileForm_eq_on_compl`), so Tau Ceti's
  `TauCeti.SmoothSimplex.integral_eq_integralTopForm` turns the integral over `τ` into the
  integral of the pulled-back form over `ℂ`, which
  `TauCeti.integralTopForm_reindex_complexManifoldOrientation_eq_integral` reads as a planar
  integral; that is the disc integral
  `setIntegral_ball_eval₂_profileForm_sub_mpullback_blowdown_curveLift_smul`.
* `SymplecticGeometry.BlowupModel.integral_curveLift_smul_profileForm_sub_sub_sum_integral_δ`:
  the relative form. For a one-form `β` that vanishes off `L(l + ε)`, such as the primitive of
  `σ` off the divisor given by `exists_mextDeriv_eq_mpullback_subtypeVal_profileForm_sub`
  extended by zero, and a simplex whose faces avoid `L(l + ε)`, the integral of `σ` minus the
  integral of `β` over the boundary is still `-π l²`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §7.1, the
  proof of Theorem 7.1.21 (v).
-/

public section

noncomputable section

open CategoryTheory Opposite Simplicial Set TopologicalSpace MeasureTheory TauCeti
open scoped ContDiff Manifold TauCeti.ComplexManifold

namespace SymplecticGeometry.BlowupModel

variable {n : ℕ} {l ε : ℝ} {h : ℝ → ℝ}

/-- **The integral of `ω̃_{l,ε} - π^* ω₀` over a simplex of a fibre.** Let `h` be a profile of
the blowup of weight `l` with collar `ε`, `v ≠ 0`, and `τ` a smooth `2`-simplex of `ℂ` that is the
restriction to `Δ²` of a map `g`, an open embedding on a neighbourhood `U` of `Δ²` preserving
orientation from the standard orientation of `ℝ²` to the complex orientation of `ℂ`. If `g(Δ²)`
contains every `t` whose image `curveLift (· • v) t` in the fibre over `[v]` of the tautological
line lies in `closedNbhd n (l + ε)`, then the image of `τ` in that fibre integrates
`profileForm n l ε h - π^* ω₀` to `-π l²`. -/
theorem integral_curveLift_smul_profileForm_sub (hh : IsBlowupProfile l ε h)
    {v : Fin (n + 1) → ℂ} (hv : v ≠ 0) (τ : SmoothSimplex 𝓘(ℝ, ℂ) ℂ 2)
    {U : Opens (EuclideanSpace ℝ (Fin 2))} (hU : fullSimplex 2 ⊆ U)
    {g : EuclideanSpace ℝ (Fin 2) → ℂ} (hgτ : ∀ x : fullSimplex 2, g x = τ.toContinuousMap x)
    (hg : Topology.IsOpenEmbedding (g ∘ ((↑) : U → EuclideanSpace ℝ (Fin 2))))
    (ho : ∀ x ∈ U, Manifold.Orientation.IsOrientationPreservingAt
      (Manifold.Orientation.euclideanSpace 2) ((complexManifoldOrientation ℂ ℂ).reindex
        (finCongr Complex.two_mul_finrank_self)) g x)
    (hD : ∀ t : ℂ, curveLift (· • v) t ∈ closedNbhd n (l + ε) → t ∈ g '' fullSimplex 2) :
    SmoothSimplex.integral ((smoothSingularSubcomplexMap (curveLift (· • v))
        (contMDiff_curveLift_smul_real hv)).app (op ⦋2⦌) τ)
      (profileForm n l ε h - SmoothForm.mpullback blowdown
        ((contMDiff_blowdown ∞).restrictScalars' ℝ) (ω₀E n)).val = -(Real.pi * l ^ 2) := by
  set σ := profileForm n l ε h - SmoothForm.mpullback blowdown
    ((contMDiff_blowdown ∞).restrictScalars' ℝ) (ω₀E n)
  have hL : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ (curveLift (· • v)) :=
    contMDiff_curveLift_smul_real hv
  set ψ := SmoothForm.mpullback (curveLift (· • v)) hL σ
  have hv0 : 0 < ‖complexToRealEuclidean (Fin (n + 1)) v‖ := by
    rw [norm_pos_iff]
    exact fun h0 ↦ hv ((complexToRealEuclidean (Fin (n + 1))).map_eq_zero_iff.1 h0)
  -- The pulled-back form vanishes wherever the fibre point is off `L(l + ε)`.
  have h0 : ∀ t, curveLift (· • v) t ∉ closedNbhd n (l + ε) → ψ.val t = 0 := fun t ht ↦ by
    have hσ : σ.val (curveLift (· • v) t) = 0 := by
      rw [Submodule.coe_sub, Pi.sub_apply, profileForm_eq_on_compl n hh _ ht, sub_self]
    refine ContinuousAlternatingMap.ext fun w ↦ ?_
    rw [SmoothForm.mpullback_apply, hσ, ContinuousAlternatingMap.coe_zero, Pi.zero_apply,
      ContinuousAlternatingMap.coe_zero, Pi.zero_apply]
  have hK : IsCompact (g '' fullSimplex 2) :=
    (isCompact_fullSimplex 2).image_of_continuousOn
      ((continuousOn_iff_continuous_domRestrict.2 hg.continuous).mono hU)
  have hsupp : tsupport (α := ℂ [⋀^Fin 2]→L[ℝ] ℝ) ψ.val ⊆ g '' fullSimplex 2 :=
    closure_minimal (fun t ht ↦ hD t (by_contra fun h' ↦ ht (h0 t h'))) hK.isClosed
  have hc : IsCompact (tsupport (α := ℂ [⋀^Fin 2]→L[ℝ] ℝ) ψ.val) :=
    hK.of_isClosed_subset (isClosed_tsupport _) hsupp
  have hcont : IsSmoothForm 𝓘(ℝ, ℂ) 0 ψ.val := (SmoothForm.isSmoothForm _).of_le (by simp)
  rw [SmoothSimplex.integral_smoothSingularSubcomplexMap_app, ← SmoothForm.coe_mpullback _ hL,
    SmoothSimplex.integral_eq_integralTopForm _ τ hU hgτ hg ho
      (hcont.integrableTopForm hc Complex.basisOneI) hsupp,
    integralTopForm_reindex_complexManifoldOrientation_eq_integral hcont hc (0 : ℂ) (by simp)]
  -- The planar integral is the integral over a disc containing the support.
  simp only [chartAt_self_eq, OpenPartialHomeomorph.refl_partialEquiv, PartialEquiv.refl_target,
    RoughForm.inChartAt_modelSpace, mem_univ, indicator_of_mem]
  set r := (l + ε) / ‖complexToRealEuclidean (Fin (n + 1)) v‖ + 1
  have hr : l + ε < r * ‖complexToRealEuclidean (Fin (n + 1)) v‖ := by
    rw [add_mul, div_mul_cancel₀ _ hv0.ne']
    linarith
  rw [← setIntegral_ball_eval₂_profileForm_sub_mpullback_blowdown_curveLift_smul hh hr,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Metric.ball (0 : ℂ) r) fun t ht ↦ ?_]
  · refine setIntegral_congr_fun measurableSet_ball fun t _ ↦ ?_
    rw [SmoothBundleForm.eval₂_apply]
    simp only [ψ, SmoothForm.coe_mpullback]
    exact mpullback_apply_pair _ _ _ _ _
  have hnot : curveLift (· • v) t ∉ closedNbhd n (l + ε) := by
    rw [mem_closedNbhd_iff, blowdown_curveLift, norm_complexToRealEuclidean_smul, not_le]
    rw [Metric.mem_ball, dist_zero_right, not_lt] at ht
    exact hr.trans_le (mul_le_mul_of_nonneg_right ht hv0.le)
  rw [h0 t hnot]
  exact congrFun ContinuousAlternatingMap.coe_zero _

/-- **The relative integral of `ω̃_{l,ε} - π^* ω₀` over a simplex of a fibre.** Under the
hypotheses of `integral_curveLift_smul_profileForm_sub`, let `β` be a one-form on the model
blowup that vanishes off `closedNbhd n (l + ε)`, and suppose that the image in the fibre of
every face of `τ` lies off `closedNbhd n (l + ε)`. Then the integral of
`profileForm n l ε h - π^* ω₀` over the image of `τ`, minus the integral of `β` over its
boundary, is `-π l²`. -/
theorem integral_curveLift_smul_profileForm_sub_sub_sum_integral_δ (hh : IsBlowupProfile l ε h)
    {v : Fin (n + 1) → ℂ} (hv : v ≠ 0) (τ : SmoothSimplex 𝓘(ℝ, ℂ) ℂ 2)
    {U : Opens (EuclideanSpace ℝ (Fin 2))} (hU : fullSimplex 2 ⊆ U)
    {g : EuclideanSpace ℝ (Fin 2) → ℂ} (hgτ : ∀ x : fullSimplex 2, g x = τ.toContinuousMap x)
    (hg : Topology.IsOpenEmbedding (g ∘ ((↑) : U → EuclideanSpace ℝ (Fin 2))))
    (ho : ∀ x ∈ U, Manifold.Orientation.IsOrientationPreservingAt
      (Manifold.Orientation.euclideanSpace 2) ((complexManifoldOrientation ℂ ℂ).reindex
        (finCongr Complex.two_mul_finrank_self)) g x)
    (hD : ∀ t : ℂ, curveLift (· • v) t ∈ closedNbhd n (l + ε) → t ∈ g '' fullSimplex 2)
    {β : RoughForm 𝓘(ℝ, Fin (n + 1) → ℂ) (BlowupModel n) ℝ 1}
    (hβ : ∀ p ∉ closedNbhd n (l + ε), β p = 0)
    (hface : ∀ (i : Fin 3) (x : fullSimplex 1),
      curveLift (· • v) (τ.toContinuousMap (simplexFace 1 i x)) ∉ closedNbhd n (l + ε)) :
    SmoothSimplex.integral ((smoothSingularSubcomplexMap (curveLift (· • v))
        (contMDiff_curveLift_smul_real hv)).app (op ⦋2⦌) τ)
      (profileForm n l ε h - SmoothForm.mpullback blowdown
        ((contMDiff_blowdown ∞).restrictScalars' ℝ) (ω₀E n)).val -
      ∑ i : Fin 3, (-1 : ℝ) ^ (i : ℕ) • SmoothSimplex.integral
        ((smoothSingularSubcomplex 𝓘(ℝ, Fin (n + 1) → ℂ) (BlowupModel n) : SSet).δ i
          ((smoothSingularSubcomplexMap (curveLift (· • v))
            (contMDiff_curveLift_smul_real hv)).app (op ⦋2⦌) τ)) β =
      -(Real.pi * l ^ 2) := by
  rw [integral_curveLift_smul_profileForm_sub hh hv τ hU hgτ hg ho hD, sub_eq_self]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  rw [SmoothSimplex.integral_eq_zero_of_forall_eq_zero _ fun x ↦ hβ _ ?_, smul_zero]
  rw [SmoothSimplex.toContinuousMap_δ_apply,
    SmoothSimplex.toContinuousMap_smoothSingularSubcomplexMap_app]
  exact hface i x

end SymplecticGeometry.BlowupModel

end
