/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.Flat
import TauCeti.Analysis.Normed.Module.Alternating.Curry

/-!
# The inverse flat map of a one-form with zero first jet

Let `σ` be a nondegenerate two-form on a boundaryless finite-dimensional manifold and `β` a
one-form. If `β` vanishes at a point `x` and its coordinate expression in the chart at `x` has
zero derivative there, then the coordinate expression of the vector field `(σ♭)⁻¹ β` in the chart
at `x` also has zero derivative at the chart point of `x`. In the relative Moser argument this is
what makes the Moser flow fix `x` to first order ([McDuffSalamon2017], §3.2;
[McDuffSalamon2019Errata], p. 109): the derivative is the hypothesis of Tau Ceti's
`TauCeti.mfderiv_timeDependentFlowOf_eq_id_of_forall_eq_zero`.

## Main results

* `TauCeti.SmoothTwoForm.IsNondegenerate.hasFDerivAt_mpullbackWithin_interiorEquiv_symm`: the
  coordinate expression of `(σ♭)⁻¹ β` has zero derivative where `β` vanishes to first order.

The proof adapts Tau Ceti's private `hasFDerivAt_mpullbackWithin_moserField`
(`TauCeti/Geometry/Symplectic/Manifold/RelativeMoser.lean`) from the cut-off Moser field to a
general inverse flat map: in the chart, the field is the inverse of the flat map of the
coordinate form applied to the coordinate expression of `β`; these inverses stay bounded near
the chart point, and `β` vanishes there to first order.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017]
* [D. McDuff and D. Salamon, *Errata*][McDuffSalamon2019Errata]
-/

public section

open Set Filter
open scoped ContDiff Manifold Topology

namespace TauCeti

namespace SmoothTwoForm

namespace IsNondegenerate

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] {σ : SmoothTwoForm I M}

/-- **The inverse flat map of a one-form with zero first jet.** Let `σ` be a nondegenerate
two-form and `β` a one-form that vanishes at `x` and whose coordinate expression in the chart at
`x` has zero derivative at the chart point of `x`. Then the coordinate expression of the vector
field `(σ♭)⁻¹ β` in the chart at `x` has zero derivative at that point. -/
theorem hasFDerivAt_mpullbackWithin_interiorEquiv_symm (h : σ.IsNondegenerate)
    {β : SmoothForm I M ℝ 1} {x : M} (hβx : β.val x = 0)
    (hβ : HasFDerivAt (RoughForm.inChartAt β.val x) (0 : E →L[ℝ] E [⋀^Fin 1]→L[ℝ] ℝ)
      (extChartAt I x x)) :
    HasFDerivAt (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm
      (h.interiorEquiv.symm β) (range I)) (0 : E →L[ℝ] E) (extChartAt I x x) := by
  set z₀ := extChartAt I x x
  set V : E → E := VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm
    (h.interiorEquiv.symm β) (range I)
  -- The flat maps of the coordinate expression of `σ`.
  set F : E → E →L[ℝ] E →L[ℝ] ℝ := fun z ↦ ContinuousAlternatingMap.flatL ℝ E ℝ
    (RoughForm.inChartAt σ.val x z)
  have hFc : ContinuousAt F z₀ := by
    have hc := (σ.isSmoothForm.contDiffWithinAt_inChartAt_self x).continuousWithinAt
    rw [I.range_eq_univ, continuousWithinAt_univ] at hc
    exact (ContinuousAlternatingMap.flatL ℝ E ℝ).continuous.continuousAt.comp hc
  have hF₀ : (F z₀).IsInvertible := by
    simp only [F, z₀, RoughForm.inChartAt_extChartAt_self, ← flat_def]
    exact h.isInvertible_flat x
  -- In the chart, `σ'♭(z) (V z) = β'(z)`, read as alternating maps of one vector.
  have hkey : ∀ᶠ z in 𝓝 z₀, ‖F z (V z)‖ = ‖RoughForm.inChartAt β.val x z‖ :=
    eventually_of_mem (extChartAt_target_mem_nhds x) fun z hz ↦ by
      have hi := RoughForm.inChartAt_interior (h.interiorEquiv.symm β) σ.val hz
      rw [interior_interiorEquiv_symm] at hi
      refine (ContinuousAlternatingMap.norm_ofSubsingleton (ι := Fin 1) 0 _).symm.trans ?_
      rw [ContinuousAlternatingMap.ofSubsingleton_flatL_apply, hi]
  -- The inverses of `σ'♭(z)` are bounded near `z₀`, so `V = O(β')`.
  set G : E → (E →L[ℝ] ℝ) →L[ℝ] E := fun z ↦ (F z).inverse
  -- Name the operator norm instance: inferring it through the dual space times out.
  let : NormedAddCommGroup ((E →L[ℝ] ℝ) →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
  have hGc : ContinuousAt G z₀ := (hF₀.contDiffAt_map_inverse (n := 0)).continuousAt.comp hFc
  have hbig : V =O[𝓝 z₀] RoughForm.inChartAt β.val x := by
    refine Asymptotics.IsBigO.of_bound (‖G z₀‖ + 1) ?_
    filter_upwards [hFc.eventually hF₀.eventually_nhds, hkey,
      hGc.norm.eventually (gt_mem_nhds (lt_add_one ‖G z₀‖))] with z hzF hzk hzG
    calc ‖V z‖ = ‖G z (F z (V z))‖ := by rw [hzF.inverse_apply_self]
      _ ≤ ‖G z‖ * ‖F z (V z)‖ := (G z).le_opNorm _
      _ ≤ (‖G z₀‖ + 1) * ‖RoughForm.inChartAt β.val x z‖ := by rw [hzk]; gcongr
  -- `β'` vanishes to first order at `z₀`, hence so does `V`.
  have hβ₀ : RoughForm.inChartAt β.val x z₀ = 0 :=
    (RoughForm.inChartAt_extChartAt_self _ x).trans hβx
  have hV₀ : V z₀ = 0 := by
    have h0 : h.interiorEquiv.symm β ((extChartAt I x).symm z₀) = 0 := by
      rw [interiorEquiv_symm_apply_eq_zero_iff, extChartAt_to_inv]
      exact hβx
    simp only [V]
    rw [VectorField.mpullbackWithin_apply, h0, map_zero]
    -- The zero of the tangent space of the model space is the zero of `E`.
    rfl
  have hβo := hβ.isLittleO
  simp only [hβ₀, sub_zero, zero_apply] at hβo
  exact .of_isLittleO (by
    simpa only [hV₀, sub_zero, zero_apply] using hbig.trans_isLittleO hβo)

end IsNondegenerate

end SmoothTwoForm

end TauCeti

end
