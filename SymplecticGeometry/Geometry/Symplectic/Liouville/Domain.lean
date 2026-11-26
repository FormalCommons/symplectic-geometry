/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Liouville.Completion
public import TauCeti.Geometry.Symplectic.Liouville.Completion
import SymplecticGeometry.Geometry.Manifold.Flow.Basic
import SymplecticGeometry.Geometry.Manifold.MFDeriv.Prod
import SymplecticGeometry.Geometry.Manifold.VectorField.Prod
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition
import TauCeti.Geometry.Manifold.MFDeriv.Curve
import TauCeti.Topology.Compactness.Normed

/-!
# The completion of a Liouville domain is a completion in Tau Ceti's sense

Let `(W, σ, Y)` be a Liouville domain: a strong filling (`SymplecticGeometry.IsStrongFilling`)
whose field `Y` is Liouville on all of `W`, with `W` compact. Its completion `Ŵ`
(`SymplecticGeometry.IsStrongFilling.Completion`, after McDuff–Salamon, the completion on p. 148)
carries the symplectic form `ω̂`, the primitive `λ̂` with `dλ̂ = -ω̂` and the field `Ŷ` with
`ι_Ŷ ω̂ = -λ̂`. This file shows that `Ŵ` is a completion of the image of `W` in the sense of Tau
Ceti, `TauCeti.IsLiouvilleCompletion ω̂ (-λ̂) (range toCompletion)`, Tau Ceti's primitive being
`-λ̂`. So Tau Ceti's results on completions apply to `Ŵ`, among them the cylindrical end chart
`TauCeti.IsLiouvilleCompletion.cylindricalEndPartialDiffeomorph` and the identification of the
flow-out of a submanifold with a symplectization,
`TauCeti.mpullback_globalFlow_comp_eq_symplectization`.

The conditions of `TauCeti.IsLiouvilleDomain` are checked as follows. The image of `W` is compact,
and lies in the interior of `Ŵ`, which has no boundary. Its Liouville field is `Ŷ`. The function
cutting it out is `max s (-ε / 2)` at the point `(s, x)` of the end `(-ε, ∞) × ∂W`, and `-ε / 2`
elsewhere: it is continuous, since it is constant near the points of `W` off the compact image of
`[-ε / 2, 0] × ∂W`; its sublevel set `{· ≤ 0}` is the image of `W`; and at its level `0`, the
boundary `{0} × ∂W`, it is the coordinate `s`, so that its derivative along `Ŷ = ∂_s` is `1`. That
derivative is computed along an integral curve, as in Tau Ceti's
`TauCeti.mvfderiv_apply_eq_one_of_eventually_apply_globalFlow_eq_add`.

The field `Ŷ` is complete for every strong filling with compact `W`
(`SymplecticGeometry.IsStrongFilling.isCompleteVectorField_completionField`): on the end its
integral curves are the lines `s ↦ (s, x)` (`isMIntegralCurveOn_completionEnd`), and the flow of
`Ŷ` is defined for a uniform time on the compact image of `W`, by the tube lemma; a uniform time
of existence makes a field complete (`TauCeti.isCompleteVectorField_of_exists_isMIntegralCurveOn`).
Every point of the end `(s, x)`, `s > 0`, flows back into `W` in time `-s`.

## Main results

* `SymplecticGeometry.IsStrongFilling.isMIntegralCurveOn_completionEnd`: the lines of the end are
  integral curves of `Ŷ`.
* `SymplecticGeometry.IsStrongFilling.isCompleteVectorField_completionField`: for compact `W`, the
  Liouville field of the completion is complete.
* `SymplecticGeometry.IsStrongFilling.exists_flowOf_completionField_mem_range`: every point of the
  completion flows into `W`.
* `SymplecticGeometry.IsStrongFilling.isLiouvilleCompletion_completion`: the completion of a
  Liouville domain is a completion of `W` in the sense of `TauCeti.IsLiouvilleCompletion`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  the completion on p. 148.
-/

public section

open Bundle Set Function TauCeti
open scoped Manifold ContDiff Topology

namespace SymplecticGeometry

variable {n : ℕ} {W : Type*} [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
  [IsManifold (𝓡∂ (n + 1)) ∞ W] [T2Space W] [CompactSpace ((𝓡∂ (n + 1)).boundary W)]

variable {σ : SmoothTwoForm (𝓡∂ (n + 1)) W} {U : Set W}
  {Y : (x : W) → TangentSpace (𝓡∂ (n + 1)) x}

namespace IsStrongFilling

variable (h : IsStrongFilling σ U Y)

/-! ### The flow of the Liouville field of the completion -/

/-- The lines `s ↦ (s, x)` of the end `(-ε, ∞) × ∂W` are integral curves of the Liouville field
of the completion. -/
theorem isMIntegralCurveOn_completionEnd (x : (𝓡∂ (n + 1)).boundary W) :
    IsMIntegralCurveOn (fun s ↦ h.completionEnd (s, x)) h.completionField
      (Ioi (-h.collarWidth)) := by
  intro t ht
  have hq : (t, x) ∈ Ioi (-h.collarWidth) ×ˢ (univ : Set ((𝓡∂ (n + 1)).boundary W)) :=
    ⟨ht, trivial⟩
  have hd : MDifferentiableAt (𝓘(ℝ).prod (𝓡 n)) (𝓡 (n + 1)) h.completionEnd (t, x) :=
    (h.contMDiffOn_completionEnd.contMDiffAt
      ((isOpen_Ioi.prod isOpen_univ).mem_nhds hq)).mdifferentiableAt (by simp)
  refine ((MDifferentiableAt.curry_left (f := fun s x ↦ h.completionEnd (s, x))
    hd).hasMFDerivAt.congr_mfderiv ?_).hasMFDerivWithinAt
  refine ContinuousLinearMap.ext_ring ?_
  have key := h.mfderiv_completionEnd_apply hq
  rw [Manifold.prodVectorField_constVectorField_zero_apply] at key
  exact (MDifferentiableAt.mfderiv_uncurry_apply_mk_zero (f := fun s x ↦ h.completionEnd (s, x))
    hd 1).symm.trans (key.trans (one_smul ℝ _).symm)

/-- Along the lines `t ↦ Φ (t, x)` of the collar map, which are integral curves of `Y` on
`(-ε, 0]`, a function `g` on `W` differentiable at `Φ (s, x)` has derivative `dg(Y)` at `s`. -/
theorem hasDerivAt_comp_collarFlow {g : W → ℝ} {s : ℝ} (hs : s ∈ Ioo (-h.collarWidth) 0)
    (x : (𝓡∂ (n + 1)).boundary W)
    (hg : MDifferentiableAt (𝓡∂ (n + 1)) 𝓘(ℝ) g (h.collarFlow (s, x))) :
    HasDerivAt (fun t ↦ g (h.collarFlow (t, x)))
      (mvfderiv (𝓡∂ (n + 1)) g (h.collarFlow (s, x)) (Y (h.collarFlow (s, x)))) s :=
  Manifold.hasDerivAt_comp_curve hg
    ((h.isMIntegralCurveOn_collarFlow x s ⟨hs.1, hs.2.le⟩).hasMFDerivAt (Ioc_mem_nhds hs.1 hs.2))

/-- Every point of the completion is carried into `W` by the flow of its Liouville field: the
point `(s, x)` of the end, `s > 0`, in time `-s`, and the points of `W` in time `0`. -/
theorem exists_flowOf_completionField_mem_range (z : h.Completion) :
    ∃ t, flowOf h.completionField t z ∈ range h.toCompletion := by
  have hz := h.range_toCompletion_union.symm ▸ mem_univ z
  rcases hz with hz | ⟨⟨s, x⟩, ⟨hs, -⟩, rfl⟩
  · exact ⟨0, by rwa [flowOf_zero]⟩
  · have hs0 : 0 < s := hs
    refine ⟨0 - s, x, ?_⟩
    have hs' : (s : ℝ) ∈ Ioi (-h.collarWidth) := (neg_lt_zero.2 h.collarWidth_pos).trans hs
    rw [((h.isMIntegralCurveOn_completionEnd x).mono Ioo_subset_Ioi_self).flowOf_sub_eq
      (a := -h.collarWidth) (b := s + 1)
      ((h.contMDiff_completionField).of_le (by simp)) ⟨hs', by linarith⟩
      ⟨neg_lt_zero.2 h.collarWidth_pos, by linarith⟩, completionEnd_zero]

/-- **The Liouville field of the completion is complete**, for a strong filling with compact
`W`. -/
theorem isCompleteVectorField_completionField [CompactSpace W] :
    IsCompleteVectorField h.completionField := by
  have hv : ContMDiff (𝓡 (n + 1)) (𝓡 (n + 1)).tangent 1 (T% h.completionField) :=
    h.contMDiff_completionField.of_le (by simp)
  have hε := h.collarWidth_pos
  -- The flow is defined for a uniform time `δ` on the compact image of `W`.
  have hK : IsCompact (range h.toCompletion) :=
    isCompact_range h.contMDiff_toCompletion.continuous
  obtain ⟨δ, hδ, hball⟩ := hK.exists_pos_forall_norm_lt
    (Q := fun (t : ℝ) z ↦ (t, z) ∈ flowDomain h.completionField) fun z _ ↦
      (isOpen_flowDomain hv).mem_nhds (mem_flowDomain_zero hv z)
  refine isCompleteVectorField_of_exists_isMIntegralCurveOn hv (lt_min hδ hε) fun z ↦ ?_
  have hz := h.range_toCompletion_union.symm ▸ mem_univ z
  rcases hz with hz | ⟨⟨s, x⟩, ⟨hs, -⟩, rfl⟩
  · refine ⟨fun t ↦ flowOf h.completionField t z, flowOf_zero _ z,
      (isMIntegralCurveOn_flowOf hv z).mono fun t ht ↦ hball (x := t) ?_ z hz⟩
    rw [Real.norm_eq_abs, abs_lt]
    exact ⟨(neg_le_neg (min_le_left δ _)).trans_lt ht.1, ht.2.trans_le (min_le_left _ _)⟩
  · refine ⟨fun t ↦ h.completionEnd (t + s, x), by simp, ?_⟩
    refine ((h.isMIntegralCurveOn_completionEnd x).comp_add s).mono fun t ht ↦ ?_
    have : -h.collarWidth < t := (neg_le_neg (min_le_right δ _)).trans_lt ht.1
    rw [mem_ofPred_eq, mem_Ioi]
    linarith [hs.out]

/-! ### The function cutting out `W` -/

open Classical in
/-- The function cutting `W` out of its completion: `max s (-ε / 2)` at the point `(s, x)` of the
end `(-ε, ∞) × ∂W`, and `-ε / 2` elsewhere. -/
private noncomputable def height (z : h.Completion) : ℝ :=
  if hz : ∃ q ∈ Ioi (-h.collarWidth) ×ˢ univ, h.completionEnd q = z then
    max hz.choose.1 (-h.collarWidth / 2)
  else -h.collarWidth / 2

private theorem height_completionEnd {q : ℝ × (𝓡∂ (n + 1)).boundary W}
    (hq : q ∈ Ioi (-h.collarWidth) ×ˢ univ) :
    h.height (h.completionEnd q) = max q.1 (-h.collarWidth / 2) := by
  have hz : ∃ q' ∈ Ioi (-h.collarWidth) ×ˢ univ, h.completionEnd q' = h.completionEnd q :=
    ⟨q, hq, rfl⟩
  rw [height, dite_eq_left hz, h.injOn_completionEnd hz.choose_spec.1 hq hz.choose_spec.2]

private theorem height_of_notMem {z : h.Completion}
    (hz : z ∉ h.completionEnd '' (Ici (-h.collarWidth / 2) ×ˢ univ)) :
    h.height z = -h.collarWidth / 2 := by
  rw [height]
  split_ifs with hz'
  · refine max_eq_right (le_of_not_ge fun hle ↦ hz ?_)
    exact ⟨hz'.choose, ⟨hle, trivial⟩, hz'.choose_spec.2⟩
  · rfl

private theorem eventuallyEq_height_comp {q : ℝ × (𝓡∂ (n + 1)).boundary W}
    (hq : q ∈ Ioi (-h.collarWidth) ×ˢ univ) :
    h.height ∘ h.completionEnd =ᶠ[𝓝 q] fun r ↦ max r.1 (-h.collarWidth / 2) :=
  Filter.eventually_of_mem ((isOpen_Ioi.prod isOpen_univ).mem_nhds hq) fun _ hr ↦
    h.height_completionEnd hr

private theorem continuous_height : Continuous h.height := by
  have hε := h.collarWidth_pos
  refine continuous_iff_continuousAt.2 fun z ↦ ?_
  by_cases hz : ∃ q ∈ Ioi (-h.collarWidth) ×ˢ univ, h.completionEnd q = z
  · obtain ⟨q, hq, rfl⟩ := hz
    have hc : ContMDiffAt (𝓘(ℝ).prod (𝓡 n)) 𝓘(ℝ) 0 (h.height ∘ h.completionEnd) q :=
      (contMDiff_zero_iff.2 (by fun_prop)).contMDiffAt.congr_of_eventuallyEq
        (h.eventuallyEq_height_comp hq)
    exact (((h.isLocalDiffeomorphOn_completionEnd ⟨q, hq⟩).contMDiffAt_comp_iff
      (by simp)).1 hc).continuousAt
  obtain ⟨p, hp, rfl⟩ := (h.exists_completionEnd_or_toCompletion z).resolve_left hz
  -- Off the compact image `K` of `[-ε / 2, 0] × ∂W`, the image of the interior of `W` is an open
  -- set on which the function is constant.
  set K := h.completionEnd '' (Icc (-h.collarWidth / 2) 0 ×ˢ univ)
  have hKc : IsClosed K := by
    refine (IsCompact.image_of_continuousOn (isCompact_Icc.prod isCompact_univ)
      (h.contMDiffOn_completionEnd.continuousOn.mono ?_)).isClosed
    exact prod_mono (fun s hs ↦ by simp only [mem_Ioi]; linarith [hs.1]) subset_rfl
  have hO : IsOpen (h.toCompletion '' (𝓡∂ (n + 1)).interior W) := by
    have := (SmoothCollar.WithEnd.interiorPart h.collar).isOpen
    rwa [SmoothCollar.WithEnd.coe_interiorPart, ← toCompletion_def] at this
  have hconst : ∀ w ∈ h.toCompletion '' (𝓡∂ (n + 1)).interior W \ K,
      h.height w = -h.collarWidth / 2 := by
    rintro w ⟨⟨p', -, rfl⟩, hwK⟩
    refine h.height_of_notMem fun ⟨r, hr, hrw⟩ ↦ ?_
    rcases le_or_gt r.1 0 with hr0 | hr0
    · exact hwK ⟨r, ⟨⟨hr.1, hr0⟩, trivial⟩, hrw⟩
    · exact disjoint_left.1 h.disjoint_range_toCompletion_completionEnd_image ⟨p', rfl⟩
        ⟨r, ⟨hr0, trivial⟩, hrw⟩
  refine continuousAt_const.congr (Filter.eventually_of_mem
    ((hO.sdiff hKc).mem_nhds ⟨⟨p, hp, rfl⟩, ?_⟩) fun w hw ↦ (hconst w hw).symm)
  rintro ⟨r, hr, hrp⟩
  exact hz ⟨r, ⟨by simp only [mem_Ioi]; linarith [hr.1.1], trivial⟩, hrp⟩

private theorem range_toCompletion_eq_setOfPred_height_le :
    range h.toCompletion = {z | h.height z ≤ 0} := by
  have hε := h.collarWidth_pos
  ext z
  refine ⟨?_, fun hz ↦ ?_⟩
  · rintro ⟨p, rfl⟩
    by_cases hz : ∃ q ∈ Ioi (-h.collarWidth) ×ˢ univ, h.completionEnd q = h.toCompletion p
    · obtain ⟨q, hq, hqp⟩ := hz
      have hq0 : q.1 ≤ 0 := le_of_not_gt fun hq0 ↦ disjoint_left.1
        h.disjoint_range_toCompletion_completionEnd_image ⟨p, rfl⟩ ⟨q, ⟨hq0, trivial⟩, hqp⟩
      rw [mem_ofPred_eq, ← hqp, h.height_completionEnd hq]
      exact max_le hq0 (by linarith)
    · rw [mem_ofPred_eq, height, dite_eq_right hz]
      linarith
  · refine (h.range_toCompletion_union.symm ▸ mem_univ z).resolve_right ?_
    rintro ⟨q, ⟨hq, -⟩, rfl⟩
    rw [mem_ofPred_eq, h.height_completionEnd ⟨(neg_lt_zero.2 hε).trans hq, trivial⟩] at hz
    exact (lt_max_of_lt_left hq).not_ge hz

/-- At the level `0`, the boundary of `W`, the function cutting out `W` is smooth and its
derivative along the Liouville field of the completion is `1`. -/
private theorem contMDiffAt_height_and_mvfderiv {z : h.Completion} (hz : h.height z = 0) :
    ContMDiffAt (𝓡 (n + 1)) 𝓘(ℝ) ∞ h.height z ∧
      mvfderiv (𝓡 (n + 1)) h.height z (h.completionField z) = 1 := by
  have hε := h.collarWidth_pos
  by_cases hE : ∃ q ∈ Ioi (-h.collarWidth) ×ˢ univ, h.completionEnd q = z
  swap
  · rw [height, dite_eq_right hE] at hz
    linarith
  obtain ⟨⟨s, x⟩, hq, rfl⟩ := hE
  rw [h.height_completionEnd hq] at hz
  obtain rfl : s = 0 := by
    rcases max_choice s (-h.collarWidth / 2) with hm | hm <;> rw [hm] at hz
    · exact hz
    · linarith
  -- Near `(0, x)`, the function read on the end is the coordinate `s`.
  have heq : h.height ∘ h.completionEnd =ᶠ[𝓝 ((0 : ℝ), x)] Prod.fst := by
    filter_upwards [h.eventuallyEq_height_comp hq,
      (isOpen_Ioi.preimage continuous_fst).mem_nhds
        (show ((0 : ℝ), x).1 ∈ Ioi (-h.collarWidth / 2) by simp only [mem_Ioi]; linarith)]
      with r hr hr'
    rw [hr]
    exact max_eq_left (le_of_lt hr')
  have hs : ContMDiffAt (𝓡 (n + 1)) 𝓘(ℝ) ∞ h.height (h.completionEnd (0, x)) :=
    ((h.isLocalDiffeomorphOn_completionEnd ⟨_, hq⟩).contMDiffAt_comp_iff le_rfl).1
      (contMDiffAt_fst.congr_of_eventuallyEq heq)
  refine ⟨hs, ?_⟩
  -- Along the integral curve `t ↦ (t, x)` of the field, the function is `t` near `0`.
  have hγ := ((h.isMIntegralCurveOn_completionEnd x) 0 hq.1).hasMFDerivAt
    (isOpen_Ioi.mem_nhds hq.1)
  have hd := Manifold.hasDerivAt_comp_curve (hs.mdifferentiableAt (by simp)) hγ
  have hid : h.height ∘ (fun t ↦ h.completionEnd (t, x)) =ᶠ[𝓝 0] id :=
    (continuous_id.prodMk continuous_const).continuousAt.tendsto.eventually heq
  exact (hd.congr_of_eventuallyEq hid.symm).unique (hasDerivAt_id 0)

/-- **The completion of a Liouville domain is a Tau Ceti completion.** Let `(W, σ, Y)` be a
Liouville domain: a strong filling whose field `Y` is Liouville on all of `W`, with `W` compact.
Then its completion, with the symplectic form `ω̂` and the primitive `-λ̂`, is a completion of
the image of `W` in the sense of `TauCeti.IsLiouvilleCompletion`. -/
theorem isLiouvilleCompletion_completion [CompactSpace W] (h : IsStrongFilling σ univ Y) :
    IsLiouvilleCompletion h.completionForm (-h.completionPrimitive) (range h.toCompletion) where
  isNondegenerate := h.isSymplectic_completionForm.isNondegenerate
  mextDeriv_eq := by
    rw [NegMemClass.coe_neg, mextDeriv_neg, ← mextDerivₗ_apply, h.mextDerivₗ_completionPrimitive,
      NegMemClass.coe_neg, neg_neg]
  isCompact := isCompact_range h.contMDiff_toCompletion.continuous
  subset_interior := by simp [ModelWithCorners.interior_eq_univ]
  exists_liouville_outward := ⟨h.completionField, h.contMDiff_completionField,
    h.interior_completionField_completionForm, h.height, 0, h.continuous_height,
    h.range_toCompletion_eq_setOfPred_height_le, fun _ hz ↦
      ⟨(h.contMDiffAt_height_and_mvfderiv hz).1,
        (h.contMDiffAt_height_and_mvfderiv hz).2 ▸ one_pos⟩⟩
  exists_isCompleteVectorField := ⟨h.completionField, h.interior_completionField_completionForm,
    h.isCompleteVectorField_completionField, h.exists_flowOf_completionField_mem_range⟩

end IsStrongFilling

end SymplecticGeometry

end
