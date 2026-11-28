/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.Complete
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import TauCeti.Geometry.Manifold.IntegralCurve.Flow
import TauCeti.Geometry.Manifold.IntegralCurve.Interval
import TauCeti.Geometry.Manifold.IntegralCurve.Reparam

/-!
# Completeness of rescaled and perturbed vector fields

Let `X` be a complete `C¹` vector field on a Hausdorff boundaryless manifold, and `a` a continuous
real function that is bounded and never zero. Then `a • X` is complete. Along a global integral
curve `γ` of `X`, the field `a • X` is `(a ∘ γ) • X`, and Tau Ceti's reparametrization
`IsMIntegralCurve.exists_homeomorph_isMIntegralCurve_comp_of_abs_le` turns `γ` into a global
integral curve `γ ∘ ψ` of `a • X` through the same point, since `ψ 0 = 0`. No regularity of `a`
beyond continuity is needed, and `a • X` need not be `C¹`.

A second criterion concerns compact perturbations. If, moreover, the model space is complete and
a `C¹` field `w` agrees with the complete `C¹` field `v` off a compact set `K`, then `w` is
complete. Let `γ` be the maximal integral curve of `w` through `x`, and `t ≥ 0` a time of its
domain. Let `σ` be the last time in `[0, t]` at which `γ` lies in `K ∪ {x}`. After `σ` the curve
avoids `K`, so it is an integral curve of `v` there; by uniqueness, which holds up to the end
point `σ`, the trajectory of `v` through `γ t` reaches `γ σ` at time `σ - t`
(`IsMIntegralCurveOn.exists_mem_of_eqOn_compl`). Hence for `|t| ≤ T` the point `γ t` lies in the
image of `[-T, T] × (K ∪ {x})` under the flow of `v`, a compact set, and the escape lemma
`TauCeti.maximalIntegralCurveInterval_eq_univ_of_forall_isCompact_mapsTo` shows that `γ` is
defined for all time. Negative times reduce to positive ones by reversing time, which replaces
`v` and `w` by `-v` and `-w`. This extends the argument of Tau Ceti's
`TauCeti.isCompleteVectorField_of_isCompact_of_eq_zero_off`, the case of a field
vanishing off `K`, where `v = 0`.

## Main results

* `TauCeti.IsCompleteVectorField.smul_of_ne_zero_of_abs_le`: `a • X` is complete when `a` is
  continuous, nowhere zero and `|a| ≤ c`.
* `TauCeti.IsCompleteVectorField.smul_of_pos_of_le`: `a • X` is complete when `a` is continuous
  and `0 < a ≤ c`.
* `IsMIntegralCurveOn.exists_mem_of_eqOn_compl`: if `w = v` off a closed set `K`, an integral
  curve of `w` on `[a, b]` that starts in `K` ends at a point whose trajectory under `v` meets `K`
  at some time in `[a - b, 0]`.
* `TauCeti.IsCompleteVectorField.of_eqOn_compl`: a `C¹` field that agrees with a complete `C¹`
  field off a compact set is complete.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  Lemma 12.1 (i), whose rescaled Liouville field is such a multiple, with `0 < a ≤ 1`.
* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Lemma 9.19 (the escape lemma) and Theorem 9.16 (compactly supported fields are
  complete).
-/

public section

open Set
open scoped Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

/-- Let the vector field `w` agree with the `C¹` vector field `v` off a closed set `K`, and let
`γ` be an integral curve of `w` on `[a, b]` with `γ a ∈ K`. Then a global integral curve `δ` of
`v` with `δ 0 = γ b` lies in `K` at some time in `[a - b, 0]`. -/
theorem IsMIntegralCurveOn.exists_mem_of_eqOn_compl [T2Space M] [IsManifold I 1 M]
    {v w : (x : M) → TangentSpace I x}
    (hv : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
    {K : Set M} (hK : IsClosed K) (hvw : EqOn w v Kᶜ) {γ δ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hγ : IsMIntegralCurveOn γ w (Icc a b)) (ha : γ a ∈ K) (hδ : IsMIntegralCurve δ v)
    (hδb : δ 0 = γ b) : ∃ s ∈ Icc (a - b) 0, δ s ∈ K := by
  -- `σ` is the last time in `[a, b]` at which `γ` lies in `K`.
  set A := Icc a b ∩ γ ⁻¹' K
  have hbdd : BddAbove A := ⟨b, fun _ h ↦ h.1.2⟩
  have hσ : sSup A ∈ A :=
    (hγ.continuousOn.preimage_isClosed_of_isClosed isClosed_Icc hK).csSup_mem
      ⟨a, ⟨le_rfl, hab⟩, ha⟩ hbdd
  set σ := sSup A
  refine ⟨σ - b, ⟨by linarith [hσ.1.1], by linarith [hσ.1.2]⟩, ?_⟩
  rcases hσ.1.2.eq_or_lt with h | h
  · rw [h, sub_self, hδb, ← h]
    exact hσ.2
  -- After `σ` the curve `γ` avoids `K`, so it is an integral curve of `v` on `(σ, b]`.
  have hγv : IsMIntegralCurveOn γ v (Ioc σ b) := fun r hr ↦ by
    have hrK : γ r ∉ K := fun hrK ↦
      (not_le.2 hr.1) (le_csSup hbdd ⟨⟨hσ.1.1.trans hr.1.le, hr.2⟩, hrK⟩)
    have := (hγ r ⟨hσ.1.1.trans hr.1.le, hr.2⟩).mono
      (Ioc_subset_Icc_self.trans (Icc_subset_Icc hσ.1.1 le_rfl))
    rwa [hvw hrK] at this
  -- It agrees there with the translate of `δ`, and so does its value at `σ`, by continuity.
  have hδ' : IsMIntegralCurve (δ ∘ (· + -b)) v := hδ.comp_add (-b)
  have heq : EqOn (δ ∘ (· + -b)) γ (Ioc σ b) :=
    (hδ'.isMIntegralCurveOn _).eqOn_of_isPreconnected hγv isPreconnected_Ioc
      (right_mem_Ioc.2 h) (fun _ _ ↦ hv _) (by simp [hδb])
  have heq' : EqOn (δ ∘ (· + -b)) γ (Icc σ b) :=
    heq.of_subset_closure hδ'.continuous.continuousOn
      (hγ.continuousOn.mono (Icc_subset_Icc hσ.1.1 le_rfl)) Ioc_subset_Icc_self
      (closure_Ioc h.ne).ge
  have hσb := heq' ⟨le_rfl, h.le⟩
  simp only [Function.comp_apply, ← sub_eq_add_neg] at hσb
  rw [hσb]
  exact hσ.2

namespace TauCeti

variable [T2Space M] [BoundarylessManifold I M] [IsManifold I 1 M]

namespace IsCompleteVectorField

/-- A complete `C¹` vector field `X` multiplied by a continuous nowhere vanishing function `a`
with `|a| ≤ c` is complete. -/
theorem smul_of_ne_zero_of_abs_le {X : (x : M) → TangentSpace I x}
    (hX : IsCompleteVectorField X)
    (hXd : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, X x⟩ : TangentBundle I M)))
    {a : M → ℝ} (ha : Continuous a) (ha0 : ∀ x, a x ≠ 0) {c : ℝ} (hc : ∀ x, |a x| ≤ c) :
    IsCompleteVectorField fun x ↦ a x • X x :=
  isCompleteVectorField_of_forall_exists_isMIntegralCurve fun x ↦
    let ⟨γ, hγ0, hγ⟩ := hX.exists_isMIntegralCurve hXd x
    let ⟨ψ, hψ0, hψ⟩ := hγ.exists_homeomorph_isMIntegralCurve_comp_of_abs_le
      (ha.comp hγ.continuous) (fun t ↦ ha0 (γ t)) (fun t ↦ hc (γ t)) fun _ ↦ rfl
    ⟨γ ∘ ψ, by simp [hψ0, hγ0], hψ⟩

/-- A complete `C¹` vector field `X` multiplied by a continuous function `a` with `0 < a ≤ c` is
complete. -/
theorem smul_of_pos_of_le {X : (x : M) → TangentSpace I x}
    (hX : IsCompleteVectorField X)
    (hXd : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, X x⟩ : TangentBundle I M)))
    {a : M → ℝ} (ha : Continuous a) (hpos : ∀ x, 0 < a x) {c : ℝ} (hc : ∀ x, a x ≤ c) :
    IsCompleteVectorField fun x ↦ a x • X x :=
  hX.smul_of_ne_zero_of_abs_le hXd ha (fun x ↦ (hpos x).ne') fun x ↦
    (abs_of_pos (hpos x)).trans_le (hc x)

/-- A `C¹` vector field `w` that agrees with a complete `C¹` vector field `v` off a compact set
is complete. -/
theorem of_eqOn_compl [CompleteSpace E] {v w : (x : M) → TangentSpace I x}
    (hv : IsCompleteVectorField v)
    (hvd : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
    (hwd : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, w x⟩ : TangentBundle I M)))
    {K : Set M} (hK : IsCompact K) (hvw : EqOn w v Kᶜ) :
    IsCompleteVectorField w := by
  rw [isCompleteVectorField_iff_maximalIntegralCurveInterval]
  intro x
  have hK' : IsClosed (insert x K) := (hK.insert x).isClosed
  have hvw' : EqOn w v (insert x K)ᶜ := hvw.mono (compl_subset_compl.2 (subset_insert x K))
  -- The flow of `v`, as a function of time and initial point, is continuous.
  have hΦ : Continuous fun p : ℝ × M ↦ flowOf v p.1 p.2 :=
    continuous_iff_continuousAt.2 fun p ↦ by
      simpa only [flowOf_apply, Function.comp_def, Prod.fst_swap, Prod.snd_swap] using
        (continuousAt_maximalIntegralCurve hvd (p := (p.2, p.1))
        (hv.mem_maximalIntegralCurveInterval _ _)).comp (f := Prod.swap)
          continuous_swap.continuousAt
  -- The trajectories of `v` are global integral curves.
  have hδ (y : M) : IsMIntegralCurve (fun s ↦ flowOf v s y) v := by
    rw [isMIntegralCurve_iff_isMIntegralCurveOn]
    simpa [hv.mem_flowDomain] using isMIntegralCurveOn_flowOf hvd y
  have hγ := isMIntegralCurveOn_maximalIntegralCurve (x := x) hwd
  have h0 := zero_mem_maximalIntegralCurveInterval (x := x) hwd.contMDiffAt
  refine maximalIntegralCurveInterval_eq_univ_of_forall_isCompact_mapsTo hwd fun T ↦
    ⟨_, (isCompact_Icc (a := -T) (b := T)).prod (hK.insert x) |>.image hΦ, ?_⟩
  rintro t ⟨ht, htT, htT'⟩
  -- It is enough that the trajectory of `v` through `γ t` meets `K ∪ {x}` within time `T`.
  suffices ∃ s ∈ Icc (-T) T, flowOf v (-s) (maximalIntegralCurve w x t) ∈ insert x K by
    obtain ⟨s, hs, hsK⟩ := this
    exact ⟨(s, _), ⟨hs, hsK⟩, flowOf_flowOf_neg hvd hv s _⟩
  rcases le_total 0 t with h | h
  · obtain ⟨s, hs, hsK⟩ := (hγ.mono (ordConnected_maximalIntegralCurveInterval.out h0 ht)
      ).exists_mem_of_eqOn_compl hvd hK' hvw' h (by simp [maximalIntegralCurve_zero]) (hδ _)
      (flowOf_zero v _)
    exact ⟨-s, ⟨by linarith [hs.2], by linarith [hs.1]⟩, by rwa [neg_neg]⟩
  -- For negative times, reverse time, replacing `v` and `w` by `-v` and `-w`.
  have hγ' : IsMIntegralCurveOn (fun r ↦ maximalIntegralCurve w x (-r)) (-w) (Icc 0 (-t)) :=
    hγ.comp_neg.mono fun r hr ↦
      ordConnected_maximalIntegralCurveInterval.out ht h0 ⟨by linarith [hr.2], by linarith [hr.1]⟩
  obtain ⟨s, hs, hsK⟩ := hγ'.exists_mem_of_eqOn_compl hvd.neg_section hK'
    (fun y hy ↦ congrArg Neg.neg (hvw' hy)) (neg_nonneg.2 h) (by simp [maximalIntegralCurve_zero])
    (δ := fun s ↦ flowOf v (-s) (maximalIntegralCurve w x t)) (hδ _).comp_neg (by simp)
  exact ⟨s, ⟨by linarith [hs.1], by linarith [hs.2]⟩, hsK⟩

end IsCompleteVectorField

end TauCeti

end
