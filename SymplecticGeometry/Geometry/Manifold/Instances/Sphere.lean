/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
import TauCeti.Geometry.Manifold.Instances.Sphere
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions

/-!
# Maps into a unit sphere that are smooth on an open set or at a point

Mathlib's `ContMDiff.codRestrict_sphere` says that a map into the unit sphere of a real inner
product space `E` is smooth when its composite with the inclusion `sphere 0 1 → E` is. This file
gives the version on an open set of a manifold, `ContMDiffOn.of_coe_sphere`, obtained from
Mathlib's lemma on the open set as a manifold of its own (`contMDiffAt_subtype_iff`), and the
version at a point, `ContMDiffAt.of_coe_sphere`, whose proof adapts that of Mathlib's
`ContMDiff.codRestrict_sphere` to a single chart. For `E = ℂ` they apply to maps into `Circle`.

It also shows that `Circle.exp : ℝ → S¹` is an analytic local diffeomorphism
(`isLocalDiffeomorph_circleExp`), by Tau Ceti's inverse function theorem for manifolds
(`TauCeti.isLocalDiffeomorphAt_of_injective_mfderiv`) and Tau Ceti's computation that the
derivative of `Circle.exp` is injective (`TauCeti.injective_mfderiv_circleExp`).
-/

public section

open Set TopologicalSpace Metric Module
open scoped Manifold ContDiff RealInnerProductSpace

variable {m : ℕ∞ω} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ EM H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- A map into the unit sphere of `E` is `C^m` on an open set if its composite with the inclusion
`sphere 0 1 → E` is `C^m` there. -/
theorem ContMDiffOn.of_coe_sphere [IsManifold I m M] {n : ℕ} [Fact (finrank ℝ E = n + 1)]
    {f : M → sphere (0 : E) 1} {s : Set M} (hs : IsOpen s)
    (hf : ContMDiffOn I 𝓘(ℝ, E) m (fun x ↦ (f x : E)) s) :
    ContMDiffOn I (𝓡 n) m f s := by
  intro x hx
  let U : Opens M := ⟨s, hs⟩
  have hU : ContMDiff I 𝓘(ℝ, E) m fun y : U ↦ (f y : E) := fun y ↦
    contMDiffAt_subtype_iff.2 ((hf y y.property).contMDiffAt (hs.mem_nhds y.property))
  have h : ContMDiff I (𝓡 n) m fun y : U ↦ f y :=
    hU.codRestrict_sphere (f := fun y : U ↦ (f y : E)) fun y ↦ (f y).property
  exact (contMDiffAt_subtype_iff (U := U) (x := ⟨x, hx⟩)).1 (h ⟨x, hx⟩) |>.contMDiffWithinAt

/-- A map into the unit sphere of `E` is `C^m` at a point if its composite with the inclusion
`sphere 0 1 → E` is `C^m` there. -/
theorem ContMDiffAt.of_coe_sphere {n : ℕ} [Fact (finrank ℝ E = n + 1)]
    {f : M → sphere (0 : E) 1} {x : M} (hf : ContMDiffAt I 𝓘(ℝ, E) m (fun y ↦ (f y : E)) x) :
    ContMDiffAt I (𝓡 n) m f x := by
  rw [contMDiffAt_iff_target]
  refine ⟨Topology.IsInducing.subtypeVal.continuousAt_iff.2 hf.continuousAt, ?_⟩
  -- the chart at `f x` is the stereographic projection from `v = -f x`, followed by `U`
  set v : sphere (0 : E) 1 := -f x with hv
  let U : _ ≃ₗᵢ[ℝ] _ :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton n (ne_zero_of_mem_unit_sphere v)).repr
  have h : ContDiffAt ℝ ω (U ∘ stereoToFun (v : E)) (f x) := by
    refine ((U.contDiff.contDiffOn (s := univ)).comp_inter
      (contDiffOn_stereoToFun (v := (v : E)))).contDiffAt ?_
    rw [preimage_univ, inter_univ]
    refine ((continuous_const.inner continuous_id).isOpen_preimage _ isOpen_ne).mem_nhds ?_
    simp [hv, inner_neg_left]
    norm_num
  convert (h.contMDiffAt.of_le le_top).comp x hf using 1
  ext y : 1
  rw [Function.comp_apply, extChartAt_coe, TauCeti.chartAt_sphere, ← hv, stereographic',
    OpenPartialHomeomorph.coe_trans, Function.comp_apply, Function.comp_apply,
    stereographic_apply]
  simp [U, hv, inner_neg_left, sub_eq_add_neg]

attribute [local instance] finrank_real_complex_fact'

/-- The map `Circle.exp : ℝ → S¹`, `t ↦ exp (t i)`, is a `C^n` local diffeomorphism for every
`n`, analytic ones included. -/
theorem isLocalDiffeomorph_circleExp (n : ℕ∞ω) :
    IsLocalDiffeomorph 𝓘(ℝ) (𝓡 1) n Circle.exp :=
  IsLocalDiffeomorph.of_le (fun t ↦ TauCeti.isLocalDiffeomorphAt_of_injective_mfderiv
    contMDiff_circleExp.contMDiffOn isOpen_univ (mem_univ t) BoundarylessManifold.isInteriorPoint
    (by simp) (TauCeti.injective_mfderiv_circleExp t) (by simp)) le_top

end
