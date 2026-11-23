/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
import TauCeti.Analysis.SpecialFunctions.Complex.Arg
import TauCeti.Geometry.Manifold.Instances.Sphere
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions

/-!
# Maps into a unit sphere that are smooth within a set, on a set or at a point

Mathlib's `ContMDiff.codRestrict_sphere` says that a map into the unit sphere of a real inner
product space `E` is smooth when its composite with the inclusion `sphere 0 1 → E` is. This file
gives the version within a set at a point, `ContMDiffWithinAt.of_coe_sphere`, whose proof adapts
that of Mathlib's `ContMDiff.codRestrict_sphere` to a single chart, and from it the versions at a
point, `ContMDiffAt.of_coe_sphere`, and on a set, `ContMDiffOn.of_coe_sphere`. For `E = ℂ` they
apply to maps into `Circle`.

It also shows that `Circle.exp : ℝ → S¹` is an analytic local diffeomorphism
(`isLocalDiffeomorph_circleExp`), by Tau Ceti's inverse function theorem for manifolds
(`TauCeti.isLocalDiffeomorphAt_of_injective_mfderiv`) and Tau Ceti's computation that the
derivative of `Circle.exp` is injective (`TauCeti.injective_mfderiv_circleExp`), and that the
direction `z ↦ z / ‖z‖ = exp (i arg z)` is a smooth map from `ℂ \ {0}` to the circle
(`Circle.contMDiffOn_exp_arg`), by Tau Ceti's `Complex.contDiffOn_div_norm_pow`.
-/

public section

open Set Metric Module
open scoped Manifold ContDiff RealInnerProductSpace

variable {m : ℕ∞ω} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ EM H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- A map into the unit sphere of `E` is `C^m` within a set at a point if its composite with the
inclusion `sphere 0 1 → E` is `C^m` within that set at that point. -/
theorem ContMDiffWithinAt.of_coe_sphere {n : ℕ} [Fact (finrank ℝ E = n + 1)]
    {f : M → sphere (0 : E) 1} {s : Set M} {x : M}
    (hf : ContMDiffWithinAt I 𝓘(ℝ, E) m (fun y ↦ (f y : E)) s x) :
    ContMDiffWithinAt I (𝓡 n) m f s x := by
  rw [contMDiffWithinAt_iff_target]
  refine ⟨Topology.IsInducing.subtypeVal.continuousWithinAt_iff.2 hf.continuousWithinAt, ?_⟩
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
  convert (h.contMDiffAt.of_le le_top).comp_contMDiffWithinAt x hf using 1
  ext y : 1
  rw [Function.comp_apply, extChartAt_coe, TauCeti.chartAt_sphere, ← hv, stereographic',
    OpenPartialHomeomorph.coe_trans, Function.comp_apply, Function.comp_apply,
    stereographic_apply]
  simp [U, hv, inner_neg_left, sub_eq_add_neg]

/-- A map into the unit sphere of `E` is `C^m` at a point if its composite with the inclusion
`sphere 0 1 → E` is `C^m` there. -/
theorem ContMDiffAt.of_coe_sphere {n : ℕ} [Fact (finrank ℝ E = n + 1)]
    {f : M → sphere (0 : E) 1} {x : M} (hf : ContMDiffAt I 𝓘(ℝ, E) m (fun y ↦ (f y : E)) x) :
    ContMDiffAt I (𝓡 n) m f x :=
  contMDiffWithinAt_univ.1 (contMDiffWithinAt_univ.2 hf).of_coe_sphere

/-- A map into the unit sphere of `E` is `C^m` on a set if its composite with the inclusion
`sphere 0 1 → E` is `C^m` there. -/
theorem ContMDiffOn.of_coe_sphere {n : ℕ} [Fact (finrank ℝ E = n + 1)]
    {f : M → sphere (0 : E) 1} {s : Set M}
    (hf : ContMDiffOn I 𝓘(ℝ, E) m (fun x ↦ (f x : E)) s) :
    ContMDiffOn I (𝓡 n) m f s :=
  fun x hx ↦ (hf x hx).of_coe_sphere

attribute [local instance] finrank_real_complex_fact'

namespace SymplecticGeometry

/-- The map `Circle.exp : ℝ → S¹`, `t ↦ exp (t i)`, is a `C^n` local diffeomorphism for every
`n`, analytic ones included. -/
theorem isLocalDiffeomorph_circleExp (n : ℕ∞ω) :
    IsLocalDiffeomorph 𝓘(ℝ) (𝓡 1) n Circle.exp :=
  IsLocalDiffeomorph.of_le (fun t ↦ TauCeti.isLocalDiffeomorphAt_of_injective_mfderiv
    contMDiff_circleExp.contMDiffOn isOpen_univ (mem_univ t) BoundarylessManifold.isInteriorPoint
    (by simp) (TauCeti.injective_mfderiv_circleExp t) (by simp)) le_top

end SymplecticGeometry

/-- The direction `z / ‖z‖ = exp (i arg z)` is a smooth map from `ℂ \ {0}` to the circle. -/
theorem Circle.contMDiffOn_exp_arg {n : ℕ∞ω} :
    ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 1) n (fun z : ℂ ↦ Circle.exp (Complex.arg z)) {0}ᶜ := by
  refine ContMDiffOn.of_coe_sphere (E := ℂ) (contMDiffOn_iff_contDiffOn.2 ?_)
  refine (Complex.contDiffOn_div_norm_pow 1).congr fun z hz ↦ ?_
  simp [Circle.coe_exp, Complex.exp_arg_mul_I (show z ≠ 0 from hz)]

end
