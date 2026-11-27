/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import TauCeti.Analysis.SpecialFunctions.Complex.Arg
import TauCeti.Geometry.Manifold.Immersion.Differential
import TauCeti.Geometry.Manifold.Instances.Sphere
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic

/-!
# Maps into a unit sphere that are smooth within a set, on a set or at a point

Mathlib's `ContMDiff.codRestrict_sphere` says that a map into the unit sphere of a real inner
product space `E` is smooth when its composite with the inclusion `sphere 0 1 → E` is. This file
gives the version within a set at a point, `ContMDiffWithinAt.of_coe_sphere`, whose proof adapts
that of Mathlib's `ContMDiff.codRestrict_sphere` to a single chart, and from it the versions at a
point, `ContMDiffAt.of_coe_sphere`, and on a set, `ContMDiffOn.of_coe_sphere`. For `E = ℂ` they
apply to maps into `Circle`.

It also shows that the inclusion `sphere 0 1 → E` of the unit sphere of an `(n + 1)`-dimensional
space is a smooth embedding at every order (`isSmoothEmbedding_coe_sphere`): a topological
embedding, and an immersion by Tau Ceti's `ContMDiff.isImmersion_of_injective_mfderiv`, its
derivative being injective by Mathlib's `injective_mvfderiv_subtypeVal_sphere`.

Next, it shows that `Circle.exp : ℝ → S¹` is an analytic local diffeomorphism
(`isLocalDiffeomorph_circleExp`), by Tau Ceti's inverse function theorem for manifolds
(`TauCeti.isLocalDiffeomorphAt_of_injective_mfderiv`) and Tau Ceti's computation that the
derivative of `Circle.exp` is injective (`TauCeti.injective_mfderiv_circleExp`), and that the
direction `z ↦ z / ‖z‖ = exp (i arg z)` is a smooth map from `ℂ \ {0}` to the circle
(`Circle.contMDiffOn_exp_arg`), by Tau Ceti's `Complex.contDiffOn_div_norm_pow`.

Last, it makes the inclusion `Circle → ℂˣ` a smooth group homomorphism
(`Circle.contMDiffToUnits`), and gives the polar decomposition of `ℂˣ` as a global
diffeomorphism `Circle.polarDiffeo : ℝ × Circle ≃ ℂˣ`, `(t, u) ↦ exp t * u`, whose inverse is
`z ↦ (log ‖z‖, exp (i arg z))` (`Circle.polarDiffeo_symm_apply`). Mathlib's `Complex.polarCoord`
is a partial homeomorphism of `ℂ` only.
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

/-- The inclusion `sphere 0 1 → E` of the unit sphere of an `(n + 1)`-dimensional real inner
product space is a `C^m` smooth embedding, for every `m`, analytic included. -/
theorem isSmoothEmbedding_coe_sphere {n : ℕ} [Fact (finrank ℝ E = n + 1)] :
    Manifold.IsSmoothEmbedding (𝓡 n) 𝓘(ℝ, E) m ((↑) : sphere (0 : E) 1 → E) := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  refine Manifold.IsSmoothEmbedding.of_le (m := ω)
    ⟨(contMDiff_coe_sphere (n := n)).isImmersion_of_injective_mfderiv (by simp) fun v ↦ ?_,
      Topology.IsEmbedding.subtypeVal⟩ le_top
  -- `mvfderiv` of the inclusion is its `mfderiv` followed by the identification of the tangent
  -- spaces of `E` with `E`.
  have h := injective_mvfderiv_subtypeVal_sphere (n := n) v
  rw [mvfderiv, ContinuousLinearMap.coe_comp] at h
  exact h.of_comp

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


noncomputable section

namespace Circle

open Complex

/-- The inclusion of the unit circle into `ℂˣ`, as a smooth group homomorphism. -/
def contMDiffToUnits : ContMDiffMonoidMorphism (𝓡 1) 𝓘(ℝ, ℂ) ∞ Circle ℂˣ where
  toMonoidHom := Circle.toUnits
  contMDiff_toFun :=
    ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val contMDiff_coe_sphere

@[simp]
theorem coe_contMDiffToUnits_apply (u : Circle) : ((contMDiffToUnits u : ℂˣ) : ℂ) = u :=
  (rfl)

/-- The inclusion of the unit circle into `ℂˣ` is injective. -/
theorem injective_contMDiffToUnits : Function.Injective contMDiffToUnits := fun u v h ↦
  Circle.ext <| by simpa using congrArg Units.val h

/-- The map `(t, u) ↦ exp t * u` from `ℝ × Circle` to `ℂˣ`. -/
private def polarFun (p : ℝ × Circle) : ℂˣ :=
  Units.mk0 (Complex.exp p.1 * p.2) (mul_ne_zero (Complex.exp_ne_zero _) p.2.coe_ne_zero)

/-- The map `z ↦ (log ‖z‖, exp (i arg z))` from `ℂˣ` to `ℝ × Circle`. -/
private def polarInv (z : ℂˣ) : ℝ × Circle :=
  (Real.log ‖(z : ℂ)‖, Circle.exp (arg z))

private theorem polarInv_polarFun (p : ℝ × Circle) : polarInv (polarFun p) = p := by
  refine Prod.ext ?_ ?_
  · simp [polarInv, polarFun, Complex.norm_exp]
  · rw [polarInv, polarFun, Units.val_mk0, ← ofReal_exp, arg_ofReal_mul (Real.exp_pos _),
      Circle.exp_arg]

private theorem polarFun_polarInv (z : ℂˣ) : polarFun (polarInv z) = z := by
  refine Units.ext ?_
  rw [polarFun, polarInv, Units.val_mk0, ← ofReal_exp, Real.exp_log (norm_pos_iff.2 z.ne_zero),
    Circle.coe_exp, norm_mul_exp_arg_mul_I]

private theorem contMDiff_polarFun : ContMDiff (𝓘(ℝ).prod (𝓡 1)) 𝓘(ℝ, ℂ) ∞ polarFun := by
  refine ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val ?_
  have h : Units.val ∘ polarFun = (fun q : ℂ × ℂ ↦ q.1 * q.2) ∘
      fun p : ℝ × Circle ↦ (Complex.exp p.1, (p.2 : ℂ)) :=
    funext fun _ ↦ Units.val_mk0 _
  rw [h]
  refine (contMDiff_iff_contDiff.2 contDiff_mul).comp (ContMDiff.prodMk_space ?_
    (contMDiff_coe_sphere.comp contMDiff_snd))
  exact (ContDiff.contMDiff (Complex.contDiff_exp.comp ofRealCLM.contDiff)).comp contMDiff_fst

private theorem contMDiff_polarInv : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ).prod (𝓡 1)) ∞ polarInv := by
  refine ContMDiff.prodMk (fun z ↦ ?_) (fun z ↦ ?_)
  · have hz : (z : ℂ) ≠ 0 := z.ne_zero
    refine ContMDiffAt.comp (g := fun w : ℂ ↦ Real.log ‖w‖) z
      (ContDiffAt.contMDiffAt ?_) Units.contMDiff_val.contMDiffAt
    exact (Real.contDiffAt_log.2 (norm_ne_zero_iff.2 hz)).comp _ (contDiffAt_norm ℝ hz)
  · exact (Circle.contMDiffOn_exp_arg.contMDiffAt
      (isOpen_compl_singleton.mem_nhds z.ne_zero)).comp z Units.contMDiff_val.contMDiffAt

/-- The polar decomposition of `ℂˣ`: the diffeomorphism `ℝ × Circle ≃ ℂˣ`, `(t, u) ↦ exp t * u`.
-/
def polarDiffeo : (ℝ × Circle) ≃ₘ⟮𝓘(ℝ).prod (𝓡 1), 𝓘(ℝ, ℂ)⟯ ℂˣ where
  toFun := polarFun
  invFun := polarInv
  left_inv := polarInv_polarFun
  right_inv := polarFun_polarInv
  contMDiff_toFun := contMDiff_polarFun
  contMDiff_invFun := contMDiff_polarInv

@[simp]
theorem coe_polarDiffeo_apply (t : ℝ) (u : Circle) :
    (polarDiffeo (t, u) : ℂ) = Complex.exp t * u :=
  -- `polarDiffeo` is `polarFun` by definition.
  Units.val_mk0 (mul_ne_zero (Complex.exp_ne_zero _) u.coe_ne_zero)

@[simp]
theorem polarDiffeo_symm_apply (z : ℂˣ) :
    polarDiffeo.symm z = (Real.log ‖(z : ℂ)‖, Circle.exp (arg z)) :=
  (rfl)

end Circle

end

end
