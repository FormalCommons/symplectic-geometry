/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.CompatibleSpace.Kahler
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Basic
import SymplecticGeometry.Geometry.Manifold.MFDeriv.NormedSpace
import SymplecticGeometry.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Bilinear
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.MFDeriv.Curve
import TauCeti.Geometry.Manifold.VectorField.Regularity
import SymplecticGeometry.LinearAlgebra.Symplectic.CompatibleTangent.Basic

/-!
# The Levi-Civita connection of the space of compatible complex structures

Let `ω` be a symplectic form on a finite-dimensional real normed space `V`, and `𝒥 ω` the
manifold of `ω`-compatible complex structures, a submanifold of `V →L[ℝ] V` through
`ω.compatibleCLM`, with the metric `⟪a, b⟫ = ½ tr(â b̂)` of `Kahler.lean`, where `â` is the
ambient reading of a tangent vector `a` at `J`, its image under the differential of
`ω.compatibleCLM`. This file computes the Levi-Civita connection of `𝒥 ω` in ambient terms
(McDuff–Salamon, Example 4.3.6 and Exercise 4.3.7): for vector fields `X`, `Y`,

`(∇_X Y)^ = D_X Ŷ - ½ J (Ŷ X̂ + X̂ Ŷ)`,

where `D_X Ŷ` is the derivative along `X` of the ambient reading `Ŷ` of `Y`, a function on `𝒥 ω`
with values in `V →L[ℝ] V`; and along a curve `J(t)`, for a field `W` along it,
`(∇_t W)^ = ∂_t Ŵ - ½ J (Ŵ J̇ + J̇ Ŵ)`.

The proof goes through the Gauss formula for the form `B(P, Q) = ½ tr(P Q)`, half the trace form
of `V →L[ℝ] V` (`ContinuousLinearMap.traceForm`), for which the inclusion is isometric
(`inner_compatibleSpace_eq_smul_traceForm`,
`CovariantDerivative.IsLeviCivitaConnection.inner_apply_eq_bilin_mvfderiv`): the connection pairs
with each tangent vector `w` as `B(D_X Ŷ, ŵ)`. The trace form is not positive definite on
`V →L[ℝ] V`, so the remaining step is algebraic. Differentiating the relations `J Ŷ + Ŷ J = 0` and
`ω(Ŷ u, v) + ω(u, Ŷ v) = 0` that define the tangent spaces shows that `D_X Ŷ - ½ J (Ŷ X̂ + X̂ Ŷ)`
is again a tangent vector at `J`. The correction term commutes with `J`, so it is
trace-orthogonal to every tangent vector, which anticommutes with `J`
(`TauCeti.AlmostComplexStructure.trace_mul_eq_zero_of_mem_tangentSpace`). The two pairings agree,
and the metric is nondegenerate, which gives the formula.

## Main results

* `TauCeti.SymplecticForm.mvfderiv_compatibleCLM_eq_of_inner_eq_trace`: the algebraic step, a
  tangent vector pairing with every `w` as `½ tr(D ŵ)` has ambient reading
  `D - ½ J (Ŷ X̂ + X̂ Ŷ)`, given the differentiated relations for `D`.
* `TauCeti.SymplecticForm.mvfderiv_mvfderiv_compatibleCLM_skew` and
  `TauCeti.SymplecticForm.compatibleCLM_mul_mvfderiv_mvfderiv_add`: the derivative of the ambient
  reading of a field along a map into `𝒥 ω` satisfies those relations.
* `TauCeti.SymplecticForm.leviCivitaConnection_compatibleSpace_apply`: the Levi-Civita connection
  of `𝒥 ω` on vector fields.
* `TauCeti.SymplecticForm.alongCurve_leviCivitaConnection_compatibleSpace`: the covariant
  derivative along a curve.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third
  edition][McDuffSalamon2017], Example 4.3.6 and Exercise 4.3.7.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Theorem 8.2 (the Gauss formula).
-/

public section

open scoped Manifold RealInnerProductSpace
open Bundle FiberBundle CovariantDerivative TauCeti.Manifold

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V}

local notation "𝒥" => {J : AlmostComplexStructure V // ω.Compatible J}

/-! ### The algebraic step -/

/-- Let `a b c` be tangent vectors at `J`, with ambient readings `X̂ Ŷ ĉ`, and `D : V →L[ℝ] V`
satisfy the derivatives of the relations defining the tangent spaces along `a`, for a field with
value `b` at `J`: `D` is skew for `ω`, and `J D + D J = -(X̂ Ŷ + Ŷ X̂)`. If `c` pairs with every
tangent vector `w` as `½ tr (D ŵ)`, then `ĉ = D - ½ J (Ŷ X̂ + X̂ Ŷ)`. -/
theorem mvfderiv_compatibleCLM_eq_of_inner_eq_trace {J : 𝒥}
    {a b c : TangentSpace 𝓘(ℝ, ω.compatibleModel) J} {D : V →L[ℝ] V}
    (hskew : ∀ u v, ω (D u) v + ω u (D v) = 0)
    (hanti : ω.compatibleCLM J * D + D * ω.compatibleCLM J =
      -(dι[ω] J a * dι[ω] J b + dι[ω] J b * dι[ω] J a))
    (hc : ∀ w, ⟪c, w⟫ = 2⁻¹ * LinearMap.trace ℝ V ↑(D * dι[ω] J w)) :
    dι[ω] J c =
      D - (2⁻¹ : ℝ) • (ω.compatibleCLM J * (dι[ω] J b * dι[ω] J a + dι[ω] J a * dι[ω] J b)) := by
  -- The ambient readings lie in the compatible tangent space at `J`.
  have hmem := mvfderiv_compatibleCLM_mem_compatibleTangentSpace J
  -- Name the ambient readings, elements of `V →L[ℝ] V`.
  obtain ⟨X, hX⟩ : ∃ X : V →L[ℝ] V, dι[ω] J a = X := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : V →L[ℝ] V, dι[ω] J b = Y := ⟨_, rfl⟩
  have hXm := hmem a
  have hYm := hmem b
  rw [hX] at hXm
  rw [hY] at hYm
  rw [hX, hY] at hanti ⊢
  rw [mem_compatibleTangentSpace] at hXm hYm
  simp only [ContinuousLinearMap.coe_coe] at hXm hYm
  set R := D - (2⁻¹ : ℝ) • (ω.compatibleCLM J * (Y * X + X * Y)) with hR
  -- `R` is a tangent vector at `J`.
  have hRm : (R : Module.End ℝ V) ∈ ω.compatibleTangentSpace J.val := by
    rw [mem_compatibleTangentSpace]
    refine ⟨fun v => ?_, fun u v => ?_⟩
    · have h := congrArg (fun P : V →L[ℝ] V => P v) hanti
      simp only [add_apply, neg_apply, mul_apply_eq_comp,
        compatibleCLM_apply] at h
      simp only [hR, ContinuousLinearMap.coe_coe, sub_apply,
        smul_apply, mul_apply_eq_comp,
        add_apply, compatibleCLM_apply, hXm.1, hYm.1, map_neg, map_add,
        map_sub, map_smul, AlmostComplexStructure.apply_apply]
      linear_combination (norm := module) h
    · -- Move `J`, `X` and `Y` to the second argument of `ω`, and `J` to the left of `X`, `Y`.
      have rX (p q : V) : ω (X p) q = -ω p (X q) := eq_neg_of_add_eq_zero_left (hXm.2 p q)
      have rY (p q : V) : ω (Y p) q = -ω p (Y q) := eq_neg_of_add_eq_zero_left (hYm.2 p q)
      simp only [hR, ContinuousLinearMap.coe_coe, sub_apply, smul_apply,
        mul_apply_eq_comp, add_apply, compatibleCLM_apply, map_sub, map_smul,
        map_add, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul,
        J.property.invariant.apply_apply_eq_neg, rX, rY, hXm.1, hYm.1, map_neg, neg_neg]
      linear_combination hskew u v
  -- So it is the ambient reading of a tangent vector `e`.
  obtain ⟨e, he⟩ : (R : V →L[ℝ] V) ∈ LinearMap.range
      (mfderiv 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V) ω.compatibleCLM J).toLinearMap := by
    rw [range_mfderiv_compatibleCLM]
    exact mem_compatibleTangentSpaceCLM.2 hRm
  have hde : dι[ω] J e = R := (mvfderiv_apply_eq_mfderiv_apply _ _ _).trans he
  -- `e` and `c` pair in the same way with every tangent vector.
  have hec : e = c := by
    refine ext_inner_right ℝ fun w => ?_
    rw [hc, inner_compatibleSpace, hde]
    obtain ⟨Wm, hW⟩ : ∃ Wm : V →L[ℝ] V, dι[ω] J w = Wm := ⟨_, rfl⟩
    have hwm : (Wm : Module.End ℝ V) ∈ J.val.tangentSpace :=
      hW ▸ compatibleTangentSpace_le_tangentSpace (hmem w)
    rw [hW]
    have hXt : (X : Module.End ℝ V) ∈ J.val.tangentSpace :=
      AlmostComplexStructure.mem_tangentSpace_iff_apply.2 hXm.1
    have hYt : (Y : Module.End ℝ V) ∈ J.val.tangentSpace :=
      AlmostComplexStructure.mem_tangentSpace_iff_apply.2 hYm.1
    -- The correction term commutes with `J`, so it is trace-orthogonal to `Wm`.
    have hS : Commute (J.val.toLinearMap * ((Y : Module.End ℝ V) * X + X * Y))
        J.val.toLinearMap :=
      (Commute.refl _).mul_left
        ((AlmostComplexStructure.commute_mul_of_mem_tangentSpace hYt hXt).add_left
          (AlmostComplexStructure.commute_mul_of_mem_tangentSpace hXt hYt))
    have h0 := AlmostComplexStructure.trace_mul_eq_zero_of_mem_tangentSpace hwm hS
    rw [LinearMap.trace_mul_comm] at h0
    simp only [hR, sub_mul, smul_mul_assoc, ContinuousLinearMap.toLinearMap_mul,
      ContinuousLinearMap.toLinearMap_sub, ContinuousLinearMap.toLinearMap_smul,
      ContinuousLinearMap.toLinearMap_add, toLinearMap_compatibleCLM, map_sub, map_smul, h0,
      smul_zero, sub_zero]
  rw [← hec, hde]

/-! ### The derivatives of the relations defining the tangent spaces -/

/-- For `u v : V`, the linear function `P ↦ ω (P u) v + ω u (P v)` on `V →L[ℝ] V`, whose kernels
cut out the endomorphisms skew for `ω`. -/
private noncomputable def skewFunctional (ω : SymplecticForm V) (u v : V) :
    (V →L[ℝ] V) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun P => ω (P u) v + ω u (P v)
      map_add' := fun P Q => by simp only [add_apply, map_add, LinearMap.add_apply]; ring
      map_smul' := fun r P => by
        simp only [smul_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }

private theorem skewFunctional_apply (u v : V) (P : V →L[ℝ] V) :
    skewFunctional ω u v P = ω (P u) v + ω u (P v) :=
  (rfl)

section Along

variable {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]

/-- Let `Y` be a field along a map `p` into the compatible complex structures, with ambient
reading `Ŷ : x ↦ Ŷ x`. Each `Ŷ x` is skew for `ω`, and so is the derivative of `Ŷ` at `x`
along any tangent vector `v` at `x`. -/
theorem mvfderiv_mvfderiv_compatibleCLM_skew {p : N → 𝒥}
    {Y : ∀ x, TangentSpace 𝓘(ℝ, ω.compatibleModel) (p x)} {x : N}
    (v : TangentSpace I x) (u w : V) :
    ω (mvfderiv I (fun x ↦ dι[ω] (p x) (Y x)) x v u) w +
      ω u (mvfderiv I (fun x ↦ dι[ω] (p x) (Y x)) x v w) = 0 := by
  by_cases hY : MDifferentiableAt I 𝓘(ℝ, V →L[ℝ] V) (fun x ↦ dι[ω] (p x) (Y x)) x
  swap
  · rw [mvfderiv_eq_zero_iff.2 (mfderiv_zero_of_not_mdifferentiableAt hY)]
    simp
  have h := (skewFunctional ω u w).mvfderiv_comp_apply hY v
  rw [show ⇑(skewFunctional ω u w) ∘ (fun x ↦ dι[ω] (p x) (Y x)) = fun _ => 0 from
    funext fun x' => by
      rw [Function.comp_apply, skewFunctional_apply]
      exact (mem_compatibleTangentSpace.1
        (mvfderiv_compatibleCLM_mem_compatibleTangentSpace (p x') (Y x'))).2 u w,
    mvfderiv_const, zero_apply] at h
  rw [← skewFunctional_apply, ← h]

/-- Let `Y` be a field along a map `p` into the compatible complex structures, differentiable
at `x` with its ambient reading `Ŷ`. Differentiating `J Ŷ + Ŷ J = 0`, with `J = p x`, along a
tangent vector `v` at `x` gives `J D + D J = -(J̇ Ŷ + Ŷ J̇)`, where `D` is the derivative of `Ŷ`
and `J̇` that of `p` read in `V →L[ℝ] V`. -/
theorem compatibleCLM_mul_mvfderiv_mvfderiv_add {p : N → 𝒥}
    {Y : ∀ x, TangentSpace 𝓘(ℝ, ω.compatibleModel) (p x)} {x : N}
    (hp : MDifferentiableAt I 𝓘(ℝ, ω.compatibleModel) p x)
    (hY : MDifferentiableAt I 𝓘(ℝ, V →L[ℝ] V) (fun x ↦ dι[ω] (p x) (Y x)) x)
    (v : TangentSpace I x) :
    ω.compatibleCLM (p x) * mvfderiv I (fun x ↦ dι[ω] (p x) (Y x)) x v +
      mvfderiv I (fun x ↦ dι[ω] (p x) (Y x)) x v * ω.compatibleCLM (p x) =
      -(mvfderiv I (ω.compatibleCLM ∘ p) x v * dι[ω] (p x) (Y x) +
        dι[ω] (p x) (Y x) * mvfderiv I (ω.compatibleCLM ∘ p) x v) := by
  set g : N → V →L[ℝ] V := fun x ↦ dι[ω] (p x) (Y x)
  have hc : MDifferentiableAt I 𝓘(ℝ, V →L[ℝ] V) (ω.compatibleCLM ∘ p) x :=
    ((contMDiff_compatibleCLM (n := 1)).mdifferentiableAt one_ne_zero).comp x hp
  -- `J g + g J = 0` everywhere; differentiate by the product rule in `V →L[ℝ] V`.
  have h0 : (fun y ↦ (ω.compatibleCLM ∘ p) y * g y + g y * (ω.compatibleCLM ∘ p) y) =
      fun _ ↦ 0 := by
    funext y
    exact compatibleCLM_mul_mvfderiv_add_mvfderiv_mul_compatibleCLM (p y) (Y y)
  have hv := congrArg (fun f ↦ mvfderiv I f x v) h0
  have hcg : MDifferentiableAt I 𝓘(ℝ, V →L[ℝ] V) (fun y ↦ (ω.compatibleCLM ∘ p) y * g y) x :=
    hc.mul hY
  have hgc : MDifferentiableAt I 𝓘(ℝ, V →L[ℝ] V) (fun y ↦ g y * (ω.compatibleCLM ∘ p) y) x :=
    hY.mul hc
  rw [mvfderiv_fun_add hcg hgc, add_apply, SymplecticGeometry.mvfderiv_fun_mul_apply' hc hY,
    SymplecticGeometry.mvfderiv_fun_mul_apply' hY hc, mvfderiv_const, zero_apply] at hv
  simp only [Function.comp_apply] at hv
  rw [eq_neg_iff_add_eq_zero, ← hv]
  abel

end Along

/-! ### The Levi-Civita connection -/

/-- **The Levi-Civita connection, in ambient terms.** For a vector field `Y` differentiable at
`J` and a tangent vector `a` at `J`, the ambient reading of `∇_a Y` is
`D_a Ŷ - ½ J (Ŷ â + â Ŷ)`, where `Ŷ` is the ambient reading of `Y`, a function on the space with
values in `V →L[ℝ] V`, and `D_a Ŷ` its derivative along `a`. The ambient readings are written
through `mvfderiv`, as elements of `V →L[ℝ] V`, and the products are taken in that ring. -/
theorem leviCivitaConnection_compatibleSpace_apply
    {Y : Π J : 𝒥, TangentSpace 𝓘(ℝ, ω.compatibleModel) J} {J : 𝒥}
    (hY : MDifferentiableAt 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, ω.compatibleModel).tangent
      (fun J' ↦ TotalSpace.mk' ω.compatibleModel J' (Y J')) J)
    (a : TangentSpace 𝓘(ℝ, ω.compatibleModel) J) :
    dι[ω] J (leviCivitaConnection 𝓘(ℝ, ω.compatibleModel) 𝒥 Y J a) =
      mvfderiv 𝓘(ℝ, ω.compatibleModel) (fun J' : 𝒥 ↦ dι[ω] J' (Y J')) J a -
        (2⁻¹ : ℝ) • (ω.compatibleCLM J *
          (dι[ω] J (Y J) * dι[ω] J a + dι[ω] J a * dι[ω] J (Y J))) := by
  have hf : ContMDiffAt 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V) 2 ω.compatibleCLM J :=
    contMDiff_compatibleCLM.contMDiffAt
  -- The ambient reading of `Y`, a function with values in `V →L[ℝ] V`.
  have hgd : MDifferentiableAt 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V)
      (fun J' : 𝒥 ↦ dι[ω] J' (Y J')) J :=
    TauCeti.mdifferentiableAt_mvfderiv_apply hf le_rfl hY
  refine mvfderiv_compatibleCLM_eq_of_inner_eq_trace (a := a) (b := Y J)
    (mvfderiv_mvfderiv_compatibleCLM_skew (p := fun J' ↦ J') a) ?_ fun w => ?_
  · simpa only [Function.comp_def] using
      compatibleCLM_mul_mvfderiv_mvfderiv_add (p := fun J' ↦ J') (Y := Y)
        mdifferentiableAt_id hgd a
  · -- The Gauss formula for the trace form.
    have h := (CovariantDerivative.isLeviCivitaConnection_leviCivitaConnection
      𝓘(ℝ, ω.compatibleModel) (M := 𝒥)).inner_apply_eq_bilin_mvfderiv hf
      (ContinuousLinearMap.smul_traceForm_comm _) inner_compatibleSpace_eq_smul_traceForm
      (mdifferentiableAt_extend _ _ a) hY w
    rwa [extend_apply_self, smul_apply, smul_apply, smul_eq_mul,
      ContinuousLinearMap.traceForm_apply] at h

/-- **The covariant derivative along a curve in the space of compatible complex structures.** For
a curve `γ` and a field `W` along it, differentiable at `t` as a curve in the tangent bundle, the
ambient reading of the covariant derivative of `W` along `γ` is `∂_t Ŵ - ½ J (Ŵ J̇ + J̇ Ŵ)`, where
`J = γ t`, `Ŵ` is the ambient reading of `W`, a curve in `V →L[ℝ] V`, and `J̇` the derivative of
`γ` read in `V →L[ℝ] V`. -/
theorem alongCurve_leviCivitaConnection_compatibleSpace {γ : ℝ → 𝒥}
    {W : ∀ r, TangentSpace 𝓘(ℝ, ω.compatibleModel) (γ r)} {t : ℝ}
    (hW : MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ, ω.compatibleModel).tangent
      (fun r ↦ TotalSpace.mk' ω.compatibleModel (γ r) (W r)) t) :
    dι[ω] (γ t) (alongCurve (leviCivitaConnection 𝓘(ℝ, ω.compatibleModel) 𝒥) γ W t) =
      deriv (fun r ↦ dι[ω] (γ r) (W r)) t -
        (2⁻¹ : ℝ) • (ω.compatibleCLM (γ t) *
          (dι[ω] (γ t) (W t) * deriv (ω.compatibleCLM ∘ γ) t +
            deriv (ω.compatibleCLM ∘ γ) t * dι[ω] (γ t) (W t))) := by
  have hγ : MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ, ω.compatibleModel) γ t :=
    ((mdifferentiableAt_totalSpace _ _).1 hW).1
  have hf : ContMDiffAt 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V) 2 ω.compatibleCLM (γ t) :=
    contMDiff_compatibleCLM.contMDiffAt
  -- The ambient reading of `W`, a curve in `V →L[ℝ] V`, and its derivative.
  set g : ℝ → V →L[ℝ] V := fun r ↦ dι[ω] (γ r) (W r) with hg
  have hgd' : MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ, V →L[ℝ] V) g t :=
    ((ContMDiffAt.contMDiffAt_mvfderiv_apply
      (p := TotalSpace.mk' ω.compatibleModel (γ t) (W t)) hf (m := 1)
        (by norm_num)).mdifferentiableAt one_ne_zero).comp t hW
  have hgd : HasDerivAt g (deriv g t) t :=
    (mdifferentiableAt_iff_differentiableAt.1 hgd').hasDerivAt
  -- The velocity of `γ`, read in `V →L[ℝ] V`.
  have hc : HasDerivAt (ω.compatibleCLM ∘ γ)
      (dι[ω] (γ t) (curveVelocity 𝓘(ℝ, ω.compatibleModel) γ t)) t :=
    hasDerivAt_comp_curve (hf.mdifferentiableAt two_ne_zero) (hasMFDerivAt_curveVelocity hγ)
  -- On curves, `mvfderiv` at the unit vector is `deriv`. The unit tangent vector `1` lives in
  -- `TangentSpace 𝓘(ℝ) t`, a type synonym of `ℝ` that the rewrite lemmas do not see through,
  -- so the last step is closed by `exact`.
  have hD : mvfderiv 𝓘(ℝ) g t 1 = deriv g t := by
    rw [mvfderiv_eq_fderiv_apply]
    exact fderiv_apply_one_eq_deriv
  have hX : mvfderiv 𝓘(ℝ) (ω.compatibleCLM ∘ γ) t 1 =
      dι[ω] (γ t) (curveVelocity 𝓘(ℝ, ω.compatibleModel) γ t) := by
    rw [mvfderiv_eq_fderiv_apply, ← hc.deriv]
    exact fderiv_apply_one_eq_deriv
  rw [hc.deriv]
  refine mvfderiv_compatibleCLM_eq_of_inner_eq_trace
    (a := curveVelocity 𝓘(ℝ, ω.compatibleModel) γ t) (b := W t) (fun u v => ?_) ?_ fun w => ?_
  · have h := mvfderiv_mvfderiv_compatibleCLM_skew (I := 𝓘(ℝ)) (p := γ) (Y := W) (x := t) 1 u v
    rwa [← hg, hD] at h
  · have h := compatibleCLM_mul_mvfderiv_mvfderiv_add (Y := W) hγ hgd' 1
    rwa [← hg, hD, hX] at h
  · -- The Gauss formula along a curve, for the trace form.
    have h := (CovariantDerivative.isLeviCivitaConnection_leviCivitaConnection
      𝓘(ℝ, ω.compatibleModel) (M := 𝒥)).inner_alongCurve_eq_bilin hf
      (ContinuousLinearMap.smul_traceForm_comm _) inner_compatibleSpace_eq_smul_traceForm hγ
      (differentiableAt_sectionCoord γ W hW (mem_baseSet_trivializationAt _ _ (γ t))) hgd w
    rwa [smul_apply, smul_apply, smul_eq_mul,
      ContinuousLinearMap.traceForm_apply] at h

/-! ### Regularity of ambient readings -/

/-- The ambient reading `J ↦ Ŷ(J)` of a smooth vector field `Y` on the compatible complex
structures, a function with values in `V →L[ℝ] V`, is smooth. -/
theorem contMDiff_mvfderiv_compatibleCLM_apply
    {Y : Π J : 𝒥, TangentSpace 𝓘(ℝ, ω.compatibleModel) J}
    (hY : ContMDiff 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, ω.compatibleModel).tangent
      ((⊤ : ℕ∞) : WithTop ℕ∞) (fun J' ↦ TotalSpace.mk' ω.compatibleModel J' (Y J'))) :
    ContMDiff 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun J' : 𝒥 ↦ dι[ω] J' (Y J')) :=
  ((contMDiff_compatibleCLM (ω := ω) (n := ((⊤ : ℕ∞) : WithTop ℕ∞))).contMDiff_mvfderiv_apply
    (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)).comp hY

end TauCeti.SymplecticForm

end
