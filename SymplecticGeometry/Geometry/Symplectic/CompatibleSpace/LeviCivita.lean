/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.CompatibleSpace.Kahler
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Basic
import SymplecticGeometry.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Bilinear
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.MFDeriv.Curve
import TauCeti.Geometry.Manifold.VectorField.Regularity

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

The proof goes through the Gauss formula for the trace form `B(P, Q) = ½ tr(P Q)` of
`V →L[ℝ] V`, for which the inclusion is isometric
(`CovariantDerivative.IsLeviCivitaConnection.inner_apply_eq_bilin_mvfderiv`): the connection pairs
with each tangent vector `w` as `B(D_X Ŷ, ŵ)`. The trace form is not positive on `V →L[ℝ] V`, so
the remaining step is algebraic. Differentiating the relations `J Ŷ + Ŷ J = 0` and
`ω(Ŷ u, v) + ω(u, Ŷ v) = 0` that define the tangent spaces shows that `D_X Ŷ - ½ J (Ŷ X̂ + X̂ Ŷ)`
is again a tangent vector at `J`. The correction term commutes with `J`, so it is
trace-orthogonal to every tangent vector, which anticommutes with `J`
(`TauCeti.AlmostComplexStructure.trace_mul_eq_zero_of_mem_tangentSpace`). The two pairings agree,
and the metric is nondegenerate, which gives the formula. This replaces the computation in the
global chart of a Christoffel map, which no later result needs.

## Main results

* `TauCeti.SymplecticForm.mfderiv_compatibleCLM_eq_of_inner_eq_trace`: the algebraic step, a
  tangent vector pairing with every `w` as `½ tr(D ŵ)` has ambient reading
  `D - ½ J (Ŷ X̂ + X̂ Ŷ)`, given the differentiated relations for `D`.
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

/-- The trace form `(P, Q) ↦ ½ tr (P Q)` on `V →L[ℝ] V`, a continuous bilinear form for which the
inclusion of the compatible complex structures is isometric. -/
private noncomputable def traceForm : (V →L[ℝ] V) →L[ℝ] (V →L[ℝ] V) →L[ℝ] ℝ :=
  (2⁻¹ : ℝ) • (ContinuousLinearMap.compL ℝ (V →L[ℝ] V) (V →L[ℝ] V) ℝ (TauCeti.traceCLM ℝ V) ∘L
    ContinuousLinearMap.mul ℝ (V →L[ℝ] V))

private theorem traceForm_apply (P Q : V →L[ℝ] V) :
    traceForm P Q = 2⁻¹ * LinearMap.trace ℝ V ↑(P ∘L Q) := by
  simp [traceForm, ContinuousLinearMap.mul_def]

/-- Let `a b c` be tangent vectors at `J`, with ambient readings `X̂ Ŷ ĉ`, and `D : V →L[ℝ] V`
satisfy the derivatives of the relations defining the tangent spaces along `a`, for a field with
value `b` at `J`: `D` is skew for `ω`, and `J D + X̂ Ŷ + Ŷ X̂ + D J = 0`. If `c` pairs with every
tangent vector `w` as `½ tr (D ŵ)`, then `ĉ = D - ½ J (Ŷ X̂ + X̂ Ŷ)`. -/
theorem mfderiv_compatibleCLM_eq_of_inner_eq_trace {J : 𝒥}
    {a b c : TangentSpace 𝓘(ℝ, ω.compatibleModel) J} {D : V →L[ℝ] V}
    (hskew : ∀ u v, ω (D u) v + ω u (D v) = 0)
    (hanti : ω.compatibleCLM J ∘L D +
      mfderiv 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V) ω.compatibleCLM J a ∘L
        mfderiv 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V) ω.compatibleCLM J b +
      (mfderiv 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V) ω.compatibleCLM J b ∘L
        mfderiv 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V) ω.compatibleCLM J a +
        D ∘L ω.compatibleCLM J) = 0)
    (hc : ∀ w, ⟪c, w⟫ = 2⁻¹ * LinearMap.trace ℝ V
      ↑(D ∘L mfderiv 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V) ω.compatibleCLM J w)) :
    mfderiv 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V) ω.compatibleCLM J c =
      D - (2⁻¹ : ℝ) • (ω.compatibleCLM J ∘L
        (mfderiv 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V) ω.compatibleCLM J b ∘L
            mfderiv 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V) ω.compatibleCLM J a +
          mfderiv 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V) ω.compatibleCLM J a ∘L
            mfderiv 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V) ω.compatibleCLM J b)) := by
  set d := mfderiv 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V) ω.compatibleCLM J
  -- Name the ambient readings, elements of `V →L[ℝ] V`.
  obtain ⟨X, hX⟩ : ∃ X : V →L[ℝ] V, d a = X := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : V →L[ℝ] V, d b = Y := ⟨_, rfl⟩
  have hXm := mfderiv_compatibleCLM_mem_compatibleTangentSpace J a
  have hYm := mfderiv_compatibleCLM_mem_compatibleTangentSpace J b
  rw [hX] at hXm
  rw [hY] at hYm
  rw [hX, hY] at hanti ⊢
  rw [mem_compatibleTangentSpace] at hXm hYm
  simp only [ContinuousLinearMap.coe_coe] at hXm hYm
  set R := D - (2⁻¹ : ℝ) • (ω.compatibleCLM J ∘L (Y ∘L X + X ∘L Y)) with hR
  -- `R` is a tangent vector at `J`.
  have hRm : (R : Module.End ℝ V) ∈ ω.compatibleTangentSpace J.val := by
    rw [mem_compatibleTangentSpace]
    refine ⟨fun v => ?_, fun u v => ?_⟩
    · have h := congrArg (fun P : V →L[ℝ] V => P v) hanti
      simp only [add_apply, ContinuousLinearMap.comp_apply,
        compatibleCLM_apply, zero_apply] at h
      simp only [hR, ContinuousLinearMap.coe_coe, sub_apply,
        smul_apply, ContinuousLinearMap.comp_apply,
        add_apply, compatibleCLM_apply, hXm.1, hYm.1, map_neg, map_add,
        map_sub, map_smul, AlmostComplexStructure.apply_apply]
      linear_combination (norm := module) h
    · -- Move `J`, `X` and `Y` to the second argument of `ω`, and `J` to the left of `X`, `Y`.
      have rJ (p q : V) : ω (J.val p) q = -ω p (J.val q) :=
        eq_neg_of_add_eq_zero_left (J.property.invariant.apply_add_apply_eq_zero p q)
      have rX (p q : V) : ω (X p) q = -ω p (X q) := eq_neg_of_add_eq_zero_left (hXm.2 p q)
      have rY (p q : V) : ω (Y p) q = -ω p (Y q) := eq_neg_of_add_eq_zero_left (hYm.2 p q)
      simp only [hR, ContinuousLinearMap.coe_coe, sub_apply, smul_apply,
        ContinuousLinearMap.comp_apply, add_apply, compatibleCLM_apply, map_sub, map_smul,
        map_add, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul,
        rJ, rX, rY, hXm.1, hYm.1, map_neg, neg_neg]
      linear_combination hskew u v
  -- So it is the ambient reading of a tangent vector `e`.
  obtain ⟨e, he⟩ : (R : V →L[ℝ] V) ∈ LinearMap.range d.toLinearMap := by
    rw [range_mfderiv_compatibleCLM]
    exact mem_compatibleTangentSpaceCLM.2 hRm
  -- `e` and `c` pair in the same way with every tangent vector.
  have hde : d e = R := he
  have hec : e = c := by
    refine ext_inner_right ℝ fun w => ?_
    rw [hc, inner_compatibleSpace, hde]
    obtain ⟨Wm, hW⟩ : ∃ Wm : V →L[ℝ] V, d w = Wm := ⟨_, rfl⟩
    have hwm : (Wm : Module.End ℝ V) ∈ J.val.tangentSpace :=
      hW ▸ mfderiv_compatibleCLM_mem_tangentSpace J w
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
    simp only [hR, ContinuousLinearMap.sub_comp, ContinuousLinearMap.smul_comp,
      ContinuousLinearMap.toLinearMap_comp, ContinuousLinearMap.toLinearMap_sub,
      ContinuousLinearMap.toLinearMap_smul, ContinuousLinearMap.toLinearMap_add,
      toLinearMap_compatibleCLM, map_sub, map_smul, ← Module.End.mul_eq_comp, h0, smul_zero,
      sub_zero]
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

/-- An endomorphism in the tangent space at `J` anticommutes with `J`. -/
theorem compatibleCLM_mul_add_mul_compatibleCLM (J : 𝒥) {X : V →L[ℝ] V}
    (hX : (X : Module.End ℝ V) ∈ J.val.tangentSpace) :
    ω.compatibleCLM J * X + X * ω.compatibleCLM J = 0 := by
  rw [AlmostComplexStructure.mem_tangentSpace_iff_apply] at hX
  ext v
  simp only [add_apply, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
    compatibleCLM_apply, zero_apply]
  rw [← ContinuousLinearMap.coe_coe X, hX, add_neg_cancel]

/-- The trace form, for which the inclusion is isometric. -/
private theorem inner_eq_traceForm (J : 𝒥) (v w : TangentSpace 𝓘(ℝ, ω.compatibleModel) J) :
    ⟪v, w⟫ = traceForm (mvfderiv 𝓘(ℝ, ω.compatibleModel) ω.compatibleCLM J v)
      (mvfderiv 𝓘(ℝ, ω.compatibleModel) ω.compatibleCLM J w) := by
  rw [traceForm_apply, mvfderiv_apply_eq_mfderiv_apply, mvfderiv_apply_eq_mfderiv_apply,
    inner_compatibleSpace]

private theorem traceForm_comm (P Q : V →L[ℝ] V) : traceForm P Q = traceForm Q P := by
  rw [traceForm_apply, traceForm_apply, ContinuousLinearMap.toLinearMap_comp,
    ContinuousLinearMap.toLinearMap_comp, ← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp,
    LinearMap.trace_mul_comm]

/-! ### The Levi-Civita connection -/

/-- **The Levi-Civita connection, in ambient terms.** For a vector
field `Y` differentiable at `J` and a tangent vector `a` at `J`, the ambient reading of `∇_a Y` is
`D_a Ŷ - ½ J (Ŷ â + â Ŷ)`, where `Ŷ` is the ambient reading of `Y`, a function on the space with
values in `V →L[ℝ] V`, and `D_a Ŷ` its derivative along `a`. -/
theorem leviCivitaConnection_compatibleSpace_apply
    {Y : Π J : 𝒥, TangentSpace 𝓘(ℝ, ω.compatibleModel) J} {J : 𝒥}
    (hY : MDifferentiableAt 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, ω.compatibleModel).tangent
      (fun J' ↦ TotalSpace.mk' ω.compatibleModel J' (Y J')) J)
    (a : TangentSpace 𝓘(ℝ, ω.compatibleModel) J) :
    mfderiv 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V) ω.compatibleCLM J
        (leviCivitaConnection 𝓘(ℝ, ω.compatibleModel) 𝒥 Y J a) =
      mvfderiv 𝓘(ℝ, ω.compatibleModel) (fun J' : 𝒥 ↦
          (mfderiv 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V) ω.compatibleCLM J' (Y J') :
            V →L[ℝ] V)) J a -
        (2⁻¹ : ℝ) • (ω.compatibleCLM J ∘L
          (mfderiv 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V) ω.compatibleCLM J (Y J) ∘L
              mfderiv 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V) ω.compatibleCLM J a +
            mfderiv 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V) ω.compatibleCLM J a ∘L
              mfderiv 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V) ω.compatibleCLM J (Y J))) := by
  have hf : ContMDiffAt 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V) 2 ω.compatibleCLM J :=
    contMDiff_compatibleCLM.contMDiffAt
  have hc : MDifferentiableAt 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V) ω.compatibleCLM J :=
    hf.mdifferentiableAt two_ne_zero
  -- The ambient reading of `Y`, a function with values in `V →L[ℝ] V`.
  set g : 𝒥 → V →L[ℝ] V := fun J' ↦
    mfderiv 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V) ω.compatibleCLM J' (Y J')
  have hgm : g = fun J' ↦ mvfderiv 𝓘(ℝ, ω.compatibleModel) ω.compatibleCLM J' (Y J') :=
    funext fun J' => (mvfderiv_apply_eq_mfderiv_apply _ _ _).symm
  have hgd : MDifferentiableAt 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V) g J :=
    hgm ▸ TauCeti.mdifferentiableAt_mvfderiv_apply hf le_rfl hY
  refine mfderiv_compatibleCLM_eq_of_inner_eq_trace (a := a) (b := Y J) (fun u v => ?_) ?_
    fun w => ?_
  · -- `g` is skew for `ω` everywhere, hence so is its derivative.
    have h := (skewFunctional ω u v).mvfderiv_comp_apply hgd a
    rw [show ⇑(skewFunctional ω u v) ∘ g = fun _ => 0 from
      funext fun J' => (mem_compatibleTangentSpace.1
        (mfderiv_compatibleCLM_mem_compatibleTangentSpace J' (Y J'))).2 u v, mvfderiv_const,
      zero_apply] at h
    rw [← skewFunctional_apply, ← h]
  · -- `g` anticommutes with the inclusion everywhere, hence the product rule.
    have h := ((hc.hasMFDerivAt.mul' hgd.hasMFDerivAt).add
      (hgd.hasMFDerivAt.mul' hc.hasMFDerivAt)).mfderiv
    have h0 : ω.compatibleCLM * g + g * ω.compatibleCLM = fun _ => 0 :=
      funext fun J' => compatibleCLM_mul_add_mul_compatibleCLM J'
        (mfderiv_compatibleCLM_mem_tangentSpace J' (Y J'))
    rw [h0, mfderiv_const] at h
    rw [mvfderiv_apply_eq_mfderiv_apply]
    -- Evaluated at `a`, the derivative of `P * Q` from `HasMFDerivAt.mul'` is `P * Q' a + P' a * Q`
    -- by definition of the actions of `V →L[ℝ] V` on maps into it.
    exact (congrArg (fun L => L a) h).symm
  · -- The Gauss formula for the trace form.
    have h := (CovariantDerivative.isLeviCivitaConnection_leviCivitaConnection
      𝓘(ℝ, ω.compatibleModel) (M := 𝒥)).inner_apply_eq_bilin_mvfderiv hf traceForm_comm
      inner_eq_traceForm (mdifferentiableAt_extend _ _ a) hY w
    rw [extend_apply_self, ← hgm, traceForm_apply, mvfderiv_apply_eq_mfderiv_apply] at h
    exact h

/-- **The covariant derivative along a curve in the space of compatible complex structures.** For
a curve `γ` and a field `W` along it, differentiable at `t` as a curve in the tangent bundle, the
ambient reading of the covariant derivative of `W` along `γ` is `∂_t Ŵ - ½ J (Ŵ J̇ + J̇ Ŵ)`, where
`J = γ t`, `Ŵ` is the ambient reading of `W`, a curve in `V →L[ℝ] V`, and `J̇` the derivative of
`γ` read in `V →L[ℝ] V`. -/
theorem alongCurve_leviCivitaConnection_compatibleSpace {γ : ℝ → 𝒥}
    {W : ∀ r, TangentSpace 𝓘(ℝ, ω.compatibleModel) (γ r)} {t : ℝ}
    (hW : MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ, ω.compatibleModel).tangent
      (fun r ↦ TotalSpace.mk' ω.compatibleModel (γ r) (W r)) t) :
    mfderiv 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V) ω.compatibleCLM (γ t)
        (alongCurve (leviCivitaConnection 𝓘(ℝ, ω.compatibleModel) 𝒥) γ W t) =
      deriv (fun r ↦ (mfderiv 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V) ω.compatibleCLM (γ r)
          (W r) : V →L[ℝ] V)) t -
        (2⁻¹ : ℝ) • (ω.compatibleCLM (γ t) ∘L
          (mfderiv 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V) ω.compatibleCLM (γ t) (W t) ∘L
              deriv (ω.compatibleCLM ∘ γ) t +
            deriv (ω.compatibleCLM ∘ γ) t ∘L
              mfderiv 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V) ω.compatibleCLM (γ t) (W t))) := by
  have hγ : MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ, ω.compatibleModel) γ t :=
    ((mdifferentiableAt_totalSpace _ _).1 hW).1
  have hf : ContMDiffAt 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V) 2 ω.compatibleCLM (γ t) :=
    contMDiff_compatibleCLM.contMDiffAt
  -- The ambient reading of `W`, a curve in `V →L[ℝ] V`, and its derivative.
  set g : ℝ → V →L[ℝ] V := fun r ↦
    mfderiv 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V) ω.compatibleCLM (γ r) (W r)
  have hgm : g = fun r ↦ mvfderiv 𝓘(ℝ, ω.compatibleModel) ω.compatibleCLM (γ r) (W r) :=
    funext fun r => (mvfderiv_apply_eq_mfderiv_apply _ _ _).symm
  have hgd : HasDerivAt g (deriv g t) t := by
    refine DifferentiableAt.hasDerivAt ?_
    rw [hgm]
    exact mdifferentiableAt_iff_differentiableAt.1
      (((ContMDiffAt.contMDiffAt_mvfderiv_apply (p := TotalSpace.mk' ω.compatibleModel (γ t) (W t))
        hf (m := 1) (by norm_num)).mdifferentiableAt one_ne_zero).comp t hW)
  -- The velocity of `γ`, read in `V →L[ℝ] V`.
  have hc : HasDerivAt (ω.compatibleCLM ∘ γ)
      (mfderiv 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V) ω.compatibleCLM (γ t)
        (curveVelocity 𝓘(ℝ, ω.compatibleModel) γ t)) t := by
    rw [← mvfderiv_apply_eq_mfderiv_apply]
    exact hasDerivAt_comp_curve (hf.mdifferentiableAt two_ne_zero) (hasMFDerivAt_curveVelocity hγ)
  rw [hc.deriv]
  refine mfderiv_compatibleCLM_eq_of_inner_eq_trace
    (a := curveVelocity 𝓘(ℝ, ω.compatibleModel) γ t) (b := W t) (fun u v => ?_) ?_ fun w => ?_
  · -- `g` is skew for `ω` at every time, hence so is its derivative.
    have h := (skewFunctional ω u v).hasFDerivAt.comp_hasDerivAt t hgd
    rw [show ⇑(skewFunctional ω u v) ∘ g = fun _ => 0 from
      funext fun r => (mem_compatibleTangentSpace.1
        (mfderiv_compatibleCLM_mem_compatibleTangentSpace (γ r) (W r))).2 u v] at h
    rw [← skewFunctional_apply, (hasDerivAt_const t (0 : ℝ)).unique h]
  · -- `g` anticommutes with the inclusion at every time, hence the product rule.
    have h := (hc.mul hgd).add (hgd.mul hc)
    have h0 : (ω.compatibleCLM ∘ γ) * g + g * (ω.compatibleCLM ∘ γ) = fun _ => 0 :=
      funext fun r => compatibleCLM_mul_add_mul_compatibleCLM (γ r)
        (mfderiv_compatibleCLM_mem_tangentSpace (γ r) (W r))
    rw [h0] at h
    have h1 := (hasDerivAt_const t (0 : V →L[ℝ] V)).unique h
    rw [add_comm _ ((ω.compatibleCLM ∘ γ) t * deriv g t),
      add_comm (deriv g t * (ω.compatibleCLM ∘ γ) t)] at h1
    -- The products in `V →L[ℝ] V` are the compositions of the statement.
    exact h1.symm
  · -- The Gauss formula along a curve, for the trace form.
    have h := (CovariantDerivative.isLeviCivitaConnection_leviCivitaConnection
      𝓘(ℝ, ω.compatibleModel) (M := 𝒥)).inner_alongCurve_eq_bilin hf traceForm_comm
      inner_eq_traceForm hγ (differentiableAt_sectionCoord γ W hW
        (mem_baseSet_trivializationAt _ _ (γ t))) (hgm ▸ hgd) w
    rw [traceForm_apply, mvfderiv_apply_eq_mfderiv_apply] at h
    exact h

end TauCeti.SymplecticForm

end
