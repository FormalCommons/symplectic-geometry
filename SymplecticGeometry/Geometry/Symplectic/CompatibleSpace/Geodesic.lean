/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.CompatibleSpace.LeviCivita
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Exponential
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Extension
public import TauCeti.Geometry.Manifold.Riemannian.Homogeneous
public import TauCeti.Geometry.Symplectic.AlmostComplex.StructureVariation

/-!
# Geodesics of the space of compatible complex structures

Let `ω` be a symplectic form on a finite-dimensional real normed space `V`, and `𝒥 ω` the
manifold of `ω`-compatible complex structures with the metric `⟪a, b⟫ = ½ tr(â b̂)` of
`Kahler.lean`, where `â` is the ambient reading of a tangent vector `a` at `J`, its image under
the differential of the inclusion `ω.compatibleCLM` into `V →L[ℝ] V`. This file finds all the
geodesics of `𝒥 ω` and shows that it is complete (McDuff–Salamon, Example 4.3.6 and
Exercise 4.3.7).

The geodesic through `J` with velocity `a` is `t ↦ J exp(-t J â)`. It is Tau Ceti's exponential
path `TauCeti.AlmostComplexStructure.tangentPath`, `t ↦ exp(t B) J exp(-t B)` with `B = ½ J â`:
since `B` anticommutes with `J`, conjugating by `J` turns `exp B` into `exp(-B)`, so
`exp(t B) J = J exp(-t B)` (`toContinuousLinearMap_tangentPath_eq_mul_exp`). Write `c(t)` for the
curve in `V →L[ℝ] V` and `A = -J â`. Then `ċ = c A` and `c̈ = c A²`, and since `A` anticommutes with
`c(t)`, `c ċ² = c A²`. By the formula for the covariant derivative along a curve of
`LeviCivita.lean`, the covariant acceleration reads `c̈ - c ċ²` in `V →L[ℝ] V`, which vanishes.

The curve is defined for all time, so `𝒥 ω` is geodesically complete at every point, and by the
uniqueness of geodesics these curves are all the geodesics. The Riemannian distance is complete
too: the isometries of `𝒥 ω` act transitively (`Kahler.lean`), and a homogeneous Riemannian
manifold of finite dimension is complete
(`TauCeti.completeSpace_ofRiemannianMetric_of_isPretransitive_isom`).

## Main definitions and results

* `TauCeti.AlmostComplexStructure.toContinuousLinearMap_tangentPath_eq_mul_exp`: Tau Ceti's
  exponential path in a direction anticommuting with `J` is `t ↦ J exp(-t J Y)`.
* `TauCeti.SymplecticForm.compatibleGeodesic`: the curve `t ↦ J exp(-t J â)` in `𝒥 ω`, with
  `compatibleCLM_compatibleGeodesic`.
* `TauCeti.SymplecticForm.isGeodesicCurveOnFrom_compatibleGeodesic`: it is a geodesic on all of
  `ℝ` with initial data `(J, a)`.
* `TauCeti.SymplecticForm.maximalGeodesic_compatibleSpace` and
  `TauCeti.SymplecticForm.eqOn_compatibleGeodesic`: every geodesic is one of these.
* `TauCeti.SymplecticForm.isGeodesicallyCompleteAt_compatibleSpace` and
  `TauCeti.SymplecticForm.completeSpace_compatibleSpace`: `𝒥 ω` is geodesically complete, and
  complete for its Riemannian distance.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third
  edition][McDuffSalamon2017], Example 4.3.6 and Exercise 4.3.7.
-/

public section

open scoped Manifold
open Bundle CovariantDerivative NormedSpace Set TauCeti.Manifold

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

attribute [local instance] TauCeti.normedAlgebraRatOfReal

namespace AlmostComplexStructure

/-- For `Y` anticommuting with `J`, the exponential path `t ↦ exp(t B) J exp(-t B)`,
`B = ½ J Y`, is `t ↦ J exp(-t J Y)`. -/
theorem toContinuousLinearMap_tangentPath_eq_mul_exp {J : AlmostComplexStructure V}
    {Y : V →L[ℝ] V} (hY : (Y : Module.End ℝ V) ∈ J.tangentSpace) (t : ℝ) :
    LinearMap.toContinuousLinearMap (J.tangentPath Y t).toLinearMap =
      LinearMap.toContinuousLinearMap J.toLinearMap *
        exp (-(t • (LinearMap.toContinuousLinearMap J.toLinearMap * Y))) := by
  set j := LinearMap.toContinuousLinearMap J.toLinearMap
  set B : V →L[ℝ] V := t • (2⁻¹ : ℝ) • (j * Y)
  have hYj : Y * j = -(j * Y) := ContinuousLinearMap.coe_injective <| by
    simpa [j] using eq_neg_of_add_eq_zero_left (mem_tangentSpace.1 hY)
  -- `B` anticommutes with `j`, so `j` conjugates `exp (-B)` to `exp B`.
  have hB : SemiconjBy j (-B) B := by
    have h : j * (j * Y) = -((j * Y) * j) := by
      rw [mul_assoc, hYj, mul_neg, neg_neg]
    simp only [SemiconjBy, B, mul_neg, mul_smul_comm, smul_mul_assoc, h, smul_neg, neg_neg]
  rw [toContinuousLinearMap_tangentPath, ← hB.exp_right.eq, mul_assoc,
    ← exp_add_of_commute (Commute.refl _)]
  congr 2
  simp only [B]
  module

end AlmostComplexStructure

namespace SymplecticForm

variable {ω : SymplecticForm V}

local notation "𝒥" => {J : AlmostComplexStructure V // ω.Compatible J}

/-! ### The geodesics -/

variable (ω) in
/-- The geodesic of the space of compatible complex structures through `J` with velocity `a`:
Tau Ceti's exponential path `t ↦ exp(t B) J exp(-t B)`, `B = ½ J â`, where `â` is the ambient
reading of `a`. It is `t ↦ J exp(-t J â)` (`compatibleCLM_compatibleGeodesic`). -/
noncomputable def compatibleGeodesic (J : 𝒥) (a : TangentSpace 𝓘(ℝ, ω.compatibleModel) J)
    (t : ℝ) : 𝒥 :=
  ⟨J.val.tangentPath (mfderiv 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V) ω.compatibleCLM J a) t,
    J.property.tangentPath (mfderiv_compatibleCLM_mem_compatibleTangentSpace J a) t⟩

theorem compatibleGeodesic_def (J : 𝒥) (a : TangentSpace 𝓘(ℝ, ω.compatibleModel) J) (t : ℝ) :
    ω.compatibleGeodesic J a t =
      ⟨J.val.tangentPath (mfderiv 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V) ω.compatibleCLM J a) t,
        J.property.tangentPath (mfderiv_compatibleCLM_mem_compatibleTangentSpace J a) t⟩ :=
  (rfl)

/-- The geodesic through `J` with velocity `a`, read in `V →L[ℝ] V`, is `t ↦ J exp(-t J â)`, where
`â` is the ambient reading of `a`. -/
theorem compatibleCLM_compatibleGeodesic (J : 𝒥) (a : TangentSpace 𝓘(ℝ, ω.compatibleModel) J)
    (t : ℝ) :
    ω.compatibleCLM (ω.compatibleGeodesic J a t) =
      ω.compatibleCLM J * exp (-(t • (ω.compatibleCLM J ∘L
        mfderiv 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V) ω.compatibleCLM J a))) := by
  have h := AlmostComplexStructure.toContinuousLinearMap_tangentPath_eq_mul_exp
    (mfderiv_compatibleCLM_mem_tangentSpace J a) t
  rw [← compatibleCLM_def J, ContinuousLinearMap.mul_def (ω.compatibleCLM J)
    (mfderiv 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V) ω.compatibleCLM J a)] at h
  rw [compatibleCLM_def (ω.compatibleGeodesic J a t), compatibleGeodesic_def]
  exact h

@[simp]
theorem compatibleGeodesic_zero (J : 𝒥) (a : TangentSpace 𝓘(ℝ, ω.compatibleModel) J) :
    ω.compatibleGeodesic J a 0 = J :=
  Subtype.ext (AlmostComplexStructure.tangentPath_zero _ _)

/-- The geodesic through `J` with velocity `a` is smooth. -/
theorem contMDiff_compatibleGeodesic (J : 𝒥) (a : TangentSpace 𝓘(ℝ, ω.compatibleModel) J)
    {n : WithTop ℕ∞} : ContMDiff 𝓘(ℝ) 𝓘(ℝ, ω.compatibleModel) n (ω.compatibleGeodesic J a) := by
  -- Read in `V →L[ℝ] V`, the curve is Tau Ceti's exponential path, which is smooth.
  have h : ω.compatibleCLM ∘ ω.compatibleGeodesic J a = fun t => LinearMap.toContinuousLinearMap
      (J.val.tangentPath
        (mfderiv 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V) ω.compatibleCLM J a) t).toLinearMap :=
    funext fun t => by rw [Function.comp_apply, compatibleCLM_def, compatibleGeodesic_def]
  rw [contMDiff_compatibleCLM_comp_iff, h, contMDiff_iff_contDiff]
  exact AlmostComplexStructure.contDiff_tangentPath _ _

/-- Read in `V →L[ℝ] V` as `c(t)`, the geodesic through `J` with velocity `a` has derivative
`ċ = c A`, with `A = -J â`. -/
theorem hasDerivAt_compatibleCLM_compatibleGeodesic (J : 𝒥)
    (a : TangentSpace 𝓘(ℝ, ω.compatibleModel) J) (t : ℝ) :
    HasDerivAt (fun r => ω.compatibleCLM (ω.compatibleGeodesic J a r))
      (ω.compatibleCLM (ω.compatibleGeodesic J a t) * -(ω.compatibleCLM J ∘L
        mfderiv 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V) ω.compatibleCLM J a)) t := by
  simp only [compatibleCLM_compatibleGeodesic, ← smul_neg]
  rw [mul_assoc]
  exact (hasDerivAt_exp_smul_const (𝕂 := ℝ) _ t).const_mul _

/-- Along the geodesic through `J` with velocity `a`, read in `V →L[ℝ] V` as `c(t)`, the ambient
reading of the velocity is `c(t) A`, with `A = -J â`. -/
theorem mfderiv_compatibleCLM_curveVelocity_compatibleGeodesic (J : 𝒥)
    (a : TangentSpace 𝓘(ℝ, ω.compatibleModel) J) (t : ℝ) :
    mfderiv 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V) ω.compatibleCLM (ω.compatibleGeodesic J a t)
        (curveVelocity 𝓘(ℝ, ω.compatibleModel) (ω.compatibleGeodesic J a) t) =
      ω.compatibleCLM (ω.compatibleGeodesic J a t) * -(ω.compatibleCLM J ∘L
        mfderiv 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V) ω.compatibleCLM J a) := by
  have hγ : MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ, ω.compatibleModel) (ω.compatibleGeodesic J a) t :=
    (contMDiff_compatibleGeodesic J a (n := 1)).mdifferentiableAt one_ne_zero
  have h := hasDerivAt_comp_curve
    ((contMDiff_compatibleCLM (n := 1)).mdifferentiableAt one_ne_zero)
    (hasMFDerivAt_curveVelocity hγ)
  rw [mvfderiv_apply_eq_mfderiv_apply] at h
  exact h.unique (hasDerivAt_compatibleCLM_compatibleGeodesic J a t)

/-- `A = -J â` anticommutes with every point `c(t)` of the geodesic through `J` with velocity `a`,
read in `V →L[ℝ] V`. -/
theorem compatibleCLM_compatibleGeodesic_mul_neg_mul (J : 𝒥)
    (a : TangentSpace 𝓘(ℝ, ω.compatibleModel) J) (t : ℝ) :
    ω.compatibleCLM (ω.compatibleGeodesic J a t) * -(ω.compatibleCLM J ∘L
        mfderiv 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V) ω.compatibleCLM J a) =
      -(-(ω.compatibleCLM J ∘L
        mfderiv 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V) ω.compatibleCLM J a) *
          ω.compatibleCLM (ω.compatibleGeodesic J a t)) := by
  rw [compatibleCLM_compatibleGeodesic]
  set j := ω.compatibleCLM J
  set Y : V →L[ℝ] V :=
    mfderiv 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V) ω.compatibleCLM J a with hY
  simp only [← ContinuousLinearMap.mul_def]
  have hYj : Y * j = -(j * Y) := by
    have h := compatibleCLM_comp_add_comp_compatibleCLM J
      (mfderiv_compatibleCLM_mem_tangentSpace J a)
    rw [← hY, ← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.mul_def] at h
    exact eq_neg_of_add_eq_zero_right h
  -- `A = -j Y` anticommutes with `j`, and commutes with the exponential factor.
  have hjA : j * -(j * Y) = -(-(j * Y) * j) := by
    rw [neg_mul, neg_neg, mul_assoc, hYj]
  have hE : Commute (-(j * Y)) (exp (-(t • (j * Y)))) :=
    (((Commute.refl (j * Y)).smul_right t).neg_right.neg_left).exp_right
  rw [mul_assoc, ← hE.eq, ← mul_assoc, hjA, neg_mul,
    mul_assoc]

/-- **The geodesics of the space of compatible complex structures.** The curve
`t ↦ J exp(-t J â)` is a geodesic defined on all of `ℝ`, through `J` with velocity `a`. -/
theorem isGeodesicCurveOnFrom_compatibleGeodesic (J : 𝒥)
    (a : TangentSpace 𝓘(ℝ, ω.compatibleModel) J) :
    IsGeodesicCurveOnFrom 𝓘(ℝ, ω.compatibleModel) (ω.compatibleGeodesic J a) univ J a := by
  set γ := ω.compatibleGeodesic J a
  set Y : V →L[ℝ] V :=
    mfderiv 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V) ω.compatibleCLM J a with hY
  -- Read in `V →L[ℝ] V`, the curve is `c(t)` with `ċ = c A`, and `A` anticommutes with `c`.
  have hv := mfderiv_compatibleCLM_curveVelocity_compatibleGeodesic J a
  have hc := hasDerivAt_compatibleCLM_compatibleGeodesic J a
  have hcA := compatibleCLM_compatibleGeodesic_mul_neg_mul J a
  rw [← hY, ← ContinuousLinearMap.mul_def] at hv hc hcA
  set A : V →L[ℝ] V := -(ω.compatibleCLM J * Y) with hA
  refine ⟨isGeodesicCurveOn_univ.2 (isGeodesicCurve_iff.2
    ⟨contMDiff_compatibleGeodesic J a, fun t => ?_⟩), mem_univ 0, ?_⟩
  · -- The ambient reading of the acceleration is `c̈ - c ċ² = c A² - c (c A)² = 0`.
    have hW := (contMDiff_compatibleGeodesic J a (n := 2)).contMDiffAt.contMDiffAt_curveVelocityLift
      (I := 𝓘(ℝ, ω.compatibleModel)) (m := 1) (t := t) (by norm_num)
    rw [show curveVelocityLift 𝓘(ℝ, ω.compatibleModel) γ =
      fun r => TotalSpace.mk' ω.compatibleModel (γ r)
        (curveVelocity 𝓘(ℝ, ω.compatibleModel) γ r) from
      funext (curveVelocityLift_apply γ)] at hW
    have hacc := alongCurve_leviCivitaConnection_compatibleSpace (hW.mdifferentiableAt one_ne_zero)
    rw [show (fun r => (mfderiv 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V) ω.compatibleCLM (γ r)
        (curveVelocity 𝓘(ℝ, ω.compatibleModel) γ r) : V →L[ℝ] V)) =
        fun r => ω.compatibleCLM (γ r) * A from funext hv, hv t, ((hc t).mul_const A).deriv,
      Function.comp_def, (hc t).deriv, ← acceleration_def] at hacc
    have hAc : A * ω.compatibleCLM (γ t) = -(ω.compatibleCLM (γ t) * A) := by
      rw [hcA t, neg_neg]
    have key : ω.compatibleCLM (γ t) * A * (ω.compatibleCLM (γ t) * A) = A * A := by
      rw [mul_assoc, ← mul_assoc A, hAc, neg_mul, mul_neg, ← mul_assoc, ← mul_assoc,
        compatibleCLM_mul_self, neg_one_mul, neg_mul, neg_neg]
    apply injective_mfderiv_compatibleCLM (γ t)
    rw [hacc]
    simp only [← ContinuousLinearMap.mul_def]
    rw [key, ← two_smul ℝ (A * A), mul_smul_comm, smul_smul, inv_mul_cancel₀ two_ne_zero,
      one_smul, mul_assoc, sub_self]
    exact (map_zero _).symm
  · -- At `0` the curve is at `J`, with velocity `â`.
    rw [curveVelocityWithin_univ]
    refine TotalSpace.ext (compatibleGeodesic_zero J a) (heq_of_eq ?_)
    apply injective_mfderiv_compatibleCLM J
    have h := hv 0
    rw [compatibleGeodesic_zero] at h
    refine h.trans ?_
    rw [hA, mul_neg, ← mul_assoc, compatibleCLM_mul_self, neg_one_mul, neg_neg]

/-- **Geodesics are unique.** The maximal geodesic through `J` with velocity `a` is
`t ↦ J exp(-t J â)`. -/
theorem maximalGeodesic_compatibleSpace (J : 𝒥) (a : TangentSpace 𝓘(ℝ, ω.compatibleModel) J) :
    maximalGeodesic 𝓘(ℝ, ω.compatibleModel) 𝒥 J a = ω.compatibleGeodesic J a :=
  funext (isGeodesicCurveOnFrom_compatibleGeodesic J a).eq_maximalGeodesic_of_univ

/-- **Every geodesic is one of the curves `t ↦ J exp(-t J â)`.** A geodesic on a preconnected
parameter set, through `J` with velocity `a` at `0`, agrees there with
`ω.compatibleGeodesic J a`. -/
theorem eqOn_compatibleGeodesic {J : 𝒥} {a : TangentSpace 𝓘(ℝ, ω.compatibleModel) J}
    {γ : ℝ → 𝒥} {s : Set ℝ} (hγ : IsGeodesicCurveOnFrom 𝓘(ℝ, ω.compatibleModel) γ s J a)
    (hs : IsPreconnected s) : EqOn γ (ω.compatibleGeodesic J a) s := by
  rw [← maximalGeodesic_compatibleSpace]
  exact (hγ.eqOn_maximalGeodesic_of_isPreconnected hs).symm

/-- **The space of compatible complex structures is geodesically complete**: every maximal
geodesic through `J` is defined for all time. -/
theorem isGeodesicallyCompleteAt_compatibleSpace (J : 𝒥) :
    IsGeodesicallyCompleteAt 𝓘(ℝ, ω.compatibleModel) 𝒥 J :=
  isGeodesicallyCompleteAt_iff_forall_one_mem_geodesicInterval.2 fun a =>
    ((isGeodesicCurveOnFrom_compatibleGeodesic J a).mono (uniqueDiffOn_Ioo (-2) 2)
      (subset_univ _) ⟨by norm_num, by norm_num⟩).subset_geodesicInterval
      ⟨by norm_num, by norm_num⟩

/-- **The space of compatible complex structures is complete** for its Riemannian distance. -/
theorem completeSpace_compatibleSpace :
    letI := EMetricSpace.ofRiemannianMetric 𝓘(ℝ, ω.compatibleModel) 𝒥
    CompleteSpace 𝒥 :=
  completeSpace_ofRiemannianMetric_of_isPretransitive_isom (I := 𝓘(ℝ, ω.compatibleModel)) 𝒥

end SymplecticForm

end TauCeti

end
