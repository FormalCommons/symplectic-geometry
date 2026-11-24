/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Flow
public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Velocity
public import TauCeti.Geometry.Manifold.DifferentialForm.Interior
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import SymplecticGeometry.Geometry.Manifold.Instances.Icc
import SymplecticGeometry.Geometry.Manifold.MFDeriv.Prod
import TauCeti.Geometry.Manifold.MFDeriv.Constancy
import TauCeti.Geometry.Manifold.MFDeriv.Prod

/-!
# The velocity of a diffeotopy

Let `φ_t`, `t ∈ [0, 1]`, be a smooth diffeotopy of a manifold `M`, with motion
`Φ.cylinderMap : (x, t) ↦ φ_t x` on the cylinder `M × [0, 1]`. Its velocity at time `t` is Tau
Ceti's vector field `X_t = (∂ₜ φ_t) ∘ φ_t⁻¹` (`TauCeti.Diffeotopy.velocity`), where `∂ₜ` is the
unit tangent vector of the interval, so that `X_t (φ_t x)` is the time derivative of the motion at
`(x, t)` (Tau Ceti's `TauCeti.Diffeotopy.velocity_apply`). This file shows that it is smooth,
jointly in time and space, and gives it as a smooth vector field. It is defined for every
`t ∈ [0, 1]`; at the two ends the time derivative is one-sided. This is the field that generates
the diffeotopy, in the sense of McDuff–Salamon, §3.1, and the time derivative that Tau Ceti's
`TauCeti.Diffeotopy.HasHamiltonian` and `TauCeti.Diffeotopy.fluxForm` use.

## Main definitions

* `TauCeti.Diffeotopy.smoothVelocity Φ t`: the velocity `X_t` of `Φ`, as a smooth vector field
  on `M`.

## Main results

* `TauCeti.Diffeotopy.mfderiv_cylinderMap_time`: the motion sends `∂ₜ` at `(x, t)` to the
  velocity of the trajectory `s ↦ φ_s x`. Its action `(v, 0) ↦ dφ_t v` on spatial vectors is Tau
  Ceti's `TauCeti.Diffeotopy.mfderiv_cylinderMap_inl`.
* `TauCeti.Diffeotopy.forall_velocity_mem_iff`: the velocity lies in a family of subspaces `D_t`
  everywhere if and only if the time derivative of the motion at `(x, t)` lies in `D_t (φ_t x)`.
* `TauCeti.Diffeotopy.contMDiff_velocity`, `TauCeti.Diffeotopy.contMDiff_smoothVelocity`: `X_t` is
  jointly smooth in `(t, y)`, up to both ends.
* `TauCeti.Diffeotopy.mfderiv_cylinderMap_curve`: the chain rule for the motion along a curve,
  `d/ds φ_s (c s) = dφ_s (c' s) + X_s (φ_s (c s))`.
* `TauCeti.Diffeotopy.apply_eq_of_mfderiv_eq_velocity`: a differentiable curve `γ` on `[0, 1]` with
  `γ' t = X_t (γ t)` is the trajectory `t ↦ φ_t (γ 0)`.
* `TauCeti.Diffeotopy.smoothVelocity_refl`: the constant diffeotopy has velocity zero.
* `TauCeti.Diffeotopy.mpullback_timeSlice_interior_velocity_apply`: `φ_t^* (ι_{X_t} σ)` on a
  vector `v` is `(Φ^* σ)(∂ₜ, (v, 0))`, the integrand of the flux form and of `HasHamiltonian`.

## Implementation notes

The velocity is read along the motion, through the derivative of `Φ.cylinderMap` on `∂ₜ`, and not
through Tau Ceti's `TauCeti.eulerianField` of a family over `ℝ`, which would need an extension of
the diffeotopy past both ends. The joint smoothness comes from the smoothness of the tangent map
of the motion and of the unit vector field of the interval (`contMDiff_totalSpaceMk_one_Icc`).
Its proof follows that of Tau Ceti's `TauCeti.contMDiff_vectorBundleEulerField`: a unit vector,
built from the zero section and a smooth vector of the other factor, is pushed forward by the
tangent map of a smooth map.

`mfderiv_cylinderMap_time` reads the derivative of the motion on `(0, ∂ₜ)` as a partial
derivative, by `MDifferentiableAt.mfderiv_curry_right_apply`, as Tau Ceti's
`TauCeti.Diffeotopy.mfderiv_cylinderMap_globalFlowDiffeotopy_time` does for a flow.

For `apply_eq_of_mfderiv_eq_velocity`, no uniqueness theorem for differential equations is
needed: the derivative `c' s` of the curve `c s = φ_s⁻¹ (γ s)` satisfies
`dφ_s (c' s) = γ' s - X_s (γ s) = 0`, by the chain rule `mfderiv_cylinderMap_curve`,
so `c` is constant by Tau Ceti's `MDifferentiable.apply_eq_of_mfderiv_eq_zero`, the interval
being connected. This needs neither a finite-dimensional model nor a boundaryless or Hausdorff
`M`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §3.1.
-/

public noncomputable section

open Set
open scoped Manifold ContDiff

namespace TauCeti.Diffeotopy

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {J : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

section Derivative

variable {n : ℕ∞ω} (Φ : Diffeotopy J n M)

/-- The motion of a `C^n` diffeotopy, `1 ≤ n`, sends the unit time vector `∂ₜ` at `(x, t)` to
the velocity of the trajectory `s ↦ Φ (s, x)` at time `t`. -/
theorem mfderiv_cylinderMap_time (hn : 1 ≤ n) (p : M × unitInterval) :
    mfderiv (J.prod (𝓡∂ 1)) J Φ.cylinderMap p ((0 : E), (1 : TangentSpace (𝓡∂ 1) p.2)) =
      mfderiv (𝓡∂ 1) J (fun s ↦ Φ (s, p.1)) p.2 1 := by
  have h : (fun s ↦ Φ.cylinderMap (p.1, s)) = fun s ↦ Φ (s, p.1) :=
    funext fun s ↦ Φ.cylinderMap_apply (p.1, s)
  have hd := Φ.contMDiff_cylinderMap.mdifferentiableAt (x := p) (zero_lt_one.trans_le hn).ne'
  exact (hd.mfderiv_curry_right_apply _).trans
    (congrArg (fun f ↦ mfderiv (𝓡∂ 1) J f p.2 (1 : TangentSpace (𝓡∂ 1) p.2)) h)

end Derivative

variable [IsManifold J ∞ M] (Φ : Diffeotopy J ∞ M)

/-- The time derivative of the motion, read at the point that has reached `y` at time `t`, as a
smooth map on `unitInterval × M` into the tangent bundle. -/
private theorem contMDiff_velocityAux :
    ContMDiff ((𝓡∂ 1).prod J) J.tangent ∞
      (fun p : unitInterval × M ↦ (⟨p.2, Φ.velocity p.1 p.2⟩ : TangentBundle J M)) := by
  -- The unit time vector at `(φ_t⁻¹ y, t)`, as a smooth map into the tangent bundle of `M × I`.
  have hs : ContMDiff ((𝓡∂ 1).prod J) (J.prod (𝓡∂ 1)).tangent ∞ (fun p : unitInterval × M ↦
      (equivTangentBundleProd J M (𝓡∂ 1) unitInterval).symm
        (Bundle.zeroSection E (TangentSpace J) (Φ.symm p),
          (⟨p.1, 1⟩ : TangentBundle (𝓡∂ 1) unitInterval))) :=
    contMDiff_equivTangentBundleProd_symm.comp
      (((Bundle.contMDiff_zeroSection ℝ (TangentSpace J)).comp Φ.symm.contMDiff).prodMk
        (SymplecticGeometry.contMDiff_totalSpaceMk_one_Icc.comp contMDiff_fst))
  refine ((Φ.contMDiff_cylinderMap.contMDiff_tangentMap (m := ∞) le_rfl).comp hs).congr
    fun p ↦ ?_
  have hb : Φ.cylinderMap (Φ.symm p, p.1) = p.2 := by
    rw [cylinderMap_apply]
    exact Φ.apply_mk_symm_apply p.1 p.2
  have key : ∀ (a b : M) (v : E), a = b → (⟨a, v⟩ : TangentBundle J M) = ⟨b, v⟩ := by
    rintro a _ v rfl
    rfl
  -- The tangent map applied to `(0, ∂ₜ)` at `(φ_t⁻¹ y, t)` is, by definition, that vector's image
  -- based at `φ_t (φ_t⁻¹ y)`; only the base point has to be moved to `y`.
  rw [velocity_def]
  exact key _ _ _ hb.symm

/-- The velocity `X_t` of a diffeotopy `φ` at time `t ∈ [0, 1]`, Tau Ceti's
`TauCeti.Diffeotopy.velocity`, as a smooth vector field on `M`. -/
def smoothVelocity (t : unitInterval) : Cₛ^∞⟮J; E, TangentSpace J (M := M)⟯ where
  toFun := Φ.velocity t
  contMDiff_toFun := (Φ.contMDiff_velocityAux).comp (contMDiff_const.prodMk contMDiff_id)

@[simp]
theorem coe_smoothVelocity (t : unitInterval) : ⇑(Φ.smoothVelocity t) = Φ.velocity t :=
  (rfl)

omit [IsManifold J ∞ M] in
/-- The velocity of a diffeotopy lies in a family of subspaces `D_t` everywhere if and only if,
for every `x` and `t`, the time derivative of the motion at `(x, t)` lies in `D_t` at `φ_t x`. -/
theorem forall_velocity_mem_iff (D : unitInterval → (y : M) → Submodule ℝ (TangentSpace J y)) :
    (∀ t y, Φ.velocity t y ∈ D t y) ↔ ∀ (t : unitInterval) (x : M),
      mfderiv (J.prod (𝓡∂ 1)) J Φ.cylinderMap (x, t)
        ((0 : E), (1 : TangentSpace (𝓡∂ 1) t)) ∈ D t (Φ (t, x)) := by
  refine ⟨fun h t x ↦ Φ.velocity_apply t x ▸ h t (Φ (t, x)), fun h t y ↦ ?_⟩
  obtain ⟨x, rfl⟩ : ∃ x, Φ (t, x) = y := ⟨_, Φ.apply_mk_symm_apply t y⟩
  exact Φ.velocity_apply t x ▸ h t x

/-- The velocity of a diffeotopy is jointly smooth in time and space, up to both ends of the
time interval. -/
theorem contMDiff_velocity :
    ContMDiff ((𝓡∂ 1).prod J) J.tangent ∞
      (fun p : unitInterval × M ↦ (⟨p.2, Φ.velocity p.1 p.2⟩ : TangentBundle J M)) :=
  Φ.contMDiff_velocityAux

/-- `TauCeti.Diffeotopy.contMDiff_velocity`, for the smooth vector fields `smoothVelocity`. -/
theorem contMDiff_smoothVelocity :
    ContMDiff ((𝓡∂ 1).prod J) J.tangent ∞
      (fun p : unitInterval × M ↦ (⟨p.2, Φ.smoothVelocity p.1 p.2⟩ : TangentBundle J M)) :=
  Φ.contMDiff_velocityAux

omit [IsManifold J ∞ M] in
/-- **The chain rule for the motion along a curve.** For a curve `c` on `[0, 1]`, differentiable
at `s`, the derivative at `s` of `s ↦ φ_s (c s)` on the unit vector is
`dφ_s (c' s) + X_s (φ_s (c s))`. -/
theorem mfderiv_cylinderMap_curve {c : unitInterval → M} {s : unitInterval}
    (hc : MDifferentiableAt (𝓡∂ 1) J c s) :
    mfderiv (𝓡∂ 1) J (fun s ↦ Φ.cylinderMap (c s, s)) s 1 =
      @HAdd.hAdd E E E _ (mfderiv J J (Φ.timeSlice s) (c s) (mfderiv (𝓡∂ 1) J c s 1))
        (Φ.velocity s (Φ.cylinderMap (c s, s))) := by
  have hd := Φ.contMDiff_cylinderMap.mdifferentiableAt (x := (c s, s)) (by simp)
  have hpd : mfderiv (𝓡∂ 1) (J.prod (𝓡∂ 1)) (fun s ↦ (c s, s)) s =
      (mfderiv (𝓡∂ 1) J c s).prod (ContinuousLinearMap.id ℝ _) := by
    rw [← mfderiv_id]
    exact mfderiv_prodMk hc mdifferentiableAt_id
  rw [← Function.comp_def Φ.cylinderMap (fun s ↦ (c s, s)),
    mfderiv_comp_apply (f := fun s ↦ (c s, s)) s hd (hc.prodMk mdifferentiableAt_id), hpd,
    mfderiv_prod_eq_add_apply hd, cylinderMap_apply, velocity_apply]
  -- The components of `(c' s 1, 1)` are read off by `ContinuousLinearMap.prod_apply` up to
  -- definitional unfolding: the tangent space of `M × I` is the product of the tangent spaces
  -- by definition, and that lemma does not rewrite across the identification.
  congr 1
  · exact (hd.mfderiv_curry_left_apply _).symm.trans (Φ.mfderiv_cylinderMap_inl (by simp) _ _)
  · exact (hd.mfderiv_curry_right_apply _).symm

/-- **The trajectories of a diffeotopy are the solutions of its equation.** A differentiable
curve `γ` on `[0, 1]` whose velocity at every time `t`, one-sided at the ends, is the velocity
`X_t (γ t)` of the diffeotopy is the trajectory `t ↦ φ_t (γ 0)` of its initial point. -/
theorem apply_eq_of_mfderiv_eq_velocity {γ : unitInterval → M}
    (hγ : MDifferentiable (𝓡∂ 1) J γ)
    (hγX : ∀ t, mfderiv (𝓡∂ 1) J γ t 1 = Φ.velocity t (γ t)) (t : unitInterval) :
    Φ (t, γ 0) = γ t := by
  -- The curve `c s = φ_s⁻¹ (γ s)` has zero derivative, so it is constant.
  obtain ⟨c, hc⟩ : ∃ c : unitInterval → M, c = fun s ↦ Φ.symm (s, γ s) := ⟨_, rfl⟩
  have hcd : MDifferentiable (𝓡∂ 1) J c := hc ▸
    (Φ.symm.contMDiff.mdifferentiable (by simp)).comp (mdifferentiable_id.prodMk hγ)
  have hγc (s : unitInterval) : Φ.cylinderMap (c s, s) = γ s := by
    rw [cylinderMap_apply, hc, Φ.apply_mk_symm_apply]
  have hzero (s : unitInterval) : mfderiv (𝓡∂ 1) J c s = 0 := by
    -- Differentiating `φ_s (c s) = γ s` gives `dφ_s (c' s) + X_s (γ s) = γ' s = X_s (γ s)`.
    have key := Φ.mfderiv_cylinderMap_curve (hcd s)
    rw [funext hγc, hγc, hγX] at key
    have hslice : mfderiv J J (Φ.timeSlice s) (c s) (mfderiv (𝓡∂ 1) J c s 1) = 0 :=
      add_eq_right.1 key.symm
    rw [← (Φ.timeSlice s).mfderivToContinuousLinearEquiv_coe (by simp),
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.map_eq_zero_iff] at hslice
    exact ContinuousLinearMap.ext_tangentSpace_Icc (hslice.trans (zero_apply _).symm)
  have h0 : c 0 = γ 0 := by rw [hc, Φ.symm.apply_zero]
  rw [← h0, MDifferentiable.apply_eq_of_mfderiv_eq_zero hcd hzero 0 t, ← hγc t,
    cylinderMap_apply]

/-- The constant diffeotopy has velocity zero, as a smooth vector field. -/
@[simp]
theorem smoothVelocity_refl (t : unitInterval) : (refl J ∞ M).smoothVelocity t = 0 := by
  ext y
  rw [coe_smoothVelocity, velocity_refl, ContMDiffSection.coe_zero]

omit [IsManifold J ∞ M] in
/-- On a spatial vector `v` at `x`, the pullback by `φ_t` of the contraction `ι_{X_t} σ` of a
two-form `σ` with the velocity is the pullback of `σ` along the motion, evaluated on `∂ₜ` and
`(v, 0)` at `(x, t)`: both are `σ_{φ_t x}(∂ₜ φ_t x, dφ_t v)`. -/
theorem mpullback_timeSlice_interior_velocity_apply {F : Type*} [AddCommGroup F] [Module ℝ F]
    [TopologicalSpace F] (σ : RoughForm J M F 2) (t : unitInterval) (x : M) (v : E) :
    mpullback J J (Φ.timeSlice t) (σ.interior (Φ.velocity t)) x ![v] =
      mpullback (J.prod (𝓡∂ 1)) J Φ.cylinderMap σ (x, t)
        ![((0 : E), (1 : TangentSpace (𝓡∂ 1) t)), (v, (0 : EuclideanSpace ℝ (Fin 1)))] := by
  have h : ⇑(Φ.timeSlice t) = fun z ↦ Φ.cylinderMap (z, t) :=
    funext fun z ↦ (Φ.timeSlice_apply t z).trans (Φ.cylinderMap_apply (z, t)).symm
  rw [h, mpullback_apply, mpullback_apply, RoughForm.interior_apply]
  congr 1
  funext i
  fin_cases i
  -- `exact` evaluates the vector `![∂ₜ, (v, 0)]` at `0`.
  · rw [Φ.cylinderMap_apply]
    exact Φ.velocity_apply t x
  · exact ((Φ.mfderiv_cylinderMap_inl (by simp) (x, t) v).trans
      (congrArg (fun f ↦ mfderiv J J f x v) h)).symm

end TauCeti.Diffeotopy

end
