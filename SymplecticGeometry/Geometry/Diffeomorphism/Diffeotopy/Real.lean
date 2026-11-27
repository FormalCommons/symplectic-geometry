/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Diffeomorphism.Diffeotopy.Velocity
public import SymplecticGeometry.Geometry.Manifold.Flow.TimeDependent
public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Flow
public import TauCeti.Geometry.Manifold.Flow.Eulerian
import SymplecticGeometry.Geometry.Manifold.SmoothTransition
import TauCeti.Geometry.Manifold.Diffeomorph.Family
import TauCeti.Geometry.Manifold.Instances.Icc

/-!
# Isotopies over `ℝ` and diffeotopies

Families of diffeomorphisms of a manifold `M` come in two forms: a family `ψ : ℝ → M ≃ₘ M` over
the real line, jointly smooth in `(t, x)`, as Tau Ceti's Eulerian field `TauCeti.eulerianField`
and its time-dependent flows use, and a `TauCeti.Diffeotopy`, a level-preserving diffeomorphism of
`unitInterval × M` that starts at the identity. This file passes between the two.

## Main definitions

* `TauCeti.Diffeotopy.ofReal ψ hψ h₀`: the restriction to `[0, 1]` of a jointly smooth family
  `ψ` over `ℝ` with `ψ 0 = id`, as a diffeotopy.
* `TauCeti.Diffeotopy.smoothTransitionFamily Φ`: the family `u ↦ φ_{s(u)}` over `ℝ` of a
  diffeotopy `Φ`, with `s = unitInterval.smoothTransition`; it is the identity for `u ≤ 0` and the
  final map `Φ.final` for `u ≥ 1`.

## Main results

* `TauCeti.Diffeotopy.mfderiv_cylinderMap_ofReal`: the time derivative of `ofReal ψ hψ h₀` at
  `(x, t)` is the Eulerian field of `ψ` at time `t` and at the point `ψ_t x`.
* `TauCeti.Diffeotopy.timeDependentFlowDiffeotopy_eq_ofReal`: the diffeotopy of a time-dependent
  vector field is the restriction of its time-dependent flow from time `0`.
* `TauCeti.Diffeotopy.contMDiff_smoothTransitionFamily`,
  `TauCeti.Diffeotopy.contMDiff_smoothTransitionFamily_symm`: the family `u ↦ φ_{s(u)}` and its
  inverses are jointly smooth.
* `TauCeti.Diffeotopy.eulerianField_smoothTransitionFamily_apply`: the Eulerian field of
  `u ↦ φ_{s(u)}` at `φ_{s(u)} x` is `s'(u)` times the time derivative of `Φ` at `(x, s(u))`.
* `TauCeti.Diffeotopy.eulerianField_smoothTransitionFamily`: as a vector field, the Eulerian field
  of `u ↦ φ_{s(u)}` at time `u` is `s'(u)` times the velocity `X_{s(u)}` of `Φ`.
* `TauCeti.Diffeotopy.contMDiff_eulerianField_smoothTransitionFamily`: that Eulerian field is
  jointly smooth.
* `TauCeti.Diffeotopy.timeDependentFlowOf_eulerianField_smoothTransitionFamily`: its
  time-dependent flow from time `u` to time `u'` is `φ_{s(u')} ∘ φ_{s(u)}⁻¹`.

Time derivatives of a diffeotopy are taken, as in Tau Ceti's `TauCeti.Diffeotopy.HasHamiltonian`,
through `Φ.cylinderMap` on the vector `∂ₜ = (0, 1)` at `(x, t)`, where `1` is the unit tangent
vector of the interval, which points towards increasing time at both ends. That derivative is the
velocity of the trajectory `s ↦ Φ (s, x)`, by `TauCeti.Diffeotopy.mfderiv_cylinderMap_time`.
The inverse of `ofReal` is smooth by `Diffeomorph.contMDiff_symm_family`, and the time-dependent
flow is a jointly smooth family by `TauCeti.contMDiff_timeDependentFlowDiffeomorph`.

`mfderiv_cylinderMap_ofReal` reads Tau Ceti's velocity of the diffeotopy as the Eulerian field
of `ψ`, by `TauCeti.Diffeotopy.velocity_apply` and `TauCeti.Diffeotopy.velocity_eq_eulerianField`.
The proof of `eulerianField_smoothTransitionFamily_apply` follows Tau Ceti's
`TauCeti.Diffeotopy.mfderiv_cylinderMap_globalFlowDiffeotopy_time`, which reads the time
derivative of the motion on a trajectory and differentiates through the inclusion of the interval.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §3.1.
-/

public noncomputable section

open Set
open scoped Manifold ContDiff

namespace TauCeti.Diffeotopy

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

/-! ### The restriction of a family over `ℝ` -/

section OfReal

variable [CompleteSpace E] [IsManifold I ∞ M] [BoundarylessManifold I M]
  (ψ : ℝ → M ≃ₘ⟮I, I⟯ M) (hψ : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M ↦ ψ p.1 p.2))
  (h₀ : ∀ x, ψ 0 x = x)

/-- The restriction to `[0, 1]` of a jointly smooth family `ψ` of diffeomorphisms over `ℝ` with
`ψ 0 = id`, as a diffeotopy: `(t, x) ↦ ψ_t x`. Its inverse is jointly smooth by
`Diffeomorph.contMDiff_symm_family`. -/
def ofReal : Diffeotopy I ∞ M where
  toDiffeomorph :=
    { toFun := fun p ↦ (p.1, ψ p.1 p.2)
      invFun := fun p ↦ (p.1, (ψ p.1).symm p.2)
      left_inv := fun p ↦ by simp
      right_inv := fun p ↦ by simp
      contMDiff_toFun := contMDiff_fst.prodMk
        (hψ.comp ((contMDiff_subtypeVal_Icc.comp contMDiff_fst).prodMk contMDiff_snd))
      contMDiff_invFun := contMDiff_fst.prodMk
        ((Diffeomorph.contMDiff_symm_family hψ (by simp)).comp
          ((contMDiff_subtypeVal_Icc.comp contMDiff_fst).prodMk contMDiff_snd)) }
  fst_apply _ := rfl
  snd_apply_zero' := h₀

/-- The restriction `ofReal ψ hψ h₀` sends `(t, x)` to `ψ_t x`. -/
@[simp]
theorem ofReal_apply (p : unitInterval × M) : ofReal ψ hψ h₀ p = ψ p.1 p.2 :=
  (rfl)

/-- The time-`t` slice of the restriction `ofReal ψ hψ h₀` is `ψ_t`. -/
@[simp]
theorem timeSlice_ofReal (t : unitInterval) : (ofReal ψ hψ h₀).timeSlice t = ψ t :=
  Diffeomorph.ext fun x ↦ by rw [timeSlice_apply, ofReal_apply]

/-- The inverse of the level-preserving diffeomorphism of `ofReal ψ hψ h₀` sends `(t, y)` to
`(t, ψ_t⁻¹ y)`. -/
@[simp]
theorem toDiffeomorph_symm_ofReal_apply (p : unitInterval × M) :
    (ofReal ψ hψ h₀).toDiffeomorph.symm p = (p.1, (ψ p.1).symm p.2) :=
  (rfl)

/-- The inverse of the restriction `ofReal ψ hψ h₀` sends `(t, y)` to `ψ_t⁻¹ y`. `simp` proves
it through `symm_apply` and `toDiffeomorph_symm_ofReal_apply`. -/
theorem symm_ofReal_apply (p : unitInterval × M) : (ofReal ψ hψ h₀).symm p = (ψ p.1).symm p.2 := by
  rw [symm_apply, toDiffeomorph_symm_ofReal_apply]

/-- The final map of the restriction `ofReal ψ hψ h₀` is `ψ_1`. -/
@[simp]
theorem final_ofReal : (ofReal ψ hψ h₀).final = ψ 1 := by
  rw [final_def, timeSlice_ofReal, Set.Icc.coe_one]

/-- The time derivative of the restriction `ofReal ψ hψ h₀` at `(x, t)` is the Eulerian field of
`ψ` at time `t` and at the point `ψ_t x`. -/
theorem mfderiv_cylinderMap_ofReal (x : M) (t : unitInterval) :
    mfderiv (I.prod (𝓡∂ 1)) I (ofReal ψ hψ h₀).cylinderMap (x, t)
      ((0 : E), (1 : TangentSpace (𝓡∂ 1) t)) =
      eulerianField I (fun u ↦ (ψ u).toEquiv) t (ψ t x) := by
  have hγ : MDifferentiableAt 𝓘(ℝ) I (fun u ↦ ψ u x) t :=
    (hψ.comp (contMDiff_id.prodMk contMDiff_const)).mdifferentiableAt (by simp)
  have hd : MDifferentiableAt 𝓘(ℝ) I
      (fun u ↦ (ψ u).toEquiv ((ψ (t : ℝ)).toEquiv.symm (ψ t x))) t := by
    simpa only [Diffeomorph.toEquiv_coe_symm, Diffeomorph.coe_toEquiv,
      Diffeomorph.symm_apply_apply] using hγ
  rw [← velocity_apply, ofReal_apply]
  exact velocity_eq_eulerianField _ (by simp) (fun s y ↦ (ofReal_apply ψ hψ h₀ (s, y)).symm) hd

end OfReal

/-! ### Time-dependent flows -/

section Flow

variable [FiniteDimensional ℝ E] [T2Space M] [BoundarylessManifold I M] [IsManifold I ∞ M]
  [IsManifold I 1 M] {X : ℝ → (x : M) → TangentSpace I x}
  (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent ∞
    (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
  (hc : IsCompleteVectorField (timeDependentSuspensionField X))

/-- The diffeotopy of a smooth time-dependent vector field `X` with complete suspension is the
restriction to `[0, 1]` of the time-dependent flow of `X` from time `0`. -/
theorem timeDependentFlowDiffeotopy_eq_ofReal :
    timeDependentFlowDiffeotopy le_top hX hc =
      ofReal (fun t ↦ timeDependentFlowDiffeomorph hc le_top hX 0 t)
        (contMDiff_timeDependentFlowDiffeomorph le_top hX hc 0)
        (fun x ↦ (timeDependentFlowDiffeomorph_apply hc le_top hX 0 0 x).trans
          (timeDependentFlowOf_self X 0 x)) :=
  ext fun p ↦ by
    rw [timeDependentFlowDiffeotopy_apply, ofReal_apply, timeDependentFlowDiffeomorph_apply]

end Flow

/-! ### The reading of a diffeotopy over `ℝ` -/

section SmoothTransition

variable (Φ : Diffeotopy I ∞ M)

/-- The family `u ↦ φ_{s(u)}` over `ℝ` of a diffeotopy `Φ`, where `s = Real.smoothTransition`:
the identity for `u ≤ 0`, the final map for `u ≥ 1`, and a reparametrization of `Φ` in between. -/
def smoothTransitionFamily (u : ℝ) : M ≃ₘ⟮I, I⟯ M :=
  Φ.timeSlice (unitInterval.smoothTransition u)

/-- The family `u ↦ φ_{s(u)}` at `u` is the time slice of `Φ` at `s(u)`. -/
theorem smoothTransitionFamily_def (u : ℝ) :
    Φ.smoothTransitionFamily u = Φ.timeSlice (unitInterval.smoothTransition u) :=
  (rfl)

/-- The family `u ↦ φ_{s(u)}` sends `x` to `Φ (s(u), x)`. -/
@[simp]
theorem smoothTransitionFamily_apply (u : ℝ) (x : M) :
    Φ.smoothTransitionFamily u x = Φ (unitInterval.smoothTransition u, x) :=
  Φ.timeSlice_apply _ x

/-- For `u ≤ 0`, the map `φ_{s(u)}` is the identity. -/
theorem smoothTransitionFamily_of_nonpos {u : ℝ} (hu : u ≤ 0) :
    Φ.smoothTransitionFamily u = Diffeomorph.refl I M ∞ := by
  rw [smoothTransitionFamily_def, unitInterval.smoothTransition_of_nonpos hu, timeSlice_zero]

/-- For `u ≥ 1`, the map `φ_{s(u)}` is the final map of `Φ`. -/
theorem smoothTransitionFamily_of_one_le {u : ℝ} (hu : 1 ≤ u) :
    Φ.smoothTransitionFamily u = Φ.final := by
  rw [smoothTransitionFamily_def, unitInterval.smoothTransition_of_one_le hu, final_def]

/-- The family `u ↦ φ_{s(u)}` is jointly smooth in `(u, x)`. -/
theorem contMDiff_smoothTransitionFamily :
    ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M ↦ Φ.smoothTransitionFamily p.1 p.2) :=
  Φ.contMDiff.comp (((unitInterval.contMDiff_smoothTransition le_rfl).comp contMDiff_fst).prodMk
    contMDiff_snd) |>.congr
    fun p ↦ Φ.smoothTransitionFamily_apply p.1 p.2

/-- The inverses of the family `u ↦ φ_{s(u)}` are jointly smooth in `(u, y)`. -/
theorem contMDiff_smoothTransitionFamily_symm :
    ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M ↦ (Φ.smoothTransitionFamily p.1).symm p.2) :=
  Φ.symm.contMDiff.comp
    (((unitInterval.contMDiff_smoothTransition le_rfl).comp contMDiff_fst).prodMk
      contMDiff_snd) |>.congr
    fun _ ↦ symm_timeSlice_apply _ _ _

/-- The Eulerian field of the family `u ↦ φ_{s(u)}`, `s = Real.smoothTransition`, at the point
`φ_{s(u)} x` is `s'(u)` times the time derivative of `Φ` at `(x, s(u))`. -/
theorem eulerianField_smoothTransitionFamily_apply (u : ℝ) (x : M) :
    eulerianField I (fun v ↦ (Φ.smoothTransitionFamily v).toEquiv) u
      (Φ.smoothTransitionFamily u x) =
      deriv Real.smoothTransition u •
        mfderiv (I.prod (𝓡∂ 1)) I Φ.cylinderMap (x, unitInterval.smoothTransition u)
          ((0 : E), (1 : TangentSpace (𝓡∂ 1) (unitInterval.smoothTransition u))) := by
  set σ : ℝ → unitInterval := unitInterval.smoothTransition
  have hσ : ContMDiff 𝓘(ℝ) (𝓡∂ 1) ∞ σ := unitInterval.contMDiff_smoothTransition le_rfl
  have hσu : MDifferentiableAt 𝓘(ℝ) (𝓡∂ 1) σ u := hσ.mdifferentiableAt (by simp)
  have hg : MDifferentiableAt (𝓡∂ 1) I (fun r ↦ Φ (r, x)) (σ u) :=
    (Φ.contMDiff.comp (contMDiff_id.prodMk contMDiff_const)).mdifferentiableAt (by simp)
  have hfun : (fun v ↦ (Φ.smoothTransitionFamily v).toEquiv x) =
      (fun r ↦ Φ (r, x)) ∘ σ :=
    funext fun v ↦ by
      rw [Diffeomorph.coe_toEquiv, smoothTransitionFamily_apply, Function.comp_apply]
  rw [← Diffeomorph.coe_toEquiv, eulerianField_apply_apply, Manifold.curveVelocity_apply, hfun]
  refine (mfderiv_comp_apply u hg hσu _).trans
    ((congrArg (mfderiv (𝓡∂ 1) I (fun r ↦ Φ (r, x)) (σ u))
      (unitInterval.mfderiv_smoothTransition_one u)).trans
    ((map_smul _ _ _).trans ?_))
  exact congrArg (deriv Real.smoothTransition u • ·)
    (Φ.mfderiv_cylinderMap_time (by simp) (x, σ u)).symm

/-- The Eulerian field at time `u` of the family `u ↦ φ_{s(u)}` over `ℝ` of a diffeotopy `Φ`,
`s = Real.smoothTransition`, is `s'(u)` times the velocity `X_{s(u)}` of `Φ`. -/
theorem eulerianField_smoothTransitionFamily [IsManifold I ∞ M] (u : ℝ) :
    eulerianField I (fun v ↦ (Φ.smoothTransitionFamily v).toEquiv) u =
      ⇑(deriv Real.smoothTransition u • Φ.smoothVelocity (unitInterval.smoothTransition u)) := by
  funext y
  obtain ⟨x, rfl⟩ : ∃ x, Φ.smoothTransitionFamily u x = y :=
    ⟨(Φ.smoothTransitionFamily u).symm y, (Φ.smoothTransitionFamily u).apply_symm_apply y⟩
  rw [eulerianField_smoothTransitionFamily_apply, ContMDiffSection.coe_smul, Pi.smul_apply,
    coe_smoothVelocity, smoothTransitionFamily_apply, velocity_apply]
  -- The sides differ only in the base point that names the fibre of the scalar multiplication,
  -- `Φ (s u, x)` on the left and `Φ.cylinderMap (x, s u)` on the right, equal by definition.
  rfl

/-- The Eulerian field of the family `u ↦ φ_{s(u)}` over `ℝ` of a diffeotopy `Φ`,
`s = Real.smoothTransition`, is jointly smooth in `(u, y)`. -/
theorem contMDiff_eulerianField_smoothTransitionFamily [IsManifold I ∞ M] :
    ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent ∞ (fun p : ℝ × M ↦ (⟨p.2,
      eulerianField I (fun v ↦ (Φ.smoothTransitionFamily v).toEquiv) p.1 p.2⟩ :
        TangentBundle I M)) :=
  contMDiff_eulerianField (by simp) Φ.contMDiff_smoothTransitionFamily
    Φ.contMDiff_smoothTransitionFamily_symm

/-- The family `u ↦ φ_{s(u)}` over `ℝ` of a diffeotopy `Φ`, `s = Real.smoothTransition`, is the
time-dependent flow of its Eulerian field: the flow from time `u` to time `u'` is
`φ_{s(u')} ∘ φ_{s(u)}⁻¹`. -/
theorem timeDependentFlowOf_eulerianField_smoothTransitionFamily
    [IsManifold I ∞ M] [T2Space M] [BoundarylessManifold I M] (u u' : ℝ) (y : M) :
    timeDependentFlowOf (eulerianField I (fun v ↦ (Φ.smoothTransitionFamily v).toEquiv)) u u' y =
      Φ.smoothTransitionFamily u' ((Φ.smoothTransitionFamily u).symm y) :=
  timeDependentFlowOf_eulerianField
    (fun z ↦ (Φ.contMDiff_smoothTransitionFamily.comp
      (contMDiff_id.prodMk contMDiff_const)).mdifferentiable (by simp))
    (Φ.contMDiff_eulerianField_smoothTransitionFamily.of_le (by simp)) u u' y

end SmoothTransition

end TauCeti.Diffeotopy

end
