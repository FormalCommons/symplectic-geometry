/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Complex.Blowup.Basic
public import SymplecticGeometry.Geometry.Manifold.Complex.Blowup.Lift
public import TauCeti.LinearAlgebra.Projectivization.Basic
import SymplecticGeometry.Analysis.Calculus.FDeriv.Equiv
import SymplecticGeometry.Geometry.Manifold.MFDeriv.Atlas
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic

/-!
# The lines at the centre of a blowup, and the charts lifted from other charts

Let `c : BlowupChart M p₀` be a chart of the complex maximal atlas of `M`, modelled on
`E = ℂⁿ⁺¹`. The points of the exceptional divisor of `Blowup c` are the lines `ℓ : ℙ ℂ E`
(`Blowup.ofDirection c ℓ`). As a chart of the maximal atlas, `c` has an invertible differential
at the centre `p₀`, with inverse the differential of `c⁻¹` at `c p₀ = 0`; so the differential
identifies the lines of the tangent space at `p₀` with the points of the divisor. This file
defines that bijection.

A second chart `φ : BlowupChart M p₀` of the same atlas gives a map `Blowup c → BlowupModel n`:
over the part of `M` where both charts are defined, it is the lift to the model blowup of the
transition map `φ ∘ c⁻¹`, which fixes `0`, by its derivative at `0`. It is `(mk (φ x), φ x)` at a
point `x ≠ p₀`, and on the divisor it acts on lines by the differential of `φ ∘ c⁻¹` at `0`, that
is, through `directionEquiv c`, by the differential of `φ` at `p₀`.

## Main definitions

* `SymplecticGeometry.BlowupChart.mfderivCenterEquiv c`: the differential of `c` at `p₀`, as a
  continuous linear equivalence `T_{p₀}M ≃L[ℂ] E` whose inverse is the differential of `c⁻¹`
  at `0`. It is Mathlib's `OpenPartialHomeomorph.MDifferentiable.mfderiv` of `c` at `p₀`, typed
  onto `E`.
* `SymplecticGeometry.Blowup.directionEquiv c`: the bijection
  `ℙ ℂ (TangentSpace 𝓘(ℂ, E) p₀) ≃ ℙ ℂ E` that it induces, through Tau Ceti's
  `LinearEquiv.mapProjectivization`.
* `SymplecticGeometry.BlowupChart.fderivTransEquiv c φ`: the derivative of `φ ∘ c⁻¹` at `0`, as
  a continuous linear equivalence of `E` (the library's `OpenPartialHomeomorph.fderivEquiv`).
* `SymplecticGeometry.Blowup.liftChart c φ`: the chart of `Blowup c` lifted from `φ`, defined by
  cases: `BlowupModel.liftMap` of `φ ∘ c⁻¹` after `Blowup.lift c` over the preimage under the
  blowdown of `c.source ∩ φ.source`, and an arbitrary value elsewhere.

## Main results

* `SymplecticGeometry.BlowupChart.coe_mfderivCenterEquiv`,
  `SymplecticGeometry.BlowupChart.coe_mfderivCenterEquiv_symm`: the equivalence is the
  differential of `c` at `p₀`, and its inverse is the differential of `c⁻¹` at `0`.
* `SymplecticGeometry.Blowup.directionEquiv_apply`: `directionEquiv c` is `Projectivization.map`
  of the differential of `c` at `p₀`.
* `SymplecticGeometry.Blowup.directionEquiv_mk`,
  `SymplecticGeometry.Blowup.directionEquiv_symm_mk`: it sends the line of `v` to the line of
  `dc(p₀) v`, and its inverse sends the line of `w` to the line of `d(c⁻¹)(0) w`.
* `SymplecticGeometry.BlowupChart.fderivTransEquiv_eq`: by the chain rule, the derivative of
  `φ ∘ c⁻¹` at `0` is `dφ(p₀) ∘ dc(p₀)⁻¹`.
* `SymplecticGeometry.Blowup.liftChart_inl`, `SymplecticGeometry.Blowup.liftChart_ofDirection`,
  `SymplecticGeometry.Blowup.blowdown_liftChart`: the values of the lifted chart off the divisor
  and on it, and its blowdown `φ ∘ blowdown c`.
* `SymplecticGeometry.Blowup.liftChart_ofDirection_directionEquiv_mk`: the lifted chart sends the
  point of the divisor over the line of `v ∈ T_{p₀}M` to the point `([dφ(p₀) v], 0)`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §7.1, Lemma 7.1.3.
* [P. Griffiths, J. Harris, *Principles of Algebraic Geometry*][GriffithsHarris1978], Chapter 1,
  §4.
-/

public section

open Projectivization
open scoped LinearAlgebra.Projectivization Manifold ContDiff

noncomputable section

namespace SymplecticGeometry

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Fin (n + 1) → ℂ) M]
  {p₀ : M} (c : BlowupChart (n := n) M p₀)
  [hc : Fact (c.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin (n + 1) → ℂ) ω M)]

namespace BlowupChart

/-- A chart of the complex maximal atlas is differentiable on its source, and its inverse on its
target. -/
theorem mdifferentiable :
    c.toOpenPartialHomeomorph.MDifferentiable 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) :=
  TauCeti.mdifferentiable_of_mem_maximalAtlas
    (IsManifold.maximalAtlas_subset_of_le (by simp) hc.out)

/-- The differential of a holomorphic chart `c` at the centre, as a continuous linear equivalence
from the tangent space at `p₀` to `ℂⁿ⁺¹`. Its inverse is the differential of `c⁻¹` at `0`. -/
def mfderivCenterEquiv : TangentSpace 𝓘(ℂ, Fin (n + 1) → ℂ) p₀ ≃L[ℂ] (Fin (n + 1) → ℂ) :=
  (mdifferentiable c).mfderiv c.mem_source

theorem mfderivCenterEquiv_def :
    mfderivCenterEquiv c = (mdifferentiable c).mfderiv c.mem_source :=
  (rfl)

/-- `mfderivCenterEquiv c` is the differential of `c` at the centre. -/
@[simp]
theorem coe_mfderivCenterEquiv :
    ⇑(mfderivCenterEquiv c) = mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) c p₀ :=
  (rfl)

/-- The inverse of `mfderivCenterEquiv c` is the differential of `c⁻¹` at `0`. -/
@[simp]
theorem coe_mfderivCenterEquiv_symm :
    ⇑(mfderivCenterEquiv c).symm =
      mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) c.toOpenPartialHomeomorph.symm 0 := by
  have h := (mdifferentiable c).coe_mfderiv_symm c.mem_source
  rw [c.map_center] at h
  exact h

end BlowupChart

namespace Blowup

/-- The bijection between the lines of the tangent space of `M` at the centre `p₀` and the
lines of `ℂⁿ⁺¹`, that is, the points of the exceptional divisor of `Blowup c`, induced by the
differential of the holomorphic chart `c` at `p₀`. -/
def directionEquiv :
    ℙ ℂ (TangentSpace 𝓘(ℂ, Fin (n + 1) → ℂ) p₀) ≃ ℙ ℂ (Fin (n + 1) → ℂ) :=
  (c.mfderivCenterEquiv).toLinearEquiv.mapProjectivization

theorem directionEquiv_def :
    directionEquiv c = c.mfderivCenterEquiv.toLinearEquiv.mapProjectivization :=
  (rfl)

/-- `directionEquiv c` is `Projectivization.map` of the differential of `c` at the centre. -/
theorem directionEquiv_apply (ℓ : ℙ ℂ (TangentSpace 𝓘(ℂ, Fin (n + 1) → ℂ) p₀)) :
    directionEquiv c ℓ =
      map (c.mfderivCenterEquiv : TangentSpace 𝓘(ℂ, Fin (n + 1) → ℂ) p₀ →ₗ[ℂ] Fin (n + 1) → ℂ)
        c.mfderivCenterEquiv.injective ℓ :=
  LinearEquiv.mapProjectivization_apply _ ℓ

/-- `directionEquiv c` sends the line of a tangent vector `v` at the centre to the line of its
image under the differential of `c`. -/
@[simp]
theorem directionEquiv_mk (v : TangentSpace 𝓘(ℂ, Fin (n + 1) → ℂ) p₀) (hv : v ≠ 0) :
    directionEquiv c (mk ℂ v hv) =
      mk ℂ (V := Fin (n + 1) → ℂ) (mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) c p₀ v)
        (by simpa using (c.mfderivCenterEquiv.injective.ne_iff' (map_zero _)).2 hv) := by
  simp only [directionEquiv_def, LinearEquiv.mapProjectivization_mk,
    ContinuousLinearEquiv.coe_toLinearEquiv, BlowupChart.coe_mfderivCenterEquiv]

/-- The inverse of `directionEquiv c` sends the line of `w : ℂⁿ⁺¹` to the line of its image
under the differential of `c⁻¹` at `0 = c p₀`. -/
@[simp]
theorem directionEquiv_symm_mk (w : Fin (n + 1) → ℂ) (hw : w ≠ 0) :
    (directionEquiv c).symm (mk ℂ w hw) =
      mk ℂ (V := TangentSpace 𝓘(ℂ, Fin (n + 1) → ℂ) p₀)
        (mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) c.toOpenPartialHomeomorph.symm 0 w)
        (by simpa using (c.mfderivCenterEquiv.symm.injective.ne_iff' (map_zero _)).2 hw) := by
  simp only [directionEquiv_def, LinearEquiv.mapProjectivization_symm,
    LinearEquiv.mapProjectivization_mk, ContinuousLinearEquiv.coe_symm_toLinearEquiv,
    BlowupChart.coe_mfderivCenterEquiv_symm]

end Blowup

/-! ### The chart of the blowup lifted from a second chart at the centre -/

variable (φ : BlowupChart (n := n) M p₀)
  [hφ : Fact (φ.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin (n + 1) → ℂ) ω M)]

namespace BlowupChart

omit hc hφ in
/-- The origin lies in the source of the transition map `φ ∘ c⁻¹`. -/
theorem zero_mem_symm_trans_source :
    (0 : Fin (n + 1) → ℂ) ∈ (c.symm.trans φ.toOpenPartialHomeomorph).source := by
  rw [OpenPartialHomeomorph.trans_source]
  exact ⟨c.zero_mem_target, by simpa using φ.mem_source⟩

omit hc hφ in
/-- The transition map `φ ∘ c⁻¹` fixes the origin. -/
@[simp]
theorem symm_trans_apply_zero : (c.symm.trans φ.toOpenPartialHomeomorph) 0 = 0 := by
  simp [φ.map_center]

/-- The derivative at `0` of the transition map `φ ∘ c⁻¹` between two holomorphic charts at the
centre, as a continuous linear equivalence of `ℂⁿ⁺¹`, whose inverse is the derivative of
`c ∘ φ⁻¹` at `0`. -/
def fderivTransEquiv : (Fin (n + 1) → ℂ) ≃L[ℂ] Fin (n + 1) → ℂ :=
  have hd := (mdifferentiable c).symm.trans (mdifferentiable φ)
  (c.symm.trans φ.toOpenPartialHomeomorph).fderivEquiv (zero_mem_symm_trans_source c φ)
    (mdifferentiableAt_iff_differentiableAt.1
      (hd.mdifferentiableAt (zero_mem_symm_trans_source c φ)))
    (mdifferentiableAt_iff_differentiableAt.1
      (hd.symm.mdifferentiableAt
        ((c.symm.trans φ.toOpenPartialHomeomorph).map_source (zero_mem_symm_trans_source c φ))))

/-- `fderivTransEquiv c φ` is the derivative of `φ ∘ c⁻¹` at `0`. -/
@[simp]
theorem coe_fderivTransEquiv :
    ⇑(fderivTransEquiv c φ) = fderiv ℂ (c.symm.trans φ.toOpenPartialHomeomorph) 0 :=
  OpenPartialHomeomorph.coe_fderivEquiv _ _ _ _

/-- The inverse of `fderivTransEquiv c φ` is the derivative of `c ∘ φ⁻¹` at `0`. -/
@[simp]
theorem coe_fderivTransEquiv_symm :
    ⇑(fderivTransEquiv c φ).symm = fderiv ℂ (c.symm.trans φ.toOpenPartialHomeomorph).symm 0 :=
  (OpenPartialHomeomorph.coe_fderivEquiv_symm _ _ _ _).trans (by rw [symm_trans_apply_zero])

/-- By the chain rule, `fderivTransEquiv c φ` is the inverse of the differential of `c` at the
centre followed by the differential of `φ` there. -/
theorem fderivTransEquiv_eq :
    fderivTransEquiv c φ = (mfderivCenterEquiv c).symm.trans (mfderivCenterEquiv φ) := by
  refine ContinuousLinearEquiv.ext <| funext fun w ↦ ?_
  have hmem : c.symm 0 ∈ φ.source := by simpa using φ.mem_source
  have hc := (mdifferentiable c).symm.mdifferentiableAt c.zero_mem_target
  have hφ := (mdifferentiable φ).mdifferentiableAt hmem
  have h := congrArg (· w) (mfderiv_comp (0 : Fin (n + 1) → ℂ) hφ hc)
  rw [mfderiv_eq_fderiv, c.symm_zero] at h
  rw [coe_fderivTransEquiv, OpenPartialHomeomorph.coe_trans, ContinuousLinearEquiv.trans_apply,
    coe_mfderivCenterEquiv_symm, coe_mfderivCenterEquiv]
  -- `h` has the derivative of `φ ∘ c⁻¹` between the identifications `fromTangentSpace` of the
  -- tangent spaces of `ℂⁿ⁺¹` with `ℂⁿ⁺¹`, which are the identity.
  exact h

/-- `fderivTransEquiv c φ` sends the image of a tangent vector `v` at the centre under the
differential of `c` to its image under the differential of `φ`. -/
@[simp]
theorem fderivTransEquiv_mfderiv (v : TangentSpace 𝓘(ℂ, Fin (n + 1) → ℂ) p₀) :
    fderivTransEquiv c φ (mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) c p₀ v) =
      mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) φ p₀ v := by
  rw [fderivTransEquiv_eq]
  -- The differentials of `c` and `φ` are the maps of `mfderivCenterEquiv` (`(rfl)`), but `rw`
  -- cannot use `coe_mfderivCenterEquiv` here: its tangent spaces at `c p₀` and at `0` differ.
  exact congrArg (mfderivCenterEquiv φ) ((mfderivCenterEquiv c).symm_apply_apply v)

end BlowupChart

namespace Blowup

open BlowupModel

open GluedAlong (inl inr)

open scoped Classical in
/-- The chart of the blowup `Blowup c` lifted from a second holomorphic chart `φ` at the centre.
Over the part of `M` where both `c` and `φ` are defined, it is the lift `BlowupModel.liftMap` of
the transition map `φ ∘ c⁻¹`, by its derivative at `0`, applied to the point `Blowup.lift c z` of
the model. Elsewhere its values are not meaningful. -/
def liftChart (z : Blowup c) : BlowupModel n :=
  if blowdown c z ∈ c.source ∩ φ.source then
    liftMap (c.symm.trans φ.toOpenPartialHomeomorph) (c.fderivTransEquiv φ) (lift c z)
  else Classical.arbitrary _

open scoped Classical in
theorem liftChart_def (z : Blowup c) :
    liftChart c φ z =
      if blowdown c z ∈ c.source ∩ φ.source then
        liftMap (c.symm.trans φ.toOpenPartialHomeomorph) (c.fderivTransEquiv φ) (lift c z)
      else Classical.arbitrary _ :=
  (rfl)

variable {c φ} in
/-- Over the part of `M` where both charts are defined, `liftChart c φ` is the lift of
`φ ∘ c⁻¹` applied to `Blowup.lift c z`. -/
theorem liftChart_of_mem {z : Blowup c} (hz : blowdown c z ∈ c.source ∩ φ.source) :
    liftChart c φ z =
      liftMap (c.symm.trans φ.toOpenPartialHomeomorph) (c.fderivTransEquiv φ) (lift c z) :=
  ite_eq_left hz

/-- Off the centre, at a point `x` where both charts are defined, the lifted chart takes the
value `(mk (φ x), φ x)`. -/
theorem liftChart_inl {x : puncturedOpens c} (hx : (x : M) ∈ c.source ∩ φ.source) :
    liftChart c φ (inl (gluingHomeomorph c) x) =
      ofNeZero (φ.apply_ne_zero hx.2 ((mem_puncturedOpens c).1 x.property)) := by
  have hne : (c.symm.trans φ.toOpenPartialHomeomorph) (c x) ≠ 0 := by
    simpa [c.left_inv hx.1] using φ.apply_ne_zero hx.2 ((mem_puncturedOpens c).1 x.property)
  rw [liftChart_of_mem (by rwa [blowdown_inl]), lift_inl c hx.1, blowdownDiffeomorph_symm_apply]
  refine eq_of_blowdown_eq (by rwa [blowdown_liftMap, blowdown_ofNeZero]) ?_
  simp [c.left_inv hx.1]

/-- On the exceptional divisor, the lifted chart sends the point over the line `ℓ` to the point
of the zero section over the image of `ℓ` under the derivative of `φ ∘ c⁻¹` at `0`. -/
@[simp]
theorem liftChart_ofDirection (ℓ : ℙ ℂ (Fin (n + 1) → ℂ)) :
    liftChart c φ (ofDirection c ℓ) =
      zeroSection ((c.fderivTransEquiv φ).mapProjectivization ℓ) := by
  rw [liftChart_of_mem (by simpa using ⟨c.mem_source, φ.mem_source⟩), ofDirection_def, lift_inr,
    liftMap_zeroSection _ (c.symm_trans_apply_zero φ)]

/-- Over the part of `M` where both charts are defined, the lifted chart lies over `φ`: the
blowdown of `liftChart c φ z` is `φ` of the blowdown of `z`. -/
theorem blowdown_liftChart {z : Blowup c} (hz : blowdown c z ∈ c.source ∩ φ.source) :
    (liftChart c φ z).blowdown = φ (blowdown c z) := by
  rw [liftChart_of_mem hz, blowdown_liftMap]
  rcases GluedAlong.exists_inl_or_exists_inr _ z with ⟨x, rfl⟩ | ⟨y, rfl⟩
  · rw [blowdown_inl] at hz ⊢
    rw [lift_inl c hz.1, blowdownDiffeomorph_symm_apply, blowdown_ofNeZero,
      OpenPartialHomeomorph.coe_trans, Function.comp_apply, c.left_inv hz.1]
  · rw [lift_inr, blowdown_inr, OpenPartialHomeomorph.coe_trans, Function.comp_apply]

/-- Through `directionEquiv c`, the lifted chart sends the point of the exceptional divisor over
the line of a tangent vector `v` at the centre to the point of the zero section over the line of
the image of `v` under the differential of `φ`. -/
theorem liftChart_ofDirection_directionEquiv_mk (v : TangentSpace 𝓘(ℂ, Fin (n + 1) → ℂ) p₀)
    (hv : v ≠ 0) :
    liftChart c φ (ofDirection c (directionEquiv c (mk ℂ v hv))) =
      zeroSection (mk ℂ (V := Fin (n + 1) → ℂ)
        (mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) φ p₀ v)
        (by simpa using (φ.mfderivCenterEquiv.injective.ne_iff' (map_zero _)).2 hv)) := by
  rw [liftChart_ofDirection, directionEquiv_def, LinearEquiv.mapProjectivization_mk,
    ContinuousLinearEquiv.mapProjectivization_mk]
  congr 2
  exact BlowupChart.fderivTransEquiv_mfderiv c φ v

end Blowup

end SymplecticGeometry

end
