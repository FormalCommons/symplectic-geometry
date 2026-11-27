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
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
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
transition map `φ ∘ c⁻¹`, which fixes `0`, by its derivative at `0`; over the rest of the source
of `φ`, which misses `p₀`, it is the point `(mk (φ x), φ x)` over `φ x`. So it takes that value at
each point `x ≠ p₀` of the source of `φ`. On the divisor it acts on lines by the differential of
`φ ∘ c⁻¹` at `0`, that is, through `directionEquiv c`, by the differential of `φ` at `p₀`.

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
  blowdown of `c.source ∩ φ.source`, the point `(mk (φ x), φ x)` over the blowdown `x` of the
  point over the rest of `φ.source`, and an arbitrary value off the preimage of `φ.source`.

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
* `SymplecticGeometry.Blowup.liftChart_inl`, `SymplecticGeometry.Blowup.liftChart_inr`,
  `SymplecticGeometry.Blowup.liftChart_ofDirection`: the values of the lifted chart on the two
  pieces of the blowup and on the divisor.
* `SymplecticGeometry.Blowup.blowdown_liftChart`: over the source of `φ`, the blowdown of the
  lifted chart is `φ ∘ blowdown c`.
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

/-- `fderivTransEquiv c φ` sends the image of a tangent vector `v` at the centre under the
differential of `c` to its image under the differential of `φ`. -/
@[simp]
theorem fderivTransEquiv_mfderiv (v : TangentSpace 𝓘(ℂ, Fin (n + 1) → ℂ) p₀) :
    fderivTransEquiv c φ (mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) c p₀ v) =
      mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) φ p₀ v := by
  have hmem := zero_mem_symm_trans_source c φ
  have h := congrArg (· v) (OpenPartialHomeomorph.mvfderiv_eq_fderiv_symm_trans_comp
    (I := 𝓘(ℂ, Fin (n + 1) → ℂ)) hmem
    ((mdifferentiable c).mdifferentiableAt (by simpa using c.mem_source))
    (mdifferentiableAt_iff_differentiableAt.1
      (((mdifferentiable c).symm.trans (mdifferentiable φ)).mdifferentiableAt hmem)))
  rw [c.symm_zero] at h
  simp only [mvfderiv_apply_eq_mfderiv_apply, ContinuousLinearMap.comp_apply] at h
  rw [coe_fderivTransEquiv]
  exact h.symm

/-- By the chain rule, `fderivTransEquiv c φ` is the inverse of the differential of `c` at the
centre followed by the differential of `φ` there. -/
theorem fderivTransEquiv_eq :
    fderivTransEquiv c φ = (mfderivCenterEquiv c).symm.trans (mfderivCenterEquiv φ) :=
  ContinuousLinearEquiv.ext <| funext fun w ↦
    (congrArg (fderivTransEquiv c φ) ((mfderivCenterEquiv c).apply_symm_apply w)).symm.trans
      (fderivTransEquiv_mfderiv c φ ((mfderivCenterEquiv c).symm w))

end BlowupChart

namespace Blowup

open BlowupModel

open GluedAlong (inl inr)

open scoped Classical in
/-- The chart of the blowup `Blowup c` lifted from a second holomorphic chart `φ` at the centre.
Over the part of `M` where both `c` and `φ` are defined, it is the lift `BlowupModel.liftMap` of
the transition map `φ ∘ c⁻¹`, by its derivative at `0`, applied to the point `Blowup.lift c z` of
the model. Over the rest of the source of `φ`, which does not contain `p₀`, it is the point
`(mk (φ x), φ x)` over `φ x`, where `x` is the blowdown of `z`. Off the preimage of the source
of `φ` its values are not meaningful. -/
def liftChart (z : Blowup c) : BlowupModel n :=
  if h : blowdown c z ∈ c.source ∩ φ.source then
    liftMap (c.symm.trans φ.toOpenPartialHomeomorph) (c.fderivTransEquiv φ) (lift c z)
  else if hφ : blowdown c z ∈ φ.source then
    ofNeZero (φ.apply_ne_zero hφ fun e ↦ h ⟨e.symm ▸ c.mem_source, hφ⟩)
  else Classical.arbitrary _

open scoped Classical in
theorem liftChart_def (z : Blowup c) :
    liftChart c φ z =
      if h : blowdown c z ∈ c.source ∩ φ.source then
        liftMap (c.symm.trans φ.toOpenPartialHomeomorph) (c.fderivTransEquiv φ) (lift c z)
      else if hφ : blowdown c z ∈ φ.source then
        ofNeZero (φ.apply_ne_zero hφ fun e ↦ h ⟨e.symm ▸ c.mem_source, hφ⟩)
      else Classical.arbitrary _ :=
  (rfl)

variable {c φ} in
/-- Over the part of `M` where both charts are defined, `liftChart c φ` is the lift of
`φ ∘ c⁻¹` applied to `Blowup.lift c z`. -/
theorem liftChart_of_mem {z : Blowup c} (hz : blowdown c z ∈ c.source ∩ φ.source) :
    liftChart c φ z =
      liftMap (c.symm.trans φ.toOpenPartialHomeomorph) (c.fderivTransEquiv φ) (lift c z) :=
  dite_eq_left hz

variable {c φ} in
/-- Over the part of the source of `φ` outside the source of `c`, `liftChart c φ z` is the point
`(mk (φ x), φ x)`, where `x` is the blowdown of `z`. -/
theorem liftChart_of_notMem {z : Blowup c} (hc : blowdown c z ∉ c.source)
    (hφ : blowdown c z ∈ φ.source) :
    liftChart c φ z = ofNeZero (φ.apply_ne_zero hφ fun e ↦ hc (e.symm ▸ c.mem_source)) := by
  rw [liftChart_def]
  split_ifs with h
  · exact absurd h.1 hc
  · rfl

/-- Off the centre, at a point `x` of the source of `φ`, the lifted chart takes the value
`(mk (φ x), φ x)`. -/
theorem liftChart_inl {x : puncturedOpens c} (hx : (x : M) ∈ φ.source) :
    liftChart c φ (inl (gluingHomeomorph c) x) =
      ofNeZero (φ.apply_ne_zero hx ((mem_puncturedOpens c).1 x.property)) := by
  by_cases hxc : (x : M) ∈ c.source
  · have hne : (c.symm.trans φ.toOpenPartialHomeomorph) (c x) ≠ 0 := by
      simpa [c.left_inv hxc] using φ.apply_ne_zero hx ((mem_puncturedOpens c).1 x.property)
    rw [liftChart_of_mem (by rw [blowdown_inl]; exact ⟨hxc, hx⟩), lift_inl c hxc,
      blowdownDiffeomorph_symm_apply]
    refine eq_of_blowdown_eq (by rwa [blowdown_liftMap, blowdown_ofNeZero]) ?_
    simp [c.left_inv hxc]
  · rw [liftChart_of_notMem (by rwa [blowdown_inl]) (by rwa [blowdown_inl])]
    simp only [blowdown_inl]

/-- On the part of the model over the target of `c` whose image in `M` lies in the source of
`φ`, the lifted chart is the lift of `φ ∘ c⁻¹` by its derivative at `0`. -/
theorem liftChart_inr {y : modelOpens c} (hy : c.symm (y : BlowupModel n).blowdown ∈ φ.source) :
    liftChart c φ (inr (gluingHomeomorph c) y) =
      liftMap (c.symm.trans φ.toOpenPartialHomeomorph) (c.fderivTransEquiv φ) y := by
  rw [liftChart_of_mem (by simpa using ⟨c.map_target ((mem_modelOpens c).1 y.property), hy⟩),
    lift_inr]

/-- On the exceptional divisor, the lifted chart sends the point over the line `ℓ` to the point
of the zero section over the image of `ℓ` under the derivative of `φ ∘ c⁻¹` at `0`. -/
@[simp]
theorem liftChart_ofDirection (ℓ : ℙ ℂ (Fin (n + 1) → ℂ)) :
    liftChart c φ (ofDirection c ℓ) =
      zeroSection ((c.fderivTransEquiv φ).mapProjectivization ℓ) := by
  rw [ofDirection_def, liftChart_inr c φ (by simpa using φ.mem_source),
    liftMap_zeroSection _ (c.symm_trans_apply_zero φ)]

/-- Over the source of `φ`, the lifted chart lies over `φ`: the blowdown of `liftChart c φ z` is
`φ` of the blowdown of `z`. -/
theorem blowdown_liftChart {z : Blowup c} (hz : blowdown c z ∈ φ.source) :
    (liftChart c φ z).blowdown = φ (blowdown c z) := by
  by_cases hzc : blowdown c z ∈ c.source
  · rw [liftChart_of_mem ⟨hzc, hz⟩, blowdown_liftMap]
    rcases GluedAlong.exists_inl_or_exists_inr _ z with ⟨x, rfl⟩ | ⟨y, rfl⟩
    · rw [blowdown_inl] at hzc ⊢
      rw [lift_inl c hzc, blowdownDiffeomorph_symm_apply, blowdown_ofNeZero,
        OpenPartialHomeomorph.coe_trans, Function.comp_apply, c.left_inv hzc]
    · rw [lift_inr, blowdown_inr, OpenPartialHomeomorph.coe_trans, Function.comp_apply]
  · rw [liftChart_of_notMem hzc hz, blowdown_ofNeZero]

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
