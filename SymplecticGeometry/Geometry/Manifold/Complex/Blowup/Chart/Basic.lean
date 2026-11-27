/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Complex.Blowup.Basic
public import SymplecticGeometry.Geometry.Manifold.Complex.Blowup.Lift
public import TauCeti.LinearAlgebra.Projectivization.Basic
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective
import SymplecticGeometry.Analysis.Calculus.FDeriv.Equiv
import SymplecticGeometry.Geometry.Manifold.MFDeriv.Atlas
import SymplecticGeometry.Geometry.Manifold.ContMDiff.Analytic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset

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

When `M` is a complex manifold, the lifted chart is a holomorphic chart of `Blowup c` with values
in the model. Near a point of the divisor it is, read through `GluedAlong.inr`, the partial
biholomorphism `BlowupModel.liftPartialDiffeomorph` of the transition map; off the divisor,
followed by the blowdown of the model, it is `φ ∘ blowdown c`, and both blowdowns are local
biholomorphisms there. Over the source of `φ` it is injective, since `φ` is and both blowdowns
are injective off the divisor, while on the divisor it acts by a bijection of lines. So it is a
partial biholomorphism onto the part of the model over the target of `φ`, and followed by a
chart of the model it is a chart of the maximal atlas of `Blowup c` (Tau Ceti's
`PartialDiffeomorph.trans_mem_maximalAtlas`).

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
* `SymplecticGeometry.Blowup.liftChartPartialDiffeomorph c φ`: the lifted chart as a partial
  biholomorphism from `blowdown c ⁻¹' φ.source` onto `BlowupModel.blowdown ⁻¹' φ.target`.

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
* `SymplecticGeometry.Blowup.isLocalDiffeomorphOn_liftChart`,
  `SymplecticGeometry.Blowup.injOn_liftChart`,
  `SymplecticGeometry.Blowup.liftChart_image_preimage_source`: over the source of `φ`, the lifted
  chart is a local biholomorphism and injective, with image the part of the model over the target
  of `φ`.
* `SymplecticGeometry.Blowup.liftChart_mem_maximalAtlas`: the lifted chart followed by a chart
  `blowupModelChart i` of the model is a chart of the complex maximal atlas of `Blowup c`.

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

/-- The inverse of the derivative at `0` of `φ ∘ c⁻¹` is the derivative at `0` of `c ∘ φ⁻¹`. -/
theorem fderivTransEquiv_symm : (fderivTransEquiv c φ).symm = fderivTransEquiv φ c := by
  ext v
  simp [fderivTransEquiv_eq]

/-- The derivative at `0` of `c ∘ c⁻¹` is the identity. -/
@[simp]
theorem fderivTransEquiv_self : fderivTransEquiv c c = ContinuousLinearEquiv.refl ℂ _ := by
  ext v
  simp [fderivTransEquiv_eq]

/-- The chain rule at the centre: the derivative at `0` of `φ ∘ c⁻¹` followed by that of
`ψ ∘ φ⁻¹` is the derivative at `0` of `ψ ∘ c⁻¹`. -/
@[simp]
theorem fderivTransEquiv_trans (ψ : BlowupChart (n := n) M p₀)
    [Fact (ψ.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin (n + 1) → ℂ) ω M)] :
    (fderivTransEquiv c φ).trans (fderivTransEquiv φ ψ) = fderivTransEquiv c ψ := by
  rw [fderivTransEquiv_eq, fderivTransEquiv_eq, fderivTransEquiv_eq]
  exact ContinuousLinearEquiv.ext <| funext fun v ↦ by
    simp only [ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.symm_apply_apply]

/-- The derivative at `0` of `φ ∘ c⁻¹` sends the line of `ℂⁿ⁺¹` that `directionEquiv c` gives a
line `ℓ` of the tangent space at the centre to the line that `directionEquiv φ` gives `ℓ`. -/
@[simp]
theorem mapProjectivization_fderivTransEquiv_directionEquiv
    (ℓ : ℙ ℂ (TangentSpace 𝓘(ℂ, Fin (n + 1) → ℂ) p₀)) :
    (fderivTransEquiv c φ).mapProjectivization (Blowup.directionEquiv c ℓ) =
      Blowup.directionEquiv φ ℓ := by
  induction ℓ using Projectivization.ind with | h v hv =>
  rw [Blowup.directionEquiv_def, Blowup.directionEquiv_def, LinearEquiv.mapProjectivization_mk,
    LinearEquiv.mapProjectivization_mk, ContinuousLinearEquiv.mapProjectivization_mk]
  congr 1
  simpa using fderivTransEquiv_mfderiv c φ v

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

/-- Over the source of `φ`, the lifted chart lies over `φ`: the blowdown of `liftChart c φ z` is
`φ` of the blowdown of `z`. -/
theorem blowdown_liftChart {z : Blowup c} (hz : blowdown c z ∈ φ.source) :
    (liftChart c φ z).blowdown = φ (blowdown c z) := by
  by_cases hzc : blowdown c z ∈ c.source
  · rw [liftChart_of_mem ⟨hzc, hz⟩, blowdown_liftMap, blowdown_lift c hzc,
      OpenPartialHomeomorph.coe_trans, Function.comp_apply, c.left_inv hzc]
  · rw [liftChart_of_notMem hzc hz, blowdown_ofNeZero]

/-- Off the centre, at a point `x` of the source of `φ`, the lifted chart takes the value
`(mk (φ x), φ x)`. -/
theorem liftChart_inl {x : puncturedOpens c} (hx : (x : M) ∈ φ.source) :
    liftChart c φ (inl (gluingHomeomorph c) x) =
      ofNeZero (φ.apply_ne_zero hx ((mem_puncturedOpens c).1 x.property)) := by
  have h := blowdown_liftChart c φ (z := inl (gluingHomeomorph c) x) (by rwa [blowdown_inl])
  rw [blowdown_inl] at h
  refine eq_of_blowdown_eq ?_ (by rw [h, blowdown_ofNeZero])
  rw [h]
  exact φ.apply_ne_zero hx ((mem_puncturedOpens c).1 x.property)

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

/-- Over the source of `φ`, the lifted chart lies over the target of `φ`, so in the second piece of
the blowup `Blowup φ`. -/
theorem liftChart_mem_modelOpens {z : Blowup c} (hz : blowdown c z ∈ φ.source) :
    liftChart c φ z ∈ modelOpens φ := by
  rw [mem_modelOpens, blowdown_liftChart c φ hz]
  exact φ.map_source hz

/-- Through `directionEquiv c`, the lifted chart sends the point of the exceptional divisor over
the line of a tangent vector `v` at the centre to the point of the zero section over the line of
the image of `v` under the differential of `φ`. -/
theorem liftChart_ofDirection_directionEquiv_mk (v : TangentSpace 𝓘(ℂ, Fin (n + 1) → ℂ) p₀)
    (hv : v ≠ 0) :
    liftChart c φ (ofDirection c (directionEquiv c (mk ℂ v hv))) =
      zeroSection (mk ℂ (V := Fin (n + 1) → ℂ)
        (mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) φ p₀ v)
        (by simpa using (φ.mfderivCenterEquiv.injective.ne_iff' (map_zero _)).2 hv)) := by
  rw [liftChart_ofDirection, BlowupChart.mapProjectivization_fderivTransEquiv_directionEquiv,
    directionEquiv_mk]

end Blowup

/-! ### The lifted chart is a holomorphic chart -/

namespace Blowup

open BlowupModel

open GluedAlong (inl inr)

variable [IsManifold 𝓘(ℂ, Fin (n + 1) → ℂ) ω M]

/-- On the exceptional divisor, the lifted chart is a local biholomorphism. -/
private theorem isLocalDiffeomorphAt_liftChart_of_mem {z : Blowup c}
    (hz : z ∈ exceptionalDivisor c) :
    IsLocalDiffeomorphAt 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) ω (liftChart c φ) z := by
  obtain ⟨y, hy0, rfl⟩ := (mem_exceptionalDivisor_iff c).1 hz
  set ψ := c.symm.trans φ.toOpenPartialHomeomorph
  have hψ : AnalyticOnNhd ℂ ψ ψ.source :=
    OpenPartialHomeomorph.analyticOnNhd_symm_trans_of_mem_maximalAtlas hc.out hφ.out
  have hψsymm : AnalyticOnNhd ℂ ψ.symm ψ.target := by
    rw [← OpenPartialHomeomorph.symm_source, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm]
    exact OpenPartialHomeomorph.analyticOnNhd_symm_trans_of_mem_maximalAtlas hφ.out hc.out
  -- The lift of `ψ = φ ∘ c⁻¹`, as a partial biholomorphism of the model.
  set Φ := liftPartialDiffeomorph (c.zero_mem_symm_trans_source φ) (c.symm_trans_apply_zero φ)
    hψ hψsymm
  have hL : c.fderivTransEquiv φ = ψ.fderivEquiv (c.zero_mem_symm_trans_source φ)
      (hψ 0 (c.zero_mem_symm_trans_source φ)).differentiableAt
      (hψsymm _ (ψ.map_source (c.zero_mem_symm_trans_source φ))).differentiableAt :=
    ContinuousLinearEquiv.ext (by
      rw [BlowupChart.coe_fderivTransEquiv, OpenPartialHomeomorph.coe_fderivEquiv])
  have hsrc : ∀ y' : modelOpens c, (y' : BlowupModel n) ∈ Φ.source →
      c.symm (y' : BlowupModel n).blowdown ∈ φ.source := fun y' hy' ↦ by
    simp only [Φ, liftPartialDiffeomorph_source, Set.mem_preimage,
      OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source] at hy'
    exact hy'.2
  have hy : (y : BlowupModel n) ∈ Φ.source := by
    simpa [Φ, hy0] using c.zero_mem_symm_trans_source φ
  have h : IsLocalDiffeomorphAt 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) ω
      (liftChart c φ ∘ inr (gluingHomeomorph c)) y := by
    refine ((TauCeti.isLocalDiffeomorph_subtype_val y).comp
      (hg := Φ.isLocalDiffeomorphAt _ _ _ hy)).congr_of_eventuallyEq ?_
    filter_upwards [(Φ.open_source.preimage continuous_subtypeVal).mem_nhds hy] with y' hy'
    rw [Function.comp_apply, liftChart_inr c φ (hsrc y' hy'), Function.comp_apply,
      liftPartialDiffeomorph_apply, hL]
  exact (isLocalDiffeomorph_inr c y).comp_iff_right.1 h

/-- Off the exceptional divisor, over the source of `φ`, the lifted chart is a local
biholomorphism: followed by the blowdown of the model, which is one there, it is
`φ ∘ blowdown c`. -/
private theorem isLocalDiffeomorphAt_liftChart_of_notMem {z : Blowup c}
    (hz : z ∉ exceptionalDivisor c) (hzφ : blowdown c z ∈ φ.source) :
    IsLocalDiffeomorphAt 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) ω (liftChart c φ) z := by
  have hU : blowdown c ⁻¹' φ.source ∩ (exceptionalDivisor c)ᶜ ∈ nhds z :=
    ((φ.open_source.preimage (blowdown c).continuous).inter
      (isClosed_exceptionalDivisor c).isOpen_compl).mem_nhds ⟨hzφ, hz⟩
  have hne : ∀ w ∈ blowdown c ⁻¹' φ.source ∩ (exceptionalDivisor c)ᶜ,
      φ (blowdown c w) ≠ 0 := fun w hw ↦
    φ.apply_ne_zero hw.1 fun h ↦ hw.2 ((blowdown_eq_center_iff c).1 h)
  have hF : ContMDiffAt 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) 1
      (fun w ↦ φ (blowdown c w)) z :=
    ((contMDiffAt_of_mem_maximalAtlas hφ.out hzφ).comp z
      ((contMDiff_blowdown c) z)).of_le (by simp)
  have hcont : ContinuousAt (liftChart c φ) z := by
    refine ((contMDiffAt_iff_contMDiffAt_pr_comp_and_blowdown_comp le_rfl).2
      ⟨contMDiffAt_of_eventually_eq_mk hF ?_, hF.congr_of_eventuallyEq ?_⟩).continuousAt
    · filter_upwards [hU] with w hw
      refine ⟨hne w hw, ?_⟩
      rw [← mk_blowdown (by rw [blowdown_liftChart c φ hw.1]; exact hne w hw)]
      congr 1
      exact blowdown_liftChart c φ hw.1
    · filter_upwards [hU] with w hw
      exact blowdown_liftChart c φ hw.1
  have h : IsLocalDiffeomorphAt 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) ω
      (BlowupModel.blowdown ∘ liftChart c φ) z := by
    refine ((isLocalDiffeomorphAt_blowdown c hz).comp
      (hg := φ.isLocalDiffeomorphAt_of_mem_maximalAtlas hφ.out hzφ)).congr_of_eventuallyEq ?_
    filter_upwards [hU] with w hw
    exact blowdown_liftChart c φ hw.1
  exact h.of_comp_left (BlowupModel.isLocalDiffeomorphAt_blowdown
    (by rw [blowdown_liftChart c φ hzφ]; exact hne z ⟨hzφ, hz⟩)) hcont

/-- The lifted chart is a local biholomorphism over the source of `φ`. -/
theorem isLocalDiffeomorphOn_liftChart :
    IsLocalDiffeomorphOn 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) ω (liftChart c φ)
      (blowdown c ⁻¹' φ.source) := fun z ↦ by
  by_cases hz : (z : Blowup c) ∈ exceptionalDivisor c
  · exact isLocalDiffeomorphAt_liftChart_of_mem c φ hz
  · exact isLocalDiffeomorphAt_liftChart_of_notMem c φ hz z.property

omit [IsManifold 𝓘(ℂ, Fin (n + 1) → ℂ) ω M] in
/-- The lifted chart is injective over the source of `φ`. -/
theorem injOn_liftChart : Set.InjOn (liftChart c φ) (blowdown c ⁻¹' φ.source) := by
  intro z hz z' hz' h
  have hb : blowdown c z = blowdown c z' :=
    φ.injOn hz hz' (by rw [← blowdown_liftChart c φ hz, ← blowdown_liftChart c φ hz', h])
  by_cases hzd : z ∈ exceptionalDivisor c
  · have hzd' : z' ∈ exceptionalDivisor c := by
      rwa [← blowdown_eq_center_iff, ← hb, blowdown_eq_center_iff]
    rw [exceptionalDivisor_def] at hzd hzd'
    obtain ⟨ℓ, rfl⟩ := hzd
    obtain ⟨ℓ', rfl⟩ := hzd'
    rw [liftChart_ofDirection, liftChart_ofDirection] at h
    rw [(c.fderivTransEquiv φ).mapProjectivization.injective (zeroSection_injective h)]
  · have hzd' : z' ∉ exceptionalDivisor c := by
      rwa [← blowdown_eq_center_iff, ← hb, blowdown_eq_center_iff]
    exact injOn_blowdown c hzd hzd' hb

omit [IsManifold 𝓘(ℂ, Fin (n + 1) → ℂ) ω M] in
/-- The lifted chart maps the preimage of the source of `φ` onto the part of the model over the
target of `φ`. -/
theorem liftChart_image_preimage_source :
    liftChart c φ '' (blowdown c ⁻¹' φ.source) = BlowupModel.blowdown ⁻¹' φ.target := by
  refine Set.Subset.antisymm ?_ fun p hp ↦ ?_
  · rintro _ ⟨z, hz, rfl⟩
    exact (mem_modelOpens φ).1 (liftChart_mem_modelOpens c φ hz)
  have hx : φ.symm p.blowdown ∈ φ.source := φ.map_target hp
  by_cases hp0 : p.blowdown = 0
  · refine ⟨ofDirection c ((c.fderivTransEquiv φ).symm.mapProjectivization p.pr), ?_, ?_⟩
    · rw [Set.mem_preimage, blowdown_ofDirection]
      exact φ.mem_source
    · rw [liftChart_ofDirection, ContinuousLinearEquiv.mapProjectivization_apply_symm_apply,
        ← eq_zeroSection_pr hp0]
  · have hne : φ.symm p.blowdown ≠ p₀ := fun h ↦
      hp0 (by rw [← φ.right_inv hp, h, φ.map_center])
    refine ⟨inl (gluingHomeomorph c) ⟨φ.symm p.blowdown, (mem_puncturedOpens c).2 hne⟩,
      by simpa using hx, ?_⟩
    rw [liftChart_inl c φ hx]
    exact eq_of_blowdown_eq (by simpa [φ.right_inv hp] using hp0) (by simp [φ.right_inv hp])

/-- **The lifted chart as a partial biholomorphism.** The chart `liftChart c φ` of the blowup,
lifted from a second holomorphic chart `φ` at the centre, as a biholomorphism from the preimage
`blowdown c ⁻¹' φ.source` onto the open set `BlowupModel.blowdown ⁻¹' φ.target` of the model. -/
def liftChartPartialDiffeomorph :
    PartialDiffeomorph 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) (Blowup c) (BlowupModel n) ω :=
  (isLocalDiffeomorphOn_liftChart c φ).partialDiffeomorphOfInjOn
    (φ.open_source.preimage (blowdown c).continuous) (injOn_liftChart c φ)

theorem liftChartPartialDiffeomorph_def :
    liftChartPartialDiffeomorph c φ =
      IsLocalDiffeomorphOn.partialDiffeomorphOfInjOn (isLocalDiffeomorphOn_liftChart c φ)
        (φ.open_source.preimage (blowdown c).continuous) (injOn_liftChart c φ) :=
  (rfl)

@[simp]
theorem coe_liftChartPartialDiffeomorph : ⇑(liftChartPartialDiffeomorph c φ) = liftChart c φ :=
  IsLocalDiffeomorphOn.coe_partialDiffeomorphOfInjOn ..

@[simp]
theorem liftChartPartialDiffeomorph_source :
    (liftChartPartialDiffeomorph c φ).source = blowdown c ⁻¹' φ.source :=
  IsLocalDiffeomorphOn.partialDiffeomorphOfInjOn_source ..

@[simp]
theorem liftChartPartialDiffeomorph_target :
    (liftChartPartialDiffeomorph c φ).target = BlowupModel.blowdown ⁻¹' φ.target :=
  (IsLocalDiffeomorphOn.partialDiffeomorphOfInjOn_target ..).trans
    (liftChart_image_preimage_source c φ)

/-- **The lifted chart is a holomorphic chart.** For holomorphic charts `c` and `φ` at the
centre, the lifted chart `liftChart c φ`, as the partial biholomorphism
`liftChartPartialDiffeomorph c φ` onto the part of the model over the target of `φ`, followed by
any chart `blowupModelChart i` of the model, is a chart of the complex maximal atlas of
`Blowup c`. -/
theorem liftChart_mem_maximalAtlas (i : Fin (n + 1)) :
    (liftChartPartialDiffeomorph c φ).toOpenPartialHomeomorph.trans (blowupModelChart i) ∈
      IsManifold.maximalAtlas 𝓘(ℂ, Fin (n + 1) → ℂ) ω (Blowup c) :=
  (liftChartPartialDiffeomorph c φ).trans_mem_maximalAtlas (blowupModelChart_mem_maximalAtlas ω i)

end Blowup

end SymplecticGeometry

end
