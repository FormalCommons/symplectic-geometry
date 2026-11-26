/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Complex.Blowup.Basic
public import TauCeti.LinearAlgebra.Projectivization.Basic
import SymplecticGeometry.Geometry.Manifold.MFDeriv.Atlas
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic

/-!
# The lines at the centre of a blowup and the exceptional divisor

Let `c : BlowupChart M p₀` be a chart of the complex maximal atlas of `M`, modelled on
`E = ℂⁿ⁺¹`. The points of the exceptional divisor of `Blowup c` are the lines `ℓ : ℙ ℂ E`
(`Blowup.ofDirection c ℓ`). As a chart of the maximal atlas, `c` has an invertible differential
at the centre `p₀`, with inverse the differential of `c⁻¹` at `c p₀ = 0`; so the differential
identifies the lines of the tangent space at `p₀` with the points of the divisor. This file
defines that bijection.

## Main definitions

* `SymplecticGeometry.BlowupChart.mfderivCenterEquiv c`: the differential of `c` at `p₀`, as a
  continuous linear equivalence `T_{p₀}M ≃L[ℂ] E` whose inverse is the differential of `c⁻¹`
  at `0`. It is Mathlib's `OpenPartialHomeomorph.MDifferentiable.mfderiv` of `c` at `p₀`, typed
  onto `E`.
* `SymplecticGeometry.Blowup.directionEquiv c`: the bijection
  `ℙ ℂ (TangentSpace 𝓘(ℂ, E) p₀) ≃ ℙ ℂ E` that it induces, through Tau Ceti's
  `LinearEquiv.mapProjectivization`.

## Main results

* `SymplecticGeometry.BlowupChart.coe_mfderivCenterEquiv`,
  `SymplecticGeometry.BlowupChart.coe_mfderivCenterEquiv_symm`: the equivalence is the
  differential of `c` at `p₀`, and its inverse is the differential of `c⁻¹` at `0`.
* `SymplecticGeometry.Blowup.directionEquiv_apply`: `directionEquiv c` is `Projectivization.map`
  of the differential of `c` at `p₀`.
* `SymplecticGeometry.Blowup.directionEquiv_mk`,
  `SymplecticGeometry.Blowup.directionEquiv_symm_mk`: it sends the line of `v` to the line of
  `dc(p₀) v`, and its inverse sends the line of `w` to the line of `d(c⁻¹)(0) w`.

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

end SymplecticGeometry

end
