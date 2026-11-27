/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Model
public import TauCeti.Geometry.Manifold.Boundary.Orientation
import SymplecticGeometry.Analysis.Calculus.FDeriv.Uncurry

/-!
# Outward fields near the boundary

Let `W` be a manifold modelled on the half-space `𝓡∂ (n + 1)` and `Y` a vector field on `W` that
points out of `W` along its boundary (`TauCeti.IsOutwardPointing`). Integral curves of `Y` cannot
start at a boundary point and go forward, but they can go backward, into the interior. Tau Ceti
builds these curves along the whole boundary, as the forward flow of `-Y`
(`TauCeti.IsOutwardPointingField.exists_contMDiffOn_boundaryFlow`), and shows that their flow-out
from the boundary is a local diffeomorphism at each boundary point
(`TauCeti.isLocalDiffeomorphAt_flowOut_boundary`); `Flow/Basic.lean` makes a collar out of them.
This file adds what the library uses besides.

An integral curve of an outward field stays in the interior at times from which it is defined for
a while forward, since its velocity there within `[t, ∞)` would be outward, which Tau Ceti's
`TauCeti.not_isOutwardPointing_curveVelocityWithin_Ici` rules out
(`IsMIntegralCurveOn.mem_interior_of_isOutwardPointing`).

## Main results

* `IsMIntegralCurveOn.mem_interior_of_isOutwardPointing`: an integral curve of an outward field is
  in the interior at each time `t` of its domain `s` with `s ∈ 𝓝[≥] t`.
* `TauCeti.injective_fderiv_flowOut_euclideanHalfSpaceBoundaryParam`: a family `Ψ x t`
  with `Ψ x 0 = x` whose velocity at time `0` is transverse to the boundary hyperplane has, out of
  that hyperplane, injective derivative.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218, 2013,
  Chapter 9 (flows; the flow-out theorem 9.20, and the collar theorem 9.25).
* M. Hirsch, *Differential Topology*, Springer GTM 33, 1976, Chapter 4, Theorem 6.1.
-/

public section

open Set Function Topology
open scoped Manifold

namespace TauCeti

variable {n : ℕ} {W : Type*} [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
  {Y : (x : W) → TangentSpace (𝓡∂ (n + 1)) x}

/-- An integral curve of a vector field that points outward along the boundary is in the interior
at every time `t` of its domain `s` from which it is defined for a while forward, that is with
`s ∈ 𝓝[≥] t`. -/
theorem _root_.IsMIntegralCurveOn.mem_interior_of_isOutwardPointing
    (hY : ∀ x ∈ (𝓡∂ (n + 1)).boundary W, IsOutwardPointing x (Y x)) {γ : ℝ → W} {s : Set ℝ}
    (hγ : IsMIntegralCurveOn γ Y s) {t : ℝ} (hs : s ∈ 𝓝[≥] t) :
    γ t ∈ (𝓡∂ (n + 1)).interior W := by
  rw [← ModelWithCorners.compl_boundary]
  intro hb
  -- The velocity of `γ` at `t` within `[t, ∞)` is `Y (γ t)`, which is outward, but no curve
  -- running forward from `t` has an outward velocity there.
  apply not_isOutwardPointing_curveVelocityWithin_Ici (n := n) γ t
  rw [Manifold.curveVelocityWithin_eq_of_hasMFDerivWithinAt
    ((hγ t (mem_of_mem_nhdsWithin self_mem_Ici hs)).mono_of_mem_nhdsWithin hs)
    (uniqueDiffOn_Ici t t self_mem_Ici)]
  exact hY _ hb

variable {Ψ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ → EuclideanSpace ℝ (Fin (n + 1))}

/-- Let `Ψ x t` be a family of points of `ℝⁿ⁺¹` with `Ψ x 0 = x` for `x` near `y₀`,
differentiable at `(y₀, 0)`, where `y₀` is the point `z₀ ∈ ℝⁿ` of the boundary hyperplane, such
that the curve `t ↦ Ψ y₀ t` has at time `0` a velocity `v` with `v 0 ≠ 0`. Then the flow-out map
`(z, τ) ↦ Ψ (z in the hyperplane) (τ 0)` on `ℝⁿ × ℝ¹` has injective derivative at `(z₀, 0)`. -/
theorem injective_fderiv_flowOut_euclideanHalfSpaceBoundaryParam
    {z₀ : EuclideanSpace ℝ (Fin n)}
    (hΨ : DifferentiableAt ℝ (fun p : EuclideanSpace ℝ (Fin (n + 1)) × ℝ ↦ Ψ p.1 p.2)
      (euclideanHalfSpaceBoundaryParam n z₀, 0))
    (hΨ0 : ∀ᶠ x in 𝓝 (euclideanHalfSpaceBoundaryParam n z₀), Ψ x 0 = x)
    {v : EuclideanSpace ℝ (Fin (n + 1))}
    (hv : HasDerivAt (Ψ (euclideanHalfSpaceBoundaryParam n z₀)) v 0) (hv0 : v 0 ≠ 0) :
    Injective (fderiv ℝ (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1) ↦
      Ψ (euclideanHalfSpaceBoundaryParam n q.1) (q.2 0)) (z₀, 0)) := by
  set ι := euclideanHalfSpaceBoundaryParam n
  set L := ι.prodMap (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1))
  have hLz₀ : L (z₀, 0) = (ι z₀, 0) := by
    simp [L]
  -- The derivative `D` of `Ψ` at `(ι z₀, 0)` is the identity in space and `v` in time.
  set D : EuclideanSpace ℝ (Fin (n + 1)) × ℝ →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
    ContinuousLinearMap.fst ℝ _ ℝ + (ContinuousLinearMap.snd ℝ _ ℝ).smulRight v
  have hD : HasFDerivAt (fun p : EuclideanSpace ℝ (Fin (n + 1)) × ℝ ↦ Ψ p.1 p.2) D (ι z₀, 0) :=
    hΨ.hasFDerivAt_uncurry_zero hΨ0 hv
  have hDapply (u : EuclideanSpace ℝ (Fin (n + 1))) (σ : ℝ) : D (u, σ) = u + σ • v := by
    simp [D]
  have hGd : HasFDerivAt (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1) ↦
      Ψ (ι q.1) (q.2 0)) (D.comp L) (z₀, 0) := by
    rw [← hLz₀] at hD
    exact hD.comp (z₀, 0) L.hasFDerivAt
  -- So that derivative is injective, since `v` leaves the hyperplane.
  rw [hGd.fderiv, injective_iff_map_eq_zero]
  rintro ⟨dz, dτ⟩ h
  simp only [L, ContinuousLinearMap.coe_comp, comp_apply, ContinuousLinearMap.coe_prodMap',
    Prod.map_apply, PiLp.proj_apply, hDapply] at h
  have h0 := congrArg (fun y : EuclideanSpace ℝ (Fin (n + 1)) ↦ y 0) h
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, ι,
    euclideanHalfSpaceBoundaryParam_apply_zero, zero_add, PiLp.zero_apply, mul_eq_zero, hv0,
    or_false] at h0
  have hτ : dτ = 0 := by
    ext i
    fin_cases i
    simpa using h0
  rw [h0, zero_smul, add_zero] at h
  have hz : dz = 0 := euclideanHalfSpaceBoundaryParam_injective n (by simpa [ι] using h)
  simp [hz, hτ]


end TauCeti

end
