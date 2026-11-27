/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Model
import SymplecticGeometry.Analysis.Calculus.FDeriv.Uncurry

/-!
# Flowing out of the boundary hyperplane of the half-space model

Tau Ceti's `euclideanHalfSpaceBoundaryParam n` includes `ℝⁿ` in `ℝⁿ⁺¹` as the hyperplane where the
zeroth coordinate vanishes, the boundary of the half-space model. Let `Ψ x t` be a family of
points of `ℝⁿ⁺¹` with `Ψ x 0 = x`, such as a local flow. Moving the points of the hyperplane along
`Ψ` gives the flow-out map `(z, τ) ↦ Ψ (z in the hyperplane) (τ 0)` on `ℝⁿ × ℝ¹`. Its derivative
at `(z₀, 0)` sends `(u, σ)` to `u` in the hyperplane plus `σ 0 • v`, where `v` is the velocity of
`t ↦ Ψ (z₀ in the hyperplane) t` at `0` (`DifferentiableAt.hasFDerivAt_uncurry_zero`). So it is
injective when `v` leaves the hyperplane, that is `v 0 ≠ 0`.

Tau Ceti proves the same fact, for `0 < v 0` and `Ψ x 0 = x` for all `x`, as the private
`injective_fderiv_flowOut_euclideanHalfSpaceBoundaryParam` in
`TauCeti/Geometry/Manifold/Boundary/BoundaryFlow/LocalDiffeomorph.lean`, on the way to its
flow-out theorem at the boundary.

## Main results

* `TauCeti.injective_fderiv_flowOut_euclideanHalfSpaceBoundaryParam`: a family `Ψ x t`
  with `Ψ x 0 = x` whose velocity at time `0` is transverse to the boundary hyperplane has, out of
  that hyperplane, injective derivative.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218, 2013,
  Chapter 9 (the flow-out theorem 9.20).
-/

public section

open Function Filter Topology

namespace TauCeti

variable {n : ℕ} {Ψ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ → EuclideanSpace ℝ (Fin (n + 1))}

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
