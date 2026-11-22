/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Riemannian.Basic
public import SymplecticGeometry.Geometry.Manifold.Riemannian.VolumeDensity.ChangeOfVariables
import Mathlib.Topology.Order.Compact

/-!
# Bounds for a partial diffeomorphism on a compact set

Let `M` be a manifold whose tangent spaces carry a continuous Riemannian metric, and let
`ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E n`, `n ≠ 0`, be a chart onto an open subset of a
finite-dimensional real normed space `E`. On a compact set `K ⊆ ψ.target`, the differential of
`ψ.symm` is bounded above and below for the Riemannian norm on the tangent spaces of `M`, and the
Riemannian Jacobian of `ψ.symm` is bounded above and away from zero. These are the estimates that
compare integrals over `M` with integrals in a chart.

The norm bounds specialize those for any `C¹` map with injective differentials
(`ContMDiffOn.exists_norm_mfderiv_le_mul_norm`, `ContMDiffOn.exists_pos_mul_norm_le_norm_mfderiv`)
to `ψ.symm`, whose differentials are invertible (Tau Ceti's
`PartialDiffeomorph.isInvertible_mfderiv`). The Jacobian is positive where the differential is
injective (`TauCeti.riemannianJacobian_pos`), and continuous
(`TauCeti.continuousOn_riemannianJacobian`).

## Main results

* `PartialDiffeomorph.exists_mul_norm_le_norm_mfderiv_symm_le`: two-sided bounds for the
  differential of `ψ.symm` on a compact subset of `ψ.target`.
* `PartialDiffeomorph.exists_norm_mvfderiv_le_mul_norm`: the differential of `ψ` is bounded on
  the image of such a set under `ψ.symm`.
* `PartialDiffeomorph.riemannianJacobian_symm_pos` and
  `PartialDiffeomorph.exists_le_riemannianJacobian_symm_le`: the Riemannian Jacobian of `ψ.symm`
  is positive on `ψ.target`, and bounded above and away from zero on a compact subset of it.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 2.
-/

public section

open Bundle Set
open scoped ContDiff Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

namespace PartialDiffeomorph

variable {n : ℕ∞ω}

/-- The Riemannian Jacobian of `ψ.symm`, for a partial diffeomorphism `ψ` from `M` onto an open
subset of `E` and any basis of `E`, is positive on `ψ.target`. -/
theorem riemannianJacobian_symm_pos {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E n) (hn : n ≠ 0) (b : Module.Basis ι ℝ E) {y : E}
    (hy : y ∈ ψ.target) : 0 < TauCeti.riemannianJacobian (I := I) b ψ.symm y :=
  TauCeti.riemannianJacobian_pos b (ψ.symm.isInvertible_mfderiv hn hy).injective

variable [IsManifold I 1 M] [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- On a compact subset `K` of the target of a partial diffeomorphism `ψ` from `M` onto an open
subset of a finite-dimensional real normed space, the differential of `ψ.symm` is bounded above
and below: `c * ‖v‖ ≤ ‖dψ⁻¹_y v‖ ≤ C * ‖v‖` for some `0 < c`, every `y ∈ K` and every `v`, the
middle norm being the Riemannian one. -/
theorem exists_mul_norm_le_norm_mfderiv_symm_le [FiniteDimensional ℝ E]
    (ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E n) (hn : n ≠ 0) {K : Set E} (hK : IsCompact K)
    (hKψ : K ⊆ ψ.target) :
    ∃ c C, 0 < c ∧ ∀ y ∈ K, ∀ v : E,
      c * ‖v‖ ≤ ‖mfderiv 𝓘(ℝ, E) I ψ.symm y v‖ ∧ ‖mfderiv 𝓘(ℝ, E) I ψ.symm y v‖ ≤ C * ‖v‖ := by
  have hn' : 1 ≤ n := ENat.one_le_iff_ne_zero_withTop.2 hn
  obtain ⟨c, hc, hcK⟩ := ψ.symm.contMDiffOn.exists_pos_mul_norm_le_norm_mfderiv hn'
    ψ.open_target hK hKψ fun y hy ↦ (ψ.symm.isInvertible_mfderiv hn (hKψ hy)).injective
  obtain ⟨C, hCK⟩ := ψ.symm.contMDiffOn.exists_norm_mfderiv_le_mul_norm hn' ψ.open_target hK hKψ
  exact ⟨c, C, hc, fun y hy v ↦ ⟨hcK y hy v, hCK y hy v⟩⟩

/-- The differential of a partial diffeomorphism `ψ` from `M` onto an open subset of a
finite-dimensional real normed space is bounded, for the Riemannian norm on the tangent spaces
of `M`, on the image under `ψ.symm` of a compact subset of `ψ.target`. -/
theorem exists_norm_mvfderiv_le_mul_norm [FiniteDimensional ℝ E]
    (ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E n) (hn : n ≠ 0) {K : Set E} (hK : IsCompact K)
    (hKψ : K ⊆ ψ.target) :
    ∃ C, ∀ x ∈ ψ.symm '' K, ∀ w : TangentSpace I x, ‖mvfderiv I ψ x w‖ ≤ C * ‖w‖ := by
  obtain ⟨c, _, hc, hcK⟩ := ψ.exists_mul_norm_le_norm_mfderiv_symm_le hn hK hKψ
  refine ⟨c⁻¹, ?_⟩
  rintro _ ⟨y, hy, rfl⟩ w
  have hx : ψ.symm y ∈ ψ.source := ψ.map_target (hKψ hy)
  -- Apply the lower bound at `ψ (ψ.symm y)` rather than at `y`, so that the differential of
  -- `ψ.symm` there undoes that of `ψ` at `ψ.symm y` without moving between tangent spaces.
  have hy' : ψ (ψ.symm y) ∈ K := by simpa [ψ.right_inv (hKψ hy)] using hy
  have key : mfderiv 𝓘(ℝ, E) I ψ.symm (ψ (ψ.symm y)) (mvfderiv I ψ (ψ.symm y) w) = w := by
    rw [mvfderiv_apply_eq_mfderiv_apply]
    exact ψ.mfderiv_symm_apply_mfderiv_apply hn hx w
  have h := (hcK _ hy' (mvfderiv I ψ (ψ.symm y) w)).1
  rw [key] at h
  calc ‖mvfderiv I ψ (ψ.symm y) w‖ = c⁻¹ * (c * ‖mvfderiv I ψ (ψ.symm y) w‖) := by field_simp
    _ ≤ c⁻¹ * ‖w‖ := mul_le_mul_of_nonneg_left
        (h.trans_eq (TauCeti.norm_tangentSpace_congr (ψ.left_inv hx) rfl)) (inv_nonneg.2 hc.le)

/-- On a compact subset of the target of a partial diffeomorphism `ψ` from `M` onto an open
subset of `E`, the Riemannian Jacobian of `ψ.symm` in any basis of `E` is bounded above and away
from zero. -/
theorem exists_le_riemannianJacobian_symm_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E n) (hn : n ≠ 0) (b : Module.Basis ι ℝ E)
    {K : Set E} (hK : IsCompact K) (hKψ : K ⊆ ψ.target) :
    ∃ c C, 0 < c ∧ ∀ y ∈ K,
      c ≤ TauCeti.riemannianJacobian (I := I) b ψ.symm y ∧
        TauCeti.riemannianJacobian (I := I) b ψ.symm y ≤ C := by
  have hcont := (TauCeti.continuousOn_riemannianJacobian (I := I) b
    (ψ.symm.contMDiffOn.of_le (ENat.one_le_iff_ne_zero_withTop.2 hn)) ψ.open_target).mono hKψ
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont
  have hle (y) (hy : y ∈ K) : TauCeti.riemannianJacobian (I := I) b ψ.symm y ≤ C :=
    (le_abs_self _).trans (hC y hy)
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, C, one_pos, by simp⟩
  obtain ⟨y₀, hy₀, hmin⟩ := hK.exists_isMinOn hne hcont
  exact ⟨_, C, ψ.riemannianJacobian_symm_pos hn b (hKψ hy₀), fun y hy ↦ ⟨hmin hy, hle y hy⟩⟩

end PartialDiffeomorph

end
