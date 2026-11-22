/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.ChangeOfVariables
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Topology.Order.Compact

/-!
# Bounds for a partial diffeomorphism on a compact set

Let `M` be a manifold whose tangent spaces carry a continuous Riemannian metric, and let
`ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E n`, `n ≠ 0`, be a chart onto an open subset of a
finite-dimensional real normed space `E`. On a compact set `K ⊆ ψ.target`, the differential of
`ψ.symm` is bounded above and below for the Riemannian norm on the tangent spaces of `M`, and the
Riemannian Jacobian of `ψ.symm` is bounded above and away from zero. These are the estimates that
compare integrals over `M` with integrals in a chart.

The norm bounds hold for every `C¹` map `f` from an open subset `U` of a finite-dimensional space,
on a compact `K ⊆ U`; the lower bound needs the differential of `f` to be injective on `K`. They
follow from the joint continuity of `(z, ξ) ↦ ‖df_z ξ‖`
(`ContMDiffOn.continuousOn_norm_mfderiv_apply`) on the compact set `K × S`, `S` the unit sphere.
The Jacobian is positive where the differential is injective, since the Gram matrix of linearly
independent vectors is positive definite, and it is continuous
(`TauCeti.continuousOn_riemannianJacobian`).

## Main results

* `ContMDiffOn.exists_norm_mfderiv_le_mul_norm`: the differential of a `C¹` map is bounded on a
  compact subset of its open domain.
* `ContMDiffOn.exists_pos_mul_norm_le_norm_mfderiv`: where the differential is injective on a
  compact set, it is bounded below there.
* `TauCeti.riemannianJacobian_pos`: the Riemannian Jacobian is positive where the differential is
  injective.
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
open NormedSpace
open scoped ContDiff Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace TauCeti

/-- The Riemannian Jacobian of `f` at `x` is positive when the differential of `f` at `x` is
injective. -/
theorem riemannianJacobian_pos {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ F) {f : F → M} {x : F}
    (hf : Function.Injective (mfderiv 𝓘(ℝ, F) I f x)) :
    0 < riemannianJacobian (I := I) b f x := by
  rw [riemannianJacobian_eq_sqrt_det_gram, Real.sqrt_pos]
  refine (Matrix.posDef_gram_of_linearIndependent ?_).det_pos
  exact b.linearIndependent.map' (mfderiv 𝓘(ℝ, F) I f x).toLinearMap
    (LinearMap.ker_eq_bot.2 hf)

end TauCeti

namespace ContinuousLinearMap

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- A continuous linear map scales norms: `‖L v‖ = ‖v‖ * ‖L u‖` for the unit vector `u` in the
direction of `v` (and `u = 0` if `v = 0`). -/
theorem norm_apply_eq_norm_mul_norm_apply_normalize (L : F →L[ℝ] G) (v : F) :
    ‖L v‖ = ‖v‖ * ‖L (normalize v)‖ := by
  conv_lhs => rw [← norm_smul_normalize v]
  rw [map_smul, norm_smul, norm_norm]

end ContinuousLinearMap

namespace ContMDiffOn

variable [IsManifold I 1 M] [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  [FiniteDimensional ℝ F] {f : F → M} {U K : Set F} {n : ℕ∞ω}

/-- The differential of a `C¹` map from an open subset `U` of a finite-dimensional real normed
space to a manifold with a continuous Riemannian metric is bounded on a compact `K ⊆ U`:
`‖df_y v‖ ≤ C * ‖v‖` for every `y ∈ K` and every `v`. -/
theorem exists_norm_mfderiv_le_mul_norm (hf : ContMDiffOn 𝓘(ℝ, F) I n f U) (hn : 1 ≤ n)
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C, ∀ y ∈ K, ∀ v : F, ‖mfderiv 𝓘(ℝ, F) I f y v‖ ≤ C * ‖v‖ := by
  obtain ⟨C, hC⟩ := (hK.prod (isCompact_sphere (0 : F) 1)).exists_bound_of_continuousOn
    ((hf.continuousOn_norm_mfderiv_apply hn hU).mono (prod_mono hKU (subset_univ _)))
  refine ⟨C, fun y hy v ↦ ?_⟩
  have hD : ‖mfderiv 𝓘(ℝ, F) I f y v‖ = ‖v‖ * ‖mfderiv 𝓘(ℝ, F) I f y (normalize (V := F) v)‖ :=
    ContinuousLinearMap.norm_apply_eq_norm_mul_norm_apply_normalize (F := F)
      (G := TangentSpace I (f y)) (mfderiv 𝓘(ℝ, F) I f y) v
  rw [hD, mul_comm C]
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg v)
  simpa using hC (y, normalize v) (mk_mem_prod hy (by simpa using norm_normalize_eq_one_iff.2 hv))

/-- If a `C¹` map from an open subset `U` of a finite-dimensional real normed space to a manifold
with a continuous Riemannian metric has injective differentials on a compact `K ⊆ U`, they are
uniformly bounded below there: `c * ‖v‖ ≤ ‖df_y v‖` for some `0 < c`, every `y ∈ K` and every
`v`. -/
theorem exists_pos_mul_norm_le_norm_mfderiv (hf : ContMDiffOn 𝓘(ℝ, F) I n f U) (hn : 1 ≤ n)
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hinj : ∀ y ∈ K, Function.Injective (mfderiv 𝓘(ℝ, F) I f y)) :
    ∃ c, 0 < c ∧ ∀ y ∈ K, ∀ v : F, c * ‖v‖ ≤ ‖mfderiv 𝓘(ℝ, F) I f y v‖ := by
  have hsph {v : F} (hv : v ≠ 0) : normalize v ∈ Metric.sphere (0 : F) 1 := by
    simpa using norm_normalize_eq_one_iff.2 hv
  rcases (K ×ˢ Metric.sphere (0 : F) 1).eq_empty_or_nonempty with he | hne
  · refine ⟨1, one_pos, fun y hy v ↦ ?_⟩
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    exact (he.subset (mk_mem_prod hy (hsph hv))).elim
  obtain ⟨⟨y₀, u₀⟩, ⟨hy₀, hu₀⟩, hmin⟩ := (hK.prod (isCompact_sphere (0 : F) 1)).exists_isMinOn
    hne ((hf.continuousOn_norm_mfderiv_apply hn hU).mono (prod_mono hKU (subset_univ _)))
  have hu₀' : u₀ ≠ 0 := ne_zero_of_mem_unit_sphere ⟨u₀, hu₀⟩
  refine ⟨‖mfderiv 𝓘(ℝ, F) I f y₀ u₀‖, norm_pos_iff.2 fun h ↦ hu₀' ?_, fun y hy v ↦ ?_⟩
  · exact (injective_iff_map_eq_zero
      (mfderiv 𝓘(ℝ, F) I f y₀ : F →L[ℝ] TangentSpace I (f y₀))).1 (hinj y₀ hy₀) u₀ h
  have hD : ‖mfderiv 𝓘(ℝ, F) I f y v‖ = ‖v‖ * ‖mfderiv 𝓘(ℝ, F) I f y (normalize (V := F) v)‖ :=
    ContinuousLinearMap.norm_apply_eq_norm_mul_norm_apply_normalize (F := F)
      (G := TangentSpace I (f y)) (mfderiv 𝓘(ℝ, F) I f y) v
  rw [hD, mul_comm]
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  exact mul_le_mul_of_nonneg_left (hmin (mk_mem_prod hy (hsph hv))) (norm_nonneg v)

end ContMDiffOn

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
