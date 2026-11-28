/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.ODE.Linear
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Stable subspaces of a linear flow

A continuous linear equivalence `e : X ≃L[ℝ] Y` conjugates the flow `exp (t • A)` of an operator
`A` on `X` to the flow of `e A e⁻¹` on `Y`. So it carries Tau Ceti's stable subspace
`ContinuousLinearMap.stableSubspace` of `A` onto that of `e A e⁻¹`.

The flow of a product operator `A × B` on `X × Y` is the product of the flows, since `prodMap` is
a continuous ring homomorphism from the product algebra and so commutes with the exponential. So
the stable subspace of `A × B` is the product of those of `A` and `B`.

A continuous bilinear map `B` with `B (A u) v + B u (A v) = B u v` grows like `e ^ t` along the
flow: `B (exp (t • A) u) (exp (t • A) v) = e ^ t • B u v`. So it vanishes on pairs of stable
vectors, since the left side then tends to `0`. For a Liouville field this is the isotropy of the
stable subspace of its linearization at a zero.

## Main results

* `ContinuousLinearEquiv.apply_mem_stableSubspace_conjContinuousAlgEquiv_iff`: `e v` is stable
  for `e A e⁻¹` if and only if `v` is stable for `A`.
* `ContinuousLinearEquiv.stableSubspace_conjContinuousAlgEquiv`: the stable subspace of
  `e A e⁻¹` is the image under `e` of that of `A`.
* `ContinuousLinearMap.exp_prodMap`: `exp (A.prodMap B) = (exp A).prodMap (exp B)`.
* `ContinuousLinearMap.stableSubspace_prodMap`: the stable subspace of `A.prodMap B` is the
  product of the stable subspaces of `A` and `B`.
* `ContinuousLinearMap.stableSubspace_smul_id_of_nonneg`: for `c ≥ 0`, the operator `c • id`
  has no nonzero stable vector.
* `ContinuousLinearMap.apply_eq_zero_of_mem_stableSubspace`: a bilinear map that `A` scales at
  rate one, in the sense above, vanishes on the stable subspace of `A`.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  Proposition 11.9 (a)
-/

public section

open Filter NormedSpace Topology

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y] [CompleteSpace X] [CompleteSpace Y]

namespace ContinuousLinearEquiv

/-- A continuous linear equivalence `e` conjugates the flow of `A` to that of `e A e⁻¹`, so `e v`
is stable for `e A e⁻¹` if and only if `v` is stable for `A`. -/
theorem apply_mem_stableSubspace_conjContinuousAlgEquiv_iff (e : X ≃L[ℝ] Y) {A : X →L[ℝ] X}
    {v : X} : e v ∈ (e.conjContinuousAlgEquiv A).stableSubspace ↔ v ∈ A.stableSubspace := by
  have hexp (t : ℝ) : exp (t • e.conjContinuousAlgEquiv A) (e v) = e (exp (t • A) v) := by
    have hA : t • e.conjContinuousAlgEquiv A = e.conjContinuousAlgEquiv (t • A) := by
      ext x
      simp
    rw [hA, ← map_exp_of_mem_ball (𝕂 := ℝ) _ e.conjContinuousAlgEquiv.continuous _
      ((expSeries_radius_eq_top ℝ (X →L[ℝ] X)).symm ▸ edist_lt_top _ _),
      conjContinuousAlgEquiv_apply_apply, symm_apply_apply]
  simp only [ContinuousLinearMap.mem_stableSubspace, hexp]
  simpa [Function.comp_def] using (e.toHomeomorph.isInducing.tendsto_nhds_iff
    (f := fun t : ℝ ↦ exp (t • A) v) (l := atTop) (y := 0)).symm

/-- The stable subspace of `e A e⁻¹` is the image under `e` of the stable subspace of `A`. -/
theorem stableSubspace_conjContinuousAlgEquiv (e : X ≃L[ℝ] Y) (A : X →L[ℝ] X) :
    (e.conjContinuousAlgEquiv A).stableSubspace = A.stableSubspace.map (e : X →ₗ[ℝ] Y) := by
  ext w
  obtain ⟨v, rfl⟩ := e.surjective w
  rw [e.apply_mem_stableSubspace_conjContinuousAlgEquiv_iff]
  simp

end ContinuousLinearEquiv

namespace ContinuousLinearMap

/-- The exponential of a product operator `A × B` on `X × Y` is the product of the exponentials:
`exp (A.prodMap B) = (exp A).prodMap (exp B)`. -/
theorem exp_prodMap (A : X →L[ℝ] X) (B : Y →L[ℝ] Y) :
    exp (A.prodMap B) = (exp A).prodMap (exp B) := by
  -- `prodMap` is a continuous ring homomorphism on the product algebra.
  let φ : (X →L[ℝ] X) × (Y →L[ℝ] Y) →+* (X × Y →L[ℝ] X × Y) :=
    { toFun := fun p ↦ p.1.prodMap p.2
      map_one' := ext fun _ ↦ by simp
      map_mul' := fun _ _ ↦ ext fun _ ↦ by simp [Prod.map]
      map_zero' := (prodMapL ℝ X X Y Y).map_zero
      map_add' := (prodMapL ℝ X X Y Y).map_add }
  have hφ : Continuous φ := Continuous.prod_mapL ℝ continuous_fst continuous_snd
  have hr : (A, B) ∈ Metric.eball 0 (expSeries ℝ ((X →L[ℝ] X) × (Y →L[ℝ] Y))).radius := by
    rw [expSeries_radius_eq_top ℝ ((X →L[ℝ] X) × (Y →L[ℝ] Y))]
    exact edist_lt_top _ _
  have h : φ (exp (A, B)) = exp (φ (A, B)) := map_exp_of_mem_ball (𝕂 := ℝ) φ hφ (A, B) hr
  have h₁ : (exp (A, B)).1 = exp A :=
    map_exp_of_mem_ball (𝕂 := ℝ) (RingHom.fst (X →L[ℝ] X) (Y →L[ℝ] Y)) continuous_fst _ hr
  have h₂ : (exp (A, B)).2 = exp B :=
    map_exp_of_mem_ball (𝕂 := ℝ) (RingHom.snd (X →L[ℝ] X) (Y →L[ℝ] Y)) continuous_snd _ hr
  rw [← h₁, ← h₂]
  exact h.symm

/-- The stable subspace of a product operator is the product of the stable subspaces: `(u, v)` is
stable for `A × B` if and only if `u` is stable for `A` and `v` for `B`. -/
theorem stableSubspace_prodMap (A : X →L[ℝ] X) (B : Y →L[ℝ] Y) :
    (A.prodMap B).stableSubspace = A.stableSubspace.prod B.stableSubspace := by
  ext ⟨u, v⟩
  have h (t : ℝ) : t • A.prodMap B = (t • A).prodMap (t • B) := by
    simpa using ((prodMapL ℝ X X Y Y).map_smul t (A, B)).symm
  simp only [mem_stableSubspace, Submodule.mem_prod, h, exp_prodMap, coe_prodMap', Prod.map,
    ← Prod.mk_zero_zero, nhds_prod_eq, tendsto_prod_iff']

/-- A nonnegative multiple `c • id` of the identity has no nonzero stable vector: its flow is
`v ↦ e ^ (t c) • v`, which does not shrink `v`. -/
theorem stableSubspace_smul_id_of_nonneg {c : ℝ} (hc : 0 ≤ c) :
    (c • ContinuousLinearMap.id ℝ X).stableSubspace = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun v hv ↦ ?_
  rw [mem_stableSubspace] at hv
  have h (t : ℝ) : exp (t • c • ContinuousLinearMap.id ℝ X) v = Real.exp (t * c) • v := by
    rw [smul_smul, ← one_def, ← Algebra.algebraMap_eq_smul_one, ← algebraMap_exp_comm,
      Real.exp_eq_exp_ℝ, Algebra.algebraMap_eq_smul_one]
    simp
  simp only [h] at hv
  have h1 : Tendsto (fun t : ℝ ↦ ‖Real.exp (t * c) • v‖) atTop (𝓝 0) := by
    simpa using hv.norm
  refine norm_le_zero_iff.1 (ge_of_tendsto h1 (eventually_atTop.2 ⟨0, fun t ht ↦ ?_⟩))
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_exp (by positivity))

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Let `B` be a continuous bilinear map with `B (A u) v + B u (A v) = B u v` for all `u`, `v`,
so that `B (exp (t • A) u) (exp (t • A) v) = e ^ t • B u v`. Then `B u v = 0` for `u` and `v` in
the stable subspace of `A`. -/
theorem apply_eq_zero_of_mem_stableSubspace {A : X →L[ℝ] X} {B : X →L[ℝ] X →L[ℝ] F}
    (hB : ∀ u v, B (A u) v + B u (A v) = B u v) {u v : X} (hu : u ∈ A.stableSubspace)
    (hv : v ∈ A.stableSubspace) : B u v = 0 := by
  rw [mem_stableSubspace] at hu hv
  -- `G t = e ^ (-t) * B (exp (t • A) u) (exp (t • A) v)` has derivative zero.
  set G : ℝ → F := fun t ↦ Real.exp (-t) • B (exp (t • A) u) (exp (t • A) v)
  have hG (t : ℝ) : HasDerivAt G 0 t := by
    have hx := (hasDerivAt_exp_smul_const' A t).clm_apply (hasDerivAt_const t u)
    have hy := (hasDerivAt_exp_smul_const' A t).clm_apply (hasDerivAt_const t v)
    have hF := B.hasDerivAt_of_bilinear (fun _ ↦ hx) (fun _ ↦ hy)
    have he := (Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)
    refine (he.smul hF).congr_deriv ?_
    have hBt := hB (exp (t • A) u) (exp (t • A) v)
    simp only [mul_apply_eq_comp, map_zero, add_zero, Function.comp_apply, mul_neg, mul_one,
      neg_smul] at hBt ⊢
    rw [add_comm (B _ _), hBt, add_neg_cancel]
  have hconst (t : ℝ) : G t = B u v := by
    simpa [G] using
      is_const_of_deriv_eq_zero (fun t ↦ (hG t).differentiableAt) (fun t ↦ (hG t).deriv) t 0
  have h0 : Tendsto (fun t : ℝ ↦ B (exp (t • A) u) (exp (t • A) v)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (B.continuous₂.tendsto (0, 0)).comp (hu.prodMk_nhds hv)
  have hlim : Tendsto G atTop (𝓝 0) := by
    simpa using Real.tendsto_exp_neg_atTop_nhds_zero.smul h0
  exact tendsto_nhds_unique (tendsto_const_nhds.congr fun t ↦ (hconst t).symm) hlim

end ContinuousLinearMap

end
