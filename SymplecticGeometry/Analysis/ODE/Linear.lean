/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.ODE.Linear
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Stable subspaces of a linear flow

A continuous linear equivalence `e : X ≃L[ℝ] Y` conjugates the flow `exp (t • A)` of an operator
`A` on `X` to the flow of `e A e⁻¹` on `Y`. So it carries Tau Ceti's stable subspace
`ContinuousLinearMap.stableSubspace` of `A` onto that of `e A e⁻¹`.

A continuous bilinear map `B` with `B (A u) v + B u (A v) = B u v` grows like `e ^ t` along the
flow: `B (exp (t • A) u) (exp (t • A) v) = e ^ t • B u v`. So it vanishes on pairs of stable
vectors, since the left side then tends to `0`. For a Liouville field this is the isotropy of the
stable subspace of its linearization at a zero.

## Main results

* `ContinuousLinearEquiv.apply_mem_stableSubspace_conjContinuousAlgEquiv_iff`: `e v` is stable
  for `e A e⁻¹` if and only if `v` is stable for `A`.
* `ContinuousLinearEquiv.stableSubspace_conjContinuousAlgEquiv`: the stable subspace of
  `e A e⁻¹` is the image under `e` of that of `A`.
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
