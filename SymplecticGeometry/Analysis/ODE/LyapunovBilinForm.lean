/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Signature
public import TauCeti.Analysis.ODE.Linear
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2
import SymplecticGeometry.Analysis.ODE.ExponentialDichotomy
import SymplecticGeometry.Analysis.ODE.Linear
import TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap
import TauCeti.Analysis.InnerProductSpace.LyapunovForm.Inertia
import TauCeti.Analysis.ODE.ExponentialDichotomy.Hyperbolic
import TauCeti.Topology.Algebra.Module.BilinearForm
import TauCeti.LinearAlgebra.QuadraticForm.Signature

/-!
# Lyapunov bilinear forms of a linear flow on a normed space

Let `A` be an operator on a finite-dimensional real normed space `X`, and `B` a symmetric
continuous bilinear form on `X` with `c * ‖v‖ ^ 2 ≤ B v (A v)` for some `c > 0`. Along the flow
`exp (t • A)` the quadratic form `v ↦ B v v` then increases. This is Tau Ceti's notion of a
Lyapunov form (`ContinuousLinearMap.HasLyapunovForm`) without a choice of inner product: on an
inner product space, `B v w = ⟪S v, w⟫` for a symmetric `S`. This file transfers Tau Ceti's
inertia theorem to this setting. It also holds a local estimate near a rest point of a nonlinear
map `Y` whose derivative at `0` is `A`, on any real normed space: there `B (P w) (P (Y w))`
bounds a multiple of `‖P w‖ ^ 2` on cones, for an operator `P` commuting with `A`.

## Main results

* `ContinuousLinearMap.eq_zero_of_apply_eq_neg_smul_of_apply_eq_smul_of_le_apply`: `A` has no
  rotating pair, so it is hyperbolic.
* `ContinuousLinearMap.exists_projection_exponential_bounds_of_le_apply`: the flow of `A` has an
  exponential dichotomy.
* `ContinuousLinearMap.apply_self_neg_of_mem_stableSubspace` and
  `ContinuousLinearMap.apply_self_pos_of_mem_unstableSubspace`: `B` is negative definite on the
  stable subspace and positive definite on the unstable one.
* `ContinuousLinearMap.stableSubspace_eq_bot_of_apply_pos`: if moreover `B` is positive definite,
  the stable subspace of `A` is `⊥`; here only `0 < B v (A v)` for `v ≠ 0` is assumed, and the
  constant `c` comes from compactness of the unit sphere.
* `ContinuousLinearMap.sigNeg_toQuadraticMap_eq_finrank_stableSubspace`: the negative index of
  inertia of `v ↦ B v v` is the dimension of the stable subspace of `A`.
* `ContinuousLinearMap.exists_forall_half_mul_norm_sq_le_apply`: for a map `Y` with derivative
  `A` at a zero `0` and an operator `P` commuting with `A`, the bound
  `c / 2 * ‖P w‖ ^ 2 ≤ B (P w) (P (Y w))` on each cone `‖w‖ ≤ C * ‖P w‖` near `0`.
* `ContinuousLinearMap.hasDerivAt_neg_apply_self_comp`: the derivative of `-B (P w) (P w)` along
  a curve `w`.

## Implementation notes

The sign statements are deduced from Tau Ceti's
`ContinuousLinearMap.inner_apply_self_neg_of_mem_stableSubspace`, after a choice of a continuous
linear equivalence of `X` with a Euclidean space, in which `B` becomes `⟪S ·, ·⟫` by
`InnerProductSpace.continuousLinearMapOfBilin`. The absence of rotating pairs follows the proof of
Tau Ceti's `ContinuousLinearMap.HasLyapunovForm.eq_zero_of_apply_eq_neg_smul_of_apply_eq_smul`,
and the index is Sylvester's law of inertia for a definite splitting,
`QuadraticForm.sigNeg_eq_finrank_of_isCompl_of_negDef`.

## References

* A. Ostrowski and H. Schneider, *Some theorems on the inertia of general matrices*, J. Math. Anal.
  Appl. **4** (1962), 72–84.
-/

public section

open Module NormedSpace
open scoped InnerProductSpace NNReal

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

namespace ContinuousLinearMap

variable {A : X →L[ℝ] X} {B : X →L[ℝ] X →L[ℝ] ℝ} {c : ℝ}

/-- **No rotating pairs.** If `B` is symmetric and `c * ‖v‖ ^ 2 ≤ B v (A v)` with `c > 0`, then
`A v = -ω • w` and `A w = ω • v` force `v = 0` and `w = 0`: the operator `A` has no purely
imaginary eigenvalue. -/
theorem eq_zero_of_apply_eq_neg_smul_of_apply_eq_smul_of_le_apply (hB : ∀ u v, B u v = B v u)
    (hc : 0 < c) (hcB : ∀ v, c * ‖v‖ ^ 2 ≤ B v (A v)) {ω : ℝ} {v w : X} (hv : A v = -ω • w)
    (hw : A w = ω • v) : v = 0 ∧ w = 0 := by
  have h₁ := hcB v
  have h₂ := hcB w
  rw [hv, map_smul, smul_eq_mul] at h₁
  rw [hw, map_smul, smul_eq_mul, hB] at h₂
  have hv0 : ‖v‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖v‖, sq_nonneg ‖w‖]
  have hw0 : ‖w‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖v‖, sq_nonneg ‖w‖]
  simpa using And.intro hv0 hw0

/-- **The projected quadratic form near a rest point.** Let `Y` vanish at `0` with derivative `A`
there, let `P` commute with `A`, and let `c * ‖v‖ ^ 2 ≤ B v (A v)` with `c > 0`. Then for each
`C` there is `δ > 0` such that `c / 2 * ‖P w‖ ^ 2 ≤ B (P w) (P (Y w))` for every `w` with
`‖w‖ < δ` in the cone `‖w‖ ≤ C * ‖P w‖`. -/
theorem exists_forall_half_mul_norm_sq_le_apply (hc : 0 < c)
    (hcB : ∀ v, c * ‖v‖ ^ 2 ≤ B v (A v)) {P : X →L[ℝ] X} (hAP : Commute A P) {Y : X → X}
    (hY0 : Y 0 = 0) (hY : HasFDerivAt Y A 0) (C : ℝ) :
    ∃ δ > 0, ∀ w, ‖w‖ < δ → ‖w‖ ≤ C * ‖P w‖ → c / 2 * ‖P w‖ ^ 2 ≤ B (P w) (P (Y w)) := by
  set M := ‖B‖ * ‖P‖ * max C 0
  have hM : 0 ≤ M := by positivity
  set ε := c / (2 * (M + 1))
  have hε : 0 < ε := by positivity
  have hεM : M * ε ≤ c / 2 := by
    rw [show M * ε = c / 2 * (M / (M + 1)) by simp only [ε]; field_simp]
    exact mul_le_of_le_one_right (by positivity) ((div_le_one (by positivity)).2 (by linarith))
  obtain ⟨δ, hδ, hδY⟩ :=
    Metric.eventually_nhds_iff.1 ((hasFDerivAt_iff_isLittleO_nhds_zero.1 hY).def hε)
  refine ⟨δ, hδ, fun w hw hwC ↦ ?_⟩
  have hYw : ‖Y w - A w‖ ≤ ε * ‖w‖ := by
    simpa [hY0] using hδY (by simpa using hw)
  have hPA : P (A w) = A (P w) := by simpa using DFunLike.congr_fun hAP.eq.symm w
  have hsplit : B (P w) (P (Y w)) = B (P w) (A (P w)) + B (P w) (P (Y w - A w)) := by
    rw [map_sub, hPA, map_sub, add_sub_cancel]
  have herr : |B (P w) (P (Y w - A w))| ≤ c / 2 * ‖P w‖ ^ 2 :=
    calc |B (P w) (P (Y w - A w))| ≤ ‖B‖ * ‖P w‖ * (‖P‖ * ‖Y w - A w‖) := by
          rw [← Real.norm_eq_abs]
          exact (B.le_opNorm₂ _ _).trans (by gcongr; exact P.le_opNorm _)
      _ ≤ ‖B‖ * ‖P w‖ * (‖P‖ * (ε * (max C 0 * ‖P w‖))) := by
          gcongr
          exact hYw.trans (mul_le_mul_of_nonneg_left
            (hwC.trans (by gcongr; exact le_max_left C 0)) hε.le)
      _ = M * ε * ‖P w‖ ^ 2 := by simp only [M]; ring
      _ ≤ c / 2 * ‖P w‖ ^ 2 := by gcongr
  have := hcB (P w)
  have := neg_abs_le (B (P w) (P (Y w - A w)))
  rw [hsplit]
  linarith

/-- The derivative of `s ↦ -B (P (w s)) (P (w s))` at `t`, along a curve `w` with derivative `w'`
at `t`, is `-2 * B (P (w t)) (P w')`, for a symmetric bilinear form `B` and an operator `P`. -/
theorem hasDerivAt_neg_apply_self_comp (hB : ∀ u v, B u v = B v u) (P : X →L[ℝ] X)
    {w : ℝ → X} {w' : X} {t : ℝ} (hw : HasDerivAt w w' t) :
    HasDerivAt (fun s ↦ -B (P (w s)) (P (w s))) (-2 * B (P (w t)) (P w')) t := by
  have h := (hasDerivAt_const t B).clm_apply_self (P.hasFDerivAt.comp_hasDerivAt t hw) hB
  rw [zero_apply, zero_apply, zero_add] at h
  rw [neg_mul]
  exact h.neg

variable [FiniteDimensional ℝ X]

/-- **Exponential dichotomy.** If `B` is symmetric and `c * ‖v‖ ^ 2 ≤ B v (A v)` with `c > 0`,
then the flow of `A` has an exponential dichotomy, in the form of Tau Ceti's
`ContinuousLinearMap.exists_projection_exponential_bounds`. -/
theorem exists_projection_exponential_bounds_of_le_apply (hB : ∀ u v, B u v = B v u)
    (hc : 0 < c) (hcB : ∀ v, c * ‖v‖ ^ 2 ≤ B v (A v)) :
    ∃ P : X →L[ℝ] X, IsIdempotentElem P ∧ Commute A P ∧ ∃ K α : ℝ≥0, 0 < K ∧ 0 < α ∧
      (∀ t : ℝ, 0 ≤ t → ∀ v : X, ‖exp (t • A) (P v)‖ ≤ K * Real.exp (-α * t) * ‖v‖) ∧
      (∀ t : ℝ, t ≤ 0 → ∀ v : X, ‖exp (t • A) (v - P v)‖ ≤ K * Real.exp (α * t) * ‖v‖) :=
  A.exists_projection_exponential_bounds fun _ _ _ hv hw ↦
    eq_zero_of_apply_eq_neg_smul_of_apply_eq_smul_of_le_apply hB hc hcB hv hw

/-- **A Lyapunov bilinear form is negative definite on the stable subspace.** If `B` is symmetric
and `c * ‖v‖ ^ 2 ≤ B v (A v)` with `c > 0`, then `B v v < 0` for every nonzero stable `v`. -/
theorem apply_self_neg_of_mem_stableSubspace (hB : ∀ u v, B u v = B v u) (hc : 0 < c)
    (hcB : ∀ v, c * ‖v‖ ^ 2 ≤ B v (A v)) {v : X} (hv : v ∈ A.stableSubspace) (hv0 : v ≠ 0) :
    B v v < 0 := by
  -- Identify `X` with a Euclidean space `F`, where `B` becomes `⟪S ·, ·⟫`.
  let F := EuclideanSpace ℝ (Fin (finrank ℝ X))
  let e : X ≃L[ℝ] F := .ofFinrankEq (finrank_euclideanSpace_fin (𝕜 := ℝ)).symm
  set B' : F →L[ℝ] F →L[ℝ] ℝ := B.bilinearComp (e.symm : F →L[ℝ] X) (e.symm : F →L[ℝ] X)
  set S : F →L[ℝ] F := InnerProductSpace.continuousLinearMapOfBilin B'
  have hS (u w : F) : ⟪S u, w⟫_ℝ = B (e.symm u) (e.symm w) :=
    InnerProductSpace.continuousLinearMapOfBilin_apply B' u w
  have hSsymm : (S : F →ₗ[ℝ] F).IsSymmetric := fun u w ↦ by
    simp only [coe_coe]
    rw [hS, real_inner_comm, hS, hB]
  set N := ‖(e : X →L[ℝ] F)‖
  have hN : 0 ≤ N := norm_nonneg _
  have hcS (u : F) : c / (N + 1) ^ 2 * ‖u‖ ^ 2 ≤
      ⟪S (e.conjContinuousAlgEquiv A u), u⟫_ℝ := by
    rw [hS, ContinuousLinearEquiv.conjContinuousAlgEquiv_apply_apply, e.symm_apply_apply, hB]
    have hu : ‖u‖ ≤ (N + 1) * ‖e.symm u‖ := by
      calc ‖u‖ = ‖(e : X →L[ℝ] F) (e.symm u)‖ := by simp
        _ ≤ N * ‖e.symm u‖ := le_opNorm _ _
        _ ≤ (N + 1) * ‖e.symm u‖ := by gcongr; linarith
    calc c / (N + 1) ^ 2 * ‖u‖ ^ 2 ≤ c / (N + 1) ^ 2 * ((N + 1) * ‖e.symm u‖) ^ 2 := by
          gcongr
      _ = c * ‖e.symm u‖ ^ 2 := by field_simp
      _ ≤ _ := hcB _
  have h := inner_apply_self_neg_of_mem_stableSubspace hSsymm (by positivity) hcS
    (e.apply_mem_stableSubspace_conjContinuousAlgEquiv_iff.2 hv) (e.map_ne_zero_iff.2 hv0)
  rwa [hS, e.symm_apply_apply] at h

/-- **A Lyapunov bilinear form is positive definite on the unstable subspace.** If `B` is
symmetric and `c * ‖v‖ ^ 2 ≤ B v (A v)` with `c > 0`, then `0 < B v v` for every nonzero unstable
`v`. -/
theorem apply_self_pos_of_mem_unstableSubspace (hB : ∀ u v, B u v = B v u) (hc : 0 < c)
    (hcB : ∀ v, c * ‖v‖ ^ 2 ≤ B v (A v)) {v : X} (hv : v ∈ A.unstableSubspace) (hv0 : v ≠ 0) :
    0 < B v v := by
  rw [← stableSubspace_neg] at hv
  have h := apply_self_neg_of_mem_stableSubspace (B := -B) (fun u w ↦ by simp [hB u w]) hc
    (fun w ↦ by simpa using hcB w) hv hv0
  simpa using h

/-- **An operator with a positive definite Lyapunov form has no nonzero stable vector.** If `B` is
symmetric and positive definite, and `0 < B v (A v)` for every nonzero `v`, then the stable
subspace of `A` is `⊥`. The bound `c * ‖v‖ ^ 2 ≤ B v (A v)` follows by compactness of the unit
sphere, and `B` would be negative on a nonzero stable vector. -/
theorem stableSubspace_eq_bot_of_apply_pos (hB : ∀ u v, B u v = B v u)
    (hBpos : ∀ v, v ≠ 0 → 0 < B v v) (hBA : ∀ v, v ≠ 0 → 0 < B v (A v)) :
    A.stableSubspace = ⊥ := by
  obtain ⟨c, hc, hcB⟩ := isCompact_singleton.exists_pos_forall_mul_norm_sq_le_compRight B
    (T := {A}) (by simpa using hBA)
  refine (Submodule.eq_bot_iff _).2 fun v hv ↦ by_contra fun hv0 ↦ ?_
  exact (apply_self_neg_of_mem_stableSubspace hB hc (hcB A rfl) hv hv0).not_gt (hBpos v hv0)

/-- **The inertia theorem for a Lyapunov bilinear form.** If `B` is symmetric and
`c * ‖v‖ ^ 2 ≤ B v (A v)` with `c > 0`, then the negative index of inertia of the quadratic form
`v ↦ B v v` is the dimension of the stable subspace of `A`. -/
theorem sigNeg_toQuadraticMap_eq_finrank_stableSubspace (hB : ∀ u v, B u v = B v u)
    (hc : 0 < c) (hcB : ∀ v, c * ‖v‖ ^ 2 ≤ B v (A v)) :
    sigNeg B.toBilinForm.toQuadraticMap = finrank ℝ A.stableSubspace := by
  obtain ⟨P, hP, hAP, K, α, -, hα, hs, hu⟩ :=
    exists_projection_exponential_bounds_of_le_apply hB hc hcB
  have hcompl := isCompl_stableSubspace_unstableSubspace_of_exponential_bounds (K := K)
    (α := α) hα hP hAP hs hu
  refine QuadraticForm.sigNeg_eq_finrank_of_isCompl_of_negDef _ hcompl ?_ fun v hv ↦ ?_
  · intro ⟨v, hv⟩ hv0
    have hv0' : v ≠ 0 := by simpa using hv0
    simpa using apply_self_neg_of_mem_stableSubspace hB hc hcB hv hv0'
  · rcases eq_or_ne v 0 with rfl | hv0
    · simp
    simpa using (apply_self_pos_of_mem_unstableSubspace hB hc hcB hv hv0).le

end ContinuousLinearMap
