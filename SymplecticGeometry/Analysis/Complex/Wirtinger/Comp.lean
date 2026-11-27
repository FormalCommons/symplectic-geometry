/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Basic

import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# The derivative of `∂̄ (g ∘ D)` after a holomorphic map

For a real-differentiable map `D : V → W` and a map `g : W → X` that is complex differentiable
near `D z`, Tau Ceti's `TauCeti.conjWirtingerDeriv_comp` gives `∂̄ (g ∘ D) = dg (D ·) ∘ ∂̄ D`
near `z`. This file differentiates that identity once more, by the product rule for composition
of operators (`HasFDerivAt.clm_comp`), and bounds the result. The defect `∂̄` is taken in the form
`ContinuousLinearMap.complexAntilinearPartL (fderiv ℝ D z)`, a real-linear map, so that its
derivative is a real derivative of a map into `V →L[ℝ] W`.

## Main results

* `TauCeti.norm_complexAntilinearPartL_fderiv`: the operator norm of
  `complexAntilinearPartL (fderiv ℝ D z)` is that of `conjWirtingerDeriv D z`.
* `TauCeti.complexAntilinearPartL_fderiv_comp`: `TauCeti.conjWirtingerDeriv_comp` for
  `complexAntilinearPartL` of the real derivative.
* `TauCeti.hasFDerivAt_complexAntilinearPartL_fderiv_comp`: for `D` real `C²` at `z` and `g`
  complex differentiable near `D z` and real `C²` at `D z`, the derivative of
  `w ↦ complexAntilinearPartL (fderiv ℝ (g ∘ D) w)` at `z` in the direction `a` is
  `D²g(D z)(dD z a) ∘ ∂̄ D z + dg(D z) ∘ d(∂̄ D)(z)(a)`.
* `TauCeti.norm_fderiv_complexAntilinearPartL_fderiv_comp_le`: the resulting pointwise bound
  `‖d(∂̄ (g ∘ D))(z)‖ ≤ ‖D²g(D z)‖ ‖dD z‖ ‖∂̄ D z‖ + ‖dg(D z)‖ ‖d(∂̄ D)(z)‖`.
* `TauCeti.exists_norm_fderiv_complexAntilinearPartL_fderiv_comp_le`: for `g` holomorphic and
  real `C²` on an open set `O`, a compact `K ⊆ O` and a bound `B`, there is `C` with
  `‖d(∂̄ (g ∘ D))(z)‖ ≤ C (‖∂̄ D z‖ + ‖d(∂̄ D)(z)‖)` at every point `z` of the open set where `D`
  is `C²` with `D z ∈ K` and `‖dD z‖ ≤ B`. Thus a holomorphic change of coordinates, defined near
  a compact set, keeps the derivative of `∂̄` of a map small where `∂̄` and its derivative are
  small and the derivative of the map is bounded.

## References

* [K. Cieliebak, Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012]:
  the proof of Proposition 5.55 composes its charts with holomorphic maps.
-/

public section

namespace TauCeti

open ContinuousLinearMap Filter Topology

variable {V W X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] [NormedAddCommGroup X] [NormedSpace ℂ X] {g : W → X} {D : V → W} {z : V}

/-- The complex-antilinear part of the real derivative, as a real-linear map, has the operator
norm of the conjugate Wirtinger derivative. -/
theorem norm_complexAntilinearPartL_fderiv (D : V → W) (z : V) :
    ‖complexAntilinearPartL (fderiv ℝ D z)‖ = ‖conjWirtingerDeriv D z‖ := by
  refine le_antisymm (opNorm_le_bound _ (norm_nonneg _) fun v ↦ ?_)
    (opNorm_le_bound _ (norm_nonneg _) fun v ↦ ?_)
  · rw [← conjWirtingerDeriv_apply_eq_complexAntilinearPartL]
    exact le_opNorm _ v
  · rw [conjWirtingerDeriv_apply_eq_complexAntilinearPartL]
    exact le_opNorm _ v

/-- For `g` complex differentiable at `D z` and `D` real differentiable at `z`, the
complex-antilinear part of the real derivative of `g ∘ D` at `z` is `dg (D z) ∘ ∂̄ D z`: the form
of `TauCeti.conjWirtingerDeriv_comp` for `ContinuousLinearMap.complexAntilinearPartL`. -/
theorem complexAntilinearPartL_fderiv_comp (hg : DifferentiableAt ℂ g (D z))
    (hD : DifferentiableAt ℝ D z) :
    complexAntilinearPartL (fderiv ℝ (g ∘ D) z) =
      (fderiv ℝ g (D z)).comp (complexAntilinearPartL (fderiv ℝ D z)) := by
  rw [fderiv_comp z (hg.restrictScalars ℝ) hD, hg.fderiv_restrictScalars ℝ,
    complexAntilinearPartL_restrictScalars_comp]

/-- **The derivative of `∂̄ (g ∘ D)`.** For `D` real `C²` at `z`, and `g` complex differentiable
near `D z` and real `C²` at `D z`, the derivative at `z` of
`w ↦ complexAntilinearPartL (fderiv ℝ (g ∘ D) w)` in the direction `a` is
`D²g(D z)(dD z a) ∘ ∂̄ D z + dg(D z) ∘ d(∂̄ D)(z)(a)`. -/
theorem hasFDerivAt_complexAntilinearPartL_fderiv_comp
    (hg : ∀ᶠ w in 𝓝 (D z), DifferentiableAt ℂ g w) (hg₂ : ContDiffAt ℝ 2 g (D z))
    (hD : ContDiffAt ℝ 2 D z) :
    HasFDerivAt (fun w ↦ complexAntilinearPartL (fderiv ℝ (g ∘ D) w))
      ((compL ℝ V W X (fderiv ℝ g (D z))).comp
          (fderiv ℝ (fun w ↦ complexAntilinearPartL (fderiv ℝ D w)) z) +
        ((compL ℝ V W X).flip (complexAntilinearPartL (fderiv ℝ D z))).comp
          ((fderiv ℝ (fderiv ℝ g) (D z)).comp (fderiv ℝ D z))) z := by
  have hD₁ : ∀ᶠ w in 𝓝 z, DifferentiableAt ℝ D w :=
    (hD.eventually (by simp)).mono fun w hw ↦ hw.differentiableAt (by norm_num)
  have hdD : DifferentiableAt ℝ (fderiv ℝ D) z :=
    (hD.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdg : DifferentiableAt ℝ (fderiv ℝ g) (D z) :=
    (hg₂.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hc : HasFDerivAt (fun w ↦ fderiv ℝ g (D w))
      ((fderiv ℝ (fderiv ℝ g) (D z)).comp (fderiv ℝ D z)) z :=
    hdg.hasFDerivAt.comp z (hD.differentiableAt (by norm_num)).hasFDerivAt
  -- `show` states the composite in the form `fun w ↦ _` of the goal, not as `_ ∘ _`.
  have hd : HasFDerivAt (fun w ↦ complexAntilinearPartL (fderiv ℝ D w))
      (fderiv ℝ (fun w ↦ complexAntilinearPartL (fderiv ℝ D w)) z) z :=
    (show DifferentiableAt ℝ (fun w ↦ complexAntilinearPartL (fderiv ℝ D w)) z from
      (complexAntilinearPartL (E := V) (F := W)).differentiableAt.comp z hdD).hasFDerivAt
  refine (hc.clm_comp hd).congr_of_eventuallyEq ?_
  filter_upwards [hD.continuousAt.eventually hg, hD₁] with w hgw hDw
  exact complexAntilinearPartL_fderiv_comp hgw hDw

/-- For `D` real `C²` at `z`, and `g` complex differentiable near `D z` and real `C²` at `D z`,
the derivative of `∂̄ (g ∘ D)` at `z` is at most
`‖D²g(D z)‖ ‖dD z‖ ‖∂̄ D z‖ + ‖dg(D z)‖ ‖d(∂̄ D)(z)‖`, with `∂̄` written as
`complexAntilinearPartL` of the real derivative where it is differentiated. -/
theorem norm_fderiv_complexAntilinearPartL_fderiv_comp_le
    (hg : ∀ᶠ w in 𝓝 (D z), DifferentiableAt ℂ g w) (hg₂ : ContDiffAt ℝ 2 g (D z))
    (hD : ContDiffAt ℝ 2 D z) :
    ‖fderiv ℝ (fun w ↦ complexAntilinearPartL (fderiv ℝ (g ∘ D) w)) z‖ ≤
      ‖fderiv ℝ (fderiv ℝ g) (D z)‖ * ‖fderiv ℝ D z‖ * ‖conjWirtingerDeriv D z‖ +
        ‖fderiv ℝ g (D z)‖ * ‖fderiv ℝ (fun w ↦ complexAntilinearPartL (fderiv ℝ D w)) z‖ := by
  rw [(hasFDerivAt_complexAntilinearPartL_fderiv_comp hg hg₂ hD).fderiv,
    ← norm_complexAntilinearPartL_fderiv]
  set dg := fderiv ℝ g (D z)
  set d2g := fderiv ℝ (fderiv ℝ g) (D z)
  set dD := fderiv ℝ D z
  set A := complexAntilinearPartL dD
  set dA := fderiv ℝ (fun w ↦ complexAntilinearPartL (fderiv ℝ D w)) z
  refine opNorm_le_bound _ (by positivity) fun a ↦ ?_
  simp only [add_apply, coe_comp, Function.comp_apply, compL_apply, flip_apply]
  calc ‖dg.comp (dA a) + (d2g (dD a)).comp A‖
      ≤ ‖dg‖ * (‖dA‖ * ‖a‖) + ‖d2g‖ * (‖dD‖ * ‖a‖) * ‖A‖ :=
        (norm_add_le _ _).trans (add_le_add
          ((opNorm_comp_le _ _).trans (by gcongr; exact le_opNorm _ _))
          ((opNorm_comp_le _ _).trans (by
            gcongr; exact (d2g.le_opNorm _).trans (by gcongr; exact dD.le_opNorm a))))
    _ = (‖d2g‖ * ‖dD‖ * ‖A‖ + ‖dg‖ * ‖dA‖) * ‖a‖ := by ring

/-- **The derivative of `∂̄ (g ∘ D)` near a compact set.** Let `D` be real `C²` on an open set
`U`, and `g` be complex differentiable and real `C²` on an open set `O` containing a compact set
`K`. For every bound `B` there is `C` such that, at every `z ∈ U` with `D z ∈ K` and
`‖dD z‖ ≤ B`, the derivative of `∂̄ (g ∘ D)` at `z` is at most `C (‖∂̄ D z‖ + ‖d(∂̄ D)(z)‖)`, with
`∂̄` written as `complexAntilinearPartL` of the real derivative where it is differentiated. -/
theorem exists_norm_fderiv_complexAntilinearPartL_fderiv_comp_le {U : Set V} {O K : Set W}
    (hU : IsOpen U) (hD : ContDiffOn ℝ 2 D U) (hO : IsOpen O) (hg : DifferentiableOn ℂ g O)
    (hg₂ : ContDiffOn ℝ 2 g O) (hK : IsCompact K) (hKO : K ⊆ O) (B : ℝ) :
    ∃ C, ∀ z ∈ U, D z ∈ K → ‖fderiv ℝ D z‖ ≤ B →
      ‖fderiv ℝ (fun w ↦ complexAntilinearPartL (fderiv ℝ (g ∘ D) w)) z‖ ≤
        C * (‖conjWirtingerDeriv D z‖ +
          ‖fderiv ℝ (fun w ↦ complexAntilinearPartL (fderiv ℝ D w)) z‖) := by
  obtain ⟨M₁, hM₁⟩ := hK.exists_bound_of_continuousOn
    ((hg₂.continuousOn_fderiv_of_isOpen hO (by norm_num)).mono hKO)
  obtain ⟨M₂, hM₂⟩ := hK.exists_bound_of_continuousOn
    (((hg₂.fderiv_of_isOpen hO (m := 1) (by norm_num)).continuousOn_fderiv_of_isOpen hO
      le_rfl).mono hKO)
  refine ⟨M₂ * |B| + M₁, fun z hz hDz hB ↦ ?_⟩
  have hgz : ∀ᶠ w in 𝓝 (D z), DifferentiableAt ℂ g w :=
    eventually_of_mem (hO.mem_nhds (hKO hDz)) fun w hw ↦ hg.differentiableAt (hO.mem_nhds hw)
  refine (norm_fderiv_complexAntilinearPartL_fderiv_comp_le hgz
    (hg₂.contDiffAt (hO.mem_nhds (hKO hDz))) (hD.contDiffAt (hU.mem_nhds hz))).trans ?_
  have h₁ := hM₁ _ hDz
  have h₂ := hM₂ _ hDz
  have h₀ : 0 ≤ ‖fderiv ℝ (fderiv ℝ g) (D z)‖ * ‖fderiv ℝ D z‖ :=
    mul_nonneg (norm_nonneg (fderiv ℝ (fderiv ℝ g) (D z))) (norm_nonneg (fderiv ℝ D z))
  have h₃ : ‖fderiv ℝ (fderiv ℝ g) (D z)‖ * ‖fderiv ℝ D z‖ ≤ M₂ * |B| :=
    mul_le_mul h₂ (hB.trans (le_abs_self B)) (norm_nonneg (fderiv ℝ D z))
      ((norm_nonneg (fderiv ℝ (fderiv ℝ g) (D z))).trans h₂)
  have h₅ : 0 ≤ ‖fderiv ℝ g (D z)‖ := norm_nonneg (fderiv ℝ g (D z))
  have ha := norm_nonneg (conjWirtingerDeriv D z)
  have hb := norm_nonneg (fderiv ℝ (fun w ↦ complexAntilinearPartL (fderiv ℝ D w)) z)
  nlinarith

end TauCeti

end
