/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Basic

import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Normed.Group.Bounded
import SymplecticGeometry.Analysis.Calculus.IteratedFDeriv.ArrowCongr
import SymplecticGeometry.Analysis.Normed.Operator.ComplexLinearPart
import TauCeti.Topology.Algebra.Module.Equiv.RestrictScalars

/-!
# `∂̄ (g ∘ D)` and its derivative after a holomorphic map

For a real-differentiable map `D : V → W` and a map `g : W → X` that is complex differentiable
near `D z`, Tau Ceti's `TauCeti.conjWirtingerDeriv_comp` gives `∂̄ (g ∘ D) = dg (D ·) ∘ ∂̄ D`
near `z`. When `g` is complex `C¹` at `D z`, the norm of `dg` stays below `‖dg (D z)‖ + 1` near
`z`, so a bound on `‖∂̄ D‖` near `z` gives one of the same form on `‖∂̄ (g ∘ D)‖`.

This file also differentiates that identity once more, by the product rule for composition
of operators (`HasFDerivAt.clm_comp`), and bounds the result. The defect `∂̄` is taken in the form
`ContinuousLinearMap.complexAntilinearPartL (fderiv ℝ D z)`, a real-linear map, so that its
derivative is a real derivative of a map into `V →L[ℝ] W`.

The file ends with `∂̄` and its derivative before a complex-linear change of variables, which
need no differentiability. The bound on the derivative is the case of order one of
`ContinuousLinearEquiv.norm_iteratedFDeriv_arrowCongr_comp_le`.

## Main results

* `TauCeti.eventually_norm_conjWirtingerDeriv_comp_le`: for `g` complex `C¹` at `D z` and a
  bound `‖∂̄ D‖ ≤ b` near `z`, the bound `‖∂̄ (g ∘ D)‖ ≤ (‖dg (D z)‖ + 1) b` near `z`.
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
* `TauCeti.complexAntilinearPartL_fderiv_comp_continuousLinearEquiv`: the complex-antilinear
  part of the real derivative of `g ∘ L`, for a complex-linear equivalence `L`.
* `TauCeti.norm_fderiv_complexAntilinearPartL_fderiv_comp_continuousLinearEquiv_le`: before a
  complex-linear equivalence `L`, the derivative of `∂̄` grows at most by `‖L‖ ^ 2`.

## References

* [K. Cieliebak, Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012]:
  the proof of Proposition 5.55 composes its charts with holomorphic maps.
-/

public section

namespace TauCeti

open ContinuousLinearMap Filter Topology

variable {V W X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] [NormedAddCommGroup X] [NormedSpace ℂ X] {g : W → X} {D : V → W} {z : V}

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
    conjWirtingerDeriv_eq_complexAntilinearPart, ← (fderiv ℝ D z).norm_complexAntilinearPartL_apply]
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
  refine (norm_fderiv_complexAntilinearPartL_fderiv_comp_le
    (hg.eventually_differentiableAt (hO.mem_nhds (hKO hDz)))
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

/-- **The bound on `∂̄ (g ∘ D)` near a point.** Let `g` be complex `C¹` at `D z`, and let `D` be
real differentiable near `z`. If `‖∂̄ D‖ ≤ b` near `z`, then
`‖∂̄ (g ∘ D)‖ ≤ (‖dg (D z)‖ + 1) b` near `z`. -/
theorem eventually_norm_conjWirtingerDeriv_comp_le (hg : ContDiffAt ℂ 1 g (D z))
    (hD : ∀ᶠ w in 𝓝 z, DifferentiableAt ℝ D w) {b : V → ℝ}
    (hb : ∀ᶠ w in 𝓝 z, ‖conjWirtingerDeriv D w‖ ≤ b w) :
    ∀ᶠ w in 𝓝 z, ‖conjWirtingerDeriv (g ∘ D) w‖ ≤ (‖fderiv ℂ g (D z)‖ + 1) * b w := by
  have hDc : ContinuousAt D z := hD.self_of_nhds.continuousAt
  have hgd : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ g (D w) :=
    hDc.eventually ((hg.eventually (by simp)).mono fun _ hy ↦ hy.differentiableAt one_ne_zero)
  have hgc : ∀ᶠ w in 𝓝 z, ‖fderiv ℂ g (D w)‖ < ‖fderiv ℂ g (D z)‖ + 1 :=
    ((hg.continuousAt_fderiv one_ne_zero).comp hDc).norm.eventually (gt_mem_nhds (lt_add_one _))
  filter_upwards [hgd, hgc, hD, hb] with w hgw hcw hDw hbw
  rw [conjWirtingerDeriv_comp hgw hDw]
  refine (opNorm_comp_le _ _).trans ?_
  calc _ ≤ (‖fderiv ℂ g (D z)‖ + 1) * ‖conjWirtingerDeriv D w‖ := by gcongr
    _ ≤ _ := by gcongr

/-- For a complex-linear equivalence `L`, the complex-antilinear part of the real derivative of
`g ∘ L` at `y` is that of `g` at `L y`, composed with `L`: the form of Tau Ceti's
`TauCeti.conjWirtingerDeriv_comp_continuousLinearEquiv` for
`ContinuousLinearMap.complexAntilinearPartL`. No differentiability is needed. -/
theorem complexAntilinearPartL_fderiv_comp_continuousLinearEquiv (L : V ≃L[ℂ] W) (g : W → X)
    (y : V) :
    complexAntilinearPartL (fderiv ℝ (g ∘ L) y) =
      (complexAntilinearPartL (fderiv ℝ g (L y))).comp ((L : V →L[ℂ] W).restrictScalars ℝ) := by
  ext v
  simpa [← restrictScalarsₛₗLI_comp_complexAntilinearPartCLM,
    ← conjWirtingerDeriv_eq_complexAntilinearPart]
    using DFunLike.congr_fun (conjWirtingerDeriv_comp_continuousLinearEquiv L g y) v

/-- **The derivative of `∂̄` before a complex-linear change of variables, in norm.** For a
complex-linear equivalence `L`, the derivative at `x` of
`y ↦ complexAntilinearPartL (fderiv ℝ (g ∘ L) y)` has norm at most `‖L‖ ^ 2` times that of
`w ↦ complexAntilinearPartL (fderiv ℝ g w)` at `L x`. No differentiability is needed. -/
theorem norm_fderiv_complexAntilinearPartL_fderiv_comp_continuousLinearEquiv_le
    (L : V ≃L[ℂ] W) (g : W → X) (x : V) :
    ‖fderiv ℝ (fun y ↦ complexAntilinearPartL (fderiv ℝ (g ∘ L) y)) x‖ ≤
      ‖(L : V →L[ℂ] W)‖ ^ 2 *
        ‖fderiv ℝ (fun w ↦ complexAntilinearPartL (fderiv ℝ g w)) (L x)‖ := by
  set Lr : W ≃L[ℝ] V := (L.restrictScalars' ℝ).symm
  have hLr : ⇑(L.restrictScalars' ℝ : V ≃L[ℝ] W) = ⇑L :=
    ContinuousLinearEquiv.coe_restrictScalars' _ _
  have hLc : ((L.restrictScalars' ℝ : V ≃L[ℝ] W) : V →L[ℝ] W) =
      (L : V →L[ℂ] W).restrictScalars ℝ := by
    ext v
    simp
  set F : W → W →L[ℝ] X := fun w ↦ complexAntilinearPartL (fderiv ℝ g w)
  have hf : (fun y ↦ complexAntilinearPartL (fderiv ℝ (g ∘ L) y)) =
      fun y ↦ Lr.arrowCongr (.refl ℝ X) (F (Lr.symm y + 0)) := by
    funext y
    rw [complexAntilinearPartL_fderiv_comp_continuousLinearEquiv, add_zero]
    ext v
    simp [Lr, F, hLr]
  have h := Lr.norm_iteratedFDeriv_arrowCongr_comp_le (.refl ℝ X) F 0 1 x
  rw [← hf, norm_iteratedFDeriv_one, norm_iteratedFDeriv_one, add_zero] at h
  refine h.trans ?_
  have hn : ‖(Lr.symm : V →L[ℝ] W)‖ = ‖(L : V →L[ℂ] W)‖ := by
    rw [ContinuousLinearEquiv.symm_symm, hLc, ContinuousLinearMap.norm_restrictScalars]
  rw [hn, show Lr.symm x = L x by simp [Lr, hLr]]
  calc _ ≤ 1 * ‖(L : V →L[ℂ] W)‖ ^ 2 * ‖fderiv ℝ F (L x)‖ := by
        gcongr
        exact ContinuousLinearMap.norm_id_le
    _ = _ := by ring

end TauCeti

end
