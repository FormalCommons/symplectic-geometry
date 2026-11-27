/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Basic

import Mathlib.Analysis.Calculus.ContDiff.Operations
import SymplecticGeometry.Analysis.Calculus.IteratedFDeriv.VanishingOrder

/-!
# Maps whose conjugate Wirtinger derivative vanishes to a given order

If `f : E → W` between complex normed spaces is `C^(k + 1)` over `ℝ` at `x`, and its conjugate
Wirtinger derivative is `O(‖z - x‖ ^ N)` near `x` with `k < N`, then the iterated derivative of
order `k` of `fderiv ℝ f` at `x` takes complex-linear values: the antilinear part of the real
derivative vanishes to order `N` at `x`, so its derivatives of order `k` vanish there
(`ContDiffAt.iteratedFDeriv_eq_zero_of_isBigO_pow`).

## Main results

* `ContDiffAt.iteratedFDeriv_fderiv_apply_I_smul_of_isBigO_conjWirtingerDeriv`: under these
  hypotheses, `D^k (Df)(x) a (I • w) = I • D^k (Df)(x) a w`.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  proof of Proposition 5.55, where this step is used.
-/

public section

open Asymptotics Filter TauCeti
open scoped Topology

variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup W]
  [NormedSpace ℂ W]

/-- If `f` is `C^(k + 1)` over `ℝ` at `x` and its conjugate Wirtinger derivative is
`O(‖z - x‖ ^ N)` near `x`, with `k < N`, then the iterated derivative of order `k` of
`fderiv ℝ f` at `x` takes complex-linear values. -/
theorem ContDiffAt.iteratedFDeriv_fderiv_apply_I_smul_of_isBigO_conjWirtingerDeriv
    {f : E → W} {x : E} {N k : ℕ} (hf : ContDiffAt ℝ (k + 1) f x)
    (hO : (fun z ↦ conjWirtingerDeriv f z) =O[𝓝 x] fun z ↦ ‖z - x‖ ^ N) (hk : k < N)
    (a : Fin k → E) (w : E) :
    iteratedFDeriv ℝ k (fderiv ℝ f) x a (Complex.I • w) =
      Complex.I • iteratedFDeriv ℝ k (fderiv ℝ f) x a w := by
  set A := ContinuousLinearMap.complexAntilinearPartL (E := E) (F := W)
  have hfd : ContDiffAt ℝ k (fderiv ℝ f) x := hf.fderiv_right le_rfl
  have hg : ContDiffAt ℝ k (A ∘ fderiv ℝ f) x := A.contDiff.contDiffAt.comp x hfd
  -- `‖A (Df z)‖ ≤ ‖\bar∂f z‖`, so the antilinear part of `Df` is `O(‖z - x‖ ^ N)` too.
  have hA : (A ∘ fderiv ℝ f) =O[𝓝 x] fun z ↦ conjWirtingerDeriv f z :=
    IsBigO.of_bound 1 <| Eventually.of_forall fun z ↦ by
      rw [one_mul]
      refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v ↦ ?_
      rw [Function.comp_apply, ← conjWirtingerDeriv_apply_eq_complexAntilinearPartL]
      exact (conjWirtingerDeriv f z).le_opNorm v
  have h0 := hg.iteratedFDeriv_eq_zero_of_isBigO_pow (hA.trans hO) le_rfl hk
  rw [A.iteratedFDeriv_comp_left hfd le_rfl] at h0
  exact ContinuousLinearMap.complexAntilinearPartL_eq_zero_iff.1 congr($h0 a) w

end
