/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Sobolev.BesselPotential.Duality
import Mathlib.Analysis.Normed.Operator.Extend
import TauCeti.Analysis.Sobolev.BesselPotential.Postcomp

/-!
# Tempered distributions that are bounded functionals on `H^s`

Let `E` be a finite-dimensional real inner product space and `s` a real number. A scalar tempered
distribution `u` that satisfies `‖u ψ‖ ≤ C ‖ψ‖_{H^s}` for every Schwartz function `ψ`, with
`0 ≤ C`, is an element of `H^{-s}` with `‖u‖_{H^{-s}} ≤ C`. Schwartz functions are dense in
`H^s`, so `u` extends to a continuous functional on `H^s`. Tau Ceti's duality
`BesselPotentialSpace.dualEquiv` represents this functional by an element of `H^{-s}(E, ℂ⋆)`.
Evaluating at `1` (`BesselPotentialSpace.postcomp`) turns it into an element of `H^{-s}(E)`, which
is `u` as a distribution, and whose norm is no larger.

That `u` lies in `H^{-s}` is Tau Ceti's `TemperedDistribution.memSobolev_neg_of_norm_le`, from
Tau Ceti's main branch (commit `149af18a4e`), copied into
`SymplecticGeometry.Analysis.Sobolev.BesselPotential.Duality.FromTauCeti`. The proof here adapts
that proof and adds the norm bound, which it bounds as the proof of Tau Ceti's
`BesselPotentialSpace.exists_inclusion_eq_and_norm_le` bounds the norm of its extension.

## Main results

* `BesselPotentialSpace.exists_toDistr_eq_and_norm_le`: for `0 ≤ C`, such a `u` is the
  distribution of an element of `H^{-s}(E)` of norm at most `C`.

## References

* G. B. Folland, *Real Analysis: Modern Techniques and Their Applications*, 2nd ed., Wiley, 1999,
  §9.3 (the dual of `H_s` is `H_{-s}`).
-/

public section

open MeasureTheory
open scoped SchwartzMap BesselPotentialSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

namespace BesselPotentialSpace

open SchwartzMap

/-- **A duality criterion for `H^{-s}`.** If a scalar tempered distribution `u` satisfies
`‖u ψ‖ ≤ C ‖ψ‖_{H^s}` for every Schwartz function `ψ`, with `0 ≤ C`, then `u` is the distribution
of an element of `H^{-s}(E)` of norm at most `C`. -/
theorem exists_toDistr_eq_and_norm_le {s C : ℝ} (hC : 0 ≤ C) {u : 𝓢'(E, ℂ)}
    (hu : ∀ ψ : 𝓢(E, ℂ), ‖u ψ‖ ≤ C * ‖toBesselPotentialSpaceCLM s 2 ψ‖) :
    ∃ v : H^{-s}(E), v.toDistr = u ∧ ‖v‖ ≤ C := by
  have hdense := denseRange_toBesselPotentialSpaceCLM (E := E) (F := ℂ) (p := 2) s
    ENNReal.ofNat_ne_top
  -- Extend `u` by density to a functional `Λ` on `H^s`, of norm at most `C`.
  set Λ := (u : 𝓢(E, ℂ) →ₗ[ℂ] ℂ).extendOfNorm (toBesselPotentialSpaceCLM s 2).toLinearMap
  have hΛ (ψ : 𝓢(E, ℂ)) : Λ (toBesselPotentialSpaceCLM s 2 ψ) = u ψ :=
    LinearMap.extendOfNorm_eq hdense ⟨C, hu⟩ ψ
  -- Represent `Λ` in `H^{-s}(E, ℂ⋆)`, and evaluate pointwise at `1`.
  set w := (dualEquiv (E := E) (F := ℂ) s).symm Λ
  let T : StrongDual ℂ ℂ →L[ℂ] ℂ := ContinuousLinearMap.apply ℂ ℂ 1
  refine ⟨postcomp E (-s) 2 T w, ?_, ?_⟩
  · ext ψ
    rw [toDistr_apply_eq_besselPotentialPairing 2,
      ContinuousLinearMap.besselPotentialPairing_apply, ← hΛ,
      ← (dualEquiv s).apply_symm_apply Λ, dualEquiv_apply_eq_integral, neg_neg, toLp_postcomp]
    refine integral_congr_ae ?_
    filter_upwards [T.coeFn_compLp w.toLp] with x hx
    simp [hx, T, w]
  · have hT : ‖T‖ ≤ 1 := T.opNorm_le_bound zero_le_one fun f ↦ by simpa [T] using f.le_opNorm 1
    rw [← norm_toLp_eq, toLp_postcomp]
    refine (T.norm_compLp_le w.toLp).trans ?_
    rw [norm_toLp_eq, LinearIsometryEquiv.norm_map]
    exact (mul_le_of_le_one_left (norm_nonneg _) hT).trans
      (LinearMap.opNorm_extendOfNorm_le hdense hC hu)

end BesselPotentialSpace
