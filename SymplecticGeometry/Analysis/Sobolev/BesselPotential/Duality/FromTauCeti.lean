/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.BesselPotential.Duality
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Bounded functionals on `H^t` are in `H^{-t}`

A scalar tempered distribution `u` with `‖u φ‖ ≤ C ‖φ‖_{H^t}` for every Schwartz function `φ`
lies in the Bessel-potential space `H^{-t}` (`TemperedDistribution.memSobolev_neg_of_norm_le`).

This declaration is from Tau Ceti's main branch
(`TauCeti/Analysis/Sobolev/BesselPotential/Duality.lean`, same name), as of the commit
`149af18a4eb25c41e443e1077353504afb3428b3`, not yet in the pinned release. It is stated here under
its Tau Ceti name and namespace, so that moving Tau Ceti past it deletes this file without renames.
This file is a part of that file, with only this declaration.

The one change is in the proof: at that commit `BesselPotentialSpace.dualEquiv` and
`BesselPotentialSpace.dualEquiv_apply_eq_integral` take the exponents `p q` and the hypotheses
`1 < p` and `p ≠ ∞`, while the pinned version has only the `L²` case, `dualEquiv s`. So
`dualEquiv t 2 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top` is written `dualEquiv t`.

## References

* G. B. Folland, *Real Analysis: Modern Techniques and Their Applications*, 2nd ed., Wiley, 1999,
  §9.3 (the dual of `H_s` is `H_{-s}` under the extension of the bilinear pairing of Schwartz
  functions).
* M. E. Taylor, *Partial Differential Equations I*, 2nd ed., Springer, 2011, Chapter 4, §1.
* J. Bergh, J. Löfström, *Interpolation Spaces: An Introduction*, Springer, 1976, §6.2 (the dual
  of `H^{s,p}` is `H^{-s,q}`).
-/

public section

noncomputable section

open MeasureTheory FourierTransform
open scoped ENNReal SchwartzMap BesselPotentialSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

namespace TemperedDistribution

/-- **Bounded functionals on `H^t` are in `H^{-t}`.** A scalar tempered distribution `u` with
`‖u φ‖ ≤ C ‖φ‖_{H^t}` for every Schwartz function `φ` lies in `H^{-t}`: it extends to a functional
on `H^t`, which `BesselPotentialSpace.dualEquiv` writes as the density pairing with an element of
`H^{-t}`. -/
theorem memSobolev_neg_of_norm_le {u : 𝓢'(E, ℂ)} {t C : ℝ}
    (hu : ∀ φ : 𝓢(E, ℂ), ‖u φ‖ ≤ C * ‖SchwartzMap.toBesselPotentialSpaceCLM t 2 φ‖) :
    u.MemSobolev (-t) 2 := by
  set A := (SchwartzMap.toBesselPotentialSpaceCLM t 2 : 𝓢(E, ℂ) →L[ℂ] H^{t}(E, ℂ)).toLinearMap
  -- Schwartz functions are dense in `H^t`, so `A φ ↦ u φ` extends to a functional `ℓ` on `H^t`.
  set ℓ := (u : 𝓢(E, ℂ) →L[ℂ] ℂ).toLinearMap.extendOfNorm A
  have hℓA (φ : 𝓢(E, ℂ)) : ℓ (A φ) = u φ :=
    LinearMap.extendOfNorm_eq
      (SchwartzMap.denseRange_toBesselPotentialSpaceCLM (p := 2) t ENNReal.ofNat_ne_top) ⟨C, hu⟩ φ
  -- By duality, `ℓ` is the density pairing with some `w ∈ H^{-t}(E, ℂ⋆)`; evaluating `w` at `1`
  -- pointwise gives a scalar element `v ∈ H^{-t}(E, ℂ)`.
  set w := (BesselPotentialSpace.dualEquiv t).symm ℓ
  obtain ⟨v, hv⟩ : ∃ v : H^{-t}(E, ℂ), ∀ᵐ x, v.toLp x = w.toLp x 1 :=
    ⟨BesselPotentialSpace.ofLp (-t) ((ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).compLp w.toLp),
      by simpa using (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).coeFn_compLp w.toLp⟩
  convert BesselPotentialSpace.memSobolev_toDistr v using 1
  ext φ
  have hw : BesselPotentialSpace.dualEquiv t w (A φ) = u φ := by
    rw [LinearIsometryEquiv.apply_symm_apply, hℓA]
  rw [← hw, BesselPotentialSpace.dualEquiv_apply_eq_integral,
    BesselPotentialSpace.toDistr_apply_eq_besselPotentialPairing (q := 2),
    ContinuousLinearMap.besselPotentialPairing_apply, neg_neg]
  refine integral_congr_ae (hv.mono fun x hx ↦ ?_)
  simp [A, hx]

end TemperedDistribution
