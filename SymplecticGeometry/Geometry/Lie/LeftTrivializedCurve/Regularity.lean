/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Lie.LeftTrivializedCurve.Deriv
public import TauCeti.Geometry.Manifold.Flow.TimeDependent
import TauCeti.Geometry.Manifold.IntegralCurve.Regularity
import SymplecticGeometry.Geometry.Manifold.Flow.TimeDependent

/-!
# Regularity of curves with a prescribed left-trivialized derivative

Let `G` be a Lie group over `ℝ` with model space `E`, so that its Lie algebra
`GroupLieAlgebra I G` is `E`. If a curve `g : ℝ → G` has left-trivialized derivative `ξ` on a
set `s` of times (`HasLeftTrivializedDerivOn g ξ s`), then `g' t` is the value at `g t` of the
left-invariant vector field of `ξ t`, so `g` solves on `s` the time-dependent equation of the
field `X t x = mulInvariantVectorField (ξ t) x`, and `t ↦ (t, g t)` is an integral curve on `s`
of its suspension `TauCeti.timeDependentSuspensionField X` on `ℝ × G`
(the first of the main results below).

When `ξ` is `C^n`, the field `X` is jointly `C^n` by Tau Ceti's
`contMDiff_mulInvariantVectorField_modelSpace`, hence so is its suspension, and Tau Ceti's
regularity of integral curves (`TauCeti.Manifold.contMDiff_succ_of_isMIntegralCurve`) shows
that the lifted curve, and so `g`, is `C^(n + 1)`. Taking every `n` shows that `g` is smooth
when `ξ` is. No completeness of `E` and no existence theorem is needed:
the curve is given.

## Main results

All in the namespace `SymplecticGeometry.HasLeftTrivializedDerivOn`:

* `isMIntegralCurveOn_prodMk_timeDependentSuspensionField_mulInvariantVectorField`: a curve
  with left-trivialized derivative `ξ` on a set of times, lifted through its clock, is an
  integral curve on that set of the suspension of the left-invariant fields of `ξ`.
* `isMIntegralCurve_prodMk_timeDependentSuspensionField_mulInvariantVectorField`: the same at
  every time.
* `contMDiff_succ`: if `ξ` is `C^n`, a curve with left-trivialized derivative `ξ` at every time
  is `C^(n + 1)`.
* `contMDiff`: if `ξ` is smooth, so is the curve.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  Theorem 9.48 (time-dependent flows, through the suspension on `ℝ × M`).
-/

public section

open Bundle Set TauCeti TauCeti.Manifold
open scoped ContDiff Manifold

namespace SymplecticGeometry.HasLeftTrivializedDerivOn

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]

/-- **A curve with left-trivialized derivative `ξ` lifts to an integral curve.** If `g : ℝ → G`
has left-trivialized derivative `ξ` on a set `s` of times, then `t ↦ (t, g t)` is an integral
curve on `s`, in `ℝ × G`, of the suspension of the time-dependent vector field
`(t, x) ↦ mulInvariantVectorField (ξ t) x`. -/
theorem isMIntegralCurveOn_prodMk_timeDependentSuspensionField_mulInvariantVectorField
    [ContMDiffMul I 1 G] {ξ : ℝ → E} {g : ℝ → G} {s : Set ℝ}
    (hg : HasLeftTrivializedDerivOn (I := I) g ξ s) :
    IsMIntegralCurveOn (fun t ↦ (t, g t))
      (timeDependentSuspensionField fun t x ↦ mulInvariantVectorField (I := I) (ξ t) x) s :=
  fun t ht ↦ hasMFDerivWithinAt_prodMk_timeDependentSuspensionField
    (hasLeftTrivializedDerivOn_iff.mp hg t ht)

/-- **A curve with left-trivialized derivative `ξ` at every time lifts to an integral curve.**
If `g : ℝ → G` has left-trivialized derivative `ξ` at every time, then `t ↦ (t, g t)` is an
integral curve on `ℝ × G` of the suspension of the time-dependent vector field
`(t, x) ↦ mulInvariantVectorField (ξ t) x`. -/
theorem isMIntegralCurve_prodMk_timeDependentSuspensionField_mulInvariantVectorField
    [ContMDiffMul I 1 G] {ξ : ℝ → E} {g : ℝ → G}
    (hg : HasLeftTrivializedDerivOn (I := I) g ξ univ) :
    IsMIntegralCurve (fun t ↦ (t, g t))
      (timeDependentSuspensionField fun t x ↦ mulInvariantVectorField (I := I) (ξ t) x) :=
  isMIntegralCurve_iff_isMIntegralCurveOn.mpr
    hg.isMIntegralCurveOn_prodMk_timeDependentSuspensionField_mulInvariantVectorField

variable [BoundarylessManifold I G]

/-- **Curves with a `C^n` left-trivialized derivative are `C^(n + 1)`.** Let `G` be a group
with `C^(n + 1)` multiplication on a boundaryless manifold, and `ξ : ℝ → E` a `C^n` curve in its
Lie algebra. A curve `g : ℝ → G` with left-trivialized derivative `ξ` at every time is
`C^(n + 1)`. -/
theorem contMDiff_succ (n : ℕ) [ContMDiffMul I (n + 1 : ℕ) G] {ξ : ℝ → E}
    (hξ : ContDiff ℝ n ξ) {g : ℝ → G} (hg : HasLeftTrivializedDerivOn (I := I) g ξ univ) :
    ContMDiff 𝓘(ℝ, ℝ) I (n + 1 : ℕ) g := by
  have : ContMDiffMul I 1 G := ContMDiffMul.of_le (n := (n + 1 : ℕ)) (by simp)
  have hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent n
      (fun p : ℝ × G ↦
        (⟨p.2, mulInvariantVectorField (I := I) (ξ p.1) p.2⟩ : TangentBundle I G)) :=
    (contMDiff_mulInvariantVectorField_modelSpace (m := n) (n := (n + 1 : ℕ))
      (by norm_cast)).comp ((hξ.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd)
  exact contMDiff_snd.comp (contMDiff_succ_of_isMIntegralCurve n
    hg.isMIntegralCurve_prodMk_timeDependentSuspensionField_mulInvariantVectorField
    (contMDiff_timeDependentSuspensionField hX))

/-- **Curves with a smooth left-trivialized derivative are smooth.** Let `G` be a group with
smooth multiplication on a boundaryless manifold, and `ξ : ℝ → E` a smooth curve in its Lie
algebra. A curve `g : ℝ → G` with left-trivialized derivative `ξ` at every time is smooth. -/
theorem contMDiff [ContMDiffMul I ∞ G] {ξ : ℝ → E} (hξ : ContDiff ℝ ∞ ξ) {g : ℝ → G}
    (hg : HasLeftTrivializedDerivOn (I := I) g ξ univ) : ContMDiff 𝓘(ℝ, ℝ) I ∞ g := by
  refine contMDiff_infty.2 fun n ↦ ?_
  have : ContMDiffMul I (n + 1 : ℕ) G :=
    ContMDiffMul.of_le (n := ∞) (by exact_mod_cast le_top)
  exact (hg.contMDiff_succ n (hξ.of_le (by exact_mod_cast le_top))).of_le
    (by exact_mod_cast Nat.le_succ n)

end SymplecticGeometry.HasLeftTrivializedDerivOn

end
