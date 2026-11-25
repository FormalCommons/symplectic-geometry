/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Weak
import SymplecticGeometry.Analysis.Complex.Wirtinger.Leibniz
import TauCeti.Analysis.Complex.Wirtinger.DolbeaultLemma
import TauCeti.Analysis.Complex.Wirtinger.Weyl
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# The weak similarity principle in the plane

A locally integrable function `u` solving `∂̄u = a u` in the sense of distributions on an open set
`Ω`, with a coefficient `a` smooth on `Ω`, is almost everywhere on `Ω` equal to `exp (-g) h`, with
`g` smooth on `Ω` and `h` holomorphic on `Ω`. In particular it agrees almost everywhere on `Ω`
with a function smooth on `Ω`. This is the distributional counterpart of
`TauCeti.exists_contDiff_analyticAt_exp_neg_mul_of_conjWirtingerDeriv_apply_one_eq_mul`, which
asks `u` to be real differentiable.

## Main results

* `TauCeti.HasWeakConjWirtingerDerivOn.exists_contDiffOn_differentiableOn_ae_eq_exp_neg_mul`:
  the weak similarity principle.
* `TauCeti.HasWeakConjWirtingerDerivOn.exists_contDiffOn_ae_eq_of_eq_mul`: a weak solution of
  `∂̄u = a u` is almost everywhere equal to a smooth function.

The proof takes `g` with `∂̄g = -a` on `Ω` from Tau Ceti's Dolbeault lemma
`IsOpen.exists_contDiffOn_conjWirtingerDeriv_apply_one_eq`; by the Leibniz rule
`TauCeti.HasWeakConjWirtingerDerivOn.contDiffOn_smul`, `∂̄(exp g u) = 0` weakly on `Ω`, and Weyl's
lemma `TauCeti.HasWeakConjWirtingerDerivOn.exists_differentiableOn_ae_eq` gives `h`.

## References

* [D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*][McDuffSalamon2012],
  Appendix B.
* I. N. Vekua, *Generalized Analytic Functions*, Chapter I.
-/

public section

open Complex MeasureTheory TopologicalSpace Filter
open scoped ContDiff

namespace TauCeti

variable {μ : Measure ℂ} [μ.IsAddHaarMeasure] {Ω : Opens ℂ} {a u : ℂ → ℂ}

/-- **The weak similarity principle.** Let `u` solve `∂̄u = a u` weakly on `Ω`, with `a` smooth
on `Ω`. Then there are a function `g` smooth on `Ω` with `∂̄g = -a` on `Ω` and a function `h`
holomorphic on `Ω` such that `u = exp (-g) h` almost everywhere on `Ω`. -/
theorem HasWeakConjWirtingerDerivOn.exists_contDiffOn_differentiableOn_ae_eq_exp_neg_mul
    (hu : HasWeakConjWirtingerDerivOn μ Ω u (fun z ↦ a z * u z)) (ha : ContDiffOn ℝ ∞ a Ω) :
    ∃ g : ℂ → ℂ, ContDiffOn ℝ ∞ g Ω ∧ (∀ w ∈ Ω, conjWirtingerDeriv g w 1 = -a w) ∧
      ∃ h : ℂ → ℂ, DifferentiableOn ℂ h Ω ∧ u =ᵐ[μ.restrict Ω] fun w ↦ exp (-g w) * h w := by
  obtain ⟨g, hg, hga⟩ := Ω.isOpen.exists_contDiffOn_conjWirtingerDeriv_apply_one_eq (n := ⊤)
    le_top ha.neg
  -- `exp g • u` solves `∂̄ = 0` weakly on `Ω`.
  have h0 : HasWeakConjWirtingerDerivOn μ Ω (fun w ↦ exp (g w) • u w) 0 := by
    refine (hu.contDiffOn_smul hg.cexp).congr_ae_deriv ?_
    rw [EventuallyEq, ae_restrict_iff' Ω.isOpen.measurableSet]
    refine Eventually.of_forall fun w hw ↦ ?_
    have hgw : DifferentiableAt ℝ g w :=
      (hg.differentiableOn (by simp)).differentiableAt (Ω.isOpen.mem_nhds hw)
    have hd : conjWirtingerDeriv (fun w ↦ exp (g w)) w 1 = exp (g w) * -a w := by
      rw [← Function.comp_def exp g,
        conjWirtingerDeriv_comp differentiableAt_exp hgw,
        ContinuousLinearMap.comp_apply, hga w hw, (hasDerivAt_exp (g w)).hasFDerivAt.fderiv]
      simp [mul_comm]
    simp only [hd, smul_eq_mul, Pi.zero_apply]
    ring
  obtain ⟨h, hh, hae⟩ := h0.exists_differentiableOn_ae_eq
  refine ⟨g, hg, hga, h, hh, hae.mono fun w hw ↦ ?_⟩
  simp only [← hw, smul_eq_mul, ← mul_assoc, ← exp_add, neg_add_cancel, exp_zero, one_mul]

/-- A weak solution of `∂̄u = a u` on `Ω`, with `a` smooth on `Ω`, agrees almost everywhere on
`Ω` with a function smooth on `Ω`. -/
theorem HasWeakConjWirtingerDerivOn.exists_contDiffOn_ae_eq_of_eq_mul
    (hu : HasWeakConjWirtingerDerivOn μ Ω u (fun z ↦ a z * u z)) (ha : ContDiffOn ℝ ∞ a Ω) :
    ∃ v : ℂ → ℂ, ContDiffOn ℝ ∞ v Ω ∧ u =ᵐ[μ.restrict Ω] v := by
  obtain ⟨g, hg, -, h, hh, hae⟩ := hu.exists_contDiffOn_differentiableOn_ae_eq_exp_neg_mul ha
  exact ⟨_, hg.neg.cexp.mul ((hh.contDiffOn Ω.isOpen).restrict_scalars ℝ), hae⟩

end TauCeti

end
