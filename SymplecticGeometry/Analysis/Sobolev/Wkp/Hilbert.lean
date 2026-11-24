/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.MeasureTheory.Function.LpSpace.ContinuousLinearEquiv
public import TauCeti.Analysis.Sobolev.Wkp.Basic

/-!
# `W^{k,2}(Ω)` is isomorphic to a Hilbert space

The norm of Tau Ceti's Sobolev space `TauCeti.Wkp μ Ω p k` is not given by an inner product,
even at `p = 2`, since the iterated weak derivatives take values in spaces of multilinear maps
with their operator norms. This file shows that at `p = 2` the space is nevertheless continuously
linearly equivalent to a real Hilbert space.

For every exponent, the pair `u ↦ (lowerOrder k u, iteratedGradient k u)` embeds
`W^{k+1,p}(Ω)` into the product of `W^{k,p}(Ω)` and the `Lᵖ` space of its highest derivatives,
with a lower bound by the factor two
(`TauCeti.Wkp.antilipschitzWith_lowerOrderL_prod_iteratedGradientL`), so with closed range. At
`p = 2` the product is equivalent to a `WithLp 2` product of Hilbert spaces, by induction on `k`
and `MeasureTheory.Lp.exists_continuousLinearEquiv_innerProductSpace`.

The lower bound is the step proved inside Tau Ceti's
`TauCeti.Wkp.isCompactOperator_of_isCompactOperator_lowerOrderL_iteratedGradientL`, here stated on
its own; its proof follows that one.

## Main results

* `TauCeti.Wkp.antilipschitzWith_lowerOrderL_prod_iteratedGradientL`: the lower bound.
* `TauCeti.Wkp.exists_continuousLinearEquiv_innerProductSpace`: `W^{k,2}(Ω)` is continuously
  linearly equivalent to a real Hilbert space.

## References

* [D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*][McDuffSalamon2012],
  Appendix B.
-/

public section

noncomputable section

open MeasureTheory

universe u

namespace TauCeti.Wkp

variable {E : Type u} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {Ω : TopologicalSpace.Opens E}

/-- The map `u ↦ (lowerOrder k u, iteratedGradient k u)` from `W^{k+1,p}(Ω)` to the product of
`W^{k,p}(Ω)` and the `Lᵖ` space of the highest derivatives is antilipschitz with constant two:
`‖u‖` is at most twice the norm of the pair. -/
theorem antilipschitzWith_lowerOrderL_prod_iteratedGradientL {p : ENNReal} [Fact (1 ≤ p)]
    (k : ℕ) :
    AntilipschitzWith 2
      ((lowerOrderL (mu := μ) (Omega := Ω) (p := p) k).prod (iteratedGradientL k)) := by
  set f := (lowerOrderL (mu := μ) (Omega := Ω) (p := p) k).prod (iteratedGradientL k)
  refine f.antilipschitz_of_bound fun u ↦ ?_
  have h := norm_le_norm_lowerOrder_add_norm_iteratedGradient k u
  have hf : f u = (lowerOrder k u, iteratedGradient k u) := by
    rw [ContinuousLinearMap.prod_apply, lowerOrderL_apply, iteratedGradientL_apply]
  have h₁ : ‖lowerOrder k u‖ ≤ ‖f u‖ := by
    rw [hf]; exact norm_fst_le (lowerOrder k u, iteratedGradient k u)
  have h₂ : ‖iteratedGradient k u‖ ≤ ‖f u‖ := by
    rw [hf]; exact norm_snd_le (lowerOrder k u, iteratedGradient k u)
  push_cast
  linarith

variable (μ Ω) in
/-- **`W^{k,2}` is a Hilbert space up to isomorphism.** For every order `k`, the Sobolev space
`W^{k,2}(Ω)` is continuously linearly equivalent to a real Hilbert space. -/
theorem exists_continuousLinearEquiv_innerProductSpace (k : ℕ) :
    ∃ (K : Type u) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℝ K) (_ : CompleteSpace K),
      Nonempty (Wkp μ Ω 2 k ≃L[ℝ] K) := by
  induction k with
  | zero => exact ⟨_, _, _, inferInstance, ⟨ContinuousLinearEquiv.refl ℝ (Lp ℝ 2 (μ.restrict Ω))⟩⟩
  | succ k ih =>
    obtain ⟨H₁, _, _, _, ⟨e₁⟩⟩ := ih
    obtain ⟨H₂, _, _, _, ⟨e₂⟩⟩ :=
      Lp.exists_continuousLinearEquiv_innerProductSpace (𝕜 := ℝ) (μ.restrict Ω)
        (IteratedGradient E k)
    have hanti := antilipschitzWith_lowerOrderL_prod_iteratedGradientL (μ := μ) (Ω := Ω) (p := 2) k
    exact
      ContinuousLinearMap.exists_continuousLinearEquiv_innerProductSpace_of_continuousLinearEquiv _
        ((e₁.prodCongr e₂).trans (WithLp.prodContinuousLinearEquiv 2 ℝ H₁ H₂).symm)
        hanti.injective (hanti.isClosed_range (ContinuousLinearMap.uniformContinuous _))

end TauCeti.Wkp

end
