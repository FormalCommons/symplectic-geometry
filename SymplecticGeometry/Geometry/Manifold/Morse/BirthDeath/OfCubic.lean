/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Morse.BirthDeath.Basic
import SymplecticGeometry.Analysis.Calculus.Morse.BirthDeathNormalForm
import TauCeti.Geometry.Manifold.MFDeriv.ModelChart

/-!
# Birth–death charts from a degenerate Hessian with a nonzero cubic term

Let `f` be a function on a finite-dimensional manifold, smooth near a point `x`, and read it in
the preferred chart at `x` as `F = f ∘ (extChartAt 𝓘(ℝ, E) x).symm` near
`u = extChartAt 𝓘(ℝ, E) x x`. If `u` is a critical point of `F`, the kernel of the Hessian of `F`
at `u` is a line `ℝ ∙ e`, and the third derivative `D³F(u)(e, e, e)` is nonzero, then `x` is the
centre of a birth–death chart of `f`
(`TauCeti.nonempty_birthDeathChart_of_ker_eq_span_singleton`).

## Main results

* `TauCeti.nonempty_birthDeathChart_of_ker_eq_span_singleton`: a critical point whose Hessian
  has a one-dimensional kernel along which the cubic term does not vanish has a birth–death
  chart.

## Implementation notes

The normal form in the model space,
`ContDiffOn.exists_openPartialHomeomorph_eq_add_pow_three_div_three_add_sum_sq`, gives a smooth
chart `Φ` of `E` at `u`, with values in `ℝ × ℝᵐ` and `m + 1 = dim E`, in which
`F = F u + a ^ 3 / 3 + ∑ σᵢ bᵢ ²`. The birth–death chart is assembled as Tau Ceti's
`TauCeti.IsManifoldNondegenerateCriticalPoint.nonempty_morseChart` assembles a Morse chart: its
chart is the preferred chart at `x` followed by `Φ` and a linear identification of
`ℝ × ℝᵐ` with `E`, and its coordinates are `(a, √2 b)`, read in `Fin (dim E) → ℝ` through
`Fin.cons`, so that the sum of squares has the normalization `(1/2) ∑ wᵢ zᵢ ²` of
`TauCeti.MorseBottChart`. The cubic coordinate is the first one, of weight `0`, and the other
weights are the signs `σᵢ`.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012]
* J. Cerf, *La stratification naturelle des espaces de fonctions différentiables réelles et le
  théorème de la pseudo-isotopie*, Publ. Math. IHÉS 39 (1970), 5–173.
-/

public section

open Function Set Filter Topology Module
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {f : M → ℝ} {x : M}

/-- **Birth–death charts from the derivatives of the function.** Let `f` be smooth near `x`, on a
manifold modelled on a finite-dimensional real normed space `E`, and let
`F = f ∘ (extChartAt 𝓘(ℝ, E) x).symm` be `f` read in the preferred chart at `x`, near
`u = extChartAt 𝓘(ℝ, E) x x`. If `u` is a critical point of `F`, the kernel of the Hessian
`D²F(u)` is the line spanned by `e`, and `D³F(u)(e, e, e) ≠ 0`, then `f` has a birth–death chart
at `x`. -/
theorem nonempty_birthDeathChart_of_ker_eq_span_singleton
    (hf : ∀ᶠ y in 𝓝 x, ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) ∞ f y) {e : E}
    (hc : fderiv ℝ (f ∘ (extChartAt 𝓘(ℝ, E) x).symm) (extChartAt 𝓘(ℝ, E) x x) = 0)
    (hker : (fderiv ℝ (fderiv ℝ (f ∘ (extChartAt 𝓘(ℝ, E) x).symm))
      (extChartAt 𝓘(ℝ, E) x x)).ker = ℝ ∙ e)
    (h3 : fderiv ℝ (fderiv ℝ (fderiv ℝ (f ∘ (extChartAt 𝓘(ℝ, E) x).symm)))
      (extChartAt 𝓘(ℝ, E) x x) e e e ≠ 0) :
    Nonempty (BirthDeathChart E f x) := by
  -- `f` read in the preferred chart is smooth near `u`.
  obtain ⟨s, hfs, hsopen, hxs⟩ := _root_.eventually_nhds_iff.1 hf
  replace hf : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞ f s := fun y hy ↦ (hfs y hy).contMDiffWithinAt
  set c := chartAt E x with hc'
  set F : E → ℝ := f ∘ (extChartAt 𝓘(ℝ, E) x).symm with hFdef
  set u : E := extChartAt 𝓘(ℝ, E) x x
  set U := (extChartAt 𝓘(ℝ, E) x).target ∩ (extChartAt 𝓘(ℝ, E) x).symm ⁻¹' s
  have hU : IsOpen U := (continuousOn_extChartAt_symm x).isOpen_inter_preimage
    (isOpen_extChartAt_target x) hsopen
  have huU : u ∈ U := ⟨mem_extChartAt_target x, by
    rw [mem_preimage, extChartAt_to_inv]
    exact hxs⟩
  have hF : ContDiffOn ℝ ∞ F U :=
    (hf.comp ((contMDiffOn_extChartAt_symm x).mono inter_subset_left)
      fun _ hz ↦ hz.2).contDiffOn
  -- The normal form in the model space.
  obtain ⟨m, σ, Φ, hm, hσ, huΦ, hΦu, hΦ, hΦsymm, hFΦ⟩ :=
    hF.exists_openPartialHomeomorph_eq_add_pow_three_div_three_add_sum_sq (hU.mem_nhds huU)
      hc hker h3
  -- The coordinates `(a, √2 b)` of `ℝ × ℝᵐ`, read in `Fin (dim E) → ℝ`.
  have h2 : Real.sqrt 2 ≠ 0 := by positivity
  let G : (ℝ × EuclideanSpace ℝ (Fin m)) ≃ₗ[ℝ] (Fin (finrank ℝ E) → ℝ) :=
    ((LinearEquiv.refl ℝ ℝ).prodCongr
      ((LinearEquiv.smulOfNeZero ℝ _ _ h2).trans (WithLp.linearEquiv 2 ℝ (Fin m → ℝ)))).trans
      ((Fin.consLinearEquiv ℝ fun _ : Fin (m + 1) ↦ ℝ).trans
        (LinearEquiv.funCongrLeft ℝ ℝ (finCongr hm.symm)))
  have hG (p : ℝ × EuclideanSpace ℝ (Fin m)) (i : Fin (finrank ℝ E)) :
      G p i = (Fin.cons p.1 fun j ↦ Real.sqrt 2 * p.2 j : Fin (m + 1) → ℝ)
        (finCongr hm.symm i) := by
    simp [G, LinearEquiv.funCongrLeft_apply, Pi.smul_def]
  let K : E ≃L[ℝ] (Fin (finrank ℝ E) → ℝ) := ContinuousLinearEquiv.ofFinrankEq (by simp)
  let A : (ℝ × EuclideanSpace ℝ (Fin m)) ≃L[ℝ] E := G.toContinuousLinearEquiv.trans K.symm
  have hKA (p : ℝ × EuclideanSpace ℝ (Fin m)) : K (A p) = G p := by simp [A]
  -- The chart of `E` at `u`, and the chart of `M` at `x`.
  obtain ⟨Θ, hΘ, hΘsrc, hΘmem⟩ := exists_trans_mem_maximalAtlas_of_contDiffOn
    (IsManifold.chart_mem_maximalAtlas x) (ContinuousLinearEquiv.refl ℝ E) Φ hΦ hΦsymm A 0
  simp only [sub_zero, ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.coe_refl',
    id_eq] at hΘ hΘsrc
  have hext : ∀ y, extChartAt 𝓘(ℝ, E) x y = c y := fun y ↦ by simp [hc']
  have hleft : ∀ y ∈ c.source, F (c y) = f y := fun y hy ↦ by
    simpa [hFdef] using (eqOn_comp_chartAt_symm x hy).symm
  have hxc : x ∈ c.source := mem_chart_source E x
  have hcu : c x = u := (hext x).symm
  have hFu : F u = f x := by rw [← hcu]; exact hleft x hxc
  set ψ := c.trans Θ
  have hx : x ∈ ψ.source := ⟨hxc, by simpa [hΘsrc, hcu] using huΦ⟩
  have hψx : ψ x = 0 := by simp [ψ, hΘ, hcu, hΦu]
  have hcoord (y : M) : K (ψ y) = G (Φ (c y)) := by simp [ψ, hΘ, hKA]
  -- The cubic coordinate, the weights, and the normal form.
  set i₀ : Fin (finrank ℝ E) := finCongr hm 0
  set w : Fin (finrank ℝ E) → ℝ := fun i ↦ (Fin.cons 0 σ : Fin (m + 1) → ℝ) (finCongr hm.symm i)
  have hi₀ (p : ℝ × EuclideanSpace ℝ (Fin m)) : G p i₀ = p.1 := by simp [hG, i₀]
  have hsum (p : ℝ × EuclideanSpace ℝ (Fin m)) :
      (2 : ℝ)⁻¹ * ∑ i, w i * G p i ^ 2 = ∑ j, σ j * p.2 j ^ 2 := by
    rw [← (finCongr hm.symm).symm.sum_comp]
    simp only [w, hG, Equiv.apply_symm_apply, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
      zero_mul, zero_add, mul_pow, Real.sq_sqrt zero_le_two, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  refine ⟨{
    quadraticPart := fun y ↦ f y - birthDeathPotential 0 (K (ψ y) i₀)
    toMorseBottChart := {
      toChart := ψ
      mem_maximalAtlas := hΘmem
      mem_source := hx
      apply_self := hψx
      coord := K.toLinearEquiv
      weight := w
      weight_eq_neg_one_or_eq_zero_or_eq_one := fun i ↦ by
        simp only [w]
        refine Fin.cases (by simp) (fun j ↦ ?_) (finCongr hm.symm i)
        rw [Fin.cons_succ]
        exact (hσ j).imp_right .inr
      eq_quadratic := fun y hy ↦ by
        simp only [ContinuousLinearEquiv.coe_toLinearEquiv, hψx, map_zero, Pi.zero_apply,
          birthDeathPotential_apply, hcoord, hi₀, hsum]
        rw [← hleft y hy.1, hFΦ _ (by simpa [hΘsrc] using hy.2), hFu]
        ring }
    cubicIndex := i₀
    weight_cubicIndex := by simp [w, i₀]
    weight_ne_zero := fun i hi ↦ by
      simp only [w]
      induction h : finCongr hm.symm i using Fin.cases with
      | zero => exact absurd (by simp [i₀, ← h]) hi
      | succ j => rw [Fin.cons_succ]; rcases hσ j with h | h <;> simp [h]
    eq_add := fun y ↦ by simp }⟩

end TauCeti
