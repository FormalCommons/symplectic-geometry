/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Morse.BirthDeath.Basic
import Mathlib.Analysis.Calculus.FDeriv.Pow
import TauCeti.Geometry.Manifold.MFDeriv.ModelChart
import SymplecticGeometry.Analysis.Calculus.FDeriv.Comp
import SymplecticGeometry.Geometry.Manifold.Morse.Bott.Chart.Hessian

/-!
# The first three derivatives at a birth–death critical point

For a birth–death chart `φ` of `f` at `x`, with coordinates `L = φ.toMorseBottChart.coord`,
weights `wᵢ` and cubic coordinate `i₀`, the normal form is
`z ↦ f x + (1/2) Σᵢ wᵢ (L z)ᵢ² + (L z)_{i₀}³ / 3`, where `w_{i₀} = 0`. This file computes its second
and third derivatives at every point and reads off the data at the origin that characterize a
birth–death critical point: the differential vanishes, the Hessian is the diagonal form
`Σᵢ wᵢ (L v)ᵢ (L w)ᵢ`, whose kernel is the line spanned by `e = L⁻¹ (Pi.single i₀ 1)`, and the third
derivative takes the value `2` on `(e, e, e)`.

The quadratic part of the second derivative is that of the Morse–Bott chart,
`TauCeti.MorseBottChart.fderiv_fderiv_quadratic_apply`; the cubic term adds the rest.

The same data can then be read in any chart `q` at `x` of the `C³` maximal atlas
(`TauCeti.BirthDeathChart.exists_ker_fderiv_fderiv_eq_span_singleton_of_mem_maximalAtlas`), in
particular in the preferred chart `extChartAt 𝓘(ℝ, E) x`
(`TauCeti.BirthDeathChart.exists_ker_fderiv_fderiv_eq_span_singleton`). Near `q x`, `f` read in
`q` is the normal form composed with the transition map `τ = q.symm.trans ψ` to the chart `ψ` of
`φ`, which is `C³` with invertible derivative since both charts lie in the maximal atlas
(`TauCeti.contDiffAt_symm_trans_of_mem_maximalAtlas`, `TauCeti.exists_hasFDerivAt_symm_trans`).
The chain rules `SymplecticGeometry.ker_fderiv_fderiv_comp_of_fderiv_eq_zero` and
`SymplecticGeometry.fderiv_fderiv_fderiv_comp_apply_of_fderiv_eq_zero` carry the vanishing
differential, the one-dimensional kernel of the Hessian and the nonzero cubic term back through
`τ`, the kernel vector being `Dτ⁻¹ e`.

## Main declarations

* `TauCeti.BirthDeathChart.fderiv_fderiv_normalForm_apply`: the second derivative at `z` is
  `(v, w) ↦ Σᵢ wᵢ (L v)ᵢ (L w)ᵢ + 2 (L z)_{i₀} (L v)_{i₀} (L w)_{i₀}`.
* `TauCeti.BirthDeathChart.fderiv_fderiv_fderiv_normalForm_apply`: the third derivative at any
  point is `(u, v, w) ↦ 2 (L u)_{i₀} (L v)_{i₀} (L w)_{i₀}`.
* `TauCeti.BirthDeathChart.fderiv_normalForm_zero`,
  `TauCeti.BirthDeathChart.fderiv_fderiv_normalForm_zero_apply`,
  `TauCeti.BirthDeathChart.ker_fderiv_fderiv_normalForm_zero` and
  `TauCeti.BirthDeathChart.fderiv_fderiv_fderiv_normalForm_zero_coord_symm_single`: the
  derivatives at the origin.
* `TauCeti.BirthDeathChart.exists_ker_fderiv_fderiv_eq_span_singleton_of_mem_maximalAtlas`: in
  a chart at `x` of the `C³` maximal atlas, the differential of `f` vanishes, the kernel of its
  Hessian is a line `ℝ ∙ e`, and its third derivative is nonzero on `(e, e, e)`.
* `TauCeti.BirthDeathChart.exists_ker_fderiv_fderiv_eq_span_singleton`: the same in the preferred
  chart at `x`.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012]
* J. Cerf, *La stratification naturelle des espaces de fonctions différentiables réelles et le
  théorème de la pseudo-isotopie*, Publ. Math. IHÉS 39 (1970), 5–173.
-/

public section

open Filter Function Set Topology
open scoped Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {f : M → ℝ} {x : M}

namespace BirthDeathChart

variable (φ : BirthDeathChart E f x)

/-- The third derivative of the normal form. -/
private noncomputable def cubicForm : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
  ((2 : ℝ) • φ.toMorseBottChart.coordFun φ.cubicIndex).smulRight
    ((φ.toMorseBottChart.coordFun φ.cubicIndex).smulRight
      (φ.toMorseBottChart.coordFun φ.cubicIndex))

private theorem fderiv_normalForm_eq :
    fderiv ℝ φ.normalForm = fun z ↦ fderiv ℝ φ.toMorseBottChart.quadratic z +
      (φ.toMorseBottChart.coordFun φ.cubicIndex z ^ 2) •
        φ.toMorseBottChart.coordFun φ.cubicIndex := by
  ext z v
  simp [fderiv_normalForm_apply, MorseBottChart.fderiv_quadratic_apply]

private theorem hasFDerivAt_fderiv_normalForm (z : E) :
    HasFDerivAt (fderiv ℝ φ.normalForm)
      ((∑ i, φ.toMorseBottChart.weight i •
        (φ.toMorseBottChart.coordFun i).smulRight (φ.toMorseBottChart.coordFun i)) +
          φ.cubicForm z) z := by
  rw [fderiv_normalForm_eq]
  have hc := (φ.toMorseBottChart.coordFun φ.cubicIndex).hasFDerivAt (x := z)
  convert (φ.toMorseBottChart.hasFDerivAt_fderiv_quadratic z).add
    ((hc.pow 2).smul_const (φ.toMorseBottChart.coordFun φ.cubicIndex)) using 2
  ext v w
  simp [cubicForm, mul_assoc]

private theorem fderiv_fderiv_normalForm_eq :
    fderiv ℝ (fderiv ℝ φ.normalForm) = fun z ↦ (∑ i, φ.toMorseBottChart.weight i •
      (φ.toMorseBottChart.coordFun i).smulRight (φ.toMorseBottChart.coordFun i)) +
        φ.cubicForm z :=
  funext fun z ↦ (φ.hasFDerivAt_fderiv_normalForm z).fderiv

/-- The second derivative of the normal form of a birth–death chart:
`(v, w) ↦ Σᵢ wᵢ (L v)ᵢ (L w)ᵢ + 2 (L z)_{i₀} (L v)_{i₀} (L w)_{i₀}`. -/
theorem fderiv_fderiv_normalForm_apply (z v w : E) :
    fderiv ℝ (fderiv ℝ φ.normalForm) z v w = ∑ i, φ.toMorseBottChart.weight i *
      φ.toMorseBottChart.coord v i * φ.toMorseBottChart.coord w i +
        2 * φ.toMorseBottChart.coord z φ.cubicIndex * φ.toMorseBottChart.coord v φ.cubicIndex *
          φ.toMorseBottChart.coord w φ.cubicIndex := by
  rw [fderiv_fderiv_normalForm_eq, add_apply, add_apply,
    ← (φ.toMorseBottChart.hasFDerivAt_fderiv_quadratic z).fderiv,
    MorseBottChart.fderiv_fderiv_quadratic_apply]
  simp [cubicForm, mul_assoc]

/-- The third derivative of the normal form of a birth–death chart is the same at every point:
`(u, v, w) ↦ 2 (L u)_{i₀} (L v)_{i₀} (L w)_{i₀}`. -/
theorem fderiv_fderiv_fderiv_normalForm_apply (z u v w : E) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ φ.normalForm)) z u v w =
      2 * φ.toMorseBottChart.coord u φ.cubicIndex * φ.toMorseBottChart.coord v φ.cubicIndex *
        φ.toMorseBottChart.coord w φ.cubicIndex := by
  -- The implicit arguments are given: elaborating with them left to unification fails on the
  -- instances of the space of bilinear maps.
  have h : fderiv ℝ (fun z ↦ (∑ i, φ.toMorseBottChart.weight i •
      (φ.toMorseBottChart.coordFun i).smulRight (φ.toMorseBottChart.coordFun i)) +
        φ.cubicForm z) z = φ.cubicForm :=
    (fderiv_const_add (𝕜 := ℝ) (F := E →L[ℝ] E →L[ℝ] ℝ) (f := ⇑φ.cubicForm) (x := z)
      _).trans (ContinuousLinearMap.fderiv (F := E →L[ℝ] E →L[ℝ] ℝ) φ.cubicForm)
  rw [fderiv_fderiv_normalForm_eq, h]
  simp [cubicForm, mul_assoc]

/-- The differential of the normal form of a birth–death chart vanishes at the origin. -/
@[simp]
theorem fderiv_normalForm_zero : fderiv ℝ φ.normalForm 0 = 0 :=
  φ.fderiv_normalForm_eq_zero_iff.2 rfl

/-- The Hessian of the normal form of a birth–death chart at the origin is the diagonal form
`(v, w) ↦ Σᵢ wᵢ (L v)ᵢ (L w)ᵢ` of the weights. -/
theorem fderiv_fderiv_normalForm_zero_apply (v w : E) :
    fderiv ℝ (fderiv ℝ φ.normalForm) 0 v w = ∑ i, φ.toMorseBottChart.weight i *
      φ.toMorseBottChart.coord v i * φ.toMorseBottChart.coord w i := by
  simp [fderiv_fderiv_normalForm_apply]

/-- The kernel of the Hessian at the origin of the normal form of a birth–death chart is the line
spanned by the cubic coordinate vector `L⁻¹ (Pi.single i₀ 1)`. -/
theorem ker_fderiv_fderiv_normalForm_zero :
    (fderiv ℝ (fderiv ℝ φ.normalForm) 0).ker =
      ℝ ∙ φ.toMorseBottChart.coord.symm (Pi.single φ.cubicIndex 1) := by
  ext v
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, Submodule.mem_span_singleton]
  constructor
  · intro hv
    refine ⟨φ.toMorseBottChart.coord v φ.cubicIndex, φ.toMorseBottChart.coord.injective ?_⟩
    ext i
    have h := congr($hv (φ.toMorseBottChart.coord.symm (Pi.single i 1)))
    rw [fderiv_fderiv_normalForm_zero_apply, zero_apply] at h
    simp only [LinearEquiv.apply_symm_apply, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
    rw [map_smul, LinearEquiv.apply_symm_apply, Pi.smul_apply, Pi.single_apply]
    by_cases hi : i = φ.cubicIndex
    · subst hi
      simp
    · simp only [hi, ↓reduceIte, smul_zero]
      exact ((mul_eq_zero.1 h).resolve_left (φ.weight_ne_zero i hi)).symm
  · rintro ⟨a, rfl⟩
    ext w
    simp [fderiv_fderiv_normalForm_zero_apply, Pi.single_apply, φ.weight_cubicIndex]

/-- The third derivative at the origin of the normal form of a birth–death chart takes the value
`2` on the cubic coordinate vector `L⁻¹ (Pi.single i₀ 1)`. -/
theorem fderiv_fderiv_fderiv_normalForm_zero_coord_symm_single :
    fderiv ℝ (fderiv ℝ (fderiv ℝ φ.normalForm)) 0
      (φ.toMorseBottChart.coord.symm (Pi.single φ.cubicIndex 1))
      (φ.toMorseBottChart.coord.symm (Pi.single φ.cubicIndex 1))
      (φ.toMorseBottChart.coord.symm (Pi.single φ.cubicIndex 1)) = 2 := by
  simp [fderiv_fderiv_fderiv_normalForm_apply]

section Chart

variable {q : OpenPartialHomeomorph M E}

/-- The change of coordinates `τ` from a chart `q` at `x` of the `C³` maximal atlas to the chart of
a birth–death chart: it is `C³` at `u = q x`, sends `u` to `0` and has invertible derivative there,
and near `u` the function `f` read in `q` is the normal form composed with `τ`. -/
private theorem exists_coordChange (hq : q ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 3 M)
    (hx : x ∈ q.source) : ∃ τ : E → E,
    ContDiffAt ℝ 3 τ (q x) ∧ τ (q x) = 0 ∧ (fderiv ℝ τ (q x)).IsInvertible ∧
      f ∘ q.symm =ᶠ[𝓝 (q x)] φ.normalForm ∘ τ := by
  set ψ := φ.toMorseBottChart.toChart
  have hψ : ψ ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 3 M :=
    IsManifold.maximalAtlas_subset_of_le (by simp) φ.toMorseBottChart.mem_maximalAtlas
  have hu : q x ∈ (q.symm.trans ψ).source := by simp [hx, ψ, φ.toMorseBottChart.mem_source]
  have hsrc : (q.symm.trans ψ).source ∈ 𝓝 (q x) := (q.symm.trans ψ).open_source.mem_nhds hu
  refine ⟨q.symm.trans ψ, contDiffAt_symm_trans_of_mem_maximalAtlas hq hψ hu,
    by simp [ψ, hx, φ.toMorseBottChart.apply_self], ?_, ?_⟩
  · obtain ⟨A, hA⟩ := exists_hasFDerivAt_symm_trans (by simp) hq hψ hu
    exact ⟨A, hA.fderiv.symm⟩
  · filter_upwards [hsrc] with z hz
    exact φ.eqOn_normalForm hz.2

include φ in
/-- **Birth–death data in a chart.** Let `f` have a birth–death chart at `x`, let `q` be a chart
at `x` of the `C³` maximal atlas, and let `F = f ∘ q.symm` be `f` read in `q`, with `u = q x`.
Then `u` is a critical point of `F`, the kernel of the Hessian `D²F(u)` is a line `ℝ ∙ e` with
`e ≠ 0`, and the third derivative satisfies `D³F(u)(e, e, e) ≠ 0`. -/
theorem exists_ker_fderiv_fderiv_eq_span_singleton_of_mem_maximalAtlas
    (hq : q ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 3 M) (hx : x ∈ q.source) :
    ∃ e : E, e ≠ 0 ∧ fderiv ℝ (f ∘ q.symm) (q x) = 0 ∧
      (fderiv ℝ (fderiv ℝ (f ∘ q.symm)) (q x)).ker = ℝ ∙ e ∧
      fderiv ℝ (fderiv ℝ (fderiv ℝ (f ∘ q.symm))) (q x) e e e ≠ 0 := by
  obtain ⟨τ, hτ, hτu, ⟨D, hD⟩, heq⟩ := exists_coordChange φ hq hx
  set u := q x
  set e₀ := φ.toMorseBottChart.coord.symm (Pi.single φ.cubicIndex 1)
  have hN : ContDiffAt ℝ 3 φ.normalForm (τ u) :=
    φ.contDiff_normalForm.contDiffAt.of_le (by simp)
  have hc : fderiv ℝ φ.normalForm (τ u) = 0 := by rw [hτu, fderiv_normalForm_zero]
  have hDe : fderiv ℝ τ u (D.symm e₀) = e₀ := by rw [← hD]; simp
  refine ⟨D.symm e₀, by simp [e₀], ?_, ?_, ?_⟩
  · rw [heq.fderiv_eq, fderiv_comp u (hN.differentiableAt (by simp))
      (hτ.differentiableAt (by simp)), hc, ContinuousLinearMap.zero_comp]
  · rw [heq.fderiv.fderiv_eq, SymplecticGeometry.ker_fderiv_fderiv_comp_of_fderiv_eq_zero
      (hN.of_le (by norm_num)) (hτ.of_le (by norm_num)) hc (hD ▸ D.surjective), hτu,
      ker_fderiv_fderiv_normalForm_zero, ← hD,
      ContinuousLinearEquiv.toLinearMap_toContinuousLinearMap, Submodule.comap_equiv_eq_map_symm,
      Submodule.map_span, Set.image_singleton]
    simp [e₀]
  · have hv : fderiv ℝ (fderiv ℝ φ.normalForm) (τ u) (fderiv ℝ τ u (D.symm e₀)) = 0 := by
      have h := Submodule.mem_span_singleton_self (R := ℝ) e₀
      rw [← ker_fderiv_fderiv_normalForm_zero] at h
      rwa [hDe, hτu]
    rw [heq.fderiv.fderiv.fderiv_eq,
      SymplecticGeometry.fderiv_fderiv_fderiv_comp_apply_of_fderiv_eq_zero hN
        (by simp [minSmoothness_of_isRCLikeNormedField]) hτ hc hv,
      hDe, hτu, fderiv_fderiv_fderiv_normalForm_zero_coord_symm_single]
    norm_num

include φ in
/-- **Birth–death data in the preferred chart.** Let `f` have a birth–death chart at `x`, and let
`F = f ∘ (extChartAt 𝓘(ℝ, E) x).symm` be `f` read in the preferred chart at `x`, with
`u = extChartAt 𝓘(ℝ, E) x x`. Then `u` is a critical point of `F`, the kernel of the Hessian
`D²F(u)` is a line `ℝ ∙ e` with `e ≠ 0`, and the third derivative satisfies
`D³F(u)(e, e, e) ≠ 0`. -/
theorem exists_ker_fderiv_fderiv_eq_span_singleton [IsManifold 𝓘(ℝ, E) 3 M] :
    ∃ e : E, e ≠ 0 ∧
      fderiv ℝ (f ∘ (extChartAt 𝓘(ℝ, E) x).symm) (extChartAt 𝓘(ℝ, E) x x) = 0 ∧
      (fderiv ℝ (fderiv ℝ (f ∘ (extChartAt 𝓘(ℝ, E) x).symm)) (extChartAt 𝓘(ℝ, E) x x)).ker =
        ℝ ∙ e ∧
      fderiv ℝ (fderiv ℝ (fderiv ℝ (f ∘ (extChartAt 𝓘(ℝ, E) x).symm)))
        (extChartAt 𝓘(ℝ, E) x x) e e e ≠ 0 := by
  simpa using exists_ker_fderiv_fderiv_eq_span_singleton_of_mem_maximalAtlas φ
    (IsManifold.chart_mem_maximalAtlas x) (mem_chart_source E x)

end Chart

end BirthDeathChart

end TauCeti

end
