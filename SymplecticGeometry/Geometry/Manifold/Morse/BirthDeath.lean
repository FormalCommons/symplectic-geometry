/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.BirthDeath
public import TauCeti.Geometry.Manifold.Morse.Bott.Chart.Basic
public import TauCeti.Geometry.Manifold.Morse.CriticalPoints

/-!
# Birth–death charts and generalized Morse functions

TODO
-/

public section

open Function Set Filter Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {f : M → ℝ} {x : M}

variable (E) in
/-- A **birth–death chart** for `f` at `x`: a chart of the maximal atlas, centred at `x`, with a
linear change of coordinates `L : E ≃ (Fin n → ℝ)`, weights `wᵢ = ±1` off one coordinate `i₀`, and
`w_{i₀} = 0`, such that on the source of the chart

`f y = f x + (1/2) Σᵢ wᵢ (L (ψ y))ᵢ² + (L (ψ y))_{i₀}³ / 3`.

It is recorded as a Morse–Bott chart (`TauCeti.MorseBottChart`) of the quadratic part
`quadraticPart`, which is `f` minus the cubic term `birthDeathPotential 0` of the coordinate
`i₀` on the source, with exactly one weight equal to `0`. -/
structure BirthDeathChart (f : M → ℝ) (x : M) where
  /-- The quadratic part of `f`: on the source of the chart, `f` minus the cubic term. -/
  quadraticPart : M → ℝ
  /-- The Morse–Bott chart in which the quadratic part is in normal form. -/
  toMorseBottChart : MorseBottChart E quadraticPart x
  /-- The coordinate along which `f` is cubic. -/
  cubicIndex : Fin (Module.finrank ℝ E)
  weight_cubicIndex : toMorseBottChart.weight cubicIndex = 0
  weight_ne_zero : ∀ i, i ≠ cubicIndex → toMorseBottChart.weight i ≠ 0
  eq_add : ∀ y ∈ toMorseBottChart.toChart.source, f y = quadraticPart y +
    birthDeathPotential 0 (toMorseBottChart.coord (toMorseBottChart.toChart y) cubicIndex)

namespace BirthDeathChart

variable (φ : BirthDeathChart E f x)

/-- The restriction of a birth–death chart to an open neighbourhood `s` of its centre: the chart is
restricted to `s`, and the quadratic part, the coordinates, the weights and the cubic coordinate
are unchanged. -/
noncomputable def restr {s : Set M} (hs : IsOpen s) (hx : x ∈ s) : BirthDeathChart E f x where
  quadraticPart := φ.quadraticPart
  toMorseBottChart := φ.toMorseBottChart.restr hs hx
  cubicIndex := φ.cubicIndex
  weight_cubicIndex := by rw [MorseBottChart.restr_weight]; exact φ.weight_cubicIndex
  weight_ne_zero := by rw [MorseBottChart.restr_weight]; exact φ.weight_ne_zero
  eq_add y hy := by
    rw [MorseBottChart.restr_source] at hy
    simpa using φ.eq_add y hy.1

section Restr

variable {s : Set M} (hs : IsOpen s) (hx : x ∈ s)

/-- Restricting a birth–death chart does not change its quadratic part. -/
@[simp]
theorem restr_quadraticPart : (φ.restr hs hx).quadraticPart = φ.quadraticPart := by
  simp [restr]

/-- The chart of a restricted birth–death chart is the restricted chart. -/
@[simp]
theorem restr_toChart :
    (φ.restr hs hx).toMorseBottChart.toChart = φ.toMorseBottChart.toChart.restr s := by
  simp [restr]

/-- Restricting a birth–death chart does not change its coordinates. -/
@[simp]
theorem restr_coord : (φ.restr hs hx).toMorseBottChart.coord = φ.toMorseBottChart.coord := by
  simp [restr]

/-- Restricting a birth–death chart does not change its weights. -/
@[simp]
theorem restr_weight : (φ.restr hs hx).toMorseBottChart.weight = φ.toMorseBottChart.weight := by
  simp [restr]

/-- Restricting a birth–death chart does not change its cubic coordinate. -/
@[simp]
theorem restr_cubicIndex : (φ.restr hs hx).cubicIndex = φ.cubicIndex := by
  simp [restr]

/-- The source of a restricted birth–death chart is the intersection of the source with `s`. -/
theorem restr_source :
    (φ.restr hs hx).toMorseBottChart.toChart.source = φ.toMorseBottChart.toChart.source ∩ s := by
  rw [restr_toChart, φ.toMorseBottChart.toChart.restr_source' s hs]

end Restr

/-- The quadratic part of `f` takes the value `f x` at the centre. -/
theorem quadraticPart_self : φ.quadraticPart x = f x := by
  simpa [birthDeathPotential_apply] using (φ.eq_add x φ.toMorseBottChart.mem_source).symm

/-- The **index** of a birth–death chart: the number of negative weights. -/
noncomputable def index : ℕ :=
  {i | φ.toMorseBottChart.weight i < 0}.ncard

/-- The normal form of `f` in a birth–death chart, as a function on the model space:
`z ↦ f x + (1/2) Σᵢ wᵢ (L z)ᵢ² + (L z)_{i₀}³ / 3`. -/
noncomputable def normalForm (z : E) : ℝ :=
  φ.toMorseBottChart.quadratic z + birthDeathPotential 0 (φ.toMorseBottChart.coord z φ.cubicIndex)

/-- The value of the normal form of a birth–death chart. -/
theorem normalForm_apply (z : E) :
    φ.normalForm z = f x + (2 : ℝ)⁻¹ * ∑ i, φ.toMorseBottChart.weight i *
      (φ.toMorseBottChart.coord z i) ^ 2 +
        birthDeathPotential 0 (φ.toMorseBottChart.coord z φ.cubicIndex) := by
  rw [normalForm, MorseBottChart.quadratic_apply, φ.quadraticPart_self]

/-- On the source of a birth–death chart, `f` is the normal form read in the chart. -/
theorem eqOn_normalForm :
    EqOn f (φ.normalForm ∘ φ.toMorseBottChart.toChart) φ.toMorseBottChart.toChart.source :=
  fun y hy ↦ by
    rw [comp_apply, normalForm, φ.eq_add y hy, φ.toMorseBottChart.eqOn_quadratic hy, comp_apply]

/-- The normal form of a birth–death chart is smooth. -/
theorem contDiff_normalForm : ContDiff ℝ ∞ φ.normalForm := by
  have := φ.toMorseBottChart.finiteDimensional
  have hi : ContDiff ℝ ∞ fun z ↦ φ.toMorseBottChart.coordL z φ.cubicIndex :=
    contDiff_pi.1 φ.toMorseBottChart.coordL.contDiff _
  simp only [MorseBottChart.coordL_apply] at hi
  exact φ.toMorseBottChart.contDiff_quadratic.add ((contDiff_birthDeathPotential 0).comp hi)

/-- The derivative of the normal form of a birth–death chart:
`v ↦ Σᵢ wᵢ (L z)ᵢ (L v)ᵢ + (L z)_{i₀}² (L v)_{i₀}`. -/
theorem fderiv_normalForm_apply (z v : E) :
    fderiv ℝ φ.normalForm z v = ∑ i, φ.toMorseBottChart.weight i *
      φ.toMorseBottChart.coord z i * φ.toMorseBottChart.coord v i +
        φ.toMorseBottChart.coord z φ.cubicIndex ^ 2 * φ.toMorseBottChart.coord v φ.cubicIndex := by
  have := φ.toMorseBottChart.finiteDimensional
  have hc : HasFDerivAt (fun z ↦ φ.toMorseBottChart.coord z φ.cubicIndex)
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (Module.finrank ℝ E) ↦ ℝ)
        φ.cubicIndex).comp (φ.toMorseBottChart.coordL : E →L[ℝ] _)) z := by
    convert ((ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin (Module.finrank ℝ E) ↦ ℝ) φ.cubicIndex).comp
        (φ.toMorseBottChart.coordL : E →L[ℝ] _)).hasFDerivAt (x := z) using 1
    ext w
    simp
  have h := (φ.toMorseBottChart.hasFDerivAt_quadratic z).add
    ((hasDerivAt_birthDeathPotential 0 _).comp_hasFDerivAt z hc)
  have hN : φ.normalForm = φ.toMorseBottChart.quadratic +
      birthDeathPotential 0 ∘ fun z ↦ φ.toMorseBottChart.coord z φ.cubicIndex := by
    funext z
    rw [normalForm, Pi.add_apply, comp_apply]
  rw [hN, h.fderiv]
  simp [mul_comm]

/-- The only critical point of the normal form of a birth–death chart is the origin. -/
theorem fderiv_normalForm_eq_zero_iff {z : E} : fderiv ℝ φ.normalForm z = 0 ↔ z = 0 := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · have hz : ∀ i, φ.toMorseBottChart.coord z i = 0 := by
      intro i
      have := congrArg (fun T : E →L[ℝ] ℝ ↦ T (φ.toMorseBottChart.coord.symm (Pi.single i 1))) h
      simp only [fderiv_normalForm_apply, LinearEquiv.apply_symm_apply,
        zero_apply] at this
      rw [Finset.sum_eq_single i (fun j _ hj ↦ by simp [hj]) (by simp)] at this
      by_cases hi : i = φ.cubicIndex
      · subst hi
        simpa [φ.weight_cubicIndex] using this
      · simpa [hi, Pi.single_apply, φ.weight_ne_zero i hi] using this
    exact φ.toMorseBottChart.coord.injective (funext fun i ↦ by simpa using hz i)
  · rintro rfl
    ext v
    simp [fderiv_normalForm_apply]

/-- In a birth–death chart, the centre is the only critical point of `f` in the source. -/
theorem mfderiv_eq_zero_iff {y : M} (hy : y ∈ φ.toMorseBottChart.toChart.source) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y = 0 ↔ y = x := by
  rw [mfderiv_eq_zero_iff_of_eqOn φ.toMorseBottChart.mem_maximalAtlas_one φ.eqOn_normalForm hy,
    φ.fderiv_normalForm_eq_zero_iff, φ.toMorseBottChart.toChart_eq_zero_iff hy]

include φ in
/-- The centre of a birth–death chart is a critical point of `f`. -/
theorem mem_criticalPoints : x ∈ criticalPoints 𝓘(ℝ, E) f :=
  mem_criticalPoints_iff_mfderiv_eq_zero.2 ((φ.mfderiv_eq_zero_iff φ.toMorseBottChart.mem_source).2
    rfl)

include φ in
/-- Near the centre of a birth–death chart, `f` has no critical point other than the centre. -/
theorem eventually_eq_of_mem_criticalPoints :
    ∀ᶠ y in 𝓝 x, y ∈ criticalPoints 𝓘(ℝ, E) f → y = x := by
  filter_upwards [φ.toMorseBottChart.toChart.open_source.mem_nhds φ.toMorseBottChart.mem_source]
    with y hy hyc
  exact (φ.mfderiv_eq_zero_iff hy).1 (mem_criticalPoints_iff_mfderiv_eq_zero.1 hyc)

/-- A function is smooth on the source of a birth–death chart. -/
theorem contMDiffOn : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞ f φ.toMorseBottChart.toChart.source :=
  (φ.contDiff_normalForm.contMDiff.comp_contMDiffOn
    (contMDiffOn_of_mem_maximalAtlas φ.toMorseBottChart.mem_maximalAtlas)).congr φ.eqOn_normalForm

end BirthDeathChart

end TauCeti

end
