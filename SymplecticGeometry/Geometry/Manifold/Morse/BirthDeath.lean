/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.BirthDeath
public import TauCeti.Geometry.Manifold.Morse.Bott.Chart.Basic
public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import SymplecticGeometry.Geometry.Manifold.Morse.Bott.Chart.LocalDiffeomorph
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
import SymplecticGeometry.Geometry.Manifold.Morse.LocalDiffeomorph
import SymplecticGeometry.Analysis.Calculus.FDeriv.Pi
import SymplecticGeometry.Analysis.Calculus.Hadamard
import SymplecticGeometry.Geometry.Manifold.Morse.CriticalPoints
import SymplecticGeometry.Topology.Maps.Proper
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
import TauCeti.Geometry.Manifold.Morse.ScalarComposition

/-!
# Birth–death charts and generalized Morse functions

A critical point `x` of a smooth function `f` is of *birth–death type* when, in some chart of the
maximal atlas centred at `x` and after a linear change of coordinates `L`, the function reads

`f y = f x + (1/2) Σ_{i ≠ i₀} wᵢ (L (ψ y))ᵢ² + (L (ψ y))_{i₀}³ / 3`, with every `wᵢ = ±1`.

This is Cerf's normal form at the parameter where a pair of nondegenerate critical points of
adjacent indices is born or dies; its cubic term is Tau Ceti's `TauCeti.birthDeathPotential 0`,
and its quadratic part has the normalization of `TauCeti.MorseChart`. A
`TauCeti.BirthDeathChart` records such a chart. Rather than repeating the fields of a centred
chart, it holds a `TauCeti.MorseBottChart` of the quadratic part of `f`, in which the cubic
coordinate `i₀` is the only coordinate of weight `0`, so that the chart calculus of Morse–Bott
charts applies to it.

A *generalized Morse function* (`TauCeti.IsGeneralizedMorse`) is a smooth function each of whose
critical points is nondegenerate or of birth–death type, as in Cieliebak–Eliashberg. These are the
functions that appear along a generic one-parameter family of functions, and in particular along a
Weinstein homotopy.

## Main declarations

* `TauCeti.BirthDeathChart`: a chart centred at a critical point in which the function is in
  birth–death normal form; `TauCeti.BirthDeathChart.restr` restricts it to an open neighbourhood
  of the centre.
* `TauCeti.BirthDeathChart.mfderiv_eq_zero_iff`: the centre is the only critical point in the
  source of the chart.
* `TauCeti.BirthDeathChart.comp`: a birth–death chart for `f` gives one for `h ∘ f`, with the same
  coordinates, weights and cubic coordinate, when `h` is smooth with `h' > 0`.
* `TauCeti.BirthDeathChart.pullback`: along a smooth local diffeomorphism `Φ : M' → M` at `y`,
  where `M'` and `M` may be modelled on different spaces, a birth–death chart for `f` at `Φ y`
  gives one for `f ∘ Φ` at `y`, of the same index (`TauCeti.BirthDeathChart.index_pullback`).
* `TauCeti.BirthDeathChart.congr`: a birth–death chart for `f` is one for any function that agrees
  with `f` on its source, so that having one depends only on the germ of the function
  (`TauCeti.BirthDeathChart.nonempty_of_eventuallyEq`).
* `TauCeti.BirthDeathChart.nonempty_of_comp_eventuallyEq`: if `f ∘ Φ` agrees near `y` with a
  function that has a birth–death chart at `y`, for a smooth local diffeomorphism `Φ` at `y`, then
  `f` has one at `Φ y`.
* `TauCeti.IsGeneralizedMorse`: smooth, with nondegenerate or birth–death critical points;
  `TauCeti.IsMorse.isGeneralizedMorse`, `TauCeti.IsGeneralizedMorse.isClosed_criticalPoints`,
  `TauCeti.IsGeneralizedMorse.isDiscrete_criticalPoints`,
  `TauCeti.IsGeneralizedMorse.finite_criticalPoints_inter_preimage_Iic`,
  `TauCeti.IsGeneralizedMorse.exists_isRegularValue_mem_Ioo`,
  `TauCeti.IsGeneralizedMorse.comp`, `TauCeti.IsGeneralizedMorse.comp_isLocalDiffeomorph` and its
  special case `TauCeti.IsGeneralizedMorse.comp_diffeomorph`.
* `TauCeti.isGeneralizedMorse_of_forall_exists_comp_eventuallyEq`: a smooth function is
  generalized Morse when near each of its critical points it is, through a local diffeomorphism,
  a generalized Morse function on another manifold.
* `TauCeti.isGeneralizedMorse_birthDeathPotential` and `TauCeti.not_isMorse_birthDeathPotential`:
  the cubic on the line is generalized Morse and not Morse.

## Implementation notes

The declarations are in the namespace `TauCeti`, since they concern only Tau Ceti's notions. The
chart `TauCeti.BirthDeathChart.comp` is built as Tau Ceti's
`TauCeti.IsManifoldNondegenerateCriticalPoint.nonempty_morseChart` builds a Morse chart: by
composing the old chart with a local diffeomorphism of the model given by the inverse function
theorem. In the chart, `h ∘ f - h (f x)` is the normal form of `f` times a smooth positive
function `a` (Hadamard's lemma, `ContDiff.exists_contDiff_sub_eq_smul`), and the local
diffeomorphism rescales the coordinates of weight `±1` by `√a` and the cubic one by `∛a`
(`SymplecticGeometry.exists_openPartialHomeomorph_pi_mul_rpow`).

`TauCeti.IsGeneralizedMorse.exists_isRegularValue_mem_Ioo` follows Tau Ceti's
`TauCeti.IsMorse.exists_isRegularValue_mem_Ioo`, with the finiteness of critical points of a
generalized Morse function in compact sets in place of that of a Morse function.

The chart `TauCeti.BirthDeathChart.pullback` is built on the pull-back of the Morse–Bott chart of
the quadratic part (`TauCeti.MorseBottChart.pullback`), whose chart is `A⁻¹ ∘ ψ ∘ Φ` near `y` for
a linear equivalence `A : E' ≃L[ℝ] E` of the models. The quadratic part of `f ∘ Φ` agrees with
that of `f` after `Φ` only on the source, so the Morse–Bott chart is moved to it by
`TauCeti.MorseBottChart.congr`. Nondegenerate critical points pull back by
`IsLocalDiffeomorphAt.isManifoldNondegenerateCriticalPoint_comp`.

The birth–death chart of `TauCeti.BirthDeathChart.nonempty_of_comp_eventuallyEq` is the pull-back
of the chart of `g` along the chosen local inverse `Ψ` of `Φ`, a chart for `g ∘ Ψ` at `Φ y`, moved
to `f` by `TauCeti.BirthDeathChart.congr` after restricting it to where `g ∘ Ψ = f`. In
`TauCeti.isGeneralizedMorse_of_forall_exists_comp_eventuallyEq`, critical points and nondegeneracy
go from `g` to `F ∘ Φ` by their germ invariance (`Filter.EventuallyEq.mem_criticalPoints_iff`,
`IsManifoldNondegenerateCriticalPoint.congr_of_eventuallyEq`), and then to `F` by
`IsLocalDiffeomorphAt.mem_criticalPoints_comp_iff` and
`IsLocalDiffeomorphAt.isManifoldNondegenerateCriticalPoint_of_comp`.

The finiteness of the critical points of a generalized Morse function in a compact set, or in a
sublevel set of a proper one bounded below, uses only that its critical points are isolated:
it follows from `TauCeti.finite_criticalPoints_inter_of_forall_eventually_notMem` and
`IsProperMap.isCompact_preimage_Iic`, which make no Morse assumption.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012]
* J. Cerf, *La stratification naturelle des espaces de fonctions différentiables réelles et le
  théorème de la pseudo-isotopie*, Publ. Math. IHÉS 39 (1970), 5–173.
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
`i₀`, with exactly one weight equal to `0`. -/
structure BirthDeathChart (f : M → ℝ) (x : M) where
  /-- The quadratic part of `f`: `f` minus the cubic term. -/
  quadraticPart : M → ℝ
  /-- The Morse–Bott chart in which the quadratic part is in normal form. -/
  toMorseBottChart : MorseBottChart E quadraticPart x
  /-- The coordinate along which `f` is cubic. -/
  cubicIndex : Fin (Module.finrank ℝ E)
  weight_cubicIndex : toMorseBottChart.weight cubicIndex = 0
  weight_ne_zero : ∀ i, i ≠ cubicIndex → toMorseBottChart.weight i ≠ 0
  eq_add : ∀ y, f y = quadraticPart y +
    birthDeathPotential 0 (toMorseBottChart.coord (toMorseBottChart.toChart y) cubicIndex)

namespace BirthDeathChart

variable (φ : BirthDeathChart E f x)

/-- The quadratic part of a birth–death chart is `f` minus the cubic term. -/
theorem quadraticPart_apply (y : M) :
    φ.quadraticPart y = f y - birthDeathPotential 0
      (φ.toMorseBottChart.coord (φ.toMorseBottChart.toChart y) φ.cubicIndex) := by
  rw [φ.eq_add y, add_sub_cancel_right]

/-- Two birth–death charts for `f` at `x` with the same chart, coordinates, weights and cubic
coordinate are equal. -/
@[ext]
theorem ext {φ₁ φ₂ : BirthDeathChart E f x}
    (htoChart : φ₁.toMorseBottChart.toChart = φ₂.toMorseBottChart.toChart)
    (hcoord : φ₁.toMorseBottChart.coord = φ₂.toMorseBottChart.coord)
    (hweight : φ₁.toMorseBottChart.weight = φ₂.toMorseBottChart.weight)
    (hcubicIndex : φ₁.cubicIndex = φ₂.cubicIndex) : φ₁ = φ₂ := by
  have hq : φ₁.quadraticPart = φ₂.quadraticPart := by
    funext y
    rw [quadraticPart_apply, quadraticPart_apply, htoChart, hcoord, hcubicIndex]
  obtain ⟨q₁, ⟨c₁, _, _, _, l₁, w₁, _, _⟩, i₁, _, _, _⟩ := φ₁
  obtain ⟨q₂, ⟨c₂, _, _, _, l₂, w₂, _, _⟩, i₂, _, _, _⟩ := φ₂
  dsimp only at htoChart hcoord hweight hcubicIndex hq
  subst hq htoChart hcoord hweight hcubicIndex
  rfl

-- The body is exposed so that `restr_toMorseBottChart` typechecks: its right side is a
-- Morse–Bott chart of `φ.quadraticPart`, which must be `(φ.restr hs hx).quadraticPart` by
-- unfolding.
/-- The restriction of a birth–death chart to an open neighbourhood `s` of its centre: the chart is
restricted to `s`, and the quadratic part, the coordinates, the weights and the cubic coordinate
are unchanged. -/
@[expose] noncomputable def restr {s : Set M} (hs : IsOpen s) (hx : x ∈ s) :
    BirthDeathChart E f x where
  quadraticPart := φ.quadraticPart
  toMorseBottChart := φ.toMorseBottChart.restr hs hx
  cubicIndex := φ.cubicIndex
  weight_cubicIndex := by rw [MorseBottChart.restr_weight]; exact φ.weight_cubicIndex
  weight_ne_zero := by rw [MorseBottChart.restr_weight]; exact φ.weight_ne_zero
  eq_add y := by
    rw [MorseBottChart.restr_coord, MorseBottChart.restr_toChart,
      OpenPartialHomeomorph.restr_apply]
    exact φ.eq_add y

section Restr

variable {s : Set M} (hs : IsOpen s) (hx : x ∈ s)

/-- Restricting a birth–death chart does not change its quadratic part. -/
@[simp]
theorem restr_quadraticPart : (φ.restr hs hx).quadraticPart = φ.quadraticPart :=
  rfl

/-- The Morse–Bott chart of a restricted birth–death chart is the restricted Morse–Bott chart. -/
@[simp]
theorem restr_toMorseBottChart :
    (φ.restr hs hx).toMorseBottChart = φ.toMorseBottChart.restr hs hx :=
  rfl

/-- Restricting a birth–death chart does not change its cubic coordinate. -/
@[simp]
theorem restr_cubicIndex : (φ.restr hs hx).cubicIndex = φ.cubicIndex :=
  rfl

end Restr

/-- The quadratic part of `f` takes the value `f x` at the centre. -/
theorem quadraticPart_self : φ.quadraticPart x = f x := by
  simp [quadraticPart_apply, birthDeathPotential_apply]

/-- The **index** of a birth–death chart: the number of negative weights. -/
noncomputable def index : ℕ :=
  {i | φ.toMorseBottChart.weight i < 0}.ncard

theorem index_def : φ.index = {i | φ.toMorseBottChart.weight i < 0}.ncard := (rfl)

/-- Restricting a birth–death chart does not change its index. -/
@[simp]
theorem restr_index {s : Set M} (hs : IsOpen s) (hx : x ∈ s) :
    (φ.restr hs hx).index = φ.index := by
  rw [index_def, index_def, restr_toMorseBottChart, MorseBottChart.restr_weight]

/-- The index of a birth–death chart is less than the dimension, since the cubic coordinate has
weight `0`. -/
theorem index_lt_finrank : φ.index < Module.finrank ℝ E := by
  have hss : {i | φ.toMorseBottChart.weight i < 0} ⊂ univ :=
    ssubset_univ_iff.2 fun h ↦ by
      have := h ▸ mem_univ φ.cubicIndex
      simp [φ.weight_cubicIndex] at this
  simpa [index_def] using Set.ncard_lt_ncard hss (toFinite _)

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

/-- Restricting a birth–death chart does not change its normal form. -/
@[simp]
theorem restr_normalForm {s : Set M} (hs : IsOpen s) (hx : x ∈ s) :
    (φ.restr hs hx).normalForm = φ.normalForm := by
  funext z
  simp [normalForm_apply]

/-- On the source of a birth–death chart, `f` is the normal form read in the chart. -/
theorem eqOn_normalForm :
    EqOn f (φ.normalForm ∘ φ.toMorseBottChart.toChart) φ.toMorseBottChart.toChart.source :=
  fun y hy ↦ by
    rw [comp_apply, normalForm, φ.eq_add y, φ.toMorseBottChart.eqOn_quadratic hy, comp_apply]

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


section Comp

/-- Rescaling the coordinates of weight `±1` by `√a` and the cubic one by `∛a` multiplies the
normal form, minus its value at the centre, by `a`. -/
private theorem normalForm_rescale {a : ℝ} (ha : 0 < a) (z : Fin (Module.finrank ℝ E) → ℝ) :
    φ.normalForm (φ.toMorseBottChart.coordL.symm
      fun i ↦ z i * a ^ (if i = φ.cubicIndex then (3 : ℝ)⁻¹ else 2⁻¹)) - f x =
      a * (φ.normalForm (φ.toMorseBottChart.coordL.symm z) - f x) := by
  have h2 : (a ^ (2⁻¹ : ℝ)) ^ 2 = a := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le]
    norm_num
  have h3 : (a ^ (3⁻¹ : ℝ)) ^ 3 = a := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le]
    norm_num
  have hsum : ∑ i, φ.toMorseBottChart.weight i *
      (z i * a ^ (if i = φ.cubicIndex then (3 : ℝ)⁻¹ else 2⁻¹)) ^ 2 =
      a * ∑ i, φ.toMorseBottChart.weight i * z i ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    by_cases hi : i = φ.cubicIndex
    · simp [hi, φ.weight_cubicIndex]
    · simp only [hi, ↓reduceIte, mul_pow, h2]
      ring
  simp only [normalForm_apply, MorseBottChart.coordL_symm_apply, LinearEquiv.apply_symm_apply]
  rw [hsum]
  simp only [birthDeathPotential_apply, ↓reduceIte, mul_pow, h3]
  ring

variable [IsManifold 𝓘(ℝ, E) ∞ M]

/-- A birth–death chart for `h ∘ f` with the coordinates, weights and cubic coordinate of `φ`. -/
private theorem exists_comp {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (hpos : 0 < deriv h (f x)) :
    ∃ φ' : BirthDeathChart E (h ∘ f) x, φ'.toMorseBottChart.coord = φ.toMorseBottChart.coord ∧
      φ'.toMorseBottChart.weight = φ.toMorseBottChart.weight ∧ φ'.cubicIndex = φ.cubicIndex := by
  classical
  have := φ.toMorseBottChart.finiteDimensional
  set ψ := φ.toMorseBottChart.toChart
  set L := φ.toMorseBottChart.coordL
  set i₀ := φ.cubicIndex
  set c := f x
  -- `h t = h c + (t - c) G t` with `G` smooth and `G c = h' c > 0`.
  obtain ⟨G, hGs, hhG, hGc⟩ :=
    ContDiff.exists_contDiff_sub_eq_smul (n := ⊤) (f := h) (by simpa using hh) c
  have hhG' : h = fun t ↦ h c + (t - c) * G t := funext fun t ↦ by
    rw [← smul_eq_mul, ← hhG]
    ring
  -- The normal form in the coordinates `L`, minus `f x`.
  set U : (Fin (Module.finrank ℝ E) → ℝ) → ℝ := fun z ↦ φ.normalForm (L.symm z) - c with hU
  have hUs : ContDiff ℝ ∞ U := (φ.contDiff_normalForm.comp L.symm.contDiff).sub contDiff_const
  have hUc : ∀ z, U z = (2 : ℝ)⁻¹ * ∑ i, φ.toMorseBottChart.weight i * z i ^ 2 +
      birthDeathPotential 0 (z i₀) := fun z ↦ by
    simp only [hU, normalForm_apply, L, MorseBottChart.coordL_symm_apply,
      LinearEquiv.apply_symm_apply]
    ring
  have hfU : ∀ y ∈ ψ.source, f y = c + U (L (ψ y)) := fun y hy ↦ by
    simp only [hU, ContinuousLinearEquiv.symm_apply_apply]
    rw [φ.eqOn_normalForm hy, comp_apply]
    ring
  set a : (Fin (Module.finrank ℝ E) → ℝ) → ℝ := fun z ↦ G (c + U z) with ha
  have has : ContDiff ℝ ∞ a := hGs.comp (contDiff_const.add hUs)
  have ha0 : 0 < a 0 := by
    simpa [ha, hUc, birthDeathPotential_apply, hGc] using hpos
  -- The rescaled coordinates `W z = (zᵢ a(z) ^ pᵢ)ᵢ`, a local diffeomorphism at `0`.
  set p : Fin (Module.finrank ℝ E) → ℝ := fun i ↦ if i = i₀ then (3 : ℝ)⁻¹ else 2⁻¹
  set W : (Fin (Module.finrank ℝ E) → ℝ) → Fin (Module.finrank ℝ E) → ℝ :=
    fun z i ↦ z i * a z ^ p i with hW
  have hWU : ∀ z, 0 < a z → U (W z) = a z * U z := fun z hz ↦ φ.normalForm_rescale hz z
  -- The rescaling is a local diffeomorphism at `0`; read it in `E` through `L`.
  obtain ⟨Θ₀, hΘ₀, h0Θ₀, hΘ₀S, hΘ₀s, hΘ₀symm⟩ :=
    SymplecticGeometry.exists_openPartialHomeomorph_pi_mul_rpow has (by simp) ha0 p
  set Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞ := L.toPartialDiffeomorph.trans
    ((TauCeti.PartialDiffeomorph.ofOpenPartialHomeomorph Θ₀ hΘ₀s hΘ₀symm).trans
      L.symm.toPartialDiffeomorph) with hΦ
  set Θ := Φ.toOpenPartialHomeomorph with hΘ
  have hΘs : ContDiffOn ℝ ∞ Θ Θ.source := contMDiffOn_iff_contDiffOn.1 Φ.contMDiffOn
  have hΘsymm : ContDiffOn ℝ ∞ Θ.symm Θ.target :=
    contMDiffOn_iff_contDiffOn.1 Φ.symm.contMDiffOn
  have hΘc : ∀ v, Θ v = L.symm (Θ₀ (L v)) := fun v ↦ by
    simp [hΘ, hΦ]
  have hΘsrc : ∀ v, v ∈ Θ.source ↔ L v ∈ Θ₀.source := fun v ↦ by
    simp [hΘ, hΦ]
  have hψx : ψ x = 0 := φ.toMorseBottChart.apply_self
  have hΘ0 : Θ 0 = 0 := by simp [hΘc, hΘ₀, Pi.zero_def]
  have hcoord : ∀ y ∈ (ψ.trans Θ).source,
      φ.toMorseBottChart.coord ((ψ.trans Θ) y) = W (L (ψ y)) := fun y _ ↦ by
    simp [hΘc, hΘ₀, hW, L]
  have hkey : ∀ y ∈ (ψ.trans Θ).source,
      h (f y) = h c + U (φ.toMorseBottChart.coord ((ψ.trans Θ) y)) := fun y hy ↦ by
    have hay : 0 < a (L (ψ y)) := hΘ₀S ((hΘsrc _).1 hy.2)
    rw [hcoord y hy, hWU _ hay, hhG', hfU y hy.1]
    simp only [ha]
    ring
  have hx' : x ∈ (ψ.trans Θ).source :=
    ⟨φ.toMorseBottChart.mem_source, (hΘsrc _).2 (by simpa [hψx] using h0Θ₀)⟩
  refine ⟨{
    quadraticPart := fun y ↦ h (f y) -
      birthDeathPotential 0 (φ.toMorseBottChart.coord ((ψ.trans Θ) y) i₀)
    toMorseBottChart := {
      toChart := ψ.trans Θ
      mem_maximalAtlas := trans_mem_maximalAtlas_of_contDiffAt
        φ.toMorseBottChart.mem_maximalAtlas
        (fun z hz ↦ (hΘs z hz).contDiffAt (Θ.open_source.mem_nhds hz))
        (fun z hz ↦ (hΘsymm z hz).contDiffAt (Θ.open_target.mem_nhds hz))
      mem_source := hx'
      apply_self := by simp [hψx, hΘ0]
      coord := φ.toMorseBottChart.coord
      weight := φ.toMorseBottChart.weight
      weight_eq_neg_one_or_eq_zero_or_eq_one :=
        φ.toMorseBottChart.weight_eq_neg_one_or_eq_zero_or_eq_one
      eq_quadratic := fun y hy ↦ by
        rw [hkey y hy, hkey x hx', hUc, hUc]
        simp [hψx, hΘ0, birthDeathPotential_apply]
        ring }
    cubicIndex := i₀
    weight_cubicIndex := φ.weight_cubicIndex
    weight_ne_zero := φ.weight_ne_zero
    eq_add := fun y ↦ by simp }, rfl, rfl, rfl⟩

/-- The birth–death chart for `h ∘ f` at `x` given by `φ`, when `h` is smooth with `h' > 0` at
`f x`. It has the coordinates, the weights and the cubic coordinate of `φ`. -/
noncomputable def comp {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (hpos : 0 < deriv h (f x)) :
    BirthDeathChart E (h ∘ f) x :=
  (φ.exists_comp hh hpos).choose

section

variable {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (hpos : 0 < deriv h (f x))

/-- The birth–death chart of `h ∘ f` has the coordinates of `φ`. -/
@[simp]
theorem comp_coord : (φ.comp hh hpos).toMorseBottChart.coord = φ.toMorseBottChart.coord :=
  (φ.exists_comp hh hpos).choose_spec.1

/-- The birth–death chart of `h ∘ f` has the weights of `φ`. -/
@[simp]
theorem comp_weight : (φ.comp hh hpos).toMorseBottChart.weight = φ.toMorseBottChart.weight :=
  (φ.exists_comp hh hpos).choose_spec.2.1

/-- The birth–death chart of `h ∘ f` has the cubic coordinate of `φ`. -/
@[simp]
theorem comp_cubicIndex : (φ.comp hh hpos).cubicIndex = φ.cubicIndex :=
  (φ.exists_comp hh hpos).choose_spec.2.2

/-- The birth–death chart of `h ∘ f` has the index of `φ`. -/
@[simp]
theorem index_comp : (φ.comp hh hpos).index = φ.index := by
  rw [index_def, index_def, comp_weight]

end

end Comp

end BirthDeathChart

/-! ### Pull-back along a local diffeomorphism -/

section Pullback

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace E' M'] [IsManifold 𝓘(ℝ, E') ∞ M']
  {Φ : M' → M} {y : M'} (φ : BirthDeathChart E f (Φ y))
  (hΦ : IsLocalDiffeomorphAt 𝓘(ℝ, E') 𝓘(ℝ, E) ∞ Φ y) (A : E' ≃L[ℝ] E)

namespace BirthDeathChart

/-- The quadratic part of `TauCeti.BirthDeathChart.pullback`: `f ∘ Φ` minus the cubic term of the
pulled-back coordinates. -/
private noncomputable def pullbackQuadraticPart (z : M') : ℝ :=
  f (Φ z) - birthDeathPotential 0 ((φ.toMorseBottChart.pullback hΦ A).coord
    ((φ.toMorseBottChart.pullback hΦ A).toChart z) ((finCongr A.toLinearEquiv.finrank_eq).symm
      φ.cubicIndex))

private theorem eqOn_pullbackQuadraticPart :
    EqOn (pullbackQuadraticPart φ hΦ A) (φ.quadraticPart ∘ Φ)
      (φ.toMorseBottChart.pullback hΦ A).toChart.source := fun z hz ↦ by
  rw [pullbackQuadraticPart, MorseBottChart.pullback_coord_apply, Equiv.apply_symm_apply,
    MorseBottChart.pullback_apply _ hΦ A hz, comp_apply, φ.quadraticPart_apply]

/-- The **pull-back of a birth–death chart along a local diffeomorphism.** If `Φ : M' → M` is a
smooth local diffeomorphism at `y`, where `M'` is modelled on `E'` and `M` on `E`, and
`A : E' ≃L[ℝ] E` is a linear equivalence of the models, such as the derivative of `Φ` at `y`, then
a birth–death chart `φ` for `f` at `Φ y` gives a birth–death chart for `f ∘ Φ` at `y`. Its
Morse–Bott chart is the pull-back of that of `φ` (`TauCeti.MorseBottChart.pullback`), and its
cubic coordinate is that of `φ`, reindexed along `finrank E' = finrank E`. -/
noncomputable def pullback : BirthDeathChart E' (f ∘ Φ) y where
  quadraticPart := pullbackQuadraticPart φ hΦ A
  toMorseBottChart :=
    (φ.toMorseBottChart.pullback hΦ A).congr (eqOn_pullbackQuadraticPart φ hΦ A)
  cubicIndex := (finCongr A.toLinearEquiv.finrank_eq).symm φ.cubicIndex
  weight_cubicIndex := by
    rw [MorseBottChart.congr_weight, MorseBottChart.pullback_weight, comp_apply,
      Equiv.apply_symm_apply, φ.weight_cubicIndex]
  weight_ne_zero i hi := by
    rw [MorseBottChart.congr_weight, MorseBottChart.pullback_weight, comp_apply]
    exact φ.weight_ne_zero _ fun h ↦ hi (by rw [← h, Equiv.symm_apply_apply])
  eq_add z := by
    rw [MorseBottChart.congr_coord, MorseBottChart.congr_toChart, pullbackQuadraticPart,
      comp_apply, sub_add_cancel]

/-- The chart of the pull-back of a birth–death chart is that of the pull-back of its Morse–Bott
chart. -/
@[simp]
theorem pullback_toChart :
    (φ.pullback hΦ A).toMorseBottChart.toChart = (φ.toMorseBottChart.pullback hΦ A).toChart :=
  MorseBottChart.congr_toChart _ _

/-- The coordinates of the pull-back of a birth–death chart are those of the pull-back of its
Morse–Bott chart. -/
@[simp]
theorem pullback_coord :
    (φ.pullback hΦ A).toMorseBottChart.coord = (φ.toMorseBottChart.pullback hΦ A).coord :=
  MorseBottChart.congr_coord _ _

/-- The weights of the pull-back of a birth–death chart are those of the pull-back of its
Morse–Bott chart. -/
@[simp]
theorem pullback_weight :
    (φ.pullback hΦ A).toMorseBottChart.weight = (φ.toMorseBottChart.pullback hΦ A).weight :=
  MorseBottChart.congr_weight _ _

/-- The quadratic normal form of the Morse–Bott chart of the pull-back of a birth–death chart is
that of `φ` after `A`. -/
@[simp]
theorem pullback_quadratic :
    (φ.pullback hΦ A).toMorseBottChart.quadratic = φ.toMorseBottChart.quadratic ∘ A :=
  (MorseBottChart.congr_quadratic _ _).trans (MorseBottChart.pullback_quadratic _ hΦ A)

/-- The cubic coordinate of the pull-back of a birth–death chart is that of `φ`, reindexed along
`finrank E' = finrank E`. -/
@[simp]
theorem pullback_cubicIndex :
    (φ.pullback hΦ A).cubicIndex = (finCongr A.toLinearEquiv.finrank_eq).symm φ.cubicIndex :=
  (rfl)

/-- On the source of the chart, the quadratic part of the pull-back of a birth–death chart along
`Φ` is that of `φ` after `Φ`. -/
theorem eqOn_pullback_quadraticPart :
    EqOn (φ.pullback hΦ A).quadraticPart (φ.quadraticPart ∘ Φ)
      (φ.pullback hΦ A).toMorseBottChart.toChart.source :=
  pullback_toChart φ hΦ A ▸ eqOn_pullbackQuadraticPart φ hΦ A

/-- Pulling a birth–death chart back along a local diffeomorphism keeps its index. -/
@[simp]
theorem index_pullback : (φ.pullback hΦ A).index = φ.index := by
  rw [index_def, index_def, pullback_weight, MorseBottChart.pullback_weight]
  exact Set.ncard_preimage_of_injective_subset_range (s := {i | φ.toMorseBottChart.weight i < 0})
    (finCongr _).injective (by simp)

/-- The normal form of the pull-back of a birth–death chart along `Φ` is that of `φ` after `A`. -/
@[simp]
theorem normalForm_pullback : (φ.pullback hΦ A).normalForm = φ.normalForm ∘ A := by
  funext z
  simp [normalForm]

end BirthDeathChart

end Pullback

/-! ### Changing the function near the centre -/

namespace BirthDeathChart

section Congr

variable (φ : BirthDeathChart E f x) {g : M → ℝ}
  (h : EqOn g f φ.toMorseBottChart.toChart.source)

/-- The quadratic part of `TauCeti.BirthDeathChart.congr`: `g` minus the cubic term of `φ`. -/
private noncomputable def congrQuadraticPart (g : M → ℝ) (z : M) : ℝ :=
  g z - birthDeathPotential 0
    (φ.toMorseBottChart.coord (φ.toMorseBottChart.toChart z) φ.cubicIndex)

include h in
private theorem eqOn_congrQuadraticPart :
    EqOn (congrQuadraticPart φ g) φ.quadraticPart φ.toMorseBottChart.toChart.source :=
  fun z hz ↦ by rw [congrQuadraticPart, h hz, φ.quadraticPart_apply]

/-- A birth–death chart `φ` for `f` at `x` is a birth–death chart for any `g` that agrees with `f`
on the source of `φ`, with the chart, the coordinates, the weights and the cubic coordinate of
`φ`. Its quadratic part is `g` minus the cubic term. -/
noncomputable def congr : BirthDeathChart E g x where
  quadraticPart := congrQuadraticPart φ g
  toMorseBottChart := φ.toMorseBottChart.congr (eqOn_congrQuadraticPart φ h)
  cubicIndex := φ.cubicIndex
  weight_cubicIndex := by rw [MorseBottChart.congr_weight]; exact φ.weight_cubicIndex
  weight_ne_zero := by rw [MorseBottChart.congr_weight]; exact φ.weight_ne_zero
  eq_add z := by
    rw [MorseBottChart.congr_coord, MorseBottChart.congr_toChart, congrQuadraticPart,
      sub_add_cancel]

/-- The chart of `φ.congr h` is that of `φ`. -/
@[simp]
theorem congr_toChart : (φ.congr h).toMorseBottChart.toChart = φ.toMorseBottChart.toChart :=
  MorseBottChart.congr_toChart _ _

/-- The coordinates of `φ.congr h` are those of `φ`. -/
@[simp]
theorem congr_coord : (φ.congr h).toMorseBottChart.coord = φ.toMorseBottChart.coord :=
  MorseBottChart.congr_coord _ _

/-- The weights of `φ.congr h` are those of `φ`. -/
@[simp]
theorem congr_weight : (φ.congr h).toMorseBottChart.weight = φ.toMorseBottChart.weight :=
  MorseBottChart.congr_weight _ _

/-- The cubic coordinate of `φ.congr h` is that of `φ`. -/
@[simp]
theorem congr_cubicIndex : (φ.congr h).cubicIndex = φ.cubicIndex :=
  (rfl)

/-- The quadratic normal form of the Morse–Bott chart of `φ.congr h` is that of `φ`. -/
@[simp]
theorem congr_quadratic :
    (φ.congr h).toMorseBottChart.quadratic = φ.toMorseBottChart.quadratic :=
  MorseBottChart.congr_quadratic _ _

/-- On the source of the chart, the quadratic part of `φ.congr h` is that of `φ`. -/
theorem eqOn_congr_quadraticPart :
    EqOn (φ.congr h).quadraticPart φ.quadraticPart
      (φ.congr h).toMorseBottChart.toChart.source :=
  congr_toChart φ h ▸ eqOn_congrQuadraticPart φ h

/-- Changing the function off the source of a birth–death chart keeps its index. -/
@[simp]
theorem index_congr : (φ.congr h).index = φ.index := by
  rw [index_def, index_def, congr_weight]

/-- Changing the function off the source of a birth–death chart keeps its normal form. -/
@[simp]
theorem normalForm_congr : (φ.congr h).normalForm = φ.normalForm := by
  funext z
  simp [normalForm]

end Congr

/-- Having a birth–death chart at `x` depends only on the germ of the function at `x`. -/
theorem nonempty_of_eventuallyEq (φ : BirthDeathChart E f x) {g : M → ℝ} (hfg : f =ᶠ[𝓝 x] g) :
    Nonempty (BirthDeathChart E g x) := by
  obtain ⟨s, hfs, hs, hx⟩ := eventually_nhds_iff.1 hfg
  refine ⟨(φ.restr hs hx).congr fun z hz ↦ (hfs z ?_).symm⟩
  rw [restr_toMorseBottChart, MorseBottChart.restr_source] at hz
  exact hz.2

end BirthDeathChart

/-! ### Birth–death charts from local models -/

section LocalModel

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace E' M'] [IsManifold 𝓘(ℝ, E) ∞ M]
  {g : M' → ℝ} {Φ : M' → M} {y : M'}

/-- **Birth–death charts from a local model.** If `Φ : M' → M` is a smooth local diffeomorphism at
`y`, where `M'` is modelled on `E'` and `M` on `E`, and `f ∘ Φ` agrees near `y` with a function `g`
that has a birth–death chart at `y`, then `f` has a birth–death chart at `Φ y`. It is the pull-back
of the chart of `g` along the local inverse of `Φ`. -/
theorem BirthDeathChart.nonempty_of_comp_eventuallyEq (φ : BirthDeathChart E' g y)
    (hΦ : IsLocalDiffeomorphAt 𝓘(ℝ, E') 𝓘(ℝ, E) ∞ Φ y) (hfg : f ∘ Φ =ᶠ[𝓝 y] g) :
    Nonempty (BirthDeathChart E f (Φ y)) := by
  have hy : hΦ.localInverse (Φ y) = y := hΦ.localInverse_left_inv hΦ.localInverse_mem_target
  have hΨ := hΦ.localInverse_isLocalDiffeomorphAt
  refine ((hy.symm ▸ φ : BirthDeathChart E' g (hΦ.localInverse (Φ y))).pullback hΨ
    (hΨ.mfderivToContinuousLinearEquiv (by simp))).nonempty_of_eventuallyEq ?_
  have ht := hΦ.continuousAt_localInverse.tendsto
  rw [hy] at ht
  filter_upwards [hfg.comp_tendsto ht, hΦ.localInverse_eventuallyEq_right] with z h₁ h₂
  simp only [comp_apply, id_eq] at h₁ h₂ ⊢
  rw [← h₁, h₂]

end LocalModel

/-! ### Generalized Morse functions -/

variable (E) in
/-- A **generalized Morse function**: a smooth function each of whose critical points is either
nondegenerate or the centre of a birth–death chart. -/
def IsGeneralizedMorse (f : M → ℝ) : Prop :=
  ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f ∧ ∀ x ∈ criticalPoints 𝓘(ℝ, E) f,
    IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f x ∨ Nonempty (BirthDeathChart E f x)

theorem isGeneralizedMorse_iff : IsGeneralizedMorse E f ↔
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f ∧ ∀ x ∈ criticalPoints 𝓘(ℝ, E) f,
      IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f x ∨ Nonempty (BirthDeathChart E f x) :=
  Iff.rfl

namespace IsGeneralizedMorse

/-- A generalized Morse function is smooth. -/
theorem contMDiff (hf : IsGeneralizedMorse E f) : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f :=
  hf.1

/-- Each critical point of a generalized Morse function is nondegenerate or a birth–death
centre. -/
theorem isManifoldNondegenerateCriticalPoint_or_nonempty (hf : IsGeneralizedMorse E f)
    (hx : x ∈ criticalPoints 𝓘(ℝ, E) f) :
    IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f x ∨ Nonempty (BirthDeathChart E f x) :=
  hf.2 x hx

/-- Near a point, a generalized Morse function has no critical point other than that point. -/
theorem eventually_eq_of_mem_criticalPoints [IsManifold 𝓘(ℝ, E) 1 M]
    (hf : IsGeneralizedMorse E f) (x : M) :
    ∀ᶠ y in 𝓝 x, y ∈ criticalPoints 𝓘(ℝ, E) f → y = x := by
  by_cases hx : x ∈ criticalPoints 𝓘(ℝ, E) f
  · rcases hf.2 x hx with hnd | hbd
    · exact TauCeti.eventually_eq_of_mem_criticalPoints
        ((hf.contMDiff x).of_le (by simp)) fun _ ↦ hnd
    · exact hbd.some.eventually_eq_of_mem_criticalPoints
  · exact TauCeti.eventually_eq_of_mem_criticalPoints ((hf.contMDiff x).of_le (by simp))
      fun h ↦ (hx h).elim

/-- Each point has a punctured neighbourhood free of critical points of a generalized Morse
function. -/
theorem eventually_notMem_criticalPoints [IsManifold 𝓘(ℝ, E) 1 M]
    (hf : IsGeneralizedMorse E f) (x : M) :
    ∀ᶠ y in 𝓝[≠] x, y ∉ criticalPoints 𝓘(ℝ, E) f := by
  filter_upwards [nhdsWithin_le_nhds (hf.eventually_eq_of_mem_criticalPoints x),
    self_mem_nhdsWithin] with y hy hyx using fun hyc ↦ hyx (hy hyc)

/-- The critical set of a generalized Morse function is closed. -/
theorem isClosed_criticalPoints [IsManifold 𝓘(ℝ, E) 1 M] (hf : IsGeneralizedMorse E f) :
    IsClosed (criticalPoints 𝓘(ℝ, E) f) :=
  TauCeti.isClosed_criticalPoints (hf.contMDiff.of_le (by simp))

/-- The critical set of a generalized Morse function is discrete. -/
theorem isDiscrete_criticalPoints [IsManifold 𝓘(ℝ, E) 1 M] (hf : IsGeneralizedMorse E f) :
    IsDiscrete (criticalPoints 𝓘(ℝ, E) f) :=
  isDiscrete_iff_nhdsNE.2 fun x _ ↦ inf_principal_eq_bot.2 (hf.eventually_notMem_criticalPoints x)

/-- A generalized Morse function has finitely many critical points in each compact set. -/
theorem finite_criticalPoints_inter [IsManifold 𝓘(ℝ, E) 1 M] (hf : IsGeneralizedMorse E f)
    {K : Set M} (hK : IsCompact K) : (criticalPoints 𝓘(ℝ, E) f ∩ K).Finite :=
  finite_criticalPoints_inter_of_forall_eventually_notMem (hf.contMDiff.of_le (by simp)) hK
    fun x _ ↦ hf.eventually_notMem_criticalPoints x

/-- A proper generalized Morse function bounded below has finitely many critical points in each
sublevel set. -/
theorem finite_criticalPoints_inter_preimage_Iic [IsManifold 𝓘(ℝ, E) 1 M]
    (hf : IsGeneralizedMorse E f) (hp : IsProperMap f) (hbdd : BddBelow (range f)) (b : ℝ) :
    (criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Iic b).Finite :=
  hf.finite_criticalPoints_inter (hp.isCompact_preimage_Iic hbdd b)

/-- A compact band `f ⁻¹' [a, b]` of a generalized Morse function contains only finitely many
critical values, so there is a regular value strictly between `a` and `b` whenever `a < b`. -/
theorem exists_isRegularValue_mem_Ioo [IsManifold 𝓘(ℝ, E) 1 M] (hf : IsGeneralizedMorse E f)
    {a b : ℝ} (hab : a < b) (hcompact : IsCompact (f ⁻¹' Icc a b)) :
    ∃ c ∈ Ioo a b, IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f c := by
  obtain ⟨c, hc, hnot⟩ :=
    ((Ioo_infinite hab).sdiff ((hf.finite_criticalPoints_inter hcompact).image f)).nonempty
  refine ⟨c, hc, isRegularValue_iff_notMem_image_criticalPoints.2 ?_⟩
  rintro ⟨x, hx, rfl⟩
  exact hnot ⟨x, ⟨hx, hc.1.le, hc.2.le⟩, rfl⟩

/-- Composing a generalized Morse function with a smooth `h : ℝ → ℝ` with `h' > 0` on the values
of `f` gives a generalized Morse function. -/
theorem comp [IsManifold 𝓘(ℝ, E) ∞ M] (hf : IsGeneralizedMorse E f) {h : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (hpos : ∀ x, 0 < deriv h (f x)) : IsGeneralizedMorse E (h ∘ f) := by
  refine ⟨hh.contMDiff.comp hf.contMDiff, fun x hx ↦ ?_⟩
  have hfx : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) f x :=
    (hf.contMDiff x).mdifferentiableAt (by simp)
  rw [mem_criticalPoints_scalar_comp_iff hfx (hpos x).ne'] at hx
  rcases hf.2 x hx with hnd | hbd
  · exact .inl (hnd.scalar_comp (hh.contDiffAt.of_le (by simp)) (hpos x).ne')
  · exact .inr ⟨hbd.some.comp hh (hpos x)⟩

/-- **Generalized Morse functions pull back along local diffeomorphisms.** If `Φ : M' → M` is a
smooth local diffeomorphism between boundaryless manifolds modelled on `E'` and on `E`, which may
differ, and `f` is a generalized Morse function, then so is `f ∘ Φ`. -/
theorem comp_isLocalDiffeomorph {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace E' M'] [IsManifold 𝓘(ℝ, E') ∞ M']
    (hf : IsGeneralizedMorse E f) {Φ : M' → M} (hΦ : IsLocalDiffeomorph 𝓘(ℝ, E') 𝓘(ℝ, E) ∞ Φ) :
    IsGeneralizedMorse E' (f ∘ Φ) := by
  refine ⟨hf.contMDiff.comp hΦ.contMDiff, fun y hy ↦ ?_⟩
  rw [(hΦ y).mem_criticalPoints_comp_iff (by simp)] at hy
  rcases hf.2 (Φ y) hy with hnd | hbd
  · exact .inl ((hΦ y).isManifoldNondegenerateCriticalPoint_comp (by simp) hnd)
  · exact .inr ⟨hbd.some.pullback (hΦ y) ((hΦ y).mfderivToContinuousLinearEquiv (by simp))⟩

/-- Pulling a generalized Morse function back along a diffeomorphism `σ : M' ≃ M` gives a
generalized Morse function. -/
theorem comp_diffeomorph {M' : Type*} [TopologicalSpace M'] [ChartedSpace E M']
    [IsManifold 𝓘(ℝ, E) ∞ M'] (hf : IsGeneralizedMorse E f) (σ : M' ≃ₘ^∞⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M) :
    IsGeneralizedMorse E (f ∘ σ) :=
  hf.comp_isLocalDiffeomorph σ.isLocalDiffeomorph

end IsGeneralizedMorse

/-- **Generalized Morse functions from local models.** Let `F : M → ℝ` be smooth, and let
`g : M' → ℝ` be a generalized Morse function on a boundaryless manifold `M'`, modelled on `E'`,
and `Φ : M' → M`. If each critical point of `F` is `Φ y` for a point `y` at which `Φ` is a smooth
local diffeomorphism and near which `F ∘ Φ` agrees with `g`, then `F` is a generalized Morse
function. -/
theorem isGeneralizedMorse_of_forall_exists_comp_eventuallyEq [IsManifold 𝓘(ℝ, E) ∞ M]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace E' M'] {F : M → ℝ}
    (hF : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ F) {g : M' → ℝ} (hg : IsGeneralizedMorse E' g) {Φ : M' → M}
    (h : ∀ x ∈ criticalPoints 𝓘(ℝ, E) F, ∃ y, Φ y = x ∧
      IsLocalDiffeomorphAt 𝓘(ℝ, E') 𝓘(ℝ, E) ∞ Φ y ∧ F ∘ Φ =ᶠ[𝓝 y] g) :
    IsGeneralizedMorse E F := by
  refine ⟨hF, fun x hx ↦ ?_⟩
  obtain ⟨y, rfl, hΦ, hFg⟩ := h x hx
  rw [← hΦ.mem_criticalPoints_comp_iff (by simp), hFg.mem_criticalPoints_iff] at hx
  rcases hg.2 y hx with hnd | hbd
  · exact .inl (hΦ.isManifoldNondegenerateCriticalPoint_of_comp (by simp)
      (hnd.congr_of_eventuallyEq hFg.symm))
  · exact .inr (hbd.some.nonempty_of_comp_eventuallyEq hΦ hFg)

/-- A Morse function is a generalized Morse function. -/
theorem IsMorse.isGeneralizedMorse (hf : IsMorse 𝓘(ℝ, E) f) : IsGeneralizedMorse E f :=
  ⟨hf.contMDiff, fun _ hx ↦ .inl (hf.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints hx)⟩

/-! ### The cubic on the line -/

/-- The birth–death chart of the cubic `t ↦ t³ / 3` at the origin of the line: the identity chart,
with the single coordinate cubic. -/
noncomputable def birthDeathChartBirthDeathPotential :
    BirthDeathChart ℝ (birthDeathPotential 0) (0 : ℝ) :=
  haveI : Unique (Fin (Module.finrank ℝ ℝ)) := by
    rw [Module.finrank_self]
    infer_instance
  { quadraticPart := fun _ ↦ 0
    toMorseBottChart :=
      { toChart := chartAt ℝ (0 : ℝ)
        mem_maximalAtlas := IsManifold.chart_mem_maximalAtlas (0 : ℝ)
        mem_source := mem_chart_source ℝ (0 : ℝ)
        apply_self := by simp
        coord := (LinearEquiv.funUnique (Fin (Module.finrank ℝ ℝ)) ℝ ℝ).symm
        weight := 0
        weight_eq_neg_one_or_eq_zero_or_eq_one := fun _ ↦ .inr (.inl rfl)
        eq_quadratic := fun _ _ ↦ by simp }
    cubicIndex := default
    weight_cubicIndex := rfl
    weight_ne_zero := fun i hi ↦ (hi (Subsingleton.elim _ _)).elim
    eq_add := fun y ↦ by simp }

/-- The cubic `t ↦ t³ / 3` on the line is a generalized Morse function. -/
theorem isGeneralizedMorse_birthDeathPotential :
    IsGeneralizedMorse ℝ (birthDeathPotential 0) := by
  refine ⟨(contDiff_birthDeathPotential 0).contMDiff, fun x hx ↦ .inr ?_⟩
  rw [mem_criticalPoints_iff_deriv_eq_zero, deriv_birthDeathPotential] at hx
  simp only [sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff] at hx
  subst hx
  exact ⟨birthDeathChartBirthDeathPotential⟩

/-- The cubic `t ↦ t³ / 3` on the line is not a Morse function: its critical point `0` is
degenerate. -/
theorem not_isMorse_birthDeathPotential : ¬IsMorse 𝓘(ℝ, ℝ) (birthDeathPotential 0) := fun h ↦
  not_isNondegenerateCriticalPoint_birthDeathPotential_zero <|
    isManifoldNondegenerateCriticalPoint_modelSpace_iff.1 <|
      h.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints
        birthDeathChartBirthDeathPotential.mem_criticalPoints

end TauCeti

end
