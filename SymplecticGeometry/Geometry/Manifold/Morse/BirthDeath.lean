/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.BirthDeath
public import TauCeti.Geometry.Manifold.Morse.Bott.Chart.Basic
public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import TauCeti.Analysis.Calculus.Hadamard
import TauCeti.Analysis.Calculus.InverseFunctionTheorem
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
* `TauCeti.BirthDeathChart.nonempty_comp`: a birth–death chart for `f` gives one for `h ∘ f` when
  `h` is smooth with `h' > 0`.
* `TauCeti.IsGeneralizedMorse`: smooth, with nondegenerate or birth–death critical points;
  `TauCeti.IsMorse.isGeneralizedMorse`, `TauCeti.IsGeneralizedMorse.isClosed_criticalPoints`,
  `TauCeti.IsGeneralizedMorse.isDiscrete_criticalPoints`,
  `TauCeti.IsGeneralizedMorse.finite_criticalPoints_inter_preimage_Iic` and
  `TauCeti.IsGeneralizedMorse.comp`.
* `TauCeti.isGeneralizedMorse_birthDeathPotential` and `TauCeti.not_isMorse_birthDeathPotential`:
  the cubic on the line is generalized Morse and not Morse.

## Implementation notes

The declarations are in the namespace `TauCeti`, since they concern only Tau Ceti's notions. The
proof of `TauCeti.BirthDeathChart.nonempty_comp` builds the new chart as Tau Ceti's
`TauCeti.IsManifoldNondegenerateCriticalPoint.nonempty_morseChart` builds a Morse chart: by
composing the old chart with a local diffeomorphism of the model given by the inverse function
theorem (`TauCeti.ContDiffOn.exists_openPartialHomeomorph`).

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

/-- The index of a birth–death chart is less than the dimension, since the cubic coordinate has
weight `0`. -/
theorem index_lt_finrank : φ.index < Module.finrank ℝ E := by
  have hss : {i | φ.toMorseBottChart.weight i < 0} ⊂ univ :=
    ssubset_univ_iff.2 fun h ↦ by
      have := h ▸ mem_univ φ.cubicIndex
      simp [φ.weight_cubicIndex] at this
  simpa [index] using Set.ncard_lt_ncard hss (toFinite _)

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

section Comp

/-- The cubic normal form in coordinates: `z ↦ (1/2) Σᵢ wᵢ zᵢ² + z_{i₀}³ / 3`. -/
private noncomputable def coordForm {n : ℕ} (w : Fin n → ℝ) (i₀ : Fin n) (z : Fin n → ℝ) : ℝ :=
  (2 : ℝ)⁻¹ * ∑ i, w i * z i ^ 2 + birthDeathPotential 0 (z i₀)

/-- Rescaling the coordinates of weight `±1` by `√a` and the cubic one by `∛a` multiplies the
cubic normal form by `a`. -/
private theorem coordForm_rescale {n : ℕ} {w : Fin n → ℝ} {i₀ : Fin n} (hw : w i₀ = 0)
    {a : ℝ} (ha : 0 < a) (z : Fin n → ℝ) :
    coordForm w i₀ (fun i ↦ z i * a ^ (if i = i₀ then (3 : ℝ)⁻¹ else 2⁻¹)) =
      a * coordForm w i₀ z := by
  have h2 : (a ^ (2⁻¹ : ℝ)) ^ 2 = a := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le]
    norm_num
  have h3 : (a ^ (3⁻¹ : ℝ)) ^ 3 = a := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le]
    norm_num
  have hsum : ∑ i, w i * (z i * a ^ (if i = i₀ then (3 : ℝ)⁻¹ else 2⁻¹)) ^ 2 =
      a * ∑ i, w i * z i ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    by_cases hi : i = i₀
    · simp [hi, hw]
    · simp only [hi, ↓reduceIte, mul_pow, h2]
      ring
  unfold coordForm
  rw [hsum]
  simp only [birthDeathPotential_apply, ↓reduceIte, mul_pow, h3]
  ring

variable [IsManifold 𝓘(ℝ, E) ∞ M]

include φ in
/-- A birth–death chart for `f` at `x` gives one for `h ∘ f`, when `h` is smooth with `h' > 0` at
`f x`. In the chart, `h (f y) - h (f x)` is the normal form of `f` times a smooth positive function
`a`; rescaling the coordinates of weight `±1` by `√a` and the cubic one by `∛a` brings it back to
the normal form. The new chart has the same coordinate change, weights and cubic coordinate. -/
theorem nonempty_comp {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (hpos : 0 < deriv h (f x)) :
    Nonempty (BirthDeathChart E (h ∘ f) x) := by
  classical
  have := φ.toMorseBottChart.finiteDimensional
  set ψ := φ.toMorseBottChart.toChart
  set L := φ.toMorseBottChart.coordL
  set w := φ.toMorseBottChart.weight
  set i₀ := φ.cubicIndex
  set c := f x
  set U := coordForm w i₀ with hU
  have hfU : ∀ y ∈ ψ.source, f y = c + U (L (ψ y)) := fun y hy ↦ by
    rw [φ.eqOn_normalForm hy, comp_apply, normalForm_apply, add_assoc]
    simp [hU, coordForm, L, w, i₀]
    rfl
  -- `h t = h c + G t * (t - c)` with `G` smooth and `G c = h' c > 0`.
  set G : ℝ → ℝ := fun t ↦ hadamardFactor h c t 1 with hG
  have hGs : ContDiff ℝ ∞ G :=
    (ContDiff.contDiff_hadamardFactor h hh c).clm_apply contDiff_const
  have hhG : ∀ t, h t = h c + G t * (t - c) := fun t ↦ by
    have := ContDiff.sub_eq_hadamardFactor_apply h (hh.of_le (by simp)) c t
    rw [show t - c = (t - c) • (1 : ℝ) by simp, map_smul, smul_eq_mul] at this
    rw [hG]
    linarith
  set a : (Fin (Module.finrank ℝ E) → ℝ) → ℝ := fun z ↦ G (c + U z) with ha
  have hUs : ContDiff ℝ ∞ U := by
    simp only [hU]
    unfold coordForm
    exact (contDiff_const.mul (ContDiff.sum fun i _ ↦ contDiff_const.mul
      ((contDiff_apply ℝ (fun _ ↦ ℝ) i).pow 2))).add
        ((contDiff_birthDeathPotential 0).comp (contDiff_apply ℝ (fun _ ↦ ℝ) i₀))
  have has : ContDiff ℝ ∞ a := hGs.comp (contDiff_const.add hUs)
  have ha0 : 0 < a 0 := by
    simp only [ha, hU, coordForm, Pi.zero_apply, birthDeathPotential_apply, hG]
    norm_num
    exact hpos
  -- The rescaled coordinates.
  set p : Fin (Module.finrank ℝ E) → ℝ := fun i ↦ if i = i₀ then (3 : ℝ)⁻¹ else 2⁻¹
  set W : (Fin (Module.finrank ℝ E) → ℝ) → Fin (Module.finrank ℝ E) → ℝ :=
    fun z i ↦ z i * a z ^ p i with hW
  have hWU : ∀ z, 0 < a z → U (W z) = a z * U z := fun z hz ↦
    coordForm_rescale φ.weight_cubicIndex hz z
  have hrs : ∀ i, ∀ z, 0 < a z → ContDiffAt ℝ ∞ (fun z ↦ a z ^ p i) z := fun i z hz ↦
    (Real.contDiffAt_rpow_const_of_ne hz.ne').comp z has.contDiffAt
  have hWs : ContDiffOn ℝ ∞ W {z | 0 < a z} :=
    contDiffOn_pi.2 fun i ↦ (contDiff_apply ℝ (fun _ ↦ ℝ) i).contDiffOn.mul fun z hz ↦
      (hrs i z hz).contDiffWithinAt
  set D : (Fin (Module.finrank ℝ E) → ℝ) →L[ℝ] Fin (Module.finrank ℝ E) → ℝ :=
    ContinuousLinearMap.pi fun i ↦ a 0 ^ p i • ContinuousLinearMap.proj i with hD
  have hWD : HasFDerivAt W D 0 := by
    refine hasFDerivAt_pi'.2 fun i ↦ ?_
    have := ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (Module.finrank ℝ E) ↦ ℝ)
      i).hasFDerivAt (x := 0)).mul ((hrs i 0 ha0).differentiableAt (by simp)).hasFDerivAt
    have hfun : (fun z ↦ W z i) = ⇑(ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Fin (Module.finrank ℝ E) ↦ ℝ) i) * fun z ↦ a z ^ p i := by
      funext z
      simp [hW]
    rw [hfun]
    refine this.congr_fderiv ?_
    ext v
    simp [hD, mul_comm]
  have hpos' : ∀ i, 0 < a 0 ^ p i := fun i ↦ Real.rpow_pos_of_pos ha0 _
  set D' : (Fin (Module.finrank ℝ E) → ℝ) →L[ℝ] Fin (Module.finrank ℝ E) → ℝ :=
    ContinuousLinearMap.pi fun i ↦ (a 0 ^ p i)⁻¹ • ContinuousLinearMap.proj i with hD'
  set e := ContinuousLinearEquiv.ofContinuousLinearMap D D'
    (by ext v i; simp [hD, hD', (hpos' i).ne'])
    (by ext v i; simp [hD, hD', (hpos' i).ne']) with he
  -- The new chart, by the inverse function theorem.
  set Φ : E → E := fun v ↦ L.symm (W (L v)) with hΦ
  set S := ψ.target ∩ L ⁻¹' {z | 0 < a z}
  have hSo : IsOpen S :=
    ψ.open_target.inter ((isOpen_lt continuous_const has.continuous).preimage L.continuous)
  have hψx : ψ x = 0 := φ.toMorseBottChart.apply_self
  have h0S : (0 : E) ∈ S :=
    ⟨hψx ▸ ψ.map_source φ.toMorseBottChart.mem_source, by simpa using ha0⟩
  have hΦs : ContDiffOn ℝ ∞ Φ S :=
    L.symm.contDiff.comp_contDiffOn (hWs.comp L.contDiff.contDiffOn fun v hv ↦ hv.2)
  have hΦD : HasFDerivAt Φ ((L.symm : _ →L[ℝ] E).comp (D.comp (L : E →L[ℝ] _))) 0 := by
    have hW' : HasFDerivAt W D (L 0) := by simpa using hWD
    exact L.symm.hasFDerivAt.comp 0 (hW'.comp 0 L.hasFDerivAt)
  obtain ⟨Θ, hΘ, h0Θ, hΘS, hΘsymm⟩ := TauCeti.ContDiffOn.exists_openPartialHomeomorph hΦs hSo h0S
    (by simp) (e := L.trans (e.trans L.symm)) (by rw [hΦD.fderiv]; ext; simp [he])
  have hΘs : ContDiffOn ℝ ∞ Θ Θ.source := hΘ ▸ hΦs.mono hΘS
  have hΘ0 : Θ 0 = 0 := by simp [hΘ, hΦ, hW, Pi.zero_def]
  have hcoord : ∀ y ∈ (ψ.trans Θ).source,
      φ.toMorseBottChart.coord ((ψ.trans Θ) y) = W (L (ψ y)) := fun y _ ↦ by
    simp [hΘ, hΦ, L]
  have hkey : ∀ y ∈ (ψ.trans Θ).source,
      h (f y) = h c + U (φ.toMorseBottChart.coord ((ψ.trans Θ) y)) := fun y hy ↦ by
    have hay : 0 < a (L (ψ y)) := by simpa using (hΘS hy.2).2
    rw [hcoord y hy, hWU _ hay, hhG (f y), hfU y hy.1]
    simp [ha]
  refine ⟨{
    quadraticPart := fun y ↦ h (f y) -
      birthDeathPotential 0 (φ.toMorseBottChart.coord ((ψ.trans Θ) y) i₀)
    toMorseBottChart := {
      toChart := ψ.trans Θ
      mem_maximalAtlas := ?_
      mem_source := ⟨φ.toMorseBottChart.mem_source, by simpa [hψx] using h0Θ⟩
      apply_self := by simp [hψx, hΘ0]
      coord := φ.toMorseBottChart.coord
      weight := w
      weight_eq_neg_one_or_eq_zero_or_eq_one :=
        φ.toMorseBottChart.weight_eq_neg_one_or_eq_zero_or_eq_one
      eq_quadratic := ?_ }
    cubicIndex := i₀
    weight_cubicIndex := φ.weight_cubicIndex
    weight_ne_zero := φ.weight_ne_zero
    eq_add := fun y _ ↦ by simp }⟩
  · rw [IsManifold.mem_maximalAtlas_iff_contMDiffOn]
    constructor
    · exact hΘs.contMDiffOn.comp ((contMDiffOn_of_mem_maximalAtlas
        φ.toMorseBottChart.mem_maximalAtlas).mono fun y hy ↦ hy.1) fun y hy ↦ hy.2
    · exact (contMDiffOn_symm_of_mem_maximalAtlas φ.toMorseBottChart.mem_maximalAtlas).comp
        (hΘsymm.contMDiffOn.mono fun y hy ↦ hy.1) fun y hy ↦ hy.2
  · intro y hy
    have hx' : x ∈ (ψ.trans Θ).source :=
      ⟨φ.toMorseBottChart.mem_source, by simpa [hψx] using h0Θ⟩
    rw [hkey y hy, hkey x hx']
    simp [hψx, hΘ0, hU, coordForm, birthDeathPotential_apply]
    ring

end Comp

end BirthDeathChart

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

/-- The critical set of a generalized Morse function is closed. -/
theorem isClosed_criticalPoints [IsManifold 𝓘(ℝ, E) 1 M] (hf : IsGeneralizedMorse E f) :
    IsClosed (criticalPoints 𝓘(ℝ, E) f) :=
  TauCeti.isClosed_criticalPoints (hf.contMDiff.of_le (by simp))

/-- The critical set of a generalized Morse function is discrete. -/
theorem isDiscrete_criticalPoints [IsManifold 𝓘(ℝ, E) 1 M] (hf : IsGeneralizedMorse E f) :
    IsDiscrete (criticalPoints 𝓘(ℝ, E) f) := by
  rw [isDiscrete_iff_nhdsNE]
  intro x _
  rw [inf_principal_eq_bot]
  filter_upwards [nhdsWithin_le_nhds (hf.eventually_eq_of_mem_criticalPoints x),
    self_mem_nhdsWithin] with y hy hyx using fun hyc ↦ hyx (hy hyc)

/-- A generalized Morse function has finitely many critical points in each compact set. -/
theorem finite_criticalPoints_inter [IsManifold 𝓘(ℝ, E) 1 M] (hf : IsGeneralizedMorse E f)
    {K : Set M} (hK : IsCompact K) : (criticalPoints 𝓘(ℝ, E) f ∩ K).Finite :=
  (hK.inter_left hf.isClosed_criticalPoints).finite
    (hf.isDiscrete_criticalPoints.mono inter_subset_left)

/-- A proper generalized Morse function bounded below has finitely many critical points in each
sublevel set. -/
theorem finite_criticalPoints_inter_preimage_Iic [IsManifold 𝓘(ℝ, E) 1 M]
    (hf : IsGeneralizedMorse E f) (hp : IsProperMap f) (hbdd : BddBelow (range f)) (b : ℝ) :
    (criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Iic b).Finite := by
  obtain ⟨a, ha⟩ := hbdd
  have hsub : f ⁻¹' Iic b = f ⁻¹' Icc a b := by
    ext y
    simp [ha (mem_range_self y)]
  rw [hsub]
  exact hf.finite_criticalPoints_inter (hp.isCompact_preimage isCompact_Icc)

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
  · exact .inr (hbd.some.nonempty_comp hh (hpos x))

end IsGeneralizedMorse

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
    eq_add := fun y _ ↦ by simp }

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
