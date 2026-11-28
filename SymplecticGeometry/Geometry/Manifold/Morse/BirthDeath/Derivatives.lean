/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Morse.BirthDeath.Basic
import Mathlib.Analysis.Calculus.FDeriv.Pow

/-!
# The first three derivatives of a birth–death normal form

For a birth–death chart `φ` of `f` at `x`, with coordinates `L = φ.toMorseBottChart.coord`,
weights `wᵢ` and cubic coordinate `i₀`, the normal form is
`z ↦ f x + (1/2) Σᵢ wᵢ (L z)ᵢ² + (L z)_{i₀}³ / 3`, where `w_{i₀} = 0`. This file computes its second
and third derivatives at every point and reads off the data at the origin that characterize a
birth–death critical point: the differential vanishes, the Hessian is the diagonal form
`Σᵢ wᵢ (L v)ᵢ (L w)ᵢ`, whose kernel is the line spanned by `e = L⁻¹ (Pi.single i₀ 1)`, and the third
derivative takes the value `2` on `(e, e, e)`.

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

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012]
* J. Cerf, *La stratification naturelle des espaces de fonctions différentiables réelles et le
  théorème de la pseudo-isotopie*, Publ. Math. IHÉS 39 (1970), 5–173.
-/

public section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {f : M → ℝ} {x : M}

namespace BirthDeathChart

variable (φ : BirthDeathChart E f x)

variable (φ : BirthDeathChart E f x)

/-- The `i`-th coordinate of a birth–death chart, as a continuous linear functional. -/
private noncomputable def coordFun (i : Fin (Module.finrank ℝ E)) : E →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (Module.finrank ℝ E) ↦ ℝ) i).comp
    (φ.toMorseBottChart.coordL : E →L[ℝ] (Fin (Module.finrank ℝ E) → ℝ))

private theorem coordFun_apply (i : Fin (Module.finrank ℝ E)) (v : E) :
    φ.coordFun i v = φ.toMorseBottChart.coord v i := by
  simp [coordFun]

/-- The constant part of the second derivative of the normal form. -/
private noncomputable def hessConst : E →L[ℝ] E →L[ℝ] ℝ :=
  ∑ i, φ.toMorseBottChart.weight i • (φ.coordFun i).smulRight (φ.coordFun i)

/-- The third derivative of the normal form. -/
private noncomputable def cubicForm : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
  ((2 : ℝ) • φ.coordFun φ.cubicIndex).smulRight
    ((φ.coordFun φ.cubicIndex).smulRight (φ.coordFun φ.cubicIndex))

private theorem fderiv_normalForm_eq :
    fderiv ℝ φ.normalForm = fun z ↦ ∑ i, (φ.toMorseBottChart.weight i * φ.coordFun i z) •
      φ.coordFun i + (φ.coordFun φ.cubicIndex z ^ 2) • φ.coordFun φ.cubicIndex := by
  ext z v
  simp [fderiv_normalForm_apply, coordFun_apply, mul_assoc]

private theorem hasFDerivAt_fderiv_normalForm (z : E) :
    HasFDerivAt (fderiv ℝ φ.normalForm) (φ.hessConst + φ.cubicForm z) z := by
  rw [fderiv_normalForm_eq]
  have h₁ := HasFDerivAt.fun_sum (u := Finset.univ) fun i _ ↦
    (((φ.coordFun i).hasFDerivAt (x := z)).const_mul (φ.toMorseBottChart.weight i)).smul_const
      (φ.coordFun i)
  have hc : HasFDerivAt (φ.coordFun φ.cubicIndex) (φ.coordFun φ.cubicIndex) z :=
    (φ.coordFun φ.cubicIndex).hasFDerivAt
  have h₂ := (hc.pow 2).smul_const (φ.coordFun φ.cubicIndex)
  convert h₁.add h₂ using 1
  ext v w
  simp [hessConst, cubicForm, mul_assoc]

private theorem fderiv_fderiv_normalForm_eq :
    fderiv ℝ (fderiv ℝ φ.normalForm) = fun z ↦ φ.hessConst + φ.cubicForm z :=
  funext fun z ↦ (φ.hasFDerivAt_fderiv_normalForm z).fderiv

/-- The second derivative of the normal form of a birth–death chart:
`(v, w) ↦ Σᵢ wᵢ (L v)ᵢ (L w)ᵢ + 2 (L z)_{i₀} (L v)_{i₀} (L w)_{i₀}`. -/
theorem fderiv_fderiv_normalForm_apply (z v w : E) :
    fderiv ℝ (fderiv ℝ φ.normalForm) z v w = ∑ i, φ.toMorseBottChart.weight i *
      φ.toMorseBottChart.coord v i * φ.toMorseBottChart.coord w i +
        2 * φ.toMorseBottChart.coord z φ.cubicIndex * φ.toMorseBottChart.coord v φ.cubicIndex *
          φ.toMorseBottChart.coord w φ.cubicIndex := by
  rw [fderiv_fderiv_normalForm_eq]
  simp [hessConst, cubicForm, coordFun_apply, mul_assoc]

/-- The third derivative of the normal form of a birth–death chart is the same at every point:
`(u, v, w) ↦ 2 (L u)_{i₀} (L v)_{i₀} (L w)_{i₀}`. -/
theorem fderiv_fderiv_fderiv_normalForm_apply (z u v w : E) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ φ.normalForm)) z u v w =
      2 * φ.toMorseBottChart.coord u φ.cubicIndex * φ.toMorseBottChart.coord v φ.cubicIndex *
        φ.toMorseBottChart.coord w φ.cubicIndex := by
  -- The implicit arguments are given: elaborating with them left to unification fails on the
  -- instances of the space of bilinear maps.
  have h : fderiv ℝ (fun z ↦ φ.hessConst + φ.cubicForm z) z = φ.cubicForm :=
    (fderiv_const_add (𝕜 := ℝ) (F := E →L[ℝ] E →L[ℝ] ℝ) (f := ⇑φ.cubicForm) (x := z)
      φ.hessConst).trans (ContinuousLinearMap.fderiv (F := E →L[ℝ] E →L[ℝ] ℝ) φ.cubicForm)
  rw [fderiv_fderiv_normalForm_eq, h]
  simp [cubicForm, coordFun_apply, mul_assoc]

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

end BirthDeathChart

end TauCeti

end
