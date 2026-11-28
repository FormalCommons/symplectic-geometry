/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.Chart.Basic

/-!
# The second derivative of the quadratic normal form of a Morse–Bott chart

For a Morse–Bott chart `φ` with coordinates `L = φ.coord` and weights `aᵢ = φ.weight i`, the
quadratic normal form is `q z = f x + (1/2) Σᵢ aᵢ (L z)ᵢ²`. Tau Ceti computes its first
derivative (`TauCeti.MorseBottChart.fderiv_quadratic_apply`). This file computes its second
derivative, which is the same at every point: `(v, w) ↦ Σᵢ aᵢ (L v)ᵢ (L w)ᵢ`.

## Main declarations

* `TauCeti.MorseBottChart.coordFun`: the `i`-th coordinate of a Morse–Bott chart, as a continuous
  linear functional on the model space, with `TauCeti.MorseBottChart.coordFun_apply`.
* `TauCeti.MorseBottChart.fderiv_quadratic`: the derivative of the quadratic normal form, as a
  sum of these functionals.
* `TauCeti.MorseBottChart.hasFDerivAt_fderiv_quadratic` and
  `TauCeti.MorseBottChart.fderiv_fderiv_quadratic_apply`: its second derivative.

## Implementation notes

The declarations are in the namespace `TauCeti`, since they concern Tau Ceti's notions.
-/

public section

namespace TauCeti

namespace MorseBottChart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {x : M}
  (φ : MorseBottChart E f x)

/-- The `i`-th coordinate `v ↦ (L v)ᵢ` of a Morse–Bott chart, as a continuous linear functional on
the model space. -/
noncomputable def coordFun (i : Fin (Module.finrank ℝ E)) : E →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (Module.finrank ℝ E) ↦ ℝ) i).comp
    (φ.coordL : E →L[ℝ] (Fin (Module.finrank ℝ E) → ℝ))

@[simp]
theorem coordFun_apply (i : Fin (Module.finrank ℝ E)) (v : E) :
    φ.coordFun i v = φ.coord v i := by
  simp [coordFun]

/-- The derivative of the quadratic normal form of a Morse–Bott chart at `z` is
`Σᵢ aᵢ (L z)ᵢ (L ·)ᵢ`. -/
theorem fderiv_quadratic :
    fderiv ℝ φ.quadratic = fun z ↦ ∑ i, (φ.weight i * φ.coordFun i z) • φ.coordFun i := by
  ext z v
  simp [fderiv_quadratic_apply]

/-- The derivative of the quadratic normal form of a Morse–Bott chart has, at every point, the
derivative `Σᵢ aᵢ (L ·)ᵢ (L ·)ᵢ`. -/
theorem hasFDerivAt_fderiv_quadratic (z : E) :
    HasFDerivAt (fderiv ℝ φ.quadratic)
      (∑ i, φ.weight i • (φ.coordFun i).smulRight (φ.coordFun i)) z := by
  rw [fderiv_quadratic]
  convert HasFDerivAt.fun_sum (u := Finset.univ) fun i _ ↦
    (((φ.coordFun i).hasFDerivAt (x := z)).const_mul (φ.weight i)).smul_const (φ.coordFun i)
    using 1
  ext v w
  simp [mul_assoc]

/-- The second derivative of the quadratic normal form of a Morse–Bott chart is, at every point,
`(v, w) ↦ Σᵢ aᵢ (L v)ᵢ (L w)ᵢ`. -/
theorem fderiv_fderiv_quadratic_apply (z v w : E) :
    fderiv ℝ (fderiv ℝ φ.quadratic) z v w = ∑ i, φ.weight i * φ.coord v i * φ.coord w i := by
  rw [(φ.hasFDerivAt_fderiv_quadratic z).fderiv]
  simp [mul_assoc]

end MorseBottChart

end TauCeti

end
