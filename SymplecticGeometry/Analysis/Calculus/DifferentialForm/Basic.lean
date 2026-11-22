/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import SymplecticGeometry.Analysis.Normed.Module.Alternating.Uncurry.Fin

/-!
# The exterior derivative in a basis

For a basis `b` of a finite-dimensional normed space `E`, with dual basis `b^*_i = b.coord i`,
the exterior derivative of a form `ω` on `E` (Mathlib's `extDeriv` and `extDerivWithin`) is
`dω = ∑ᵢ ε_{b^*_i} (∂_{b_i} ω)`, where `ε_ξ` is the exterior product with a covector
(`ContinuousAlternatingMap.extProdCLM`). This follows from
`ContinuousAlternatingMap.alternatizeUncurryFin_eq_sum_coord_smulRight`.

## Main results

* `extDerivWithin_eq_sum_extProdCLM_coord`: the expansion of `extDerivWithin ω s x`.
* `extDeriv_eq_sum_extProdCLM_coord`: the expansion of `extDeriv ω x`.
-/

public section

open ContinuousAlternatingMap

variable {𝕜 E F ι : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [Fintype ι] {n : ℕ}

/-- In a basis `b`, the exterior derivative within `s` of a form `ω` is
`∑ᵢ ε_{b^*_i} (∂_{b_i} ω)`, with the derivatives taken within `s`. -/
theorem extDerivWithin_eq_sum_extProdCLM_coord (b : Module.Basis ι 𝕜 E)
    (ω : E → E [⋀^Fin n]→L[𝕜] F) (s : Set E) (x : E) :
    extDerivWithin ω s x =
      ∑ i, extProdCLM n (LinearMap.toContinuousLinearMap (b.coord i))
        (fderivWithin 𝕜 ω s x (b i)) := by
  rw [extDerivWithin, alternatizeUncurryFin_eq_sum_coord_smulRight b]
  simp only [extProdCLM_apply]

/-- In a basis `b`, the exterior derivative of a form `ω` is `∑ᵢ ε_{b^*_i} (∂_{b_i} ω)`. -/
theorem extDeriv_eq_sum_extProdCLM_coord (b : Module.Basis ι 𝕜 E)
    (ω : E → E [⋀^Fin n]→L[𝕜] F) (x : E) :
    extDeriv ω x =
      ∑ i, extProdCLM n (LinearMap.toContinuousLinearMap (b.coord i))
        (fderiv 𝕜 ω x (b i)) := by
  rw [extDeriv, alternatizeUncurryFin_eq_sum_coord_smulRight b]
  simp only [extProdCLM_apply]

end
