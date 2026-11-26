/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Basic
public import TauCeti.Topology.Algebra.Module.Alternating.Wedge.Pow.Basic
import SymplecticGeometry.Topology.Algebra.Module.Alternating.Wedge.Pow
import TauCeti.Analysis.Matrix.EuclideanLin
import TauCeti.Data.Fin.VecNotation
import SymplecticGeometry.Topology.Algebra.Module.Alternating.Basic

/-!
# Top wedge powers of weighted standard two-forms

For weights `c : ι → ℝ`, the constant two-form `ω_c = ∑ⱼ cⱼ dxⱼ ∧ dyⱼ` on `StdSpace ι` is the
pullback of the standard form `ω₀ = stdForm ι` under the diagonal map that multiplies the
coordinate `xⱼ` by `cⱼ` and fixes the coordinates `yⱼ`. That map has determinant `∏ⱼ cⱼ`, and
`2 n = 2 * Fintype.card ι` is the dimension of `StdSpace ι`, so

* `SymplecticGeometry.wedgePow_card_eq_prod_smul`: `ω_cⁿ = (∏ⱼ cⱼ) • ω₀ⁿ`, where `n` is the
  number of coordinate pairs; dividing both sides by `n!` gives the same identity for the
  symplectic volume forms `ωⁿ / n!`.

The statement covers dimension zero: for empty `ι` both top powers are the constant `1` and the
product is empty.

The proof applies `ContinuousAlternatingMap.wedgePow_compContinuousLinearMap_eq_det_smul` (on a
space of dimension `2 n`, pulling a two-form back along an endomorphism multiplies its `n`-th
wedge power by the determinant) to that diagonal map.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Section 2.1 and Chapter 3 (the volume form `ωⁿ / n!`)
-/

public section

namespace SymplecticGeometry

open Matrix StdSpace

variable {ι : Type*} [Fintype ι]

/-- **The top wedge power of a weighted standard two-form.** Let `c : ι → ℝ` be weights and
`n = Fintype.card ι`. If `ω₀` is the standard form `ω₀ = ∑ⱼ dxⱼ ∧ dyⱼ` on `StdSpace ι` and `ω` is
the weighted form `∑ⱼ cⱼ dxⱼ ∧ dyⱼ`, both as continuous alternating maps, then
`ωⁿ = (∏ⱼ cⱼ) • ω₀ⁿ`. -/
theorem wedgePow_card_eq_prod_smul {c : ι → ℝ} {ω ω₀ : StdSpace ι [⋀^Fin 2]→L[ℝ] ℝ}
    (hω₀ : ∀ v w, ω₀ ![v, w] = stdForm ι v w)
    (hω : ∀ v w, ω ![v, w] = ∑ j, c j * (v.x j * w.y j - v.y j * w.x j)) :
    ω.wedgePow (Fintype.card ι) = (∏ j, c j) • ω₀.wedgePow (Fintype.card ι) := by
  classical
  -- The diagonal map `D` scaling each `xⱼ` by `cⱼ`; `ω` is the pullback of `ω₀` under it.
  set D : StdSpace ι →L[ℝ] StdSpace ι := toEuclideanCLM (𝕜 := ℝ) (diagonal (Sum.elim c 1))
  have hDx (v : StdSpace ι) (j : ι) : (D v).x j = c j * v.x j := by
    simp [D, x_apply, mulVec_diagonal]
  have hDy (v : StdSpace ι) (j : ι) : (D v).y j = v.y j := by
    simp [D, y_apply, mulVec_diagonal]
  have hωD : ω = ω₀.compContinuousLinearMap D := by
    ext v w
    rw [ContinuousAlternatingMap.compContinuousLinearMap_apply, Matrix.comp_vec2, hω, hω₀]
    simp only [stdForm_apply, hDx, hDy]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  -- `D` scales top-degree forms on `StdSpace ι`, of dimension `2 * card ι`, by `det D = ∏ cⱼ`.
  have hdet : LinearMap.det (D : StdSpace ι →ₗ[ℝ] StdSpace ι) = ∏ j, c j := by
    rw [← ContinuousLinearMap.det, det_toEuclideanCLM_diagonal, Fintype.prod_sum_type]
    simp
  rw [hωD, ← hdet]
  exact ContinuousAlternatingMap.wedgePow_compContinuousLinearMap_eq_det_smul finrank_stdSpace
    ω₀ D

end SymplecticGeometry

end
