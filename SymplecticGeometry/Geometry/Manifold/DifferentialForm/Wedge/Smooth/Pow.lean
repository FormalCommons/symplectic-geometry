/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import TauCeti.Geometry.Manifold.DifferentialForm.Interior
public import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Smooth.Pow
import SymplecticGeometry.Topology.Algebra.Module.Alternating.Wedge.TwoForm
import SymplecticGeometry.Topology.Algebra.Module.Alternating.Wedge.Pow

/-!
# Wedge powers of smooth forms

The zeroth wedge power of a smooth real form is the `0`-form of the constant function `1`
(`TauCeti.SmoothForm.wedgePow_zero_eq_ofFunction_one`; Tau Ceti's `TauCeti.SmoothForm.wedgePow_zero`
states it for the underlying rough form, and the statement here follows from it), and the first
wedge power of a smooth real two-form `σ` is `σ` itself (`TauCeti.SmoothForm.wedgePow_one`), which
holds pointwise by `ContinuousAlternatingMap.wedgePow_one` and Tau Ceti's
`TauCeti.SmoothForm.wedgePow_apply`.

On a manifold of dimension `2 n + 2`, the top-degree form `γ ∧ ι_X σ ∧ σ ^ n` vanishes at every
point where the one-form `γ` vanishes on `X`
(`TauCeti.SmoothForm.wedge_interior_wedge_wedgePow_apply_eq_zero`). This is the pointwise statement
of `ContinuousAlternatingMap.pairedWedge_curryLeftTopological_wedgePow_eq_zero`.

## Main results

* `TauCeti.SmoothForm.wedgePow_zero_eq_ofFunction_one`: `wedgePow φ 0 = ofFunction 1`.
* `TauCeti.SmoothForm.wedgePow_one`: `wedgePow σ 1 = σ` for a smooth two-form `σ`.
* `TauCeti.SmoothForm.wedge_interior_wedge_wedgePow_apply_eq_zero`: `γ ∧ ι_X σ ∧ σ ^ n` vanishes
  at `x` in dimension `2 n + 2` when `γ_x(X x) = 0`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 14.
* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  proof of Theorem 5.1.6.
-/

public section

open scoped ContDiff Manifold

namespace TauCeti

namespace SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H} [IsManifold I 1 M]

/-- The zeroth wedge power of a smooth form is the `0`-form of the constant function `1`. -/
@[simp]
theorem wedgePow_zero_eq_ofFunction_one {k : ℕ} (φ : SmoothForm I M ℝ k) :
    φ.wedgePow 0 = ofFunction (1 : C^∞⟮I, M; ℝ⟯) :=
  Subtype.ext <| by rw [wedgePow_zero, coe_ofFunction, ContMDiffMap.coe_one, Pi.one_def]

/-- The first wedge power of a smooth two-form is the form itself. -/
@[simp]
theorem wedgePow_one (σ : SmoothForm I M ℝ 2) : σ.wedgePow 1 = σ :=
  Subtype.ext (funext fun x ↦ by rw [wedgePow_apply, ContinuousAlternatingMap.wedgePow_one])

variable [FiniteDimensional ℝ E] in
/-- **Contracting a wedge power in top degree, pointwise.** On a manifold of dimension `2 n + 2`,
if a one-form `γ` vanishes on the vector `X x`, then the top-degree form `γ ∧ ι_X σ ∧ σ ^ n` built
from a smooth two-form `σ` vanishes at `x`. -/
theorem wedge_interior_wedge_wedgePow_apply_eq_zero {n : ℕ}
    (hE : Module.finrank ℝ E = 2 * n + 2) (γ : RoughForm I M ℝ 1) (σ : SmoothForm I M ℝ 2)
    (X : (x : M) → TangentSpace I x) {x : M} (hγ : γ x ![X x] = 0) :
    RoughForm.wedge γ (RoughForm.wedge (RoughForm.interior (k := 1) X (σ : RoughForm I M ℝ 2))
      (σ.wedgePow n : RoughForm I M ℝ (2 * n))) x = 0 := by
  have hX : RoughForm.interior (k := 1) X (σ : RoughForm I M ℝ 2) x =
      ContinuousAlternatingMap.curryLeftTopological (σ.val x) (X x) := by
    rw [RoughForm.interior_def]
    exact bundleInterior_apply_eq_curryLeftTopological X _ x
  rw [RoughForm.wedge_def, RoughForm.wedgeWith_apply', RoughForm.wedge_def,
    RoughForm.wedgeWith_apply', hX, wedgePow_apply]
  exact ContinuousAlternatingMap.pairedWedge_curryLeftTopological_wedgePow_eq_zero hE _ _ _ hγ

end SmoothForm

end TauCeti

end
