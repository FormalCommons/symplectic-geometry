/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Smooth.Basic

/-!
# The wedge of smooth forms is linear over smooth functions

The wedge of real smooth forms is bilinear over the smooth functions: a smooth function `g` comes
out of either factor, `(g φ) ∧ ψ = g (φ ∧ ψ)` (`TauCeti.SmoothForm.wedge_funSMulₗ_left`) and
`φ ∧ (g ψ) = g (φ ∧ ψ)` (`TauCeti.SmoothForm.wedge_funSMulₗ_right`), where `g φ` is Tau Ceti's
`TauCeti.SmoothForm.funSMulₗ g φ`.

The proofs are those of Tau Ceti's `TauCeti.SmoothForm.extDerivWedgeₗ_funSMulₗ`, the case of the
right factor when the left one is `df`: pointwise, they are Tau Ceti's
`ContinuousAlternatingMap.pairedWedge_smul_left` and
`ContinuousAlternatingMap.pairedWedge_smul_right`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 14.
-/

public section

open scoped ContDiff Manifold

namespace TauCeti.SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H} [IsManifold I 1 M]
  {k l : ℕ}

/-- A smooth function comes out of the left factor of a wedge: `(g φ) ∧ ψ = g (φ ∧ ψ)`. -/
@[simp]
theorem wedge_funSMulₗ_left (g : C^∞⟮I, M; ℝ⟯) (φ : SmoothForm I M ℝ k)
    (ψ : SmoothForm I M ℝ l) : wedge (funSMulₗ g φ) ψ = funSMulₗ g (wedge φ ψ) := by
  ext x v
  simp [coe_wedge, coe_funSMulₗ, RoughForm.wedge_def, RoughForm.wedgeWith_apply',
    ContinuousAlternatingMap.pairedWedge_smul_left]

/-- A smooth function comes out of the right factor of a wedge: `φ ∧ (g ψ) = g (φ ∧ ψ)`. -/
@[simp]
theorem wedge_funSMulₗ_right (g : C^∞⟮I, M; ℝ⟯) (φ : SmoothForm I M ℝ k)
    (ψ : SmoothForm I M ℝ l) : wedge φ (funSMulₗ g ψ) = funSMulₗ g (wedge φ ψ) := by
  ext x v
  simp [coe_wedge, coe_funSMulₗ, RoughForm.wedge_def, RoughForm.wedgeWith_apply',
    ContinuousAlternatingMap.pairedWedge_smul_right]

end TauCeti.SmoothForm

end
