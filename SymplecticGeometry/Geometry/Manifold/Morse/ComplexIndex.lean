/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Hessian
public import TauCeti.Geometry.Symplectic.Finrank
import SymplecticGeometry.Analysis.Calculus.Morse.ComplexIndex

/-!
# Lower bounds for the manifold Morse index from complex negativity

Fix an almost complex structure `J` on the model space `E` of a manifold, read on the tangent
space at `x`. If the critical Hessian of `f` at `x` satisfies

`Hess f(v, v) + Hess f(Jv, Jv) < 0`

for every nonzero tangent vector `v`, then the manifold Morse index of `f` at `x` is at least the
complex dimension defined by `J`. The manifold Morse index is the Morse index of the coordinate
expression in the preferred chart, whose Hessian quadratic form is the diagonal of the critical
Hessian (`TauCeti.criticalHessian_apply_self`), so this follows from
`TauCeti.AlmostComplexStructure.complexFinrank_le_morseIndex_of_add_comp_neg`. It is the
lower-bound counterpart of Tau Ceti's
`TauCeti.AlmostComplexStructure.manifoldMorseIndex_le_complexFinrank_of_add_comp_posDef`.

## Main declarations

* `TauCeti.AlmostComplexStructure.complexFinrank_le_manifoldMorseIndex_of_criticalHessian_add_neg`:
  the manifold Morse index is at least the complex dimension.

## References

* [D. Auroux, *Asymptotically holomorphic families of symplectic submanifolds*][Auroux1997]
* J. Milnor, *Morse Theory*, Princeton University Press, 1963, Section 7.
-/

public section

namespace TauCeti.AlmostComplexStructure

variable {E H M : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable [TopologicalSpace M] [ChartedSpace H M]
variable (J : TauCeti.AlmostComplexStructure E) (f : M → ℝ) (x : M)

/-- If the critical Hessian of `f` at `x` satisfies `Hess f(v, v) + Hess f(Jv, Jv) < 0` for every
nonzero tangent vector `v`, then the manifold Morse index of `f` at `x` is at least the complex
dimension defined by `J`. -/
theorem complexFinrank_le_manifoldMorseIndex_of_criticalHessian_add_neg
    (h : ∀ v : TangentSpace I x, v ≠ 0 →
      TauCeti.criticalHessian I f x v v + TauCeti.criticalHessian I f x (J v) (J v) < 0) :
    J.complexFinrank ≤ TauCeti.manifoldMorseIndex I f x := by
  rw [TauCeti.manifoldMorseIndex_def]
  refine J.complexFinrank_le_morseIndex_of_add_comp_neg _ _ fun v hv ↦ ?_
  -- `v` is a tangent vector, so `criticalHessian_apply_self` matches the goal only up to
  -- `TangentSpace I x = E`, which `rw` and `simp` do not see through.
  convert h v hv using 2 <;> exact (TauCeti.criticalHessian_apply_self _).symm

end TauCeti.AlmostComplexStructure
