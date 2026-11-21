/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Manifold

/-!
# Regularity of Hamiltonian vector fields

For a nondegenerate two-form `σ` on a manifold modelled on a finite-dimensional space, every
Hamiltonian vector field `X` of a `C^(n+1)` function `f`, that is every `X` with `ι_X σ = df`, is a
`C^n` vector field, for `n ≤ ∞`
(`TauCeti.SmoothTwoForm.IsNondegenerate.contMDiff_of_isHamiltonianVectorField`). Since `σ` is
nondegenerate, `X` is the Hamiltonian vector field `X_f`
(`TauCeti.SmoothTwoForm.IsNondegenerate.isHamiltonianVectorField_iff_eq`), whose regularity is
Tau Ceti's `TauCeti.SmoothTwoForm.IsNondegenerate.contMDiff_hamiltonianVectorField`.

The result extends Tau Ceti's file of the same path, in its namespace.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §3.1
-/

public section

open scoped ContDiff Manifold

namespace TauCeti.SmoothTwoForm.IsNondegenerate

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {σ : SmoothTwoForm I M} {f : M → ℝ} {X : (x : M) → TangentSpace I x}

/-- **Regularity of Hamiltonian vector fields.** For a nondegenerate two-form `σ` on a manifold
modelled on a finite-dimensional space, a Hamiltonian vector field of a `C^(n+1)` function is a
`C^n` vector field, for `n ≤ ∞`. -/
theorem contMDiff_of_isHamiltonianVectorField (h : σ.IsNondegenerate) {n : WithTop ℕ∞}
    (hn : n ≤ ∞) (hf : ContMDiff I 𝓘(ℝ) (n + 1) f) (hX : σ.IsHamiltonianVectorField f X) :
    ContMDiff I I.tangent n (fun x ↦ (⟨x, X x⟩ : TangentBundle I M)) := by
  obtain rfl := h.isHamiltonianVectorField_iff_eq.1 hX
  exact h.contMDiff_hamiltonianVectorField hn hf

end TauCeti.SmoothTwoForm.IsNondegenerate

end
