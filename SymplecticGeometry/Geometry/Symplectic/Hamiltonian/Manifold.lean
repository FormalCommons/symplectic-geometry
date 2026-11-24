/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Manifold
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import SymplecticGeometry.Geometry.Manifold.MFDeriv.Constancy

/-!
# Regularity and linearity of Hamiltonian vector fields

For a nondegenerate two-form `σ` on a manifold modelled on a finite-dimensional space, every
Hamiltonian vector field `X` of a `C^(n+1)` function `f`, that is every `X` with `ι_X σ = df`, is a
`C^n` vector field, for `n ≤ ∞`
(`TauCeti.SmoothTwoForm.IsNondegenerate.contMDiff_of_isHamiltonianVectorField`). Since `σ` is
nondegenerate, `X` is the Hamiltonian vector field `X_f`
(`TauCeti.SmoothTwoForm.IsNondegenerate.isHamiltonianVectorField_iff_eq`), whose regularity is
Tau Ceti's `TauCeti.SmoothTwoForm.IsNondegenerate.contMDiff_hamiltonianVectorField`.

For any two-form, the relation `ι_X σ = df` is linear in the pair `(f, X)`: the zero field is a
Hamiltonian vector field of the zero function
(`TauCeti.SmoothTwoForm.IsHamiltonianVectorField.zero`), and sums of differentiable functions and
real multiples of functions have the sums and multiples of their Hamiltonian vector fields (Tau
Ceti's `TauCeti.SmoothTwoForm.IsHamiltonianVectorField.add` and
`TauCeti.SmoothTwoForm.IsHamiltonianVectorField.const_smul`). More generally than the first, the
zero field is a Hamiltonian vector field of every locally constant function
(`TauCeti.SmoothTwoForm.isHamiltonianVectorField_zero_of_isLocallyConstant`).

The results extend Tau Ceti's file of the same path, in its namespace.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §3.1
-/

public section

open scoped ContDiff Manifold

namespace TauCeti.SmoothTwoForm.IsHamiltonianVectorField

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {σ : SmoothTwoForm I M}

/-- The zero vector field is a Hamiltonian vector field of the zero function. -/
theorem zero : σ.IsHamiltonianVectorField 0 0 :=
  isHamiltonianVectorField_iff_flat.2 fun x ↦ by
    rw [Pi.zero_apply, map_zero, mvfderiv_zero]

end TauCeti.SmoothTwoForm.IsHamiltonianVectorField

namespace TauCeti.SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {σ : SmoothTwoForm I M} {f : M → ℝ}

/-- The zero vector field is a Hamiltonian vector field of every locally constant function. -/
theorem isHamiltonianVectorField_zero_of_isLocallyConstant (hf : IsLocallyConstant f) :
    σ.IsHamiltonianVectorField f 0 :=
  isHamiltonianVectorField_iff_flat.2 fun x ↦ by
    rw [Pi.zero_apply, map_zero, eq_comm, mvfderiv_eq_zero_iff, hf.mfderiv_eq_zero]

end TauCeti.SmoothTwoForm

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
