/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.LieDeriv
public import TauCeti.Geometry.Symplectic.Hamiltonian.Manifold
import TauCeti.Geometry.Manifold.DifferentialForm.Squared
import TauCeti.Geometry.Manifold.MFDeriv.Constancy

/-!
# Regularity of Hamiltonian vector fields, and Hamiltonians with zero vector field

For a nondegenerate two-form `σ` on a manifold modelled on a finite-dimensional space, every
Hamiltonian vector field `X` of a `C^(n+1)` function `f`, that is every `X` with `ι_X σ = df`, is a
`C^n` vector field, for `n ≤ ∞`
(`TauCeti.SmoothTwoForm.IsNondegenerate.contMDiff_of_isHamiltonianVectorField`). Since `σ` is
nondegenerate, `X` is the Hamiltonian vector field `X_f`
(`TauCeti.SmoothTwoForm.IsNondegenerate.isHamiltonianVectorField_iff_eq`), whose regularity is
Tau Ceti's `TauCeti.SmoothTwoForm.IsNondegenerate.contMDiff_hamiltonianVectorField`.

For any two-form, the zero field is a Hamiltonian vector field of every locally constant function
(`TauCeti.SmoothTwoForm.isHamiltonianVectorField_zero_of_isLocallyConstant`). This follows from
Tau Ceti's `TauCeti.SmoothTwoForm.isHamiltonianVectorField_zero_iff`, by which the zero field is a
Hamiltonian vector field of `f` exactly when `df` vanishes everywhere, and from Tau Ceti's
`IsLocallyConstant.mvfderiv_eq_zero`, by which it does for a locally constant `f`; for constant
functions it is Tau Ceti's `TauCeti.SmoothTwoForm.isHamiltonianVectorField_const`.

Adding to `σ` a two-form that pairs a Hamiltonian vector field with every tangent vector to zero
keeps it a Hamiltonian vector field of the same function
(`TauCeti.SmoothTwoForm.IsHamiltonianVectorField.add_of_eval₂_eq_zero`).

Hamiltonian vector fields of differentiable functions sum over a finite set, with the Hamiltonians
summed (`TauCeti.SmoothTwoForm.IsHamiltonianVectorField.sum`), by induction from Tau Ceti's
`TauCeti.SmoothTwoForm.IsHamiltonianVectorField.add`.

For a closed `σ`, a differentiable Hamiltonian vector field `X` of a `C²` function `f` preserves
`σ`: `L_X σ = 0` (`TauCeti.SmoothTwoForm.IsHamiltonianVectorField.mlieDerivForm_eq_zero`). By
Cartan's formula for closed forms, Tau Ceti's
`TauCeti.SmoothForm.mlieDerivForm_eq_mextDeriv_interior`, `L_X σ = d(ι_X σ) = d(df) = 0`. For a
smooth field and a smooth function this also follows from Tau Ceti's
`TauCeti.SmoothTwoForm.mem_symplecticVectorFields_of_isHamiltonianVectorField` and
`TauCeti.SmoothTwoForm.mem_symplecticVectorFields_iff_mlieDerivForm_eq_zero`.

The results extend Tau Ceti's file of the same path, in its namespace.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §3.1
  (a Hamiltonian vector field preserves the symplectic form)
-/

public section

open scoped ContDiff Manifold

namespace TauCeti.SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {σ : SmoothTwoForm I M} {f : M → ℝ}

/-- The zero vector field is a Hamiltonian vector field of every locally constant function. -/
theorem isHamiltonianVectorField_zero_of_isLocallyConstant (hf : IsLocallyConstant f) :
    σ.IsHamiltonianVectorField f 0 :=
  isHamiltonianVectorField_zero_iff.2 hf.mvfderiv_eq_zero

/-- If `X` is a Hamiltonian vector field of `f` for `σ` and the two-form `τ` pairs `X` with every
tangent vector to zero, then `X` is a Hamiltonian vector field of `f` for `σ + τ`. -/
theorem IsHamiltonianVectorField.add_of_eval₂_eq_zero {τ : SmoothTwoForm I M}
    {X : (x : M) → TangentSpace I x} (hX : σ.IsHamiltonianVectorField f X)
    (hτ : ∀ x v, SmoothBundleForm.eval₂ τ x (X x) v = 0) :
    (σ + τ).IsHamiltonianVectorField f X :=
  isHamiltonianVectorField_iff.2 fun x v ↦ by
    rw [SmoothBundleForm.eval₂_add, hτ, add_zero, isHamiltonianVectorField_iff.1 hX]

/-- **Hamiltonian vector fields sum.** If, for each `i ∈ s`, `X i` is a Hamiltonian vector field
of the differentiable function `f i`, then `∑ i ∈ s, X i` is a Hamiltonian vector field of
`∑ i ∈ s, f i`. -/
theorem IsHamiltonianVectorField.sum {ι : Type*} {s : Finset ι} {f : ι → M → ℝ}
    {X : ι → (x : M) → TangentSpace I x} (hX : ∀ i ∈ s, σ.IsHamiltonianVectorField (f i) (X i))
    (hf : ∀ i ∈ s, MDifferentiable I 𝓘(ℝ) (f i)) :
    σ.IsHamiltonianVectorField (∑ i ∈ s, f i) (∑ i ∈ s, X i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact isHamiltonianVectorField_zero_iff.2 fun x ↦ by simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    refine (hX a (s.mem_insert_self a)).add (ih (fun i hi ↦ hX i (s.mem_insert_of_mem hi))
      fun i hi ↦ hf i (s.mem_insert_of_mem hi)) (hf a (s.mem_insert_self a))
      (MDifferentiable.sum fun i hi ↦ hf i (s.mem_insert_of_mem hi))

/-- **A Hamiltonian vector field preserves a closed form.** If `σ` is closed and `X` is a
differentiable Hamiltonian vector field of a `C²` function `f`, then `L_X σ = 0`. -/
theorem IsHamiltonianVectorField.mlieDerivForm_eq_zero {X : (x : M) → TangentSpace I x}
    (hX : σ.IsHamiltonianVectorField f X) (hσ : σ.IsClosed) (hf : ContMDiff I 𝓘(ℝ) 2 f)
    (hXd : MDifferentiable I I.tangent (fun y ↦ (X y : TangentBundle I M))) :
    mlieDerivForm X σ.val = 0 := by
  rw [SmoothForm.mlieDerivForm_eq_mextDeriv_interior hXd hσ,
    isHamiltonianVectorField_iff_interior_eq.1 hX, mextDeriv_mextDeriv_ofFunction hf]

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
