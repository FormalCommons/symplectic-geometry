/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Quadratic
public import TauCeti.Geometry.Symplectic.SymplecticTransport

/-!
# Hamiltonian endomorphisms under linear symplectomorphisms

For a linear symplectomorphism `e : (V, ω₁) → (W, ω₂)` and a quadratic form `Q` on `W`, the
Hamiltonian endomorphism of the pulled back form `Q ∘ e` is the conjugate
`e⁻¹ ∘ A_Q ∘ e` of the Hamiltonian endomorphism `A_Q` of `Q`
(`TauCeti.SymplecticForm.IsSymplectomorphism.hamiltonianEnd_comp`). This is the linear,
quadratic case of the naturality of Hamiltonian vector fields
(`TauCeti.SymplecticForm.IsSymplectomorphism.hamiltonianVectorField_comp`), proved directly
from the characterizing identity `ω (A_Q v) w = polar Q v w`.

The result extends Tau Ceti's file of the same path, in its namespace.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.4
  (the uniqueness of the radii in Lemma 2.4.6)
-/

public section

namespace TauCeti.SymplecticForm

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
  {ω₁ : SymplecticForm V} {ω₂ : SymplecticForm W} {e : V ≃ₗ[ℝ] W}

/-- **Hamiltonian endomorphisms are natural under symplectomorphisms.** For a linear
symplectomorphism `e : (V, ω₁) → (W, ω₂)` and a quadratic form `Q` on `W`, the Hamiltonian
endomorphism of `Q ∘ e` is `e⁻¹ ∘ A_Q ∘ e`. -/
theorem IsSymplectomorphism.hamiltonianEnd_comp (he : IsSymplectomorphism ω₁ ω₂ e)
    (Q : QuadraticForm ℝ W) :
    ω₁.hamiltonianEnd (Q.comp (e : V →ₗ[ℝ] W)) =
      (e.symm : W →ₗ[ℝ] V) ∘ₗ ω₂.hamiltonianEnd Q ∘ₗ (e : V →ₗ[ℝ] W) := by
  refine ((ω₁.eq_hamiltonianEnd_iff).2 fun v w ↦ ?_).symm
  rw [← he.apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, apply_hamiltonianEnd]
  simp [QuadraticMap.polar]

end TauCeti.SymplecticForm

end
