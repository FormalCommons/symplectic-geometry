/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.Projectivization.Action
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import TauCeti.Topology.ComplexProjectiveSpace.Charts
public import TauCeti.Topology.ComplexProjectiveSpace.Homogeneous
public import TauCeti.Topology.ComplexProjectiveSpace.Projectivization

/-!
# Projectivizations of complex vector spaces as Tau Ceti's `ℂPⁿ`

For a Hausdorff complex topological vector space `V` with `finrank ℂ V = n + 1`, this file gives
the homeomorphism `Projectivization.complexProjectiveSpaceHomeomorph` from Tau Ceti's
sphere-quotient model `ComplexProjectiveSpace n` of `ℂPⁿ` to the projectivization `ℙ ℂ V`. It is
Tau Ceti's `TauCeti.ComplexProjectiveSpace.homeomorphProjectivization`, onto
`ℙ ℂ (Fin (n + 1) → ℂ)`, followed by the homeomorphism
`ContinuousLinearEquiv.mapProjectivization` induced by a continuous linear equivalence
`(Fin (n + 1) → ℂ) ≃L[ℂ] V`. Topological facts that Tau Ceti proves for its model, such as its
cohomology or its simple connectivity, are carried along it to `ℙ ℂ V`.

It also says how Tau Ceti's homeomorphism meets the structure on both sides. In the affine charts
at the coordinate `k`, both inverse charts are `z ↦ [Fin.insertNth k 1 z]`: the homeomorphism sends
`TauCeti.ComplexProjectiveSpace.affineParam k z` to `(Projectivization.affineChart k).symm z`, so
in these charts it and its inverse are the identity. It is also equivariant for the unitary group
`U(n + 1)`: on `CPⁿ` a unitary matrix acts on unit representatives
(`TauCeti.ComplexProjectiveSpace.instMulActionUnitaryGroup`), and on `ℙ ℂ (Fin (n + 1) → ℂ)` it
acts linearly on representatives (Mathlib's `Projectivization.smul_mk`). Both send the class of a
unit vector `x` to the class of `A *ᵥ x`, which is again a unit vector.

## Main declarations

* `Projectivization.complexProjectiveSpaceHomeomorph`: the homeomorphism `CPⁿ ≃ₜ ℙ ℂ V`.
* `TauCeti.ComplexProjectiveSpace.homeomorphProjectivization_affineParam`: the homeomorphism
  matches the standard affine parametrizations of the two models;
  `TauCeti.ComplexProjectiveSpace.homeomorphProjectivization_symm_mk_insertNth` is its inverse
  form, and
  `TauCeti.ComplexProjectiveSpace.homeomorphProjectivization_eq_affineChart_symm_affineChart` and
  `TauCeti.ComplexProjectiveSpace.homeomorphProjectivization_symm_eq_affineParam_affineChart`
  are its forms on the affine opens.
* `TauCeti.ComplexProjectiveSpace.homeomorphProjectivization_smul` and
  `TauCeti.ComplexProjectiveSpace.homeomorphProjectivization_symm_smul`: the homeomorphism and its
  inverse commute with the actions of `Matrix.unitaryGroup (Fin (n + 1)) ℂ`.

## References

* [P. Griffiths and J. Harris, *Principles of Algebraic Geometry*][GriffithsHarris1978], §0.2.
-/

public section

noncomputable section

open Module TauCeti
open scoped LinearAlgebra.Projectivization

namespace Projectivization

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousSMul ℂ V] [T2Space V] {n : ℕ}

/-- A complex projective space `ℙ ℂ V`, for a Hausdorff complex topological vector space `V` with
`finrank ℂ V = n + 1`, is homeomorphic to Tau Ceti's `ℂPⁿ`, through Tau Ceti's
`ComplexProjectiveSpace.homeomorphProjectivization` and a continuous linear equivalence
`(Fin (n + 1) → ℂ) ≃L[ℂ] V`. -/
def complexProjectiveSpaceHomeomorph (hV : finrank ℂ V = n + 1) :
    ComplexProjectiveSpace n ≃ₜ ℙ ℂ V :=
  have : FiniteDimensional ℂ V := Module.finite_of_finrank_eq_succ hV
  (ComplexProjectiveSpace.homeomorphProjectivization n).trans
    (ContinuousLinearEquiv.ofFinrankEq (E := Fin (n + 1) → ℂ) (F := V)
      (by rw [finrank_fin_fun, hV])).mapProjectivization

end Projectivization

open Matrix Metric

namespace TauCeti.ComplexProjectiveSpace

variable (n : ℕ)

/-- The homeomorphism `CPⁿ ≃ₜ ℙ ℂ (Fin (n + 1) → ℂ)` sends the point with affine coordinates `z`
in the chart `X_k ≠ 0` of the sphere-quotient model to the point with the same affine coordinates
in the chart `X_k ≠ 0` of the projectivization: both are the line through
`Fin.insertNth k 1 z`. -/
@[simp]
theorem homeomorphProjectivization_affineParam (k : Fin (n + 1)) (z : Fin n → ℂ) :
    homeomorphProjectivization n (affineParam k z) = (Projectivization.affineChart k).symm z := by
  rw [affineParam_def, homeomorphProjectivization_mk, Projectivization.affineChart_symm_apply,
    Projectivization.mk_eq_mk_iff']
  refine ⟨((‖affineVector k z‖⁻¹ : ℝ) : ℂ), ?_⟩
  funext j
  rw [Pi.smul_apply, smul_eq_mul, affineUnitVector_apply]
  rcases Fin.eq_self_or_eq_succAbove k j with rfl | ⟨j, rfl⟩
  · rw [Fin.insertNth_apply_same, affineVector_apply_self]
  · rw [Fin.insertNth_apply_succAbove, affineVector_apply_succAbove]

/-- The inverse of the homeomorphism `CPⁿ ≃ₜ ℙ ℂ (Fin (n + 1) → ℂ)` sends the line through
`Fin.insertNth k 1 z` to the point with affine coordinates `z` in the chart `X_k ≠ 0` of the
sphere-quotient model. -/
@[simp]
theorem homeomorphProjectivization_symm_mk_insertNth (k : Fin (n + 1)) (z : Fin n → ℂ) :
    (homeomorphProjectivization n).symm (Projectivization.mk ℂ
      (Fin.insertNth (α := fun _ ↦ ℂ) k 1 z) (Fin.insertNth_one_ne_zero k z)) =
      affineParam k z := by
  rw [Homeomorph.symm_apply_eq, homeomorphProjectivization_affineParam,
    Projectivization.affineChart_symm_apply]

/-- On the affine open `X_k ≠ 0`, the homeomorphism `CPⁿ ≃ₜ ℙ ℂ (Fin (n + 1) → ℂ)` reads, in the
standard charts, as the identity: it is the inverse of the chart of `ℙ ℂ (Fin (n + 1) → ℂ)`
after the chart of `CPⁿ`. -/
theorem homeomorphProjectivization_eq_affineChart_symm_affineChart (k : Fin (n + 1))
    {p : ComplexProjectiveSpace n} (hp : p ∈ affineOpen k) :
    homeomorphProjectivization n p = (Projectivization.affineChart k).symm (affineChart k p) := by
  conv_lhs => rw [← (affineChart k).left_inv (x := p) (by rwa [affineChart_source])]
  rw [affineChart_symm_apply]
  exact homeomorphProjectivization_affineParam n k _

/-- On the affine open `X_k ≠ 0` of `ℙ ℂ (Fin (n + 1) → ℂ)`, the inverse of the homeomorphism
`CPⁿ ≃ₜ ℙ ℂ (Fin (n + 1) → ℂ)` is the standard affine parametrization of `CPⁿ` after the chart of
`ℙ ℂ (Fin (n + 1) → ℂ)`. -/
theorem homeomorphProjectivization_symm_eq_affineParam_affineChart (k : Fin (n + 1))
    {x : ℙ ℂ (Fin (n + 1) → ℂ)} (hx : x ∈ Projectivization.affineOpen k) :
    (homeomorphProjectivization n).symm x = affineParam k (Projectivization.affineChart k x) := by
  rw [Homeomorph.symm_apply_eq, homeomorphProjectivization_affineParam]
  exact ((Projectivization.affineChart k).left_inv
    (by rwa [Projectivization.affineChart_source])).symm

/-- The homeomorphism `CPⁿ ≃ₜ ℙ ℂ (Fin (n + 1) → ℂ)` is equivariant for the unitary group: it
intertwines the action `A • [x] = [A x]` on unit representatives with the linear action
`A • [v] = [A v]` on lines. -/
@[simp]
theorem homeomorphProjectivization_smul (A : unitaryGroup (Fin (n + 1)) ℂ)
    (p : ComplexProjectiveSpace n) :
    homeomorphProjectivization n (A • p) = A • homeomorphProjectivization n p := by
  induction p using ComplexProjectiveSpace.inductionOn with
  | h x =>
    rw [smul_mk, homeomorphProjectivization_mk, homeomorphProjectivization_mk,
      Projectivization.smul_mk]
    simp only [LinearIsometryEquiv.coe_smul_unitSphere, UnitaryGroup.toLinearIsometryEquiv_apply,
      WithLp.ofLp_toLp, Submonoid.smul_def, smul_eq_mulVec]

/-- The inverse of the homeomorphism `CPⁿ ≃ₜ ℙ ℂ (Fin (n + 1) → ℂ)` is equivariant for the
unitary group. -/
@[simp]
theorem homeomorphProjectivization_symm_smul (A : unitaryGroup (Fin (n + 1)) ℂ)
    (x : ℙ ℂ (Fin (n + 1) → ℂ)) :
    (homeomorphProjectivization n).symm (A • x) = A • (homeomorphProjectivization n).symm x := by
  rw [Homeomorph.symm_apply_eq, homeomorphProjectivization_smul, Homeomorph.apply_symm_apply]

end TauCeti.ComplexProjectiveSpace

end
