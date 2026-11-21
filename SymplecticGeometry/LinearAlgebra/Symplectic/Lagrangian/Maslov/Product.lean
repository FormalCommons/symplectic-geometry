/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.LinearAlgebra.Symplectic.Lagrangian.Maslov.Basic
public import TauCeti.Analysis.Matrix.SymplecticGroup.Maslov

/-!
# The product axiom for the Maslov index of Lagrangian loops

Write `ℒ ι` for the space of Lagrangian subspaces of the standard model `(StdSpace ι, ω₀)`. A loop
`Ψ` of symplectic matrices moves a loop `γ` of Lagrangian subspaces to the loop `t ↦ Ψ t • γ t`.
Its Maslov index is `μ(γ) + 2 μ(Ψ)`, where `μ(Ψ)` is the Maslov index
`TauCeti.GLSymplectic.maslovIndex` of the symplectic loop.

## Main results

* `SymplecticGeometry.LagrangianGrassmannian.maslovIndex_smul`: the product axiom
  `μ(Ψ γ) = μ(γ) + 2 μ(Ψ)`.
* `SymplecticGeometry.LagrangianGrassmannian.maslovIndex_smul_const`: for a fixed Lagrangian `Λ`,
  the loop `t ↦ Ψ t • Λ` has Maslov index `2 μ(Ψ)`.

## Implementation notes

Tau Ceti's symplectic polar homotopy `TauCeti.GLSymplectic.polarHomotopy` deforms `Ψ`, through
loops of symplectic matrices, into its loop of orthogonal polar factors, which are realified
unitary matrices `U t`. Acting on `γ`, it gives a free homotopy of Lagrangian loops, and at its
end the Maslov phase is `(det U t)² ρ(γ t)` (`maslovPhase_unitary_smul`), whose degree is
`2 μ(Ψ) + μ(γ)`. This follows the proof of `TauCeti.GLSymplectic.maslovIndex_mul`, which deforms
two symplectic loops the same way.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.3
  (Theorem 2.3.7, the product axiom).
-/

public section

namespace SymplecticGeometry

open Matrix TauCeti
open Matrix.UnitaryGroup (detCircle)
open scoped unitInterval

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local notation "ℒ" ι => LagrangianGrassmannian (stdForm ι)

namespace LagrangianGrassmannian

/-- An orthogonal symplectic matrix `U`, acting on Lagrangian subspaces, multiplies the Maslov
phase by the square of its symplectic Maslov phase. -/
private theorem maslovPhase_inclusion_smul
    (U : ↥(GLSymplectic ι ℝ ⊓ unitarySubgroup (GL (ι ⊕ ι) ℝ))) (Λ : ℒ ι) :
    maslovPhase (Subgroup.inclusion inf_le_left U • Λ) =
      GLSymplectic.maslovPhase (Subgroup.inclusion inf_le_left U) ^ 2 * maslovPhase Λ := by
  have hU : Subgroup.inclusion inf_le_left U =
      GLSymplectic.ofUnitary (unitaryGroupEquivSymplecticInfOrthogonal.symm U) := by
    rw [GLSymplectic.ofUnitary_apply, ContinuousMulEquiv.apply_symm_apply]
  rw [hU, ← unitary_smul_def, maslovPhase_unitary_smul, GLSymplectic.maslovPhase_ofUnitary]

/-- **The product axiom.** A loop `Ψ` of symplectic matrices moves a loop `γ` of Lagrangian
subspaces to the loop `t ↦ Ψ t • γ t`, whose Maslov index is that of `γ` plus twice the Maslov
index of `Ψ`. -/
@[simp]
theorem maslovIndex_smul {A : GLSymplectic ι ℝ} {Λ : ℒ ι} (Ψ : Path A A) (γ : Path Λ Λ) :
    maslovIndex ((Ψ.prod γ).map continuous_smul) =
      maslovIndex γ + 2 * GLSymplectic.maslovIndex Ψ := by
  -- Contract the positive polar factors of `Ψ` through symplectic matrices.
  let D := GLSymplectic.polarHomotopy (n := ι)
  let F : C(I × I, Circle) :=
    ⟨fun p ↦ maslovPhase (D (p.1, Ψ p.2) • γ p.2),
      continuous_maslovPhase.comp
        ((D.continuous.comp (continuous_fst.prodMk (Ψ.continuous.comp continuous_snd))).smul
          (γ.continuous.comp continuous_snd))⟩
  rw [maslovIndex_def, maslovIndex_def, GLSymplectic.maslovIndex_def]
  trans Circle.degree
    (((Ψ.map GLSymplectic.continuous_maslovPhase).map (continuous_pow 2)).mul
      (γ.map continuous_maslovPhase))
  swap
  · rw [Circle.degree_mul, Circle.degree_map_pow]
    push_cast
    ring
  refine Circle.degree_eq_of_homotopy _ _ F (fun t ↦ ?_) (fun t ↦ ?_) (fun s ↦ ?_)
  · simp [F, D]
  · -- After the contraction `Ψ t` is orthogonal, where the phases multiply.
    simp only [F, D, ContinuousMap.coe_mk, ContinuousMap.Homotopy.apply_one, Path.mul_apply,
      Path.map_coe, Function.comp_apply]
    rw [maslovPhase_inclusion_smul, GLSymplectic.maslovPhase_inclusion_polarUnitary]
  · simp only [F, ContinuousMap.coe_mk, Path.source, Path.target]

/-- A loop `Ψ` of symplectic matrices moves a fixed Lagrangian subspace `Λ` along the loop
`t ↦ Ψ t • Λ`, whose Maslov index is twice the Maslov index of `Ψ`. -/
@[simp]
theorem maslovIndex_smul_const {A : GLSymplectic ι ℝ} (Ψ : Path A A) (Λ : ℒ ι) :
    maslovIndex (Ψ.map (continuous_id.smul continuous_const : Continuous fun B ↦ B • Λ)) =
      2 * GLSymplectic.maslovIndex Ψ := by
  rw [← zero_add (2 * _), ← maslovIndex_refl Λ, ← maslovIndex_smul]
  rw [maslovIndex_def, maslovIndex_def]
  exact Circle.degree_congr _ _ fun t ↦ by simp

end LagrangianGrassmannian

end SymplecticGeometry

end
