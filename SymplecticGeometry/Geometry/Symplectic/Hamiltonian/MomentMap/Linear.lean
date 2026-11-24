/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap

/-!
# The moment map of a linear map into `sp(V, σ)`

For a symplectic vector space `(V, σ)`, Tau Ceti's `TauCeti.SymplecticForm.linearMomentMap` is the
moment map `V → sp(V, σ)*` of the linear action of `sp(V, σ)` on `V`. Composing it with a linear
map `ρ : 𝔥 → sp(V, σ)` from a real vector space `𝔥` gives the moment map `μ_V : V → 𝔥*`,
`μ_V v ξ = ½ σ (ρ ξ v, v)`, of the infinitesimal action of `𝔥` through `ρ`. In the
Marle–Guillemin–Sternberg local model, `𝔥` is the Lie algebra of the stabilizer and `ρ` its
action on the symplectic slice.

## Main results

* `TauCeti.SymplecticForm.linearMomentMapComp`: the map `μ_V`, with `μ_V 0 = 0`
  (`TauCeti.SymplecticForm.linearMomentMapComp_zero`).
* `TauCeti.SymplecticForm.contDiff_linearMomentMapComp`: for a finite-dimensional `V`, the map
  `v ↦ L (μ_V v)` is smooth for every linear functional `L` on `𝔥*`; no topology on `𝔥` is used.
* `TauCeti.SymplecticForm.fderiv_linearMomentMapComp_apply`: the moment equation
  `d(μ_V(·) ξ)_v w = σ (ρ ξ v, w)`, from Tau Ceti's `fderiv_linearMomentMap_apply`.

## References

* [V. Guillemin and S. Sternberg][GuilleminSternberg1990]
* C.-M. Marle, *Modèle d'action hamiltonienne d'un groupe de Lie sur une variété symplectique*,
  Rend. Sem. Mat. Univ. Politec. Torino 43 (1985).
-/

public section

open scoped Manifold ContDiff

namespace TauCeti.SymplecticForm

variable {𝔥 : Type*} [AddCommGroup 𝔥] [Module ℝ 𝔥]

section Algebraic

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
  (σ : SymplecticForm V) (ρ : 𝔥 →ₗ[ℝ] skewAdjointLieSubalgebra σ.toBilinForm)

/-- The moment map `μ_V : V → 𝔥*` of a linear map `ρ : 𝔥 → sp(V, σ)` on a symplectic vector
space `(V, σ)`: the linear moment map `TauCeti.SymplecticForm.linearMomentMap` of `sp(V, σ)`
composed with `ρ`, so that `μ_V v ξ = ½ σ (ρ ξ v, v)`. -/
noncomputable def linearMomentMapComp (v : V) : Module.Dual ℝ 𝔥 :=
  σ.linearMomentMap v ∘ₗ ρ

theorem linearMomentMapComp_def (v : V) :
    σ.linearMomentMapComp ρ v = σ.linearMomentMap v ∘ₗ ρ :=
  (rfl)

@[simp]
theorem linearMomentMapComp_apply (v : V) (ξ : 𝔥) :
    σ.linearMomentMapComp ρ v ξ = σ ((ρ ξ : Module.End ℝ V) v) v / 2 := by
  rw [linearMomentMapComp_def, LinearMap.comp_apply, linearMomentMap_apply]

@[simp]
theorem linearMomentMapComp_zero : σ.linearMomentMapComp ρ 0 = 0 := by
  ext
  simp

end Algebraic

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  (σ : SymplecticForm V) (ρ : 𝔥 →ₗ[ℝ] skewAdjointLieSubalgebra σ.toBilinForm)

/-- For a finite-dimensional `V` and every linear functional `L` on `𝔥*`, the function
`v ↦ L (μ_V v)` is smooth, where `μ_V = σ.linearMomentMapComp ρ`. No topology on `𝔥` is
needed. -/
theorem contDiff_linearMomentMapComp (L : Module.Dual ℝ 𝔥 →ₗ[ℝ] ℝ) :
    ContDiff ℝ ∞ fun v ↦ L (σ.linearMomentMapComp ρ v) := by
  have h (v : V) : L (σ.linearMomentMapComp ρ v) = σ.linearMomentMap v
      ((Module.evalEquiv ℝ _).symm (L ∘ₗ ρ.dualMap)) := by
    rw [Module.apply_evalEquiv_symm_apply, LinearMap.comp_apply, LinearMap.dualMap_apply',
      linearMomentMapComp_def]
  simp only [h]
  exact contMDiff_iff_contDiff.1 (σ.isMomentMap_linearMomentMap.contMDiff _)

/-- The moment equation of `μ_V = σ.linearMomentMapComp ρ`: the derivative of `v ↦ μ_V v ξ` at
`v` sends `w` to `σ (ρ ξ v, w)`. -/
theorem fderiv_linearMomentMapComp_apply (ξ : 𝔥) (v w : V) :
    fderiv ℝ (fun x ↦ σ.linearMomentMapComp ρ x ξ) v w = σ ((ρ ξ : Module.End ℝ V) v) w := by
  simp only [linearMomentMapComp_def, LinearMap.comp_apply]
  exact fderiv_linearMomentMap_apply σ (ρ ξ) v w

end TauCeti.SymplecticForm

end
