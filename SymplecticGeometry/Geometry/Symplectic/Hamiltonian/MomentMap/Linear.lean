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
* `TauCeti.SymplecticForm.linearMomentMapCompPolar`: the covector `ζ ↦ σ (ρ ζ v, w)` on `𝔥`, the
  polarization of `μ_V`.
* `TauCeti.SymplecticForm.fderiv_apply_linearMomentMapComp`: for every linear functional `L` on
  `𝔥*`, the derivative of `v ↦ L (μ_V v)` at `v` sends `w` to `L` of that covector.

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

/-- The polarization of `μ_V = σ.linearMomentMapComp ρ`: the covector `ζ ↦ σ (ρ ζ v, w)` on `𝔥`.
It is the derivative of `μ_V` at `v` in the direction `w`
(`TauCeti.SymplecticForm.fderiv_apply_linearMomentMapComp`). -/
def linearMomentMapCompPolar (v w : V) : Module.Dual ℝ 𝔥 where
  toFun ζ := σ ((ρ ζ : Module.End ℝ V) v) w
  map_add' ζ ζ' := by simp
  map_smul' c ζ := by simp

@[simp]
theorem linearMomentMapCompPolar_apply (v w : V) (ζ : 𝔥) :
    σ.linearMomentMapCompPolar ρ v w ζ = σ ((ρ ζ : Module.End ℝ V) v) w :=
  (rfl)

end Algebraic

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  (σ : SymplecticForm V) (ρ : 𝔥 →ₗ[ℝ] skewAdjointLieSubalgebra σ.toBilinForm)

/-- For a finite-dimensional `V`, a linear functional `L` on `𝔥*` composed with
`μ_V = σ.linearMomentMapComp ρ` is the component of the linear moment map at the element of
`sp(V, σ)` that represents the functional `L ∘ ρ*` on `sp(V, σ)*`. -/
theorem apply_linearMomentMapComp_eq_linearMomentMap (L : Module.Dual ℝ 𝔥 →ₗ[ℝ] ℝ) (v : V) :
    L (σ.linearMomentMapComp ρ v) =
      σ.linearMomentMap v ((Module.evalEquiv ℝ _).symm (L ∘ₗ ρ.dualMap)) := by
  rw [Module.apply_evalEquiv_symm_apply, LinearMap.comp_apply, LinearMap.dualMap_apply',
    linearMomentMapComp_def]

/-- For a finite-dimensional `V` and every linear functional `L` on `𝔥*`, the function
`v ↦ L (μ_V v)` is smooth, where `μ_V = σ.linearMomentMapComp ρ`. No topology on `𝔥` is
needed. -/
theorem contDiff_linearMomentMapComp (L : Module.Dual ℝ 𝔥 →ₗ[ℝ] ℝ) :
    ContDiff ℝ ∞ fun v ↦ L (σ.linearMomentMapComp ρ v) := by
  simp only [apply_linearMomentMapComp_eq_linearMomentMap]
  exact contMDiff_iff_contDiff.1 (σ.isMomentMap_linearMomentMap.contMDiff _)

/-- The moment equation of `μ_V = σ.linearMomentMapComp ρ`: the derivative of `v ↦ μ_V v ξ` at
`v` sends `w` to `σ (ρ ξ v, w)`. -/
theorem fderiv_linearMomentMapComp_apply (ξ : 𝔥) (v w : V) :
    fderiv ℝ (fun x ↦ σ.linearMomentMapComp ρ x ξ) v w = σ ((ρ ξ : Module.End ℝ V) v) w := by
  simp only [linearMomentMapComp_def, LinearMap.comp_apply]
  exact fderiv_linearMomentMap_apply σ (ρ ξ) v w

/-- The derivative of `v ↦ L (μ_V v)` at `v`, for a linear functional `L` on `𝔥*`, sends `w` to
`L (σ.linearMomentMapCompPolar ρ v w)`, the value of `L` on the covector `ζ ↦ σ (ρ ζ v, w)`. -/
theorem fderiv_apply_linearMomentMapComp (L : Module.Dual ℝ 𝔥 →ₗ[ℝ] ℝ) (v w : V) :
    fderiv ℝ (fun x ↦ L (σ.linearMomentMapComp ρ x)) v w =
      L (σ.linearMomentMapCompPolar ρ v w) := by
  let f : Module.Dual ℝ (skewAdjointLieSubalgebra σ.toBilinForm) :=
    { toFun A := σ ((A : Module.End ℝ V) v) w
      map_add' A B := by simp
      map_smul' c A := by simp }
  have hf : σ.linearMomentMapCompPolar ρ v w = ρ.dualMap f := by
    ext ζ
    simp [f]
  simp only [apply_linearMomentMapComp_eq_linearMomentMap]
  rw [fderiv_linearMomentMap_apply, hf, ← LinearMap.comp_apply L ρ.dualMap f,
    ← Module.apply_evalEquiv_symm_apply ℝ _ f]
  simp only [f, LinearMap.coe_mk, AddHom.coe_mk]

end TauCeti.SymplecticForm

end
