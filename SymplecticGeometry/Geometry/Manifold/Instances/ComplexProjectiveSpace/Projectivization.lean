/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import TauCeti.Geometry.Manifold.Instances.ComplexProjectiveSpace.Basic
public import TauCeti.Geometry.Manifold.Instances.Projectivization
public import TauCeti.Topology.ComplexProjectiveSpace.Projectivization
import SymplecticGeometry.Geometry.Manifold.ContMDiff.RestrictScalars

/-!
# The sphere-quotient model of `CPⁿ` and `ℙ ℂ (Fin (n + 1) → ℂ)` as manifolds

Tau Ceti's homeomorphism `TauCeti.ComplexProjectiveSpace.homeomorphProjectivization n` from the
circle quotient of the unit sphere to the space of complex lines in `ℂⁿ⁺¹` is a diffeomorphism.
Both spaces are charted by their standard affine charts, and in the charts at the coordinate `k`
both inverse charts are `z ↦ [Fin.insertNth k 1 z]`: the homeomorphism sends
`TauCeti.ComplexProjectiveSpace.affineParam k z` to `(Projectivization.affineChart k).symm z`.
So in these charts the homeomorphism and its inverse are the identity, and both are holomorphic.

## Main declarations

* `TauCeti.ComplexProjectiveSpace.homeomorphProjectivization_affineParam`: the homeomorphism
  matches the standard affine parametrizations of the two models;
  `TauCeti.ComplexProjectiveSpace.homeomorphProjectivization_symm_mk_insertNth` is its inverse
  form.
* `TauCeti.ComplexProjectiveSpace.contMDiff_homeomorphProjectivization` and
  `TauCeti.ComplexProjectiveSpace.contMDiff_homeomorphProjectivization_symm`: the homeomorphism
  and its inverse are `C^r` for the complex models `𝓘(ℂ, Fin n → ℂ)`, for every `r`.
* `TauCeti.ComplexProjectiveSpace.diffeomorphProjectivization n`: the analytic diffeomorphism
  `ComplexProjectiveSpace n ≃ₘ^ω⟮𝓘(ℝ, Fin n → ℂ), 𝓘(ℝ, Fin n → ℂ)⟯ ℙ ℂ (Fin (n + 1) → ℂ)` of the
  underlying real manifolds, whose map is `homeomorphProjectivization n`.

## References

* [P. Griffiths and J. Harris, *Principles of Algebraic Geometry*][GriffithsHarris1978], §0.2.
-/

public section

open Metric
open scoped ContDiff Manifold LinearAlgebra.Projectivization

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

/-- The homeomorphism `CPⁿ ≃ₜ ℙ ℂ (Fin (n + 1) → ℂ)` is `C^r` for the complex manifold
structures, for every `r`; for `r = ω` it is holomorphic. -/
theorem contMDiff_homeomorphProjectivization (r : ℕ∞ω) :
    ContMDiff 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin n → ℂ) r (homeomorphProjectivization n) := by
  intro p
  obtain ⟨k, hk⟩ := exists_mem_affineOpen p
  refine (((Projectivization.contMDiff_affineChart_symm k r).comp_contMDiffOn
    (contMDiffOn_affineChart k r)).congr fun q hq ↦ ?_).contMDiffAt
    ((isOpen_affineOpen k).mem_nhds hk)
  exact homeomorphProjectivization_eq_affineChart_symm_affineChart n k hq

/-- The inverse of the homeomorphism `CPⁿ ≃ₜ ℙ ℂ (Fin (n + 1) → ℂ)` is `C^r` for the complex
manifold structures, for every `r`; for `r = ω` it is holomorphic. -/
theorem contMDiff_homeomorphProjectivization_symm (r : ℕ∞ω) :
    ContMDiff 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin n → ℂ) r (homeomorphProjectivization n).symm := by
  intro x
  obtain ⟨k, hk⟩ := Projectivization.exists_mem_affineOpen x
  refine ((((contMDiff_affineChart_symm k r).comp_contMDiffOn
    (Projectivization.contMDiffOn_affineChart k r)).congr fun y hy ↦ ?_).contMDiffAt
    ((Projectivization.isOpen_affineOpen k).mem_nhds hk))
  rw [Function.comp_apply, affineChart_symm_apply]
  exact homeomorphProjectivization_symm_eq_affineParam_affineChart n k hy

/-- The sphere-quotient model `CPⁿ` and the projectivization `ℙ ℂ (Fin (n + 1) → ℂ)` are
analytically diffeomorphic as real manifolds, by the map sending the class of a unit vector to the
line it spans. -/
noncomputable def diffeomorphProjectivization :
    ComplexProjectiveSpace n ≃ₘ^ω⟮𝓘(ℝ, Fin n → ℂ), 𝓘(ℝ, Fin n → ℂ)⟯ ℙ ℂ (Fin (n + 1) → ℂ) where
  toEquiv := (homeomorphProjectivization n).toEquiv
  contMDiff_toFun := (contMDiff_homeomorphProjectivization n ω).restrictScalars' ℝ
  contMDiff_invFun := (contMDiff_homeomorphProjectivization_symm n ω).restrictScalars' ℝ

/-- The map of the diffeomorphism `CPⁿ ≃ ℙ ℂ (Fin (n + 1) → ℂ)` is the homeomorphism
`homeomorphProjectivization n`. -/
@[simp]
theorem coe_diffeomorphProjectivization :
    ⇑(diffeomorphProjectivization n) = homeomorphProjectivization n :=
  (rfl)

/-- The inverse of the diffeomorphism `CPⁿ ≃ ℙ ℂ (Fin (n + 1) → ℂ)` is the inverse of the
homeomorphism `homeomorphProjectivization n`. -/
@[simp]
theorem coe_diffeomorphProjectivization_symm :
    ⇑(diffeomorphProjectivization n).symm = (homeomorphProjectivization n).symm :=
  (rfl)

/-- The homeomorphism underlying the diffeomorphism `CPⁿ ≃ ℙ ℂ (Fin (n + 1) → ℂ)` is
`homeomorphProjectivization n`. -/
@[simp]
theorem diffeomorphProjectivization_toHomeomorph :
    (diffeomorphProjectivization n).toHomeomorph = homeomorphProjectivization n :=
  (rfl)

/-- The diffeomorphism `CPⁿ ≃ ℙ ℂ (Fin (n + 1) → ℂ)` sends the class of a unit vector to the line
it spans. -/
theorem diffeomorphProjectivization_mk
    (x : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) :
    diffeomorphProjectivization n (mk n x) =
      Projectivization.mk ℂ (WithLp.ofLp (x : EuclideanSpace ℂ (Fin (n + 1))))
        ((WithLp.ofLp_eq_zero _).not.2 (ne_zero_of_mem_sphere one_ne_zero x)) := by
  rw [coe_diffeomorphProjectivization, homeomorphProjectivization_mk]

/-- The inverse of the diffeomorphism `CPⁿ ≃ ℙ ℂ (Fin (n + 1) → ℂ)` sends the line spanned by a
unit vector to its class. -/
theorem diffeomorphProjectivization_symm_mk
    (x : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1)
    (hx : WithLp.ofLp (x : EuclideanSpace ℂ (Fin (n + 1))) ≠ 0) :
    (diffeomorphProjectivization n).symm (Projectivization.mk ℂ (WithLp.ofLp
      (x : EuclideanSpace ℂ (Fin (n + 1)))) hx) = mk n x := by
  rw [coe_diffeomorphProjectivization_symm, homeomorphProjectivization_symm_mk]

end TauCeti.ComplexProjectiveSpace

end
