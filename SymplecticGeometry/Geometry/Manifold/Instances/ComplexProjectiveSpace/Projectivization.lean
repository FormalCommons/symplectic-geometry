/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import SymplecticGeometry.Topology.ComplexProjectiveSpace.Homeomorph
public import TauCeti.Geometry.Manifold.Instances.ComplexProjectiveSpace.Basic
public import TauCeti.Geometry.Manifold.Instances.Projectivization
import SymplecticGeometry.Geometry.Manifold.ContMDiff.RestrictScalars

/-!
# The sphere-quotient model of `CPⁿ` and `ℙ ℂ (Fin (n + 1) → ℂ)` as manifolds

Tau Ceti's homeomorphism `TauCeti.ComplexProjectiveSpace.homeomorphProjectivization n` from the
circle quotient of the unit sphere to the space of complex lines in `ℂⁿ⁺¹` is a diffeomorphism.
Both spaces are charted by their standard affine charts, and in these charts the homeomorphism and
its inverse are the identity
(`TauCeti.ComplexProjectiveSpace.homeomorphProjectivization_eq_affineChart_symm_affineChart` and
`TauCeti.ComplexProjectiveSpace.homeomorphProjectivization_symm_eq_affineParam_affineChart`, in
`SymplecticGeometry.Topology.ComplexProjectiveSpace.Homeomorph`), so both are holomorphic. The
diffeomorphism is equivariant for the unitary group `U(n + 1)`, as the homeomorphism is
(`TauCeti.ComplexProjectiveSpace.homeomorphProjectivization_smul`).

## Main declarations

* `TauCeti.ComplexProjectiveSpace.contMDiff_homeomorphProjectivization` and
  `TauCeti.ComplexProjectiveSpace.contMDiff_homeomorphProjectivization_symm`: the homeomorphism
  and its inverse are `C^r` for the complex models `𝓘(ℂ, Fin n → ℂ)`, for every `r`.
* `TauCeti.ComplexProjectiveSpace.diffeomorphProjectivization n`: the analytic diffeomorphism
  `ComplexProjectiveSpace n ≃ₘ^ω⟮𝓘(ℝ, Fin n → ℂ), 𝓘(ℝ, Fin n → ℂ)⟯ ℙ ℂ (Fin (n + 1) → ℂ)` of the
  underlying real manifolds, whose map is `homeomorphProjectivization n`.
* `TauCeti.ComplexProjectiveSpace.diffeomorphProjectivization_smul` and
  `TauCeti.ComplexProjectiveSpace.diffeomorphProjectivization_symm_smul`: the diffeomorphism and
  its inverse commute with the actions of `Matrix.unitaryGroup (Fin (n + 1)) ℂ`.

## References

* [P. Griffiths and J. Harris, *Principles of Algebraic Geometry*][GriffithsHarris1978], §0.2.
-/

public section

open Matrix Metric
open scoped ContDiff Manifold LinearAlgebra.Projectivization

namespace TauCeti.ComplexProjectiveSpace

variable (n : ℕ)

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

/-- The diffeomorphism `CPⁿ ≃ ℙ ℂ (Fin (n + 1) → ℂ)` is equivariant for the unitary group. -/
theorem diffeomorphProjectivization_smul (A : unitaryGroup (Fin (n + 1)) ℂ)
    (p : ComplexProjectiveSpace n) :
    diffeomorphProjectivization n (A • p) = A • diffeomorphProjectivization n p := by
  rw [coe_diffeomorphProjectivization, homeomorphProjectivization_smul]

/-- The inverse of the diffeomorphism `CPⁿ ≃ ℙ ℂ (Fin (n + 1) → ℂ)` is equivariant for the
unitary group. -/
theorem diffeomorphProjectivization_symm_smul (A : unitaryGroup (Fin (n + 1)) ℂ)
    (x : ℙ ℂ (Fin (n + 1) → ℂ)) :
    (diffeomorphProjectivization n).symm (A • x) = A • (diffeomorphProjectivization n).symm x := by
  rw [coe_diffeomorphProjectivization_symm, homeomorphProjectivization_symm_smul]

end TauCeti.ComplexProjectiveSpace

end
