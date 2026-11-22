/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.RepresentationTheory.Continuous.Basic
public import TauCeti.Analysis.Matrix.EuclideanLin

/-!
# The standard continuous representation of the general linear group

This file defines `Matrix.GeneralLinearGroup.contRep 𝕜 ι`, the continuous representation of
`GL ι 𝕜` on `EuclideanSpace 𝕜 ι` in which an invertible matrix acts by multiplication on
column vectors, and shows that it depends continuously on the matrix. A subgroup of `GL ι 𝕜`
acts on `EuclideanSpace 𝕜 ι` through `ContRepresentation.restrict`.

The construction is that of the private tautological representation of a subgroup of `GL ι 𝕜`
in Tau Ceti's `TauCeti/LinearAlgebra/Matrix/GeneralLinearGroup/MaximalCompact.lean`, made public
and stated for the whole group.

## Main definitions and results

* `Matrix.GeneralLinearGroup.contRep`: the standard representation of `GL ι 𝕜` on
  `EuclideanSpace 𝕜 ι`, as a `ContRepresentation`.
* `Matrix.GeneralLinearGroup.continuous_contRep`: it is continuous in the group element.
* `Matrix.GeneralLinearGroup.toEuclideanLin_apply_toEuclideanLin_inv_apply`: on
  `EuclideanSpace 𝕜 ι`, an invertible matrix undoes the action of its inverse.
-/

public section

namespace Matrix.GeneralLinearGroup

variable (𝕜 ι : Type*) [RCLike 𝕜] [Fintype ι] [DecidableEq ι]

/-- The standard representation of `GL ι 𝕜` on `EuclideanSpace 𝕜 ι`: an invertible matrix `A`
acts by the continuous linear map `v ↦ A *ᵥ v`. -/
noncomputable def contRep : ContRepresentation 𝕜 (GL ι 𝕜) (EuclideanSpace 𝕜 ι) :=
  .ofMonoidHom <| (toEuclideanCLM (n := ι) (𝕜 := 𝕜)).toAlgEquiv.toMonoidHom.comp
    (Units.coeHom _)

variable {𝕜 ι}

/-- An element of `GL ι 𝕜` acts through `contRep` by its continuous linear map. -/
@[simp]
theorem contRep_apply (A : GL ι 𝕜) :
    contRep 𝕜 ι A = toEuclideanCLM (n := ι) (𝕜 := 𝕜) (A : Matrix ι ι 𝕜) :=
  (rfl)

variable (𝕜 ι)

/-- The standard representation of `GL ι 𝕜` depends continuously on the matrix. -/
theorem continuous_contRep : Continuous (contRep 𝕜 ι) :=
  continuous_toEuclideanCLM.comp Units.continuous_val

variable {𝕜 ι}

/-- On `EuclideanSpace 𝕜 ι`, an invertible matrix undoes the action of its inverse. -/
@[simp]
theorem toEuclideanLin_apply_toEuclideanLin_inv_apply (A : GL ι 𝕜) (v : EuclideanSpace 𝕜 ι) :
    toEuclideanLin (A : Matrix ι ι 𝕜) (toEuclideanLin ((A⁻¹ : GL ι 𝕜) : Matrix ι ι 𝕜) v) = v := by
  rw [← LinearMap.comp_apply, ← toLpLin_mul_same, Units.mul_inv, toLpLin_one, LinearMap.id_apply]

end Matrix.GeneralLinearGroup

end
