/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import TauCeti.Topology.ComplexProjectiveSpace.Projectivization

/-!
# Complex projective space as the projectivization of a space of dimension `n + 1`

Tau Ceti identifies its sphere-quotient model `ComplexProjectiveSpace n` of `ℂℙⁿ` with the
projectivization `ℙ ℂ (Fin (n + 1) → ℂ)`
(`TauCeti.ComplexProjectiveSpace.homeomorphProjectivization`). This file extends that
identification to `ℙ ℂ V` for any complex normed space `V` with `finrank ℂ V = n + 1`
(`TauCeti.ComplexProjectiveSpace.homeomorphProjectivizationOfFinrankEq`), so that the facts Tau
Ceti proves about `ComplexProjectiveSpace n` can be carried to `ℙ ℂ V`.
-/

public section

noncomputable section

open Module
open scoped LinearAlgebra.Projectivization

namespace TauCeti.ComplexProjectiveSpace

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {n : ℕ}

/-- A homeomorphism from Tau Ceti's model `ComplexProjectiveSpace n` onto `ℙ ℂ V`, for
`finrank ℂ V = n + 1`: `homeomorphProjectivization` onto `ℙ ℂ (Fin (n + 1) → ℂ)`, followed by the
map of projective spaces of a continuous linear equivalence `(Fin (n + 1) → ℂ) ≃ V`. -/
def homeomorphProjectivizationOfFinrankEq (hV : finrank ℂ V = n + 1) :
    ComplexProjectiveSpace n ≃ₜ ℙ ℂ V :=
  have : FiniteDimensional ℂ V := Module.finite_of_finrank_eq_succ hV
  (homeomorphProjectivization n).trans
    (ContinuousLinearEquiv.ofFinrankEq (E := Fin (n + 1) → ℂ) (F := V)
      (by rw [finrank_fin_fun, hV])).mapProjectivization

theorem homeomorphProjectivizationOfFinrankEq_def (hV : finrank ℂ V = n + 1) :
    homeomorphProjectivizationOfFinrankEq hV =
      have : FiniteDimensional ℂ V := Module.finite_of_finrank_eq_succ hV
      (homeomorphProjectivization n).trans
        (ContinuousLinearEquiv.ofFinrankEq (E := Fin (n + 1) → ℂ) (F := V)
          (by rw [finrank_fin_fun, hV])).mapProjectivization :=
  (rfl)

end TauCeti.ComplexProjectiveSpace

end
