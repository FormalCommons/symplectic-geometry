/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import TauCeti.LinearAlgebra.Complex.Conjugate

/-!
# The dimension of the conjugate of a complex vector space

The conjugate `TauCeti.Conjugate V` of a complex vector space `V` has the same underlying additive
group, with complex scalars acting through complex conjugation. Since conjugation is a bijection
of `ℂ`, the identity `V → Conjugate V` carries bases to bases, so `V` and its conjugate have the
same complex dimension (`TauCeti.Conjugate.finrank_eq`).
-/

public section

open Module

namespace TauCeti

namespace Conjugate

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The conjugate of a complex vector space has the same complex rank. -/
theorem rank_eq : Module.rank ℂ (Conjugate V) = Module.rank ℂ V :=
  (rank_eq_of_equiv_equiv (starRingEnd ℂ) (toConjₗ (V := V)).toAddEquiv
    (starRingAut (R := ℂ)).bijective fun c v ↦ toConjₗ.map_smulₛₗ c v).symm

/-- The conjugate of a complex vector space has the same complex dimension. -/
theorem finrank_eq : finrank ℂ (Conjugate V) = finrank ℂ V :=
  congrArg Cardinal.toNat rank_eq

end Conjugate

end TauCeti
