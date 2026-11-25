/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialComplex.Basic

/-!
# Abstract simplicial complexes

Supplementary API for Mathlib's abstract simplicial complexes.

## Main results

* `PreAbstractSimplicialComplex.mem_addSingletons`: the faces of
  `PreAbstractSimplicialComplex.addSingletons ι K` are the faces of `K` and the singletons.
-/

public section

namespace PreAbstractSimplicialComplex

variable {ι : Type*}

/-- A finite set is a face of `addSingletons ι K` exactly when it is a face of `K` or a
singleton. -/
@[simp]
theorem mem_addSingletons (K : PreAbstractSimplicialComplex ι) {t : Finset ι} :
    t ∈ addSingletons ι K ↔ t ∈ K ∨ ∃ v, t = {v} :=
  Iff.rfl

end PreAbstractSimplicialComplex

end
