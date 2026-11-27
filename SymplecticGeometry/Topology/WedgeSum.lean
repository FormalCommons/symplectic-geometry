/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.WedgeSum

/-!
# Compactness of a wedge sum

A wedge sum `TauCeti.WedgeSum x` of finitely many compact spaces is compact: it is a quotient of
the compact space `Unit ⊕ Σ i, X i` (`TauCeti.WedgeSum.isQuotientMap_sumElim`).
-/

public section

namespace TauCeti.WedgeSum

variable {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)] {x : ∀ i, X i}

/-- A wedge sum of finitely many compact spaces is compact. -/
instance compactSpace [Finite ι] [∀ i, CompactSpace (X i)] : CompactSpace (WedgeSum x) :=
  isQuotientMap_sumElim.surjective.compactSpace isQuotientMap_sumElim.continuous

end TauCeti.WedgeSum

end
