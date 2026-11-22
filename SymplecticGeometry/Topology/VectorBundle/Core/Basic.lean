/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.VectorBundle.Basic

/-!
# Extensionality of vector-bundle cores

`VectorBundleCore.ext`: a vector-bundle core is determined by its chart domains, its preferred
charts and its transitions, since the remaining fields are propositions.
-/

public section

/-- A vector-bundle core is determined by its chart domains, its preferred charts and its
transitions. -/
theorem VectorBundleCore.ext {R B F ι : Type*} [NontriviallyNormedField R] [TopologicalSpace B]
    [NormedAddCommGroup F] [NormedSpace R F] {Z Z' : VectorBundleCore R B F ι}
    (hbase : Z.baseSet = Z'.baseSet) (hindex : Z.indexAt = Z'.indexAt)
    (hcoord : Z.coordChange = Z'.coordChange) : Z = Z' := by
  cases Z; cases Z'
  simp only at hbase hindex hcoord
  subst hbase hindex hcoord
  rfl
