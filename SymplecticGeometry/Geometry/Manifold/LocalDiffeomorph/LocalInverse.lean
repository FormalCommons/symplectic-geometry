/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic

/-!
# A local diffeomorphism on the target of its local inverse

Mathlib's `IsLocalDiffeomorphAt.localInverse` is a partial diffeomorphism `Λ` defined near `f x`
for a local diffeomorphism `f` at `x`. On the target of `Λ`, the map `f` agrees with `Λ.symm`,
since `f ∘ Λ` is the identity on the source of `Λ`. Hence `f` is a local diffeomorphism at every
point of that target, not only at `x`.

## Main results

* `IsLocalDiffeomorphAt.isLocalDiffeomorphOn_localInverse_target`: a local diffeomorphism `f` at
  `x` is a local diffeomorphism on the target of `hf.localInverse`.
-/

public section

open Set

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners 𝕜 E H}
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] {I' : ModelWithCorners 𝕜 E' H'}
  {n : WithTop ℕ∞} {f : M → M'} {x : M}

namespace IsLocalDiffeomorphAt

/-- A local diffeomorphism `f` at `x` is a local diffeomorphism at every point of the target of
its local inverse. -/
theorem isLocalDiffeomorphOn_localInverse_target (hf : IsLocalDiffeomorphAt I I' n f x) :
    IsLocalDiffeomorphOn I I' n f hf.localInverse.target := fun z ↦ by
  -- `f` agrees with the inverse of `Λ` on the target of `Λ`, since `f ∘ Λ = id` on its source.
  refine TauCeti.isLocalDiffeomorphAt_of_eqOn (Φ := hf.localInverse.symm)
    (by simp) fun x' hx' ↦ ?_
  have hx'' : x' ∈ hf.localInverse.target := by simpa using hx'
  have h := hf.localInverse_right_inv (hf.localInverse.map_target hx'')
  rw [hf.localInverse.right_inv hx''] at h
  simpa using h

end IsLocalDiffeomorphAt

end
