/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic

/-!
# Local diffeomorphisms at a point and their local inverses

A map `f` is a `C^n` local diffeomorphism at `x` when it agrees, on the source of some `C^n`
partial diffeomorphism containing `x`, with that partial diffeomorphism. Mathlib's
`IsLocalDiffeomorphAt` is defined this way, but its body is not exposed to other modules, which
only see the chosen local inverse `Λ = IsLocalDiffeomorphAt.localInverse`. This file shows that
`f` agrees with `Λ.symm` on the target of `Λ`, since `f ∘ Λ` is the identity on the source of
`Λ`. So `Λ.symm` is a partial diffeomorphism that `f` agrees with (the converse is Tau Ceti's
`TauCeti.isLocalDiffeomorphAt_of_eqOn`), and `f` is a local diffeomorphism at every point of the
target of `Λ`, not only at `x`.

## Main results

* `IsLocalDiffeomorphAt.eqOn_localInverse_symm`: `f` agrees with the inverse of its local inverse
  on the target of the local inverse.
* `IsLocalDiffeomorphAt.exists_partialDiffeomorph`: a local diffeomorphism at `x` agrees with a
  partial diffeomorphism on a source that contains `x`.
* `IsLocalDiffeomorphAt.isLocalDiffeomorphOn_localInverse_target`: a local diffeomorphism `f` at
  `x` is a local diffeomorphism on the target of `hf.localInverse`.
-/

public section

open Set

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {J : ModelWithCorners 𝕜 E' H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {n : WithTop ℕ∞} {f : M → N} {x : M}

namespace IsLocalDiffeomorphAt

/-- A local diffeomorphism `f` at `x` agrees with the inverse of its local inverse
`hf.localInverse` on the target of `hf.localInverse`. -/
theorem eqOn_localInverse_symm (hf : IsLocalDiffeomorphAt I J n f x) :
    EqOn f hf.localInverse.symm hf.localInverse.target :=
  eqOn_of_leftInvOn_of_rightInvOn hf.localInverse_eqOn_right
    hf.localInverse.toPartialEquiv.rightInvOn hf.localInverse.toPartialEquiv.mapsTo_symm

/-- A `C^n` local diffeomorphism `f` at `x` agrees with some `C^n` partial diffeomorphism on
its source, and that source contains `x`. It is the inverse of
`IsLocalDiffeomorphAt.localInverse`. -/
theorem exists_partialDiffeomorph (hf : IsLocalDiffeomorphAt I J n f x) :
    ∃ Φ : PartialDiffeomorph I J M N n, x ∈ Φ.source ∧ EqOn f Φ Φ.source :=
  ⟨hf.localInverse.symm, by simpa using hf.localInverse_mem_target, by
    simpa using hf.eqOn_localInverse_symm⟩

/-- A local diffeomorphism `f` at `x` is a local diffeomorphism at every point of the target of
its local inverse. -/
theorem isLocalDiffeomorphOn_localInverse_target (hf : IsLocalDiffeomorphAt I J n f x) :
    IsLocalDiffeomorphOn I J n f hf.localInverse.target := fun z ↦
  TauCeti.isLocalDiffeomorphAt_of_eqOn (Φ := hf.localInverse.symm) (by simp)
    (by simpa using hf.eqOn_localInverse_symm)

end IsLocalDiffeomorphAt

end
