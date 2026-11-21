/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Local diffeomorphisms at a point as partial diffeomorphisms

A map `f` is a `C^n` local diffeomorphism at `x` when it agrees, on the source of some `C^n`
partial diffeomorphism containing `x`, with that partial diffeomorphism. Mathlib's
`IsLocalDiffeomorphAt` is defined this way, but its body is not exposed to other modules, which
only see the chosen local inverse `IsLocalDiffeomorphAt.localInverse`. This file recovers the
partial diffeomorphism from it; the converse is Tau Ceti's `TauCeti.isLocalDiffeomorphAt_of_eqOn`.

## Main results

* `IsLocalDiffeomorphAt.exists_partialDiffeomorph`: a local diffeomorphism at `x` agrees with a
  partial diffeomorphism on a source that contains `x`.
-/

public section

open Set

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {J : ModelWithCorners 𝕜 E' H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {n : WithTop ℕ∞} {f : M → N} {x : M}

/-- A `C^n` local diffeomorphism `f` at `x` agrees with some `C^n` partial diffeomorphism on
its source, and that source contains `x`. It is the inverse of
`IsLocalDiffeomorphAt.localInverse`. -/
theorem IsLocalDiffeomorphAt.exists_partialDiffeomorph (hf : IsLocalDiffeomorphAt I J n f x) :
    ∃ Φ : PartialDiffeomorph I J M N n, x ∈ Φ.source ∧ EqOn f Φ Φ.source := by
  refine ⟨hf.localInverse.symm, hf.localInverse_mem_target, fun z hz ↦ ?_⟩
  rw [PartialDiffeomorph.symm_toPartialEquiv, PartialEquiv.symm_source] at hz
  calc f z = f (hf.localInverse (hf.localInverse.toPartialEquiv.symm z)) := by
        rw [hf.localInverse.toPartialEquiv.right_inv hz]
    -- `PartialDiffeomorph` coerces to functions through `toFun` of its `PartialEquiv`, and has no
    -- lemma for the coercion of `symm`, so the last step is by definition.
    _ = _ := hf.localInverse_right_inv (hf.localInverse.toPartialEquiv.map_target hz)

end
