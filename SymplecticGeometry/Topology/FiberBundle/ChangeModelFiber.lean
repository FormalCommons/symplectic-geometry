/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.FiberBundle.Basic
public import TauCeti.Topology.FiberBundle.MapFiber

/-!
# Trivializations read through homeomorphisms

API for Mathlib's operations that read a trivialization through a homeomorphism of its model fibre
or of its total space. Tau Ceti's change of model fibre of a fibre bundle
(`Bundle.Trivialization.transModelFiber`, `FiberBundle.ofModelFiberHomeomorph`, in
`TauCeti.Topology.FiberBundle.ModelFiber`) is built from these operations.

## Main definitions and results

* `Bundle.Trivialization.transFiberHomeomorph_baseSet`, `_source`, `_target`, `_symm_apply`: the
  base set, source, target and inverse of Mathlib's `Bundle.Trivialization.transFiberHomeomorph`,
  which composes a trivialization with a homeomorphism of the model fibre.
* `Bundle.Trivialization.mapFiberHomeomorph`: the fibre `TauCeti.MapFiber proj b` over a point `b`
  of the base set of a trivialization, identified with the model fibre.
* `Bundle.Trivialization.compHomeomorph_apply`, `_baseSet`, `_source`, `_target`, `_symm_apply`:
  the map, base set, source, target and inverse of Mathlib's
  `Bundle.Trivialization.compHomeomorph`, which precomposes a trivialization with a homeomorphism
  of the total space.
-/

public section

open Bundle

namespace Bundle.Trivialization

section transFiberHomeomorph

variable {B F F' Z : Type*} [TopologicalSpace B] [TopologicalSpace F] [TopologicalSpace F']
  [TopologicalSpace Z] {proj : Z → B} (e : Trivialization F proj) (h : F ≃ₜ F')

@[simp]
theorem transFiberHomeomorph_baseSet : (e.transFiberHomeomorph h).baseSet = e.baseSet :=
  (rfl)

@[simp]
theorem transFiberHomeomorph_source : (e.transFiberHomeomorph h).source = e.source :=
  (rfl)

@[simp]
theorem transFiberHomeomorph_target :
    (e.transFiberHomeomorph h).target = e.baseSet ×ˢ Set.univ := by
  rw [target_eq, transFiberHomeomorph_baseSet]

/-- The inverse of `e.transFiberHomeomorph h` sends `q` to the image of `(q.1, h.symm q.2)`
under the inverse of `e`. -/
@[simp]
theorem transFiberHomeomorph_symm_apply (q : B × F') :
    (e.transFiberHomeomorph h).toOpenPartialHomeomorph.symm q =
      e.toOpenPartialHomeomorph.symm (q.1, h.symm q.2) :=
  (rfl)

end transFiberHomeomorph

section mapFiberHomeomorph

variable {B F Z : Type*} [TopologicalSpace B] [TopologicalSpace F] [TopologicalSpace Z]
  {proj : Z → B} (e : Trivialization F proj) {b : B} (hb : b ∈ e.baseSet)

/-- The fibre `TauCeti.MapFiber proj b` of `proj` over a point `b` of the base set of a
trivialization `e` is homeomorphic to the model fibre `F`, by the fibre coordinate of `e`. This is
Mathlib's `Bundle.Trivialization.preimageSingletonHomeomorph`, read on `TauCeti.MapFiber proj b`
rather than on the subtype `proj ⁻¹' {b}`. -/
def mapFiberHomeomorph : TauCeti.MapFiber proj b ≃ₜ F :=
  ((Homeomorph.refl Z).subtype fun _ ↦ Set.mem_singleton_iff.symm).trans
    (e.preimageSingletonHomeomorph hb)

@[simp]
theorem mapFiberHomeomorph_apply (x : TauCeti.MapFiber proj b) :
    e.mapFiberHomeomorph hb x = (e x).2 :=
  (rfl)

@[simp]
theorem mapFiberHomeomorph_symm_apply (v : F) :
    (e.mapFiberHomeomorph hb).symm v =
      ⟨e.toOpenPartialHomeomorph.symm (b, v), e.proj_symm_apply' hb⟩ :=
  (rfl)

end mapFiberHomeomorph

section compHomeomorph

variable {B F Z Z' : Type*} [TopologicalSpace B] [TopologicalSpace F] [TopologicalSpace Z]
  [TopologicalSpace Z'] {proj : Z → B} (e : Trivialization F proj) (h : Z' ≃ₜ Z)

@[simp]
theorem compHomeomorph_apply (x : Z') : e.compHomeomorph h x = e (h x) :=
  (rfl)

@[simp]
theorem compHomeomorph_baseSet : (e.compHomeomorph h).baseSet = e.baseSet :=
  (rfl)

@[simp]
theorem compHomeomorph_source : (e.compHomeomorph h).source = h ⁻¹' e.source :=
  (rfl)

@[simp]
theorem compHomeomorph_target : (e.compHomeomorph h).target = e.target :=
  (rfl)

/-- The inverse of `e.compHomeomorph h` sends `x` to the image under `h.symm` of the image of `x`
under the inverse of `e`. -/
@[simp]
theorem compHomeomorph_symm_apply (x : B × F) :
    (e.compHomeomorph h).toOpenPartialHomeomorph.symm x =
      h.symm (e.toOpenPartialHomeomorph.symm x) :=
  (rfl)

end compHomeomorph

end Bundle.Trivialization

end
