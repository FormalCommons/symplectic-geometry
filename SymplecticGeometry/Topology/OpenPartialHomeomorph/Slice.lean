/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.OpenPartialHomeomorph.Defs
import Mathlib.Topology.Constructions.SumProd

/-!
# Slices of an open partial homeomorphism that preserves a parameter

Let `e : T × X → T × Y` be an open partial homeomorphism that keeps the first coordinate, both
forwards on its source and backwards on its target, such as a chart for a family of functions
that does not move the parameter. For each value `t` of the parameter, its restriction
`x ↦ (e (t, x)).2` to the slice `{t} × X` is an open partial homeomorphism
`OpenPartialHomeomorph.slice e he he' t` of `X` onto `Y`, whose source and target are the slices
of those of `e` and whose inverse is `y ↦ (e.symm (t, y)).2`. This is the analogue for open
partial homeomorphisms of `Diffeomorph.slice`.

## Main definitions

* `OpenPartialHomeomorph.slice`: the slice at `t` of an open partial homeomorphism of `T × X`
  onto `T × Y` that preserves the first coordinate.
-/

public section

open Set

namespace OpenPartialHomeomorph

variable {T X Y : Type*} [TopologicalSpace T] [TopologicalSpace X] [TopologicalSpace Y]

section slice

variable (e : OpenPartialHomeomorph (T × X) (T × Y)) (he : ∀ z ∈ e.source, (e z).1 = z.1)
  (he' : ∀ z ∈ e.target, (e.symm z).1 = z.1)

/-- The slice at `t` of an open partial homeomorphism `e` of `T × X` onto `T × Y` that keeps the
first coordinate on its source, and whose inverse keeps it on its target: the open partial
homeomorphism of `X` onto `Y` that sends `x` to the second coordinate of `e (t, x)`, with
source `{x | (t, x) ∈ e.source}` and target `{y | (t, y) ∈ e.target}`. -/
def slice (t : T) : OpenPartialHomeomorph X Y where
  toFun x := (e (t, x)).2
  invFun y := (e.symm (t, y)).2
  source := Prod.mk t ⁻¹' e.source
  target := Prod.mk t ⁻¹' e.target
  map_source' x hx := by
    have hp : (t, (e (t, x)).2) = e (t, x) := Prod.ext (he _ hx).symm rfl
    rw [mem_preimage, hp]
    exact e.map_source hx
  map_target' y hy := by
    have hp : (t, (e.symm (t, y)).2) = e.symm (t, y) := Prod.ext (he' _ hy).symm rfl
    rw [mem_preimage, hp]
    exact e.map_target hy
  left_inv' x hx := by
    have hp : (t, (e (t, x)).2) = e (t, x) := Prod.ext (he _ hx).symm rfl
    rw [hp, e.left_inv hx]
  right_inv' y hy := by
    have hp : (t, (e.symm (t, y)).2) = e.symm (t, y) := Prod.ext (he' _ hy).symm rfl
    rw [hp, e.right_inv hy]
  open_source := e.open_source.preimage (.prodMk_right t)
  open_target := e.open_target.preimage (.prodMk_right t)
  continuousOn_toFun := continuous_snd.comp_continuousOn
    (e.continuousOn.comp (Continuous.prodMk_right t).continuousOn fun _ hx ↦ hx)
  continuousOn_invFun := continuous_snd.comp_continuousOn
    (e.continuousOn_symm.comp (Continuous.prodMk_right t).continuousOn fun _ hy ↦ hy)

@[simp]
theorem slice_apply (t : T) (x : X) : e.slice he he' t x = (e (t, x)).2 :=
  (rfl)

@[simp]
theorem symm_slice_apply (t : T) (y : Y) : (e.slice he he' t).symm y = (e.symm (t, y)).2 :=
  (rfl)

@[simp]
theorem slice_source (t : T) : (e.slice he he' t).source = Prod.mk t ⁻¹' e.source :=
  (rfl)

@[simp]
theorem slice_target (t : T) : (e.slice he he' t).target = Prod.mk t ⁻¹' e.target :=
  (rfl)

end slice

end OpenPartialHomeomorph

end
