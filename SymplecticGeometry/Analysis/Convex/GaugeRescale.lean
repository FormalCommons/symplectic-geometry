/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Convex.GaugeRescale
public import Mathlib.Analysis.Normed.Module.Ball.Homeomorph

/-!
# Bounded open convex sets are homeomorphic to the ambient space

A nonempty bounded open convex set `s` of a real normed space `E` is homeomorphic to `E`: Mathlib's
gauge rescaling (`exists_homeomorph_image_interior_closure_frontier_eq_unitBall`) carries `s` onto
the open unit ball by a homeomorphism of `E`, and the open unit ball is homeomorphic to `E`
(`Homeomorph.unitBall`).

## Main results

* `Convex.nonempty_homeomorph_of_isOpen_of_isBounded`: `s ≃ₜ E` for a nonempty bounded open convex
  set `s`.
-/

public section

open Bornology Metric Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A nonempty bounded open convex set of a real normed space is homeomorphic to the space. -/
theorem Convex.nonempty_homeomorph_of_isOpen_of_isBounded {s : Set E} (hc : Convex ℝ s)
    (ho : IsOpen s) (hne : s.Nonempty) (hb : IsBounded s) : Nonempty (s ≃ₜ E) := by
  obtain ⟨e, he, -, -⟩ := exists_homeomorph_image_interior_closure_frontier_eq_unitBall hc
    (by rwa [ho.interior_eq]) hb
  rw [ho.interior_eq] at he
  exact ⟨(e.image s).trans ((Homeomorph.setCongr he).trans Homeomorph.unitBall.symm)⟩

end
