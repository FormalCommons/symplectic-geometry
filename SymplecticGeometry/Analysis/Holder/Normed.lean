/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.Normed

/-!
# Hölder bounds on a subset from the Hölder space of the subset

A function that agrees on a set `s` with an element `f` of the bounded Hölder space of `s` is
Hölder on `s`, with constant the Hölder-space norm of `f`
(`TauCeti.HolderSpace.holderOnWith_of_apply_eq`).

These declarations are a part of Tau Ceti's file
`TauCeti/Analysis/Holder/Normed.lean`, on its main branch, as of the commit
`0fef288e2f0539135f050168f1153e762b0189a8` (Tau Ceti's pull request #40860), and are not yet in
the pinned release. They keep their Tau Ceti names, namespaces, statements and proofs unchanged,
so that moving Tau Ceti past them deletes this file without renames.
-/

public section

namespace TauCeti

open scoped NNReal

namespace HolderSpace

variable {α : ℝ≥0} {X : Type*} {Y : Type*} [MetricSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- A function equal on `s` to an element `f` of the Hölder space of `s` is `α`-Hölder on `s` with
constant the Hölder-space norm of `f`. This reads Hölder bounds on a subset off Hölder-space
elements on that subset. -/
theorem holderOnWith_of_apply_eq {s : Set X} {g : X → Y} (f : HolderSpace α s Y)
    (hf : ∀ x : s, f x = g x) : HolderOnWith ‖f‖₊ α g s := by
  rw [← HolderWith.restrict_iff]
  have he : s.domRestrict g = ⇑f := funext fun x ↦ (hf x).symm
  rw [he]
  exact f.holderWith_nnnorm

end HolderSpace

end TauCeti

end
