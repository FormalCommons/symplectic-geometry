/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.VectorBundle.Basic

/-!
# Restricting a linear trivialization to an open set

Mathlib's `Bundle.Trivialization.restrOpen` restricts a local trivialization `e` to the part of
its base set inside an open set `s`, with the same forward map. This file records that the
restriction is `R`-linear when `e` is (`Bundle.Trivialization.isLinear_restrOpen`). It lets a
trivialization be shrunk to an open set on which a change of frame, such as Tau Ceti's
`Bundle.Trivialization.transFiberwiseLinear`, is continuous.
-/

public section

open Bundle

namespace Bundle.Trivialization

variable {R B F : Type*} {E : B → Type*} [Semiring R] [TopologicalSpace B] [TopologicalSpace F]
  [AddCommMonoid F] [Module R F] [∀ b, AddCommMonoid (E b)] [∀ b, Module R (E b)]
  [TopologicalSpace (TotalSpace F E)]

/-- The restriction of an `R`-linear trivialization to an open set is `R`-linear. -/
instance isLinear_restrOpen (e : Trivialization F (π F E)) [e.IsLinear R] (s : Set B)
    (hs : IsOpen s) : (e.restrOpen s hs).IsLinear R where
  linear _ hb := e.linear R hb.1

end Bundle.Trivialization

end
