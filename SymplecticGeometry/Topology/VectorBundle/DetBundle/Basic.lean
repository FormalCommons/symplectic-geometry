/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.VectorBundle.Determinant

/-!
# Continuity of scalar multiplication on the determinant line

Tau Ceti gives each fibre of its determinant line `TauCeti.DetBundle 𝕜' G E` the module topology
over `𝕜'`, so scalar multiplication by `𝕜'` is continuous. This file adds the instance that
scalar multiplication by any `𝕜` acting continuously on `𝕜'` is continuous too, for any action
of `𝕜` on the fibres that forms a scalar tower with `𝕜` acting on `𝕜'`, such as `𝕜 = ℝ≥0`.
The main case is `𝕜 = ℝ` and `𝕜' = ℂ`: the determinant line of a complex vector bundle, read as
a real vector bundle, then has the continuous real scalar multiplication that real metrics on it
ask for.

## Main results

* `TauCeti.DetBundle.continuousSMul`: scalar multiplication by `𝕜` on a fibre of the determinant
  line is continuous.
-/

public section

namespace TauCeti.DetBundle

variable {𝕜 𝕜' : Type*} [TopologicalSpace 𝕜] [NontriviallyNormedField 𝕜'] [SMul 𝕜 𝕜']
  [ContinuousSMul 𝕜 𝕜'] {B G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜' G]
  {E : B → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜' (E x)]

/-- On a fibre of the determinant line over `𝕜'`, scalar multiplication by `𝕜` is continuous,
for any action of `𝕜` on the fibre that forms a scalar tower with a continuous action of `𝕜`
on `𝕜'`. -/
instance continuousSMul (x : B) [SMul 𝕜 (DetBundle 𝕜' G E x)]
    [IsScalarTower 𝕜 𝕜' (DetBundle 𝕜' G E x)] : ContinuousSMul 𝕜 (DetBundle 𝕜' G E x) :=
  IsScalarTower.continuousSMul 𝕜'

end TauCeti.DetBundle

end
