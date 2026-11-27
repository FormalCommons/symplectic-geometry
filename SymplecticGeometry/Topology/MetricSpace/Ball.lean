/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

import Mathlib.Logic.Equiv.Set
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Bijections preserving a ball and fixing its sphere

A bijection of a pseudometric space that maps an open ball onto itself and fixes the sphere of
the same centre and radius pointwise maps the closed ball onto itself, since the closed ball is
the union of the open ball and the sphere (`Metric.ball_union_sphere`).

## Main results

* `Equiv.image_closedBall_eq_of_eqOn_sphere`: the closed ball is mapped onto itself.
-/

public section

open Set Metric

/-- A bijection of a pseudometric space that maps the open ball `ball a r` onto itself
(`σ x ∈ ball a r ↔ x ∈ ball a r`) and fixes the sphere `sphere a r` pointwise maps the closed
ball `closedBall a r` onto itself. -/
theorem Equiv.image_closedBall_eq_of_eqOn_sphere {X : Type*} [PseudoMetricSpace X]
    (σ : X ≃ X) {a : X} {r : ℝ} (hball : ∀ x, σ x ∈ ball a r ↔ x ∈ ball a r)
    (hsphere : EqOn σ id (sphere a r)) : σ '' closedBall a r = closedBall a r := by
  have hb : σ '' ball a r = ball a r := by
    rw [σ.image_eq_preimage_symm]
    ext y
    simpa using (hball (σ.symm y)).symm
  rw [← ball_union_sphere, image_union, hb, hsphere.image_eq_self]

end
