/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Thickenings of products

For the sup edistance on a product of two pseudo-emetric spaces, the open `r`-thickening of a
product set is the product of the open `r`-thickenings of its factors.

## Main results

* `Metric.thickening_prod`: `thickening r (s ×ˢ t) = thickening r s ×ˢ thickening r t`.
-/

public section

namespace Metric

variable {X Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y]

/-- The open `r`-thickening of a product set, for the sup edistance on a product of
pseudo-emetric spaces, is the product of the open `r`-thickenings of its factors. -/
theorem thickening_prod (r : ℝ) (s : Set X) (t : Set Y) :
    thickening r (s ×ˢ t) = thickening r s ×ˢ thickening r t := by
  ext x
  simp [mem_thickening_iff_infEDist_lt, Set.mem_prod, infEDist_prod]

end Metric

end
