/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giada Franz, The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Riemannian.Basic

/-!
# Open balls of the Riemannian distance

This file is a part of Tau Ceti's `TauCeti/Geometry/Manifold/Riemannian/Distance.lean`, copied
from Tau Ceti's main branch at commit `07c8b6b1f5ff5bdab8363e207e59d68eccc82bef`, which the
pinned version of Tau Ceti does not have yet. It contains one declaration of that file,
`TauCeti.Manifold.isOpen_setOfPred_riemannianEDist_lt`: open Riemannian balls are open. The
pinned version has only its special case `r = ⊤`,
`TauCeti.Manifold.isOpen_setOfPred_riemannianEDist_lt_top`.

Changes from Tau Ceti's file: only this declaration is taken, with the `variable` lines it needs
and the one import it uses; this module docstring replaces Tau Ceti's; the declaration, its
docstring and its proof are unchanged.

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 7 §2, Def. 2.4.
* `Mathlib/Geometry/Manifold/Riemannian/Basic.lean` (S. Gouëzel):
  `PseudoEMetricSpace.ofRiemannianMetric`, `EMetricSpace.ofRiemannianMetric`, and their
  `IsRiemannianManifold` instances, which the (pseudo)metric constructions here adapt.
-/

public section

open Bundle Manifold Set
open scoped ENNReal Manifold NNReal Topology

noncomputable section

namespace TauCeti

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

namespace Manifold

section Finiteness

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

variable [IsManifold I 1 M] [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

variable (I) in
/-- Open Riemannian balls are open: any point close enough to a point `y` at Riemannian distance
less than `r` from `x` is again at distance less than `r` from `x`, by the triangle inequality. In
particular, with `r = ⊤`, the set of points at finite Riemannian distance from `x` is open. -/
theorem isOpen_setOfPred_riemannianEDist_lt (x : M) (r : ℝ≥0∞) :
    IsOpen {y | riemannianEDist I x y < r} := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  obtain ⟨δ, hδ, hδr⟩ := ENNReal.lt_iff_exists_add_pos_lt.1 hy
  filter_upwards [eventually_riemannianEDist_lt I y (ENNReal.coe_pos.2 hδ)] with z hz
  exact (riemannianEDist_triangle (y := y)).trans_lt
    ((ENNReal.add_lt_add_left (ne_top_of_lt hy) hz).trans hδr)

end Finiteness

end Manifold

end TauCeti
