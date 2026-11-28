/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Tactic.Group

/-!
# Products of two subgroups of a topological group

For subgroups `P` and `Q` of a topological group, the set `P * Q` is open as soon as it is a
neighbourhood of `1`, and an open `P * Q` is closed when `Q` is compact. These are analogues for
two subgroups of Mathlib's `Subgroup.isOpen_of_mem_nhds` and `OpenSubgroup.isClosed`.

## Main results

* `Subgroup.isOpen_mul_of_mem_nhds_one`: if `P * Q ∈ 𝓝 1`, then `P * Q` is open.
* `Subgroup.isClosed_mul_of_isOpen_of_isCompact`: if `P * Q` is open and `Q` is compact, then
  `P * Q` is closed, since it equals `closure P * Q` (by Mathlib's
  `closure_subset_mul_right_of_mem_nhds_one`), which is closed by
  `IsClosed.mul_right_of_isCompact`.
-/

public section

open Topology
open scoped Pointwise

namespace Subgroup

variable {K : Type*} [TopologicalSpace K] [Group K]

/-- If the products `p * q` of two subgroups `P` and `Q` form a neighbourhood of `1`, they form
an open set. -/
@[to_additive /-- If the sums `p + q` of two additive subgroups `P` and `Q` form a neighbourhood
of `0`, they form an open set. -/]
theorem isOpen_mul_of_mem_nhds_one [SeparatelyContinuousMul K] (P Q : Subgroup K)
    (h : (P : Set K) * (Q : Set K) ∈ 𝓝 1) : IsOpen ((P : Set K) * (Q : Set K)) := by
  refine isOpen_iff_mem_nhds.2 ?_
  rintro _ ⟨p, hp, q, hq, rfl⟩
  have hc : Continuous fun x : K ↦ p⁻¹ * x * q⁻¹ := (continuous_const_mul p⁻¹).mul_const q⁻¹
  have h1 : p⁻¹ * (p * q) * q⁻¹ = 1 := by group
  refine Filter.mem_of_superset (hc.continuousAt.preimage_mem_nhds (h1 ▸ h)) ?_
  rintro x ⟨p', hp', q', hq', hx⟩
  refine ⟨p * p', mul_mem hp hp', q' * q, mul_mem hq' hq, ?_⟩
  simp only at hx ⊢
  rw [show x = p * (p⁻¹ * x * q⁻¹) * q by group, ← hx]
  group

/-- If the products `p * q` of two subgroups `P` and `Q` form an open set and `Q` is compact,
they form a closed set. -/
@[to_additive /-- If the sums `p + q` of two additive subgroups `P` and `Q` form an open set and
`Q` is compact, they form a closed set. -/]
theorem isClosed_mul_of_isOpen_of_isCompact [IsTopologicalGroup K] (P Q : Subgroup K)
    (hQ : IsCompact (Q : Set K)) (h : IsOpen ((P : Set K) * (Q : Set K))) :
    IsClosed ((P : Set K) * (Q : Set K)) := by
  have hV : (P : Set K) * (Q : Set K) ∈ 𝓝 1 :=
    h.mem_nhds ⟨1, one_mem P, 1, one_mem Q, one_mul 1⟩
  have hsub : _root_.closure (P : Set K) * (Q : Set K) ⊆ (P : Set K) * (Q : Set K) := by
    rintro _ ⟨k, hk, q, hq, rfl⟩
    obtain ⟨p, hp, _, ⟨p', hp', q', hq', rfl⟩, rfl⟩ :=
      closure_subset_mul_right_of_mem_nhds_one _ hV hk
    exact ⟨p * p', mul_mem hp hp', q' * q, mul_mem hq' hq, by group⟩
  rw [← hsub.antisymm (Set.mul_subset_mul_right _root_.subset_closure)]
  exact isClosed_closure.mul_right_of_isCompact hQ

end Subgroup
