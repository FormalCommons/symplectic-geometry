/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance
public import TauCeti.Topology.Homotopy.Extension.NDRPair
import TauCeti.Topology.Compactness.Compact

/-!
# Singular homology near the subset of an NDR pair

Let `N` be NDR data for a subset `Q` of a space `X` (`TauCeti.NDRPair`), and let `U ⊇ Q` be
open. This file shows that `Q` has an open neighbourhood `V ⊆ U` whose singular homology, pushed
into `U`, comes from `Q` in every degree. The neighbourhood is the set of points where the control
function of `N` is below `1` and whose whole track under the deformation of `N` stays in `U`. It
is open by the tube lemma, as `unitInterval` is compact. On `V` the deformation is a homotopy, in
`U`, from the inclusion of `V` to a map that factors through `Q`, so homotopy invariance of
singular homology (`ContinuousMap.singularHomologyMap_eq_of_homotopic`) gives the claim. No
compactness of `Q` is needed.

## Main results

* `TauCeti.NDRPair.exists_isOpen_range_singularHomologyMap_le`: an open `V` with `Q ⊆ V ⊆ U`
  such that the image of `Hₖ(V; ℤ)` in `Hₖ(U; ℤ)` lies in the image of `Hₖ(Q; ℤ)`, for all `k`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], third
  edition, Theorem 3.3.2, whose proof uses this step.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 2.1 (homotopy
  invariance of singular homology).
-/

public section

open Set unitInterval

namespace TauCeti.NDRPair

variable {X : Type} [TopologicalSpace X] {Q U : Set X}

/-- **Singular homology near the subset of an NDR pair.** For NDR data on `Q` and an open
`U ⊇ Q`, there is an open `V` with `Q ⊆ V ⊆ U` such that in every degree, the image of the
singular homology of `V` in that of `U` lies in the image of the singular homology of `Q`. -/
theorem exists_isOpen_range_singularHomologyMap_le (N : NDRPair Q) (hU : IsOpen U)
    (hQU : Q ⊆ U) :
    ∃ V : Set X, IsOpen V ∧ ∃ (hQV : Q ⊆ V) (hVU : V ⊆ U), ∀ k : ℕ,
      LinearMap.range (ContinuousMap.singularHomologyMap ℤ k (ContinuousMap.inclusion hVU)) ≤
        LinearMap.range
          (ContinuousMap.singularHomologyMap ℤ k (ContinuousMap.inclusion (hQV.trans hVU))) := by
  set V := {x | N.control x < 1} ∩ {x | ∀ t, N.deformation (t, x) ∈ U}
  -- The tube lemma, as `unitInterval` is compact.
  have htrack : IsOpen {x | ∀ t, N.deformation (t, x) ∈ U} :=
    isOpen_forall_prodMk_mem continuous_id (hU.preimage (N.deformation.continuous.comp
      continuous_swap))
  have hV : IsOpen V := (isOpen_lt N.control.continuous continuous_const).inter htrack
  have hQV : Q ⊆ V := fun q hq ↦
    ⟨by simp [(N.control_eq_zero_iff q).2 hq], fun t ↦ by
      rw [N.deformation_of_mem t hq]; exact hQU hq⟩
  have hVU : V ⊆ U := fun x hx ↦ by simpa using hx.2 0
  -- The deformation at time `1` retracts `V` into `Q`.
  let r : C(V, Q) :=
    ⟨fun x ↦ ⟨N.deformation (1, x), N.deformation_one_mem x.property.1⟩, by fun_prop⟩
  -- The deformation, restricted to `V`, is a homotopy in `U` from the inclusion to `r`.
  let F : (ContinuousMap.inclusion hVU).Homotopy
      ((ContinuousMap.inclusion (hQV.trans hVU)).comp r) :=
    { toFun := fun p ↦ ⟨N.deformation (p.1, p.2), p.2.property.2 p.1⟩
      continuous_toFun := by fun_prop
      map_zero_left := fun x ↦ Subtype.ext (N.deformation_zero x)
      map_one_left := fun x ↦ Subtype.ext (by simp [r]) }
  refine ⟨V, hV, hQV, hVU, fun k ↦ ?_⟩
  rw [ContinuousMap.singularHomologyMap_eq_of_homotopic ℤ k ⟨F⟩,
    ContinuousMap.singularHomologyMap_comp']
  exact LinearMap.range_comp_le_range _ _

end TauCeti.NDRPair
