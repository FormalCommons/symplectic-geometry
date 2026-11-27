/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.FundamentalGroup.BasepointChange

/-!
# Change of base point for subgroups of the fundamental group

Tau Ceti's `FundamentalGroup.basepointChangeSubgroup γ H` moves a subgroup `H` of `π₁(X, x₀)` to
`π₁(X, x₁)` along a path `γ` from `x₀` to `x₁`, as its image under the change of base point
`FundamentalGroup.fundamentalGroupMulEquivOfPath γ`. This file states that description as a
rewrite rule, and that the change of base point carries the image of the map induced by a
continuous map `g` at `x₀` onto its image at `x₁`, along the image of `γ` under `g`: this is
Tau Ceti's `FundamentalGroup.map_fundamentalGroupMulEquivOfPath` for subgroups.

## Main results

* `FundamentalGroup.basepointChangeSubgroup_eq_map`: `basepointChangeSubgroup γ H` is the image of
  `H` under the change of base point along `γ`.
* `FundamentalGroup.basepointChangeSubgroup_map_range`: the change of base point along `g ∘ γ`
  carries the image of `g_* : π₁(X, x₀) → π₁(Y, g x₀)` onto that of
  `g_* : π₁(X, x₁) → π₁(Y, g x₁)`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Cambridge University Press, 2002, §1.1, change of base point.
-/

public section

namespace FundamentalGroup

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x₀ x₁ : X}

/-- The change of base point of a subgroup `H` of `π₁(X, x₀)` along a path `γ` is the image of `H`
under the change of base point isomorphism along `γ`. -/
theorem basepointChangeSubgroup_eq_map (γ : Path x₀ x₁) (H : Subgroup (FundamentalGroup X x₀)) :
    basepointChangeSubgroup γ H = H.map (fundamentalGroupMulEquivOfPath γ).toMonoidHom :=
  Subgroup.ext fun g ↦ (mem_basepointChangeSubgroup γ H g).trans (by simp [Subgroup.mem_map])

/-- For a continuous map `g : X → Y` and a path `γ` from `x₀` to `x₁`, the change of base point
along `g ∘ γ` carries the image of `π₁(X, x₀)` in `π₁(Y, g x₀)` onto the image of `π₁(X, x₁)` in
`π₁(Y, g x₁)`. -/
theorem basepointChangeSubgroup_map_range (g : C(X, Y)) (γ : Path x₀ x₁) :
    basepointChangeSubgroup (γ.map g.continuous) (map g x₀).range = (map g x₁).range := by
  have h : (fundamentalGroupMulEquivOfPath (γ.map g.continuous)).toMonoidHom.comp (map g x₀) =
      (map g x₁).comp (fundamentalGroupMulEquivOfPath γ).toMonoidHom :=
    MonoidHom.ext fun h ↦ (map_fundamentalGroupMulEquivOfPath g γ h).symm
  rw [basepointChangeSubgroup_eq_map, MonoidHom.map_range, h, MonoidHom.range_comp,
    MonoidHom.range_eq_top.2 (fundamentalGroupMulEquivOfPath γ).surjective, Subgroup.map_top]

end FundamentalGroup

end
