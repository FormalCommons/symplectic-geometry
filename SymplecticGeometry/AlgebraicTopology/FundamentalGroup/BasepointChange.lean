/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.FundamentalGroup.BasepointChange
import TauCeti.AlgebraicTopology.FundamentalGroup.Basic

/-!
# Change of base point for subgroups of the fundamental group

Tau Ceti's `FundamentalGroup.basepointChangeSubgroup γ H` moves a subgroup `H` of `π₁(X, x₀)` to
`π₁(X, x₁)` along a path `γ` from `x₀` to `x₁`, as its image under the change of base point
`FundamentalGroup.fundamentalGroupMulEquivOfPath γ`. This file states that description as a
rewrite rule, and that the change of base point along a concatenation is the change along one path
and then the other. Along the image of `γ` under a continuous map `g`, it commutes with `g_*`:
this is Tau Ceti's `FundamentalGroup.map_fundamentalGroupMulEquivOfPath` for subgroups, and it
carries the image of `g_*` at `x₀` onto its image at `x₁`.

Two paths from `x₀` to `x₁` differ by a loop at `x₁`, and the change of base point along a loop
is conjugation by its class (Tau Ceti's `FundamentalGroup.fundamentalGroupMulEquivOfPath_eq_conj`).
So the normal closure of a subgroup moved along a path does not depend on the path. This lets one
compare the normal closures of the images of `π₁` under maps that factor through a common space,
with no care for the paths that move them to a common base point.

## Main results

* `FundamentalGroup.basepointChangeSubgroup_eq_map`: `basepointChangeSubgroup γ H` is the image of
  `H` under the change of base point along `γ`.
* `FundamentalGroup.basepointChangeSubgroup_trans`: the change of base point along `γ.trans η`.
* `FundamentalGroup.basepointChangeSubgroup_map`: the change of base point along `g ∘ γ` of
  `g_* H` is `g_*` of the change of base point of `H` along `γ`.
* `FundamentalGroup.basepointChangeSubgroup_map_range`: the change of base point along `g ∘ γ`
  carries the image of `g_* : π₁(X, x₀) → π₁(Y, g x₀)` onto that of
  `g_* : π₁(X, x₁) → π₁(Y, g x₁)`.
* `FundamentalGroup.normalClosure_basepointChangeSubgroup_eq`: the normal closure of a moved
  subgroup does not depend on the path.
* `FundamentalGroup.normalClosure_basepointChangeSubgroup_range_eq_of_eq_comp`: for `k = g ∘ f`,
  the normal closure of the image of `k_*` moved along any path is that of the image under `g_*`
  of the image of `f_*` moved along any path.

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

/-- Changing the base point along `γ` and then along `η` is changing it along `γ.trans η`. -/
theorem basepointChangeSubgroup_trans {x₂ : X} (γ : Path x₀ x₁) (η : Path x₁ x₂)
    (H : Subgroup (FundamentalGroup X x₀)) :
    basepointChangeSubgroup (γ.trans η) H =
      basepointChangeSubgroup η (basepointChangeSubgroup γ H) := by
  ext g
  rw [mem_basepointChangeSubgroup_iff, mem_basepointChangeSubgroup_iff,
    mem_basepointChangeSubgroup_iff, fundamentalGroupMulEquivOfPath_trans,
    MulEquiv.symm_trans_apply]

/-- For a continuous map `g : X → Y`, a path `γ` from `x₀` to `x₁` and `H ≤ π₁(X, x₀)`, the
change of base point along `g ∘ γ` carries `g_* H` to the image under `g_*` of `H` moved along
`γ`. -/
theorem basepointChangeSubgroup_map (g : C(X, Y)) (γ : Path x₀ x₁)
    (H : Subgroup (FundamentalGroup X x₀)) :
    basepointChangeSubgroup (γ.map g.continuous) (H.map (map g x₀)) =
      (basepointChangeSubgroup γ H).map (map g x₁) := by
  have h : (fundamentalGroupMulEquivOfPath (γ.map g.continuous)).toMonoidHom.comp (map g x₀) =
      (map g x₁).comp (fundamentalGroupMulEquivOfPath γ).toMonoidHom :=
    MonoidHom.ext fun h ↦ (map_fundamentalGroupMulEquivOfPath g γ h).symm
  rw [basepointChangeSubgroup_eq_map, basepointChangeSubgroup_eq_map, Subgroup.map_map, h,
    ← Subgroup.map_map]

/-- For a continuous map `g : X → Y` and a path `γ` from `x₀` to `x₁`, the change of base point
along `g ∘ γ` carries the image of `π₁(X, x₀)` in `π₁(Y, g x₀)` onto the image of `π₁(X, x₁)` in
`π₁(Y, g x₁)`. -/
theorem basepointChangeSubgroup_map_range (g : C(X, Y)) (γ : Path x₀ x₁) :
    basepointChangeSubgroup (γ.map g.continuous) (map g x₀).range = (map g x₁).range := by
  rw [MonoidHom.range_eq_map, basepointChangeSubgroup_map, basepointChangeSubgroup_eq_map,
    Subgroup.map_top_of_surjective _ (fundamentalGroupMulEquivOfPath γ).surjective,
    ← MonoidHom.range_eq_map]

/-- The normal closure of a subgroup of `π₁(X, x₀)` moved to `x₁` along a path does not depend
on the path. -/
theorem normalClosure_basepointChangeSubgroup_eq (γ η : Path x₀ x₁)
    (H : Subgroup (FundamentalGroup X x₀)) :
    Subgroup.normalClosure (basepointChangeSubgroup γ H : Set (FundamentalGroup X x₁)) =
      Subgroup.normalClosure (basepointChangeSubgroup η H) := by
  -- moving along `η` is moving along `γ` and then along the loop `γ⁻¹ η` at `x₁`, which is
  -- conjugation by the class of that loop
  suffices key : ∀ γ η : Path x₀ x₁, Subgroup.normalClosure (basepointChangeSubgroup η H :
      Set (FundamentalGroup X x₁)) ≤ Subgroup.normalClosure (basepointChangeSubgroup γ H) from
    le_antisymm (key η γ) (key γ η)
  intro γ η
  have hη : basepointChangeSubgroup η H =
      basepointChangeSubgroup (γ.symm.trans η) (basepointChangeSubgroup γ H) := by
    ext g
    rw [mem_basepointChangeSubgroup_iff, mem_basepointChangeSubgroup_iff,
      mem_basepointChangeSubgroup_iff, fundamentalGroupMulEquivOfPath_trans,
      fundamentalGroupMulEquivOfPath_symm, MulEquiv.symm_trans_apply, MulEquiv.symm_symm,
      MulEquiv.symm_apply_apply]
  refine Subgroup.normalClosure_le_normal fun g hg ↦ ?_
  rw [hη, SetLike.mem_coe, mem_basepointChangeSubgroup] at hg
  obtain ⟨h, hh, rfl⟩ := hg
  rw [fundamentalGroupMulEquivOfPath_loop_apply]
  exact (Subgroup.normalClosure_normal).conj_mem _ (Subgroup.subset_normalClosure hh) _

/-- If `k : W → Y` factors as `g ∘ f` through `f : W → X`, then the normal closure of
`k_* π₁(W, w)` moved to `g x` along any path `η` is the normal closure of the image under `g_*`
of `f_* π₁(W, w)` moved to `x` along any path `γ`. -/
theorem normalClosure_basepointChangeSubgroup_range_eq_of_eq_comp {W : Type*}
    [TopologicalSpace W] {k : C(W, Y)} (f : C(W, X)) (g : C(X, Y)) (hk : k = g.comp f) {w : W}
    {x : X} (η : Path (k w) (g x)) (γ : Path (f w) x) :
    Subgroup.normalClosure (basepointChangeSubgroup η (map k w).range :
        Set (FundamentalGroup Y (g x))) =
      Subgroup.normalClosure ((basepointChangeSubgroup γ (map f w).range).map (map g x)) := by
  subst hk
  rw [normalClosure_basepointChangeSubgroup_eq η (γ.map g.continuous), FundamentalGroup.map_comp,
    MonoidHom.range_comp, basepointChangeSubgroup_map]

end FundamentalGroup

end
