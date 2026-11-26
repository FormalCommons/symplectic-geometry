/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Algebra.SMul
import TauCeti.Geometry.Manifold.Diffeomorph.Basic

/-!
# Differentiability of equivariant maps along an orbit

Let a group `G` act on manifolds `M` and `M'` by `C¹` maps (`ContMDiffConstSMul`). If
`f : M → M'` commutes with `z ↦ g • z` and is differentiable at `y`, then it is differentiable at
`g • y` (`MDifferentiableAt.at_smul_of_map_smul`). Indeed `f` composed with Tau Ceti's
diffeomorphism `Diffeomorph.constSmul g` on the right is `Diffeomorph.constSmul g` composed with
`f` on the left, and both compositions keep differentiability, by Tau Ceti's
`Diffeomorph.mdifferentiableAt_comp_diffeomorph_iff` and `Diffeomorph.mdifferentiableAt_comp_iff`.

## Main results

* `MDifferentiableAt.at_smul_of_map_smul`: differentiability of a `G`-equivariant map at `y`
  gives it at `g • y`.
-/

public section

open scoped Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {G : Type*} [Group G] [MulAction G M] [ContMDiffConstSMul I 1 G M] [MulAction G M']
  [ContMDiffConstSMul I' 1 G M'] {f : M → M'}

/-- Let a group `G` act on `M` and on `M'` by `C¹` maps, and let `f : M → M'` commute with
`z ↦ g • z`. If `f` is differentiable at `y`, then it is differentiable at `g • y`. -/
theorem MDifferentiableAt.at_smul_of_map_smul (g : G) (hfg : ∀ z, f (g • z) = g • f z) {y : M}
    (hf : MDifferentiableAt I I' f y) : MDifferentiableAt I I' f (g • y) := by
  rw [← Diffeomorph.constSmul_apply (I := I) (n := 1) g,
    ← Diffeomorph.mdifferentiableAt_comp_diffeomorph_iff _ one_ne_zero,
    show f ∘ Diffeomorph.constSmul I 1 g = Diffeomorph.constSmul I' 1 g ∘ f from
      funext fun z ↦ by simpa only [Function.comp_apply, Diffeomorph.constSmul_apply] using hfg z,
    Diffeomorph.mdifferentiableAt_comp_iff _ one_ne_zero]
  exact hf

end
