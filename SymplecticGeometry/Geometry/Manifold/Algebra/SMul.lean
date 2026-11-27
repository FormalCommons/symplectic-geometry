/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Group
public import TauCeti.Geometry.Manifold.Algebra.SMul
import TauCeti.Geometry.Manifold.Diffeomorph.Basic

/-!
# Smooth group actions as diffeomorphisms

Let a group `G` act on a manifold `M` by `Cⁿ` maps (`ContMDiffConstSMul I n G M`). Tau Ceti's
`Diffeomorph.constSmul I n g` is the diffeomorphism `x ↦ g • x`, and `Diffeomorph.constSmul_one`
and `Diffeomorph.constSmul_mul` say that `g ↦ Diffeomorph.constSmul I n g` respects the group law.
This file bundles it as a group homomorphism `Diffeomorph.constSmulHom I n` from `G` to the group
`TauCeti.Diff I M n` of `Cⁿ` self-diffeomorphisms of `M`.

It also moves differentiability of equivariant maps along an orbit. Let `G` act on manifolds `M`
and `M'` by `C¹` maps. If `f : M → M'` commutes with `z ↦ g • z` and is differentiable at `y`,
then it is differentiable at `g • y` (`MDifferentiableAt.at_smul_of_map_smul`). Indeed `f`
composed with Tau Ceti's diffeomorphism `Diffeomorph.constSmul g` on the right is
`Diffeomorph.constSmul g` composed with `f` on the left, and both compositions keep
differentiability, by Tau Ceti's `Diffeomorph.mdifferentiableAt_comp_diffeomorph_iff` and
`Diffeomorph.mdifferentiableAt_comp_iff`.

## Main definitions

* `Diffeomorph.constSmulHom`: the homomorphism `g ↦ (x ↦ g • x)` from `G` to the group of `Cⁿ`
  diffeomorphisms of `M`.

## Main results

* `Diffeomorph.constSmulHom_injective`: for a faithful action, `Diffeomorph.constSmulHom` is
  injective.
* `MDifferentiableAt.at_smul_of_map_smul`: differentiability of a `G`-equivariant map at `y`
  gives it at `g • y`.
-/

public section

open scoped Manifold ContDiff

namespace Diffeomorph

section constSmulHom

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {G : Type*} [Group G] [MulAction G M]
  {n : ℕ∞ω} [ContMDiffConstSMul I n G M]

variable (I n) in
/-- For a group `G` acting on `M` by `Cⁿ` maps, the group homomorphism from `G` to the group of
`Cⁿ` self-diffeomorphisms of `M` that sends `g` to the diffeomorphism `x ↦ g • x`. -/
def constSmulHom : G →* TauCeti.Diff I M n where
  toFun := constSmul I n
  map_one' := constSmul_one
  map_mul' := constSmul_mul

/-- The image of `g` under `Diffeomorph.constSmulHom I n` is `Diffeomorph.constSmul I n g`. -/
@[simp]
theorem constSmulHom_apply (g : G) : constSmulHom I n g = constSmul (M := M) I n g := (rfl)

/-- For a faithful action, distinct elements of `G` give distinct diffeomorphisms of `M`. -/
theorem constSmulHom_injective [FaithfulSMul G M] :
    Function.Injective (constSmulHom I n : G →* TauCeti.Diff I M n) :=
  fun _ _ h ↦ constSmul_injective (I := I) (n := n) (M := M) <| by
    simpa only [constSmulHom_apply] using h

end constSmulHom

end Diffeomorph

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
