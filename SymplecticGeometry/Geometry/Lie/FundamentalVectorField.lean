/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Lie.FundamentalVectorField

/-!
# Fundamental vector fields under equivariant maps

Let a real Lie group `G` act smoothly on manifolds `M` and `N`, and let `f : M → N` satisfy
`f (g • x) = g • f x` for all `g : G` and be differentiable at `x`. Then the differential of `f`
at `x` carries the infinitesimal action of `𝔤 = GroupLieAlgebra I G` at `x` to that at `f x`:

* `TauCeti.InfinitesimalAction.mfderiv_comp_eval_fundamental_of_map_smul`:
  `df_x ∘ (ξ ↦ ξ_M(x)) = (ξ ↦ ξ_N(f x))`, as linear maps out of `𝔤`;
* `TauCeti.InfinitesimalAction.map_orbitTangent_fundamental_of_map_smul`: `df_x` maps the orbit
  tangent space `𝔤 · x` of `M` onto the orbit tangent space `𝔤 · f x` of `N`.

These are the pointwise statement `TauCeti.mfderiv_fundamentalVectorField_of_map_smul` of Tau
Ceti's `TauCeti/Geometry/Lie/FundamentalVectorField.lean`, put in the language of
`TauCeti.InfinitesimalAction.eval` and `TauCeti.InfinitesimalAction.orbitTangent`. They sit in Tau
Ceti's namespace, beside `TauCeti.orbitTangent_fundamental_smul`, its analogue for the translation
`y ↦ g • y` (which intertwines the actions only up to conjugation by `g`), so that they can move
there unchanged.

The file also has `TauCeti.InfinitesimalAction.coe_fundamental_toSectionLinearMap`: the smooth
section `(InfinitesimalAction.fundamental I G I' M).toSectionLinearMap ξ` is, as a function, the
fundamental vector field `fundamentalVectorField I' ξ`.
-/

public section

open scoped Manifold ContDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I (minSmoothness ℝ 3) G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [MulAction G M]
  [ContMDiffSMul I I' ∞ G M]
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E''] [CompleteSpace E'']
  {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners ℝ E'' H''}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H'' N] [IsManifold I'' ∞ N] [MulAction G N]
  [ContMDiffSMul I I'' ∞ G N]
  {f : M → N} {x : M}

namespace InfinitesimalAction

/-- The smooth section of the tangent bundle given by the fundamental vector field of `ξ` is, as a
function, that vector field. -/
@[simp]
theorem coe_fundamental_toSectionLinearMap (ξ : GroupLieAlgebra I G) :
    ⇑((fundamental I G I' M).toSectionLinearMap ξ) = fundamentalVectorField I' ξ :=
  funext fun x ↦ by rw [toSectionLinearMap_apply, fundamental_apply]

/-- **Equivariant maps intertwine the infinitesimal actions.** If `f : M → N` is differentiable
at `x` and `f (g • x) = g • f x` for every `g : G`, then composing the evaluation `ξ ↦ ξ_M(x)` of
the fundamental vector fields of `M` at `x` with the differential of `f` at `x` gives the
evaluation `ξ ↦ ξ_N(f x)` of those of `N` at `f x`. -/
theorem mfderiv_comp_eval_fundamental_of_map_smul (hf : MDifferentiableAt I' I'' f x)
    (hfx : ∀ g : G, f (g • x) = g • f x) :
    (mfderiv I' I'' f x).toLinearMap ∘ₗ (fundamental I G I' M).eval x =
      (fundamental I G I'' N).eval (f x) := by
  ext ξ
  rw [LinearMap.comp_apply, eval_apply, eval_apply, fundamental_apply, fundamental_apply,
    ContinuousLinearMap.coe_coe]
  exact mfderiv_fundamentalVectorField_of_map_smul hf
    ((ContMDiffSMul.contMDiff_smul_const (I := I) (I' := I') (n := ∞) x).mdifferentiableAt
      (by simp)) hfx ξ

/-- **Equivariant maps carry orbit tangent spaces onto orbit tangent spaces.** If `f : M → N` is
differentiable at `x` and `f (g • x) = g • f x` for every `g : G`, then the differential of `f`
at `x` maps the orbit tangent space `𝔤 · x` of `M` onto the orbit tangent space `𝔤 · f x` of
`N`. -/
theorem map_orbitTangent_fundamental_of_map_smul (hf : MDifferentiableAt I' I'' f x)
    (hfx : ∀ g : G, f (g • x) = g • f x) :
    ((fundamental I G I' M).orbitTangent x).map (mfderiv I' I'' f x).toLinearMap =
      (fundamental I G I'' N).orbitTangent (f x) := by
  rw [orbitTangent_eq_range, orbitTangent_eq_range, ← LinearMap.range_comp,
    mfderiv_comp_eval_fundamental_of_map_smul hf hfx]

end InfinitesimalAction

end TauCeti

end
