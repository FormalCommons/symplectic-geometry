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

For a commutative group, `TauCeti.mfderiv_fundamentalVectorField_eq_of_eventually_smul_eq`
says that an element `g` fixing `x` fixes the orbit directions `ξ_M(x)`, read through any map
`f` that turns `y ↦ g • y` into a linear map `L` near `x`: `L (df_x ξ_M(x)) = df_x ξ_M(x)`. It
follows from Tau Ceti's `TauCeti.mfderiv_smul_fundamentalVectorField`, since `Ad_g` is the
identity (`TauCeti.Lie.adjointContinuousLinearMap_eq_id`).

Last, `TauCeti.mfderiv_inv_smul_one_apply` says that the derivative at `1` of `g ↦ g⁻¹ • x`
sends `ξ` to `-ξ_M(x)`, for any action of a Lie group over a nontrivially normed field. When the
orbit map is differentiable at `1`, it differentiates through inversion (Tau Ceti's
`TauCeti.GroupLieAlgebra.mfderiv_inv_one_apply`), with the steps of Tau Ceti's
`TauCeti.LeftToRightAction.mfderiv_equiv_symm_rightFundamentalVectorField_of_mdifferentiableAt`;
when it is not, neither is `g ↦ g⁻¹ • x`, and both sides are zero.
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

section Inverse

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M]

/-- **The inverse orbit map differentiates to minus the fundamental vector field.** For a Lie
group `G` acting on `M`, the derivative at `1` of `g ↦ g⁻¹ • x` sends `ξ` to `-ξ_M(x)`. -/
theorem mfderiv_inv_smul_one_apply [LieGroup I 1 G] [MulAction G M] {x : M}
    (ξ : GroupLieAlgebra I G) :
    mfderiv I I' (fun g : G ↦ g⁻¹ • x) 1 ξ = -fundamentalVectorField I' ξ x := by
  have hinv : MDifferentiableAt I I (fun g : G ↦ g⁻¹) 1 :=
    (contMDiff_inv I 1).mdifferentiableAt one_ne_zero
  by_cases horbit : MDifferentiableAt I I' (fun g : G ↦ g • x) 1
  · have h := mfderiv_comp_apply_of_eq 1 horbit hinv inv_one ξ
    rw [GroupLieAlgebra.mfderiv_inv_one_apply, map_neg, ← fundamentalVectorField_apply] at h
    exact h
  · -- Inversion is its own inverse, so `g ↦ g⁻¹ • x` is not differentiable at `1` either.
    have h : ¬ MDifferentiableAt I I' (fun g : G ↦ g⁻¹ • x) 1 := fun h ↦ horbit <| by
      simpa [Function.comp_def] using h.comp_of_eq (x := 1) hinv inv_one
    rw [mfderiv_zero_of_not_mdifferentiableAt h, fundamentalVectorField_apply,
      mfderiv_zero_of_not_mdifferentiableAt horbit]
    exact neg_zero.symm

end TauCeti

end Inverse

section Commutative

open scoped Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I 1 G]
  [IsMulCommutative G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [MulAction G M] [ContMDiffSMul I I' 1 G M]

/-- **A commutative group fixes the orbit directions at a fixed point, in any equivariant
reading.** Let a commutative Lie group `G` act on `M`, let `g : G` fix `x`, and let
`f : M → F`, differentiable at `x`, satisfy `f (g • y) = L (f y)` for `y` near `x`, with `L` a
continuous linear map of `F`. Then `L` fixes `df_x (ξ_M(x))` for every `ξ` in the Lie algebra:
since `Ad_g` is the identity, `dg_x` fixes `ξ_M(x)`. -/
theorem mfderiv_fundamentalVectorField_eq_of_eventually_smul_eq
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : M → F} {x : M} {g : G}
    (hf : MDifferentiableAt I' 𝓘(ℝ, F) f x) (hgx : g • x = x) (L : F →L[ℝ] F)
    (hL : ∀ᶠ y in 𝓝 x, f (g • y) = L (f y)) (ξ : GroupLieAlgebra I G) :
    L (mfderiv I' 𝓘(ℝ, F) f x (fundamentalVectorField I' ξ x)) =
      mfderiv I' 𝓘(ℝ, F) f x (fundamentalVectorField I' ξ x) := by
  have hsmul : MDifferentiableAt I' I' (fun y : M ↦ g • y) x :=
    (ContMDiffSMul.contMDiff_const_smul (I := I) (I' := I') (n := 1) g).mdifferentiableAt
      one_ne_zero
  have hfg : MDifferentiableAt I' 𝓘(ℝ, F) f (g • x) := by rw [hgx]; exact hf
  have hcomp : mfderiv I' 𝓘(ℝ, F) (f ∘ fun y : M ↦ g • y) x =
      mfderiv I' 𝓘(ℝ, F) (L ∘ f) x := Filter.EventuallyEq.mfderiv_eq hL
  have h := mfderiv_comp_apply_of_eq x hfg hsmul rfl (fundamentalVectorField I' ξ x)
  rw [hcomp, mfderiv_comp x L.mdifferentiableAt hf, ContinuousLinearMap.mfderiv_eq,
    mfderiv_smul_fundamentalVectorField, Lie.adjointContinuousLinearMap_eq_id,
    ContinuousLinearMap.id_apply] at h
  -- `h` reads `(L ∘L df_x) (ξ_M x) = df_{g • x} (ξ_M (g • x))`, and `g • x = x`.
  refine h.trans ?_
  rw [hgx]

end TauCeti

end Commutative

end
