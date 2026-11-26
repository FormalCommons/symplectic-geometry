/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Lie.FundamentalVectorField
public import TauCeti.Geometry.Lie.FundamentalVectorField.Right

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

For any infinitesimal action, a point `x` and an injective linear map `L : P → T_x M` whose
range meets `𝔤 · x` only in `0`, `TauCeti.InfinitesimalAction.ker_eval_coprod` and
`TauCeti.InfinitesimalAction.apply_add_eq_zero_iff` say that `(Z, p) ↦ Z_M(x) + L p` vanishes
exactly on `𝔤_x × 0`. This is the kernel half of the linear algebra of a slice through `x`, by
Mathlib's `LinearMap.ker_coprod_of_disjoint_range`, and follows the steps of the proof of Tau
Ceti's `TauCeti.mfderiv_smul_slice_eq_zero_iff`, which treats the inclusion of a subspace in place
of `L`. The other half, that the map is onto `T_x M` exactly when `𝔤 · x + range L = T_x M`, is
Tau Ceti's `LinearMap.surjective_coprod_iff`, since `𝔤 · x` is the range of
`TauCeti.InfinitesimalAction.eval`.

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
`TauCeti.mfderiv_inv_smul_apply` moves this to any point `g`: since
`h⁻¹ • x = (g⁻¹ * h)⁻¹ • (g⁻¹ • x)`, the derivative at `g` sends `v` to `-ξ_M(g⁻¹ • x)`, for `ξ`
the image of `v` under the derivative of `h ↦ g⁻¹ * h`. `TauCeti.mfderiv_inv_smul_comp_apply`
is its form along a map `γ : N → G`, for `y ↦ (γ y)⁻¹ • x`.

`Diffeomorph.mfderiv_fundamentalVectorField` says that an equivariant `C^n` diffeomorphism
`Φ : M → N`, with `n ≠ 0`, sends `ξ_M(x)` to `ξ_N(Φ x)`, over any nontrivially normed field and
with no hypothesis on the actions. Where the orbit map of `x` is differentiable at `1`, this is
`TauCeti.mfderiv_fundamentalVectorField_of_map_smul`; where it is not, neither is that of `Φ x`,
which is `Φ` composed with the orbit map of `x` (Tau Ceti's
`Diffeomorph.mdifferentiableAt_comp_iff`), and both sides are zero.

`TauCeti.mfderiv_rightFundamentalVectorField_of_map_op_smul_eq_smul` is the mixed case of the
first statement: a map `f : M → N` with `f (x • g) = g • f x`, from a right action to a left one,
sends the right fundamental vector field of `ξ` at `x` to the fundamental vector field of `ξ` at
`f x`. Its proof is that of Tau Ceti's
`TauCeti.mfderiv_rightFundamentalVectorField_of_map_op_smul`, the case of two right actions.

`TauCeti.mfderiv_linearEquiv_apply_adjointContinuousLinearMap` is the equivariance of the
fundamental vector fields for a linear representation `rep : G →* V ≃ₗ[ℝ] V` that is jointly
`C¹`, written with the orbit maps `g' ↦ rep g' v`: the derivative at `1` at `Ad_g ξ` of the orbit
map of `v` is `rep g` applied to that at `ξ` of the orbit map of `rep g⁻¹ v`. It is Tau Ceti's
`TauCeti.mfderiv_smul_fundamentalVectorField` for the action through `rep`, whose translations
`rep g` are their own derivatives.
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

section Coprod

namespace TauCeti.InfinitesimalAction

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] (a : InfinitesimalAction 𝔤 I M) {x : M}
  {P : Type*} [AddCommGroup P] [Module ℝ P] {L : P →ₗ[ℝ] TangentSpace I x}

/-- For an injective `L` whose range meets the orbit tangent space `𝔤 · x` only in `0`, the
kernel of `(Z, p) ↦ Z_M(x) + L p` is `𝔤_x × 0`, where `𝔤_x` is the isotropy algebra of `x`. -/
theorem ker_eval_coprod (hL : Function.Injective L)
    (h : Disjoint (a.orbitTangent x) (LinearMap.range L)) :
    LinearMap.ker ((a.eval x).coprod L) = (a.isotropy x).toSubmodule.prod ⊥ := by
  rw [LinearMap.ker_coprod_of_disjoint_range _ _ ((a.orbitTangent_eq_range x) ▸ h),
    isotropy_toSubmodule, LinearMap.ker_eq_bot.2 hL]

/-- For an injective `L` whose range meets the orbit tangent space `𝔤 · x` only in `0`,
`Z_M(x) + L p` vanishes exactly when `Z` lies in the isotropy algebra `𝔤_x` and `p = 0`. -/
theorem apply_add_eq_zero_iff (hL : Function.Injective L)
    (h : Disjoint (a.orbitTangent x) (LinearMap.range L)) {Z : 𝔤} {p : P} :
    a Z x + L p = 0 ↔ Z ∈ a.isotropy x ∧ p = 0 := by
  have := SetLike.ext_iff.1 (a.ker_eval_coprod hL h) (Z, p)
  rwa [LinearMap.mem_ker, LinearMap.coprod_apply, eval_apply, Submodule.mem_prod,
    Submodule.mem_bot] at this

end TauCeti.InfinitesimalAction

end Coprod

section Inverse

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M]
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 E'' H''}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H'' N]

/-- **The inverse orbit map differentiates to minus the fundamental vector field.** For a Lie
group `G` acting on `M`, the derivative at `1` of `g ↦ g⁻¹ • x` sends `ξ` to `-ξ_M(x)`. -/
theorem mfderiv_inv_smul_one_apply [LieGroup I 1 G] [MulAction G M] {x : M}
    (ξ : GroupLieAlgebra I G) :
    mfderiv I I' (fun g : G ↦ g⁻¹ • x) 1 ξ = -fundamentalVectorField (I := I) (G := G) I' ξ x := by
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

/-- **The inverse orbit map at any point.** For a Lie group `G` acting on `M`, the derivative at
`g` of `h ↦ h⁻¹ • x` sends `v` to `-ξ_M(g⁻¹ • x)`, where `ξ` is the left trivialization of `v`:
its image under the derivative at `g` of `h ↦ g⁻¹ * h`. -/
theorem mfderiv_inv_smul_apply [LieGroup I 1 G] [MulAction G M] {x : M} (g : G)
    (v : TangentSpace I g) :
    mfderiv I I' (fun h : G ↦ h⁻¹ • x) g v =
      -fundamentalVectorField (I := I) (G := G) I' (mfderiv I I (g⁻¹ * ·) g v) (g⁻¹ • x) := by
  have hL : MDifferentiableAt I I (g⁻¹ * ·) g :=
    (contMDiff_mul_left (I := I) (n := 1)).mdifferentiableAt one_ne_zero
  -- `h⁻¹ • x = (g⁻¹ * h)⁻¹ • (g⁻¹ • x)`: the map factors through `h ↦ g⁻¹ * h`.
  have hcomp : (fun h : G ↦ h⁻¹ • x) = (fun k : G ↦ k⁻¹ • g⁻¹ • x) ∘ (g⁻¹ * ·) := by
    funext h
    simp [mul_smul]
  have h1 := mfderiv_inv_smul_one_apply (I := I) (G := G) (I' := I') (x := g⁻¹ • x)
    (mfderiv I I (g⁻¹ * ·) g v : GroupLieAlgebra I G)
  rw [hcomp, ← h1]
  by_cases hk : MDifferentiableAt I I' (fun k : G ↦ k⁻¹ • g⁻¹ • x) 1
  · exact mfderiv_comp_apply_of_eq g hk hL (inv_mul_cancel g) v
  · -- Left multiplication by `g` undoes that by `g⁻¹`, so neither map is differentiable.
    have hR : MDifferentiableAt I I (g * ·) 1 :=
      (contMDiff_mul_left (I := I) (n := 1)).mdifferentiableAt one_ne_zero
    have h : ¬ MDifferentiableAt I I' ((fun k : G ↦ k⁻¹ • g⁻¹ • x) ∘ (g⁻¹ * ·)) g :=
      fun h ↦ hk <| by
        simpa [Function.comp_def] using h.comp_of_eq (x := 1) hR (mul_one g)
    rw [mfderiv_zero_of_not_mdifferentiableAt h, mfderiv_zero_of_not_mdifferentiableAt hk]
    -- Both sides are the zero vector, of tangent spaces at points that agree only up to
    -- `inv_mul_cancel`, so `ContinuousLinearMap.zero_apply` cannot rewrite them.
    rfl

/-- **The inverse orbit map along a map.** If `γ : N → G` is differentiable at `y` and
`h ↦ h⁻¹ • x` is differentiable at `γ y`, then the derivative at `y` of `y ↦ (γ y)⁻¹ • x`
sends `w` to `-ξ_M((γ y)⁻¹ • x)`, where `ξ` is the left trivialization at `γ y` of `dγ_y w`. -/
theorem mfderiv_inv_smul_comp_apply [LieGroup I 1 G] [MulAction G M] {x : M} {γ : N → G} {y : N}
    (hγ : MDifferentiableAt I'' I γ y)
    (hx : MDifferentiableAt I I' (fun h : G ↦ h⁻¹ • x) (γ y)) (w : TangentSpace I'' y) :
    mfderiv I'' I' (fun y ↦ (γ y)⁻¹ • x) y w =
      -fundamentalVectorField (I := I) (G := G) I'
        (mfderiv I I ((γ y)⁻¹ * ·) (γ y) (mfderiv I'' I γ y w))
        ((γ y)⁻¹ • x) := by
  rw [← mfderiv_inv_smul_apply (G := G)]
  exact mfderiv_comp_apply_of_eq (g := fun h : G ↦ h⁻¹ • x) y hx hγ rfl w

end TauCeti

end Inverse

section Diffeomorph

namespace Diffeomorph

open TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [MulAction G M]
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 E'' H''}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H'' N] [MulAction G N]

/-- **Equivariant diffeomorphisms carry fundamental vector fields.** If a `C^n` diffeomorphism
`Φ : M → N`, with `n ≠ 0`, satisfies `Φ (g • x) = g • Φ x` for all `g` and `x`, then its
differential at `x` sends the fundamental vector field of `ξ` at `x` to that at `Φ x`. -/
theorem mfderiv_fundamentalVectorField {n : ℕ∞ω} (Φ : M ≃ₘ^n⟮I', I''⟯ N) (hn : n ≠ 0)
    (hΦ : ∀ (g : G) (x : M), Φ (g • x) = g • Φ x) (ξ : GroupLieAlgebra I G) (x : M) :
    mfderiv I' I'' Φ x (fundamentalVectorField I' ξ x) =
      fundamentalVectorField I'' ξ (Φ x) := by
  by_cases h : MDifferentiableAt I I' (fun g : G ↦ g • x) 1
  · exact mfderiv_fundamentalVectorField_of_map_smul (Φ.mdifferentiable hn x) h
      (fun g ↦ hΦ g x) ξ
  -- Otherwise the orbit map of `Φ x` is `Φ` composed with that of `x`, so it is not
  -- differentiable at `1` either, and both sides vanish.
  have hc : (fun g : G ↦ g • Φ x) = Φ ∘ fun g : G ↦ g • x := funext fun g ↦ (hΦ g x).symm
  have h' : ¬MDifferentiableAt I I'' (fun g : G ↦ g • Φ x) 1 :=
    hc ▸ (Φ.mdifferentiableAt_comp_iff hn).not.mpr h
  rw [fundamentalVectorField_apply, fundamentalVectorField_apply,
    mfderiv_zero_of_not_mdifferentiableAt h, mfderiv_zero_of_not_mdifferentiableAt h',
    zero_apply]
  exact map_zero _

end Diffeomorph

end Diffeomorph

section RightToLeft

namespace TauCeti

open MulOpposite

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [MulAction Gᵐᵒᵖ M]
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 E'' H''}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H'' N] [MulAction G N]

/-- **Maps from a right action to a left action relate the fundamental vector fields.** Let `G`
act on the right on `M` and on the left on `N`. If `f : M → N` satisfies `f (x • g) = g • f x`
for every `g`, and `f` at `x` and the orbit map of `x` at `1` are differentiable, then `df_x`
sends `rightFundamentalVectorField I' ξ x` to `fundamentalVectorField I'' ξ (f x)`. -/
theorem mfderiv_rightFundamentalVectorField_of_map_op_smul_eq_smul {f : M → N} {x : M}
    (hf : MDifferentiableAt I' I'' f x)
    (horbit : MDifferentiableAt I I' (fun g : G ↦ op g • x) 1)
    (hfx : ∀ g : G, f (op g • x) = g • f x) (ξ : GroupLieAlgebra I G) :
    mfderiv I' I'' f x (rightFundamentalVectorField I' ξ x) =
      fundamentalVectorField I'' ξ (f x) := by
  have hcomp : (f ∘ fun g : G ↦ op g • x) = fun g : G ↦ g • f x := funext hfx
  rw [fundamentalVectorField_apply, rightFundamentalVectorField_apply, ← hcomp]
  exact (mfderiv_comp_apply_of_eq (1 : G) hf horbit (by simp) ξ).symm

end TauCeti

end RightToLeft

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

section LinearRepresentation

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I 1 G]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **The orbit derivatives of a linear representation are `Ad`-equivariant.** Let
`rep : G →* V ≃ₗ[ℝ] V` be a representation of a real Lie group with `(g, v) ↦ rep g v` of class
`C¹`. Then the derivative at `1` of the orbit map `g' ↦ rep g' v` takes `Ad_g ξ` to
`rep g` applied to the derivative at `1` of `g' ↦ rep g' (rep g⁻¹ v)` at `ξ`. -/
theorem mfderiv_linearEquiv_apply_adjointContinuousLinearMap (rep : G →* V ≃ₗ[ℝ] V)
    (hrep : ContMDiff (I.prod 𝓘(ℝ, V)) 𝓘(ℝ, V) 1 fun p : G × V ↦ rep p.1 p.2)
    (g : G) (ξ : GroupLieAlgebra I G) (v : V) :
    mfderiv I 𝓘(ℝ, V) (fun g' : G ↦ rep g' v) 1 (Lie.adjointContinuousLinearMap g ξ) =
      rep g (mfderiv I 𝓘(ℝ, V) (fun g' : G ↦ rep g' (rep g⁻¹ v)) 1 ξ) := by
  let : MulAction G V := MulAction.compHom V rep
  have : ContMDiffSMul I 𝓘(ℝ, V) 1 G V := ⟨hrep⟩
  -- `rep g` is a continuous linear map, since the action is continuous.
  let L : V →L[ℝ] V := ⟨(rep g).toLinearMap, hrep.continuous.comp (Continuous.prodMk_right g)⟩
  have hL : ⇑L = rep g := by rw [ContinuousLinearMap.coe_mk', LinearEquiv.coe_coe]
  have h := mfderiv_smul_fundamentalVectorField (I' := 𝓘(ℝ, V)) g ξ (rep g⁻¹ v)
  simp only [fundamentalVectorField_apply, MulAction.compHom_smul_def, LinearEquiv.smul_def] at h
  have hv : rep g (rep g⁻¹ v) = v := by simp
  rw [← hL, L.mfderiv_eq, hL, hv] at h
  exact h.symm

end TauCeti

end LinearRepresentation

end
