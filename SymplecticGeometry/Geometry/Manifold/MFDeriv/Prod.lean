/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Prod

/-!
# Partial derivatives of a map on a product manifold

For a family `f : M → M' → M''` whose uncurried form is differentiable at `(x, y)`, the
derivative of `Function.uncurry f` at `(x, y)` on a tangent vector `(v, 0)` is the derivative at
`x` of the slice `z ↦ f z y` on `v` (`MDifferentiableAt.mfderiv_uncurry_apply_mk_zero`). This is
the counterpart, for the first factor, of Tau Ceti's
`MDifferentiableAt.mfderiv_uncurry_apply_zero_mk`, which treats tangent vectors `(0, w)`. It is
stated in the same form, and has the proof of Tau Ceti's lemma with the two summands of Mathlib's
`mfderiv_prod_eq_add_apply` exchanged.

The differentiability hypothesis cannot be dropped: if `Function.uncurry f` is not differentiable
at `(x, y)`, its `mfderiv` is `0`, while a slice can still be differentiable with a nonzero
derivative.

Read through Tau Ceti's identification `TauCeti.Manifold.tangentSpaceProdEquiv` of the tangent
space of a product with the product of the tangent spaces, the differential of the slice inclusion
`y ↦ (x, y)` sends `w` to `(0, w)` (`TauCeti.Manifold.tangentSpaceProdEquiv_mfderiv_prodMk_right`)
and that of `x ↦ (x, y)` sends `v` to `(v, 0)`
(`TauCeti.Manifold.tangentSpaceProdEquiv_mfderiv_prodMk_left`). These restate Mathlib's
`mfderiv_prod_right` and `mfderiv_prod_left` on vectors, so that proofs need not unfold the tangent
space of a product to the product of the model spaces. They sit next to Tau Ceti's
`TauCeti.Manifold.tangentSpaceProdEquiv_mfderiv_prodMap_id`, which treats `Prod.map id φ`.

That identification is the identity map, so the same two facts also hold with the tangent vector of
`M × M'` written directly as a pair (`mfderiv_prodMk_right_apply`, `mfderiv_prodMk_left_apply`).
These are the forms that `rw` and `simp` can use on the differential of a slice inclusion applied
to a vector.

The differential of the graph `z ↦ (f z, z)` of a map `f`, with its factors exchanged, has
second coordinate `v` on each tangent vector `v` at a point where `f` is differentiable
(`TauCeti.Manifold.mfderiv_graph_swap_snd_apply`). This is the counterpart of Tau Ceti's
`TauCeti.Manifold.mfderiv_graph_fst_apply` for `z ↦ (z, f z)`, with the same proof.

A tangent vector of `M × M'` is in the kernel of the differential of the first projection exactly
when its first component is zero (`mem_ker_mfderiv_fst_iff`).

On a product `E₁ × E₂` of model vector spaces, Mathlib has two models: the product
`𝓘(𝕜, E₁).prod 𝓘(𝕜, E₂)` of the self-models and the self-model `𝓘(𝕜, E₁ × E₂)`, whose charted
space structures agree only up to `modelWithCornersSelf_prod` and `chartedSpaceSelf_prod`. The
differentials of a map for the two are equal, for a map from `E₁ × E₂`
(`mfderiv_prod_modelWithCornersSelf_source`) and for a map into it
(`mfderiv_prod_modelWithCornersSelf_target`). These are the `mfderiv` counterparts of Tau Ceti's
`contMDiffAt_prod_modelWithCornersSelf_iff`, with the same proof.

For a map `f : M → M'`, the differential of `z ↦ (f z, z)`, the graph of `f` with its factors
exchanged, has first coordinate `df v` on a tangent vector `v`
(`TauCeti.Manifold.mfderiv_graph_swap_fst_apply`), whether or not `f` is differentiable at the
point. This adapts the proof of Tau Ceti's `TauCeti.Manifold.mfderiv_graph_snd_apply`, which
treats `z ↦ (z, f z)`, with the two factors exchanged.
-/

public section

open scoped Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] {H'' : Type*}
  [TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 E'' H''} {M'' : Type*}
  [TopologicalSpace M''] [ChartedSpace H'' M'']

namespace MDifferentiableAt

variable {f : M → M' → M''} {x : M} {y : M'}

/-- The differential of an uncurried family `(x, y) ↦ f x y`, differentiable at `(x, y)`, on a
horizontal tangent vector `(v, 0)` is the differential of the slice `z ↦ f z y` at `x` on `v`. -/
theorem mfderiv_uncurry_apply_mk_zero
    (hf : MDifferentiableAt (I.prod I') I'' (Function.uncurry f) (x, y)) (v : TangentSpace I x) :
    mfderiv (I.prod I') I'' (Function.uncurry f) (x, y) (v, 0) =
      mfderiv I I'' (fun z ↦ f z y) x v :=
  (mfderiv_prod_eq_add_apply hf).trans <| (congrArg (_ + ·) (map_zero _)).trans (add_zero _)

end MDifferentiableAt

namespace TauCeti.Manifold

variable {x : M} {y : M'}

/-- Under the identification of the tangent space of `M × M'` with the product of the tangent
spaces, the differential at `y` of the slice inclusion `z ↦ (x, z)` sends `w` to `(0, w)`. -/
theorem tangentSpaceProdEquiv_mfderiv_prodMk_right (w : TangentSpace I' y) :
    tangentSpaceProdEquiv (x, y) (mfderiv I' (I.prod I') (fun z ↦ (x, z)) y w) = (0, w) := by
  rw [mfderiv_prod_right, tangentSpaceProdEquiv_apply]
  exact ContinuousLinearMap.inr_apply ..

/-- Under the identification of the tangent space of `M × M'` with the product of the tangent
spaces, the differential at `x` of the slice inclusion `z ↦ (z, y)` sends `v` to `(v, 0)`. -/
theorem tangentSpaceProdEquiv_mfderiv_prodMk_left (v : TangentSpace I x) :
    tangentSpaceProdEquiv (x, y) (mfderiv I (I.prod I') (fun z ↦ (z, y)) x v) = (v, 0) := by
  rw [mfderiv_prod_left, tangentSpaceProdEquiv_apply]
  exact ContinuousLinearMap.inl_apply ..

/-- The differential of the graph `z ↦ (f z, z)`, with its factors exchanged, of a map `f`
differentiable at `x` has second coordinate `v` on `v`. -/
@[simp]
theorem mfderiv_graph_swap_snd_apply {f : M → M'} (hf : MDifferentiableAt I I' f x)
    (v : TangentSpace I x) : (mfderiv I (I'.prod I) (fun z ↦ (f z, z)) x v).2 = v := by
  have hg : MDifferentiableAt I (I'.prod I) (fun z ↦ (f z, z)) x := hf.prodMk mdifferentiableAt_id
  rw [← hg.mfderiv_snd_apply]
  -- The second coordinate of `z ↦ (f z, z)` is the identity by definition.
  exact DFunLike.congr_fun (mfderiv_id (I := I) (x := x)) v

end TauCeti.Manifold

variable {x : M} {y : M'}

/-- The differential at `y` of the slice inclusion `z ↦ (x, z)` sends `w` to the tangent vector
`(0, w)` of `M × M'` at `(x, y)`. -/
theorem mfderiv_prodMk_right_apply (w : TangentSpace I' y) :
    mfderiv I' (I.prod I') (fun z ↦ (x, z)) y w = (0, w) :=
  (TauCeti.Manifold.tangentSpaceProdEquiv_apply _ _).symm.trans
    (TauCeti.Manifold.tangentSpaceProdEquiv_mfderiv_prodMk_right w)

/-- The differential at `x` of the slice inclusion `z ↦ (z, y)` sends `v` to the tangent vector
`(v, 0)` of `M × M'` at `(x, y)`. -/
theorem mfderiv_prodMk_left_apply (v : TangentSpace I x) :
    mfderiv I (I.prod I') (fun z ↦ (z, y)) x v = (v, 0) :=
  (TauCeti.Manifold.tangentSpaceProdEquiv_apply _ _).symm.trans
    (TauCeti.Manifold.tangentSpaceProdEquiv_mfderiv_prodMk_left v)

/-- A tangent vector of `M × M'` at `p` lies in the kernel of the differential of the first
projection exactly when its first component vanishes. -/
theorem mem_ker_mfderiv_fst_iff {p : M × M'} {v : TangentSpace (I.prod I') p} :
    v ∈ (mfderiv (I.prod I') I Prod.fst p).ker ↔ v.1 = 0 := by
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, TauCeti.mfderiv_fst_apply]
  -- The left side compares `v.1` with the zero of `TangentSpace I p.1`, the right side with the
  -- zero of `E`; the two spaces agree only by definition.
  exact Iff.rfl

namespace TauCeti.Manifold

/-- The differential of the graph `z ↦ (f z, z)` of a map `f`, with its factors exchanged, has
first coordinate `df v` on each tangent vector `v`. -/
@[simp]
theorem mfderiv_graph_swap_fst_apply {f : M → M'} {x : M} (v : TangentSpace I x) :
    (mfderiv I (I'.prod I) (fun z ↦ (f z, z)) x v).1 = mfderiv I I' f x v := by
  by_cases hf : MDifferentiableAt I I' f x
  swap
  · -- Neither the graph nor `f` is differentiable at `x`, so both differentials are `0`.
    have hg : ¬ MDifferentiableAt I (I'.prod I) (fun z ↦ (f z, z)) x :=
      fun hg ↦ hf (mdifferentiableAt_fst.comp x hg)
    rw [mfderiv_zero_of_not_mdifferentiableAt hg, mfderiv_zero_of_not_mdifferentiableAt hf]
    rfl
  have hg : MDifferentiableAt I (I'.prod I) (fun z ↦ (f z, z)) x := hf.prodMk mdifferentiableAt_id
  exact (hg.mfderiv_fst_apply v).symm

end TauCeti.Manifold

section ModelWithCornersSelf

variable {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] [NormedAddCommGroup E₂]
  [NormedSpace 𝕜 E₂]

/-- On a product of model vector spaces, the differential of a map for the product of the
self-models is its differential for the self-model of the product. -/
theorem mfderiv_prod_modelWithCornersSelf_source (f : E₁ × E₂ → M') (p : E₁ × E₂) :
    mfderiv (𝓘(𝕜, E₁).prod 𝓘(𝕜, E₂)) I' f p = mfderiv 𝓘(𝕜, E₁ × E₂) I' f p := by
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]

/-- For a map into a product of model vector spaces, its differential for the product of the
self-models is its differential for the self-model of the product. -/
theorem mfderiv_prod_modelWithCornersSelf_target (f : M → E₁ × E₂) (x : M) :
    mfderiv I (𝓘(𝕜, E₁).prod 𝓘(𝕜, E₂)) f x = mfderiv I 𝓘(𝕜, E₁ × E₂) f x := by
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]

end ModelWithCornersSelf

end
