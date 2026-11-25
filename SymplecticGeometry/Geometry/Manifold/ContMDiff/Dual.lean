/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SMul
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import TauCeti.Geometry.Manifold.ContMDiff.FiniteDimension
public import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Smoothness of the values of linear functionals

Let `x : N → X` be a family of vectors of a vector space `X` over a nontrivially normed field
`𝕜`, indexed by a manifold `N`. The functionals `f : Module.Dual 𝕜 X` for which
`t ↦ f (x t)` is `C^n` form a submodule of the dual space. So if this holds for every functional
of a set `s` that spans the dual space, it holds for every functional. When `X` is
finite-dimensional, a set of functionals spans the dual space as soon as it separates the
points of `X` (Mathlib's `Submodule.span_eq_top_of_ne_zero`), which gives a variant with that
hypothesis. For a finite-dimensional `X`, the family itself, read through any linear map
`f : X → V` into a normed space, is then `C^n`: in a basis `b` of `X`, `f ∘ x` is the finite sum
`t ↦ ∑ i, b.coord i (x t) • f (b i)`.

No topology on `X` is involved: smoothness is only asked of the scalar functions
`t ↦ f (x t)`. The last two results are the exceptions: for a finite-dimensional normed space `E`
over a complete field, a family of linear functionals on `E` whose values are `C^n` is `C^n` as
a family of continuous linear maps `E →L[𝕜] 𝕜`, by Tau Ceti's `TauCeti.contMDiffAt_clm_apply`.
Through that family, the derivative of the values of `ν` on a varying vector comes from Mathlib's
`fderiv_clm_apply`.

## Main results

* `contMDiff_dual_apply_of_span_eq_top`: if `t ↦ g (x t)` is `C^n` for every `g` of a set `s`
  that spans the dual space, then `t ↦ f (x t)` is `C^n` for every linear functional `f`.
* `contMDiff_dual_apply_of_separating`: the same for a finite-dimensional `X` and a set `s` of
  functionals such that every nonzero vector has a functional of `s` that does not vanish on it.
* `contMDiff_linearMap_comp_of_dual`: for a finite-dimensional `X`, if `t ↦ g (x t)` is `C^n`
  for every linear functional `g`, then `f ∘ x` is `C^n` for every linear map `f` from `X` to a
  normed space.
* `contMDiff_toContinuousLinearMap_of_contMDiff_apply`: for a finite-dimensional normed space `E`,
  if `t ↦ ν t ξ` is `C^n` for every `ξ : E`, then `ν` is `C^n` as a map into `E →L[𝕜] 𝕜`.
* `fderiv_dual_comp_apply`: for a family `ν` of functionals on a finite-dimensional normed space
  `X`, indexed by `N`, with values `C^1` at `x y`, a map `x : F → N` from a normed space, `C^1`
  at `y`, and a map `c : F → X` differentiable at `y`, the derivative of `z ↦ ν (x z) (c z)` at
  `y` is `ν (x y)` applied to that of `c`, plus the derivative of `ν · (c y)` along `x`.
-/

public section

namespace SymplecticGeometry

open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EN HN N : Type*} [NormedAddCommGroup EN] [NormedSpace 𝕜 EN] [TopologicalSpace HN]
  {J : ModelWithCorners 𝕜 EN HN} [TopologicalSpace N] [ChartedSpace HN N] {n : ℕ∞ω}
  {X : Type*} [AddCommMonoid X] [Module 𝕜 X] {s : Set (Module.Dual 𝕜 X)} {x : N → X}

/-- **Smoothness against a spanning set of functionals.** Let `x` be a family of vectors of a
vector space `X`, indexed by a manifold `N`, and `s` a set of linear functionals on `X` that spans
the dual space. If `t ↦ g (x t)` is `C^n` for every `g ∈ s`, then `t ↦ f (x t)` is `C^n` for
every linear functional `f` on `X`. -/
theorem contMDiff_dual_apply_of_span_eq_top (hs : Submodule.span 𝕜 s = ⊤)
    (hx : ∀ g ∈ s, ContMDiff J 𝓘(𝕜) n (fun t ↦ g (x t))) (f : Module.Dual 𝕜 X) :
    ContMDiff J 𝓘(𝕜) n (fun t ↦ f (x t)) := by
  have hf : f ∈ Submodule.span 𝕜 s := hs ▸ Submodule.mem_top
  induction hf using Submodule.span_induction with
  | mem f hf => exact hx f hf
  | zero => exact contMDiff_const
  | add f g _ _ hf hg => exact hf.add hg
  | smul c f _ hf => exact ((contDiff_const_smul c).contMDiff).comp hf

/-- **Smoothness against a separating set of functionals.** Let `x` be a family of vectors of a
finite-dimensional vector space `X`, indexed by a manifold `N`, and `s` a set of linear
functionals on `X` such that every nonzero vector of `X` has a functional of `s` that does not
vanish on it. If `t ↦ g (x t)` is `C^n` for every `g ∈ s`, then `t ↦ f (x t)` is `C^n` for every
linear functional `f` on `X`. -/
theorem contMDiff_dual_apply_of_separating {X : Type*} [AddCommGroup X] [Module 𝕜 X]
    [FiniteDimensional 𝕜 X] {s : Set (Module.Dual 𝕜 X)} {x : N → X}
    (hs : ∀ z ≠ 0, ∃ g ∈ s, g z ≠ 0)
    (hx : ∀ g ∈ s, ContMDiff J 𝓘(𝕜) n (fun t ↦ g (x t))) (f : Module.Dual 𝕜 X) :
    ContMDiff J 𝓘(𝕜) n (fun t ↦ f (x t)) :=
  contMDiff_dual_apply_of_span_eq_top (Submodule.span_eq_top_of_ne_zero hs) hx f

/-- **Smoothness of a family read through a linear map.** Let `x` be a family of vectors of a
finite-dimensional vector space `X` over a nontrivially normed field `𝕜`, indexed by a manifold
`N`, such that `t ↦ g (x t)` is `C^n` for every linear functional `g` on `X`. Then
`f ∘ x` is `C^n` for every linear map `f` (of any `LinearMapClass`) from `X` to a normed space
`V`. -/
theorem contMDiff_linearMap_comp_of_dual {X : Type*} [AddCommGroup X] [Module 𝕜 X]
    [FiniteDimensional 𝕜 X] {x : N → X}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    {F : Type*} [FunLike F X V] [LinearMapClass F 𝕜 X V]
    (hx : ∀ g : Module.Dual 𝕜 X, ContMDiff J 𝓘(𝕜) n (fun t ↦ g (x t))) (f : F) :
    ContMDiff J 𝓘(𝕜, V) n (f ∘ x) := by
  let b := Module.finBasis 𝕜 X
  have hfx : f ∘ x = fun t ↦ ∑ i, b.coord i (x t) • f (b i) := by
    funext t
    rw [Function.comp_apply]; nth_rewrite 1 [← b.sum_repr (x t)]
    simp only [map_sum, map_smul, Module.Basis.coord_apply]
  rw [hfx]
  exact contMDiff_finsetSum fun i _ ↦ (hx (b.coord i)).smul contMDiff_const

/-- **Smoothness of a family of covectors.** Let `ν` be a family of linear functionals on a
finite-dimensional normed space `E` over a complete nontrivially normed field `𝕜`, indexed by a
manifold `N`. If `t ↦ ν t ξ` is `C^n` for every `ξ : E`, then `ν`, read as a family of continuous
linear maps `E →L[𝕜] 𝕜`, is `C^n`. -/
theorem contMDiff_toContinuousLinearMap_of_contMDiff_apply [CompleteSpace 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    {ν : N → Module.Dual 𝕜 E} (hν : ∀ ξ, ContMDiff J 𝓘(𝕜) n fun t ↦ ν t ξ) :
    ContMDiff J 𝓘(𝕜, E →L[𝕜] 𝕜) n fun t ↦ LinearMap.toContinuousLinearMap (ν t) :=
  fun t ↦ TauCeti.contMDiffAt_clm_apply.2 fun ξ ↦ hν ξ t

/-- **The derivative of a family of functionals evaluated on a family of vectors.** Let
`ν : N → Module.Dual 𝕜 X` be a family of functionals on a finite-dimensional normed space `X`,
indexed by a manifold `N`, and `x : F → N` a map from a normed space, such that `x` is `C^1` at
`y` and every value `t ↦ ν t ξ` is `C^1` at `x y`. If `c : F → X` is differentiable at `y`, the
derivative of `z ↦ ν (x z) (c z)` at `y` in the direction `v` is
`ν (x y) (dc_y v) + d(ν · (c y))_{x y} (dx_y v)`. -/
theorem fderiv_dual_comp_apply [CompleteSpace 𝕜] {X : Type*} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] [FiniteDimensional 𝕜 X] {ν : N → Module.Dual 𝕜 X}
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {x : F → N} {y : F}
    (hν : ∀ ξ, ContMDiffAt J 𝓘(𝕜) 1 (fun t ↦ ν t ξ) (x y)) (hx : ContMDiffAt 𝓘(𝕜, F) J 1 x y)
    {c : F → X} (hc : DifferentiableAt 𝕜 c y) (v : F) :
    fderiv 𝕜 (fun z ↦ ν (x z) (c z)) y v =
      ν (x y) (fderiv 𝕜 c y v) +
        mvfderiv J (fun t ↦ ν t (c y)) (x y) (mfderiv 𝓘(𝕜, F) J x y v) := by
  -- Read `ν ∘ x` as a family of continuous linear maps, and differentiate the evaluation.
  set L : F → X →L[𝕜] 𝕜 := fun z ↦ LinearMap.toContinuousLinearMap (ν (x z))
  have hν' : ContMDiffAt J 𝓘(𝕜, X →L[𝕜] 𝕜) 1
      (fun t ↦ LinearMap.toContinuousLinearMap (ν t)) (x y) :=
    TauCeti.contMDiffAt_clm_apply.2 fun ξ ↦ by simpa using hν ξ
  have hLd : DifferentiableAt 𝕜 L y :=
    (contMDiffAt_iff_contDiffAt.1 (hν'.comp y hx)).differentiableAt one_ne_zero
  have h1 : (fun z ↦ ν (x z) (c z)) = fun z ↦ L z (c z) := by simp [L]
  have h2 : (fun z ↦ ν (x z) (c y)) = fun z ↦ L z (c y) := by simp [L]
  have hchain : mvfderiv J (fun t ↦ ν t (c y)) (x y) (mfderiv 𝓘(𝕜, F) J x y v) =
      fderiv 𝕜 (fun z ↦ L z (c y)) y v := by
    rw [← h2, ← mvfderiv_comp_apply y ((hν (c y)).mdifferentiableAt one_ne_zero)
      (hx.mdifferentiableAt one_ne_zero) v]
    exact TauCeti.mvfderiv_eq_fderiv_apply _ y v
  rw [hchain, h1, fderiv_clm_apply hLd hc, fderiv_clm_apply hLd (differentiableAt_const (c y))]
  simp [L]

end SymplecticGeometry

end
