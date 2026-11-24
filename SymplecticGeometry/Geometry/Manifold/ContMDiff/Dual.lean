/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SMul
public import Mathlib.LinearAlgebra.Dual.Lemmas

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
`t ↦ f (x t)`.

## Main results

* `contMDiff_dual_apply_of_span_eq_top`: if `t ↦ g (x t)` is `C^n` for every `g` of a set `s`
  that spans the dual space, then `t ↦ f (x t)` is `C^n` for every linear functional `f`.
* `contMDiff_dual_apply_of_separating`: the same for a finite-dimensional `X` and a set `s` of
  functionals such that every nonzero vector has a functional of `s` that does not vanish on it.
* `contMDiff_linearMap_comp_of_dual`: for a finite-dimensional `X`, if `t ↦ g (x t)` is `C^n`
  for every linear functional `g`, then `f ∘ x` is `C^n` for every linear map `f` from `X` to a
  normed space.
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

end SymplecticGeometry

end
