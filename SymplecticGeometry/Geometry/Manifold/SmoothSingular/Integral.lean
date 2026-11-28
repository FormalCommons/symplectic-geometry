/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothSingular.Integral

/-!
# Integrals over smooth simplices: locality

Tau Ceti's integral `TauCeti.SmoothSimplex.integral σ φ` of a form `φ` over a smooth singular
simplex `σ` only sees the values of `φ` at points of the image of `σ`, and a map that carries a
simplex need only be differentiable there. This file records:

* `TauCeti.SmoothSimplex.integral_congr`: two forms that agree on the image of `σ` have the same
  integral over `σ`;
* `TauCeti.SmoothSimplex.integral_eq_zero_of_forall_eq_zero`: the integral vanishes when `φ` is
  zero at every point of that image;
* `TauCeti.SmoothSimplex.integral_eq_integral_mpullback_of_eq_comp`: if a simplex `S` is `f ∘ σ`
  and `f` is differentiable at each point of the image of `σ`, then integrating over `S` is
  integrating the pull-back by `f` over `σ`. This is a local form of Tau Ceti's naturality
  `TauCeti.SmoothSimplex.integral_smoothSingularSubcomplexMap_app`, which asks `f` to be smooth
  everywhere; its proof adapts the proof of that lemma.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 18.
-/

public section

open MeasureTheory Set
open scoped Manifold

namespace TauCeti.SmoothSimplex

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℕ}

/-- The integral of a form over a smooth simplex depends only on the values of the form at the
points of the image of the simplex. -/
theorem integral_congr (σ : SmoothSimplex I M p) {φ ψ : RoughForm I M F p}
    (h : ∀ x, φ (σ.toContinuousMap x) = ψ (σ.toContinuousMap x)) :
    σ.integral φ = σ.integral ψ := by
  rw [integral_def, integral_def]
  refine setIntegral_congr_fun (isClosed_fullSimplex p).measurableSet fun x hx ↦ ?_
  have hx' : σ.extension x = σ.toContinuousMap ⟨x, hx⟩ := σ.extension_coe ⟨x, hx⟩
  refine (mpullbackWithin_apply (I := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin p)))
    (I' := I) σ.extension _ φ x _).trans ?_
  refine Eq.trans ?_ (mpullbackWithin_apply (I := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin p)))
    (I' := I) σ.extension _ ψ x _).symm
  rw [hx', h]

/-- The integral of a form over a smooth simplex vanishes if the form is zero at every point of
the image of the simplex. -/
theorem integral_eq_zero_of_forall_eq_zero (σ : SmoothSimplex I M p) {φ : RoughForm I M F p}
    (hφ : ∀ x, φ (σ.toContinuousMap x) = 0) : σ.integral φ = 0 :=
  (σ.integral_congr (ψ := 0) hφ).trans σ.integral_zero

/-- **Local naturality of integration over smooth simplices.** If a smooth simplex `S` of `N` is
the image of a smooth simplex `σ` of `M` under a map `f` that is differentiable at each point of
the image of `σ`, then the integral of a form over `S` is that of its pull-back by `f` over
`σ`. -/
theorem integral_eq_integral_mpullback_of_eq_comp {E' H' : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} {N : Type*}
    [TopologicalSpace N] [ChartedSpace H' N] {f : M → N}
    (σ : SmoothSimplex I M p) (S : SmoothSimplex J N p)
    (hS : ∀ x, S.toContinuousMap x = f (σ.toContinuousMap x))
    (hf : ∀ x, MDifferentiableAt I J f (σ.toContinuousMap x)) (ψ : RoughForm J N F p) :
    S.integral ψ = σ.integral (mpullback I J f ψ) := by
  rw [integral_eq_setIntegral_mpullbackWithin S ψ (g := f ∘ σ.extension) fun x ↦ by
    rw [Function.comp_apply, σ.extension_coe, hS], integral_def]
  refine setIntegral_congr_fun (isClosed_fullSimplex p).measurableSet fun x hx ↦ ?_
  have hfx : MDifferentiableAt I J f (σ.extension x) := σ.extension_coe ⟨x, hx⟩ ▸ hf ⟨x, hx⟩
  rw [mpullbackWithin_comp_at (t := univ)
    ((σ.contMDiffOn_extension x hx).mdifferentiableWithinAt (by simp))
    hfx.mdifferentiableWithinAt (mapsTo_univ _ _)
    (uniqueMDiffWithinAt_iff_uniqueDiffWithinAt.2 (uniqueDiffOn_fullSimplex p x hx)),
    mpullbackWithin_univ]

end TauCeti.SmoothSimplex

end
