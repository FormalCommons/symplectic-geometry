/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
import SymplecticGeometry.Geometry.Manifold.Diffeomorph.FDeriv
import TauCeti.Geometry.Manifold.Diffeomorph.NormedSpace

/-!
# Holonomic approximation: transport of a formal section along a diffeomorphism

In the coordinates of `SymplecticGeometry.Analysis.Calculus.HolonomicApproximation.Basic`,
`D = (Fin m → ℝ) × (Fin k → ℝ)`, a vector `w : D` lies in the *directions* `J ⊆ Fin m` when
`∀ i ∉ J, w.1 i = 0`: it has no core component outside `J`, and any transverse component. A formal
section `(f, G)` is holonomic in the directions `J` at `x` when `fderiv ℝ f x w = G x w` for
every such `w`.

The induction over the directions of a cube (the `Cube.lean` section of the design of the
h-principle part) first approximates in the directions `J'`, by a diffeotopy whose final map `Φ`
keeps the core coordinates outside `J'`, and then straightens the displaced cube `Φ '' Q` by
pulling the problem back along `Φ`. This file proves what that transport needs:

* `fderiv ℝ Φ x` and `fderiv ℝ Φ.symm y` send vectors in the directions `J ⊇ J'` to vectors in
  the directions `J`;
* the pulled-back formal section `(f ∘ Φ, x ↦ G (Φ x) ∘L fderiv ℝ Φ x)` is smooth when `(f, G)`
  is, and holonomic in the directions `J` at `x` when `(f, G)` is so at `Φ x`;
* an approximation `f'` of the pulled-back section gives the approximation `f' ∘ Φ.symm` of
  `(f, G)`, whose error on `w` is the pulled-back error on `fderiv ℝ Φ.symm y w`; so it is at most
  `ε * L * ‖w‖` when the pulled-back error is at most `ε` on vectors in the directions `J` and
  `‖fderiv ℝ Φ.symm y‖ ≤ L`.

The facts that hold for every diffeomorphism of a normed space are in
`SymplecticGeometry.Geometry.Manifold.Diffeomorph.FDeriv`: the pulled-back `G` is smooth by
`Diffeomorph.contDiff_clm_comp_fderiv` (and `f ∘ Φ` by `ContDiff.comp`), and the error of
`f' ∘ Φ.symm` is rewritten by `Diffeomorph.fderiv_comp_symm_sub_apply`. The constant `L`, with
`Φ` also `L`-Lipschitz, is
`Diffeomorph.exists_lipschitzWith_and_norm_fderiv_symm_le` of
`SymplecticGeometry.Geometry.Manifold.Diffeomorph.CompactSupport`. The pulled-back section is
written out rather than defined; it is the second component of Tau Ceti's
`ContinuousLinearMap.firstJetPullback` with fibre map the identity and fibre derivative `0`.

## Main results

* `SymplecticGeometry.fderiv_apply_fst_apply_eq_zero`: the derivative of a map keeping the core
  coordinates outside `J'` keeps the directions `J ⊇ J'`.
* `SymplecticGeometry.fderiv_diffeomorph_apply_fst_apply_eq_zero`,
  `SymplecticGeometry.fderiv_diffeomorph_symm_apply_fst_apply_eq_zero`: the same for `Φ` and its
  inverse.
* `SymplecticGeometry.fderiv_comp_diffeomorph_apply_eq`: the pulled-back section is holonomic in
  the directions `J` where `(f, G)` is.
* `SymplecticGeometry.norm_fderiv_comp_diffeomorph_symm_sub_apply_le`: the bound on the
  transported error.

## References

* [Y. Eliashberg and N. Mishachev, *Introduction to the h-Principle*][EliashbergMishachev2002]
-/

public section

open scoped Manifold ContDiff

namespace SymplecticGeometry

variable {m k : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Φ : ((Fin m → ℝ) × (Fin k → ℝ)) ≃ₘ^∞⟮𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ)),
    𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ))⟯ ((Fin m → ℝ) × (Fin k → ℝ))}
  {J J' : Finset (Fin m)}

/-- If a map `g` of `D` keeps the core coordinates outside `J'`, then at a point where it is
differentiable its derivative keeps them as well: `(fderiv ℝ g x w).1 i = w.1 i` for `i ∉ J'`. -/
theorem fderiv_apply_fst_apply_eq {g : (Fin m → ℝ) × (Fin k → ℝ) → (Fin m → ℝ) × (Fin k → ℝ)}
    {x : (Fin m → ℝ) × (Fin k → ℝ)} (hg : DifferentiableAt ℝ g x)
    (hgJ' : ∀ y, ∀ i ∉ J', (g y).1 i = y.1 i) (w : (Fin m → ℝ) × (Fin k → ℝ)) {i : Fin m}
    (hi : i ∉ J') : (fderiv ℝ g x w).1 i = w.1 i := by
  set p : (Fin m → ℝ) × (Fin k → ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℝ _ _)
  have hp : p ∘ g = p := funext fun y ↦ hgJ' y i hi
  have h₁ : HasFDerivAt (p ∘ g) (p.comp (fderiv ℝ g x)) x := p.hasFDerivAt.comp x hg.hasFDerivAt
  rw [hp] at h₁
  simpa [p] using (congrArg (· w) (p.hasFDerivAt.unique h₁)).symm

/-- If a map `g` of `D` keeps the core coordinates outside `J'`, then at a point where it is
differentiable its derivative sends vectors in the directions `J ⊇ J'` to vectors in the
directions `J`. -/
theorem fderiv_apply_fst_apply_eq_zero
    {g : (Fin m → ℝ) × (Fin k → ℝ) → (Fin m → ℝ) × (Fin k → ℝ)}
    {x : (Fin m → ℝ) × (Fin k → ℝ)} (hg : DifferentiableAt ℝ g x)
    (hgJ' : ∀ y, ∀ i ∉ J', (g y).1 i = y.1 i) (hJ : J' ⊆ J) {w : (Fin m → ℝ) × (Fin k → ℝ)}
    (hw : ∀ i ∉ J, w.1 i = 0) : ∀ i ∉ J, (fderiv ℝ g x w).1 i = 0 := fun i hi ↦ by
  rw [fderiv_apply_fst_apply_eq hg hgJ' w fun h ↦ hi (hJ h), hw i hi]

/-- The inverse of a diffeomorphism of `D` that keeps the core coordinates outside `J'` keeps them
too. -/
theorem diffeomorph_symm_apply_fst_apply (hΦ : ∀ x, ∀ i ∉ J', (Φ x).1 i = x.1 i)
    (y : (Fin m → ℝ) × (Fin k → ℝ)) {i : Fin m} (hi : i ∉ J') : (Φ.symm y).1 i = y.1 i := by
  conv_rhs => rw [← Φ.apply_symm_apply y]
  exact (hΦ _ i hi).symm

/-- The derivative of a diffeomorphism of `D` that keeps the core coordinates outside `J'` sends
vectors in the directions `J ⊇ J'` to vectors in the directions `J`. -/
theorem fderiv_diffeomorph_apply_fst_apply_eq_zero (hΦ : ∀ x, ∀ i ∉ J', (Φ x).1 i = x.1 i)
    (hJ : J' ⊆ J) (x : (Fin m → ℝ) × (Fin k → ℝ)) {w : (Fin m → ℝ) × (Fin k → ℝ)}
    (hw : ∀ i ∉ J, w.1 i = 0) : ∀ i ∉ J, (fderiv ℝ Φ x w).1 i = 0 :=
  fderiv_apply_fst_apply_eq_zero (Φ.differentiable (by simp) x) hΦ hJ hw

/-- The derivative of the inverse of a diffeomorphism of `D` that keeps the core coordinates
outside `J'` sends vectors in the directions `J ⊇ J'` to vectors in the directions `J`. -/
theorem fderiv_diffeomorph_symm_apply_fst_apply_eq_zero
    (hΦ : ∀ x, ∀ i ∉ J', (Φ x).1 i = x.1 i) (hJ : J' ⊆ J) (y : (Fin m → ℝ) × (Fin k → ℝ))
    {w : (Fin m → ℝ) × (Fin k → ℝ)} (hw : ∀ i ∉ J, w.1 i = 0) :
    ∀ i ∉ J, (fderiv ℝ Φ.symm y w).1 i = 0 :=
  fderiv_apply_fst_apply_eq_zero (Φ.symm.differentiable (by simp) y)
    (fun y _ hi ↦ diffeomorph_symm_apply_fst_apply hΦ y hi) hJ hw

/-- **The pulled-back section is holonomic.** If `(f, G)` is holonomic in the directions
`J ⊇ J'` at `Φ x`, where `Φ` keeps the core coordinates outside `J'`, then the pulled-back
section `(f ∘ Φ, y ↦ G (Φ y) ∘L fderiv ℝ Φ y)` is holonomic in the directions `J` at `x`. -/
theorem fderiv_comp_diffeomorph_apply_eq {f : (Fin m → ℝ) × (Fin k → ℝ) → F}
    {G : (Fin m → ℝ) × (Fin k → ℝ) → ((Fin m → ℝ) × (Fin k → ℝ)) →L[ℝ] F}
    (hΦ : ∀ x, ∀ i ∉ J', (Φ x).1 i = x.1 i) (hJ : J' ⊆ J) {x : (Fin m → ℝ) × (Fin k → ℝ)}
    (hf : DifferentiableAt ℝ f (Φ x))
    (hfG : ∀ w, (∀ i ∉ J, w.1 i = 0) → fderiv ℝ f (Φ x) w = G (Φ x) w)
    {w : (Fin m → ℝ) × (Fin k → ℝ)} (hw : ∀ i ∉ J, w.1 i = 0) :
    fderiv ℝ (f ∘ Φ) x w = (G (Φ x)).comp (fderiv ℝ Φ x) w := by
  rw [fderiv_comp x hf (Φ.differentiable (by simp) x), ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply,
    hfG _ (fderiv_diffeomorph_apply_fst_apply_eq_zero hΦ hJ x hw)]

/-- **The transported estimate.** If `Φ` keeps the core coordinates outside `J' ⊆ J`, the error
of `f'` against the pulled-back `G (Φ z) ∘L fderiv ℝ Φ z` at `z` is at most `ε * ‖v‖` on vectors
`v` in the directions `J`, and `‖fderiv ℝ Φ.symm (Φ z)‖ ≤ L`, then the error of `f' ∘ Φ.symm`
against `G` at `Φ z` is at most `ε * L * ‖w‖` on vectors `w` in the directions `J`. -/
theorem norm_fderiv_comp_diffeomorph_symm_sub_apply_le {f' : (Fin m → ℝ) × (Fin k → ℝ) → F}
    {G : (Fin m → ℝ) × (Fin k → ℝ) → ((Fin m → ℝ) × (Fin k → ℝ)) →L[ℝ] F}
    (hΦ : ∀ x, ∀ i ∉ J', (Φ x).1 i = x.1 i) (hJ : J' ⊆ J) {z : (Fin m → ℝ) × (Fin k → ℝ)}
    (hf' : DifferentiableAt ℝ f' z) {ε L : ℝ} (hε : 0 ≤ ε)
    (herr : ∀ v, (∀ i ∉ J, v.1 i = 0) →
      ‖(fderiv ℝ f' z - (G (Φ z)).comp (fderiv ℝ Φ z)) v‖ ≤ ε * ‖v‖)
    (hL : ‖fderiv ℝ Φ.symm (Φ z)‖ ≤ L) {w : (Fin m → ℝ) × (Fin k → ℝ)}
    (hw : ∀ i ∉ J, w.1 i = 0) :
    ‖(fderiv ℝ (f' ∘ Φ.symm) (Φ z) - G (Φ z)) w‖ ≤ ε * L * ‖w‖ := by
  rw [Φ.fderiv_comp_symm_sub_apply (by simp) hf' w, mul_assoc]
  refine (herr _ (fderiv_diffeomorph_symm_apply_fst_apply_eq_zero hΦ hJ _ hw)).trans ?_
  gcongr
  exact (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr)

end SymplecticGeometry

end
