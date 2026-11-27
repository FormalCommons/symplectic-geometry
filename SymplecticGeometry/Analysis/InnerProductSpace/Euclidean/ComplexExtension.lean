/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Analysis.InnerProductSpace.Euclidean.Complex
public import TauCeti.LinearAlgebra.TotallyReal.Basic

import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-!
# The complex-linear extension of a real map from `ℝⁿ`

Let `F` be a complex normed space. A real-linear map `f : ℝⁿ → F` extends uniquely to a
complex-linear map `ℂⁿ → F`, namely `x + i y ↦ f x + i f y`, where `x + i y` is the splitting of a
point of `ℂⁿ` into its real and imaginary parts (Tau Ceti's
`TauCeti.complexEuclideanEquivRealProd`). This file defines this extension, as a real continuous
linear map in `f`, and gives its basic properties.

## Main definitions

* `ContinuousLinearMap.complexExtension`: the map `f ↦ (x + i y ↦ f x + i f y)` from
  `EuclideanSpace ℝ ι →L[ℝ] F` to `EuclideanSpace ℂ ι →L[ℝ] F`.

## Main results

* `ContinuousLinearMap.complexExtension_apply`: the formula `f x + i f y`.
* `ContinuousLinearMap.complexExtension_apply_smul`: the extension is complex linear.
* `ContinuousLinearMap.complexExtension_unique`: it is the only real-linear map that commutes
  with multiplication by `i` and agrees with `f` on the real points.
* `ContinuousLinearMap.complexExtension_apply_symm_real`: it restricts to `f` on the real points.
* `ContinuousLinearMap.comp_complexExtension`: a real-linear map that commutes with
  multiplication by `i` commutes with the extension.
* `ContinuousLinearMap.complexExtension_injective`: the extension of an injective map whose image
  is totally real (Tau Ceti's `TauCeti.IsTotallyReal`) is injective.

## References

* D. Huybrechts, *Complex Geometry: An Introduction*, Springer (2005), §1.2 (complexification
  of real vector spaces and of linear maps).
-/

public section

noncomputable section

open TauCeti

namespace ContinuousLinearMap

variable {ι : Type*} [Fintype ι] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]

variable (ι F) in
/-- The complex-linear extension `x + i y ↦ f x + i f y` of a real-linear map `f : ℝⁿ → F` to
`ℂⁿ`, for a complex normed space `F`, as a real continuous linear map in `f`. Here `x` and `y`
are the real and imaginary parts of a point of `ℂⁿ`. -/
def complexExtension : (EuclideanSpace ℝ ι →L[ℝ] F) →L[ℝ] (EuclideanSpace ℂ ι →L[ℝ] F) :=
  precomp F ((fst ℝ _ _).comp (complexEuclideanEquivRealProd ι).toContinuousLinearMap) +
    (Complex.I • ContinuousLinearMap.id ℝ (EuclideanSpace ℂ ι →L[ℝ] F)).comp
      (precomp F ((snd ℝ _ _).comp (complexEuclideanEquivRealProd ι).toContinuousLinearMap))

/-- The complex-linear extension of `f` sends `z` to `f x + i f y`, where `(x, y)` are the real
and imaginary parts of `z`. -/
theorem complexExtension_apply (f : EuclideanSpace ℝ ι →L[ℝ] F) (z : EuclideanSpace ℂ ι) :
    complexExtension ι F f z = f (complexEuclideanEquivRealProd ι z).1 +
      Complex.I • f (complexEuclideanEquivRealProd ι z).2 :=
  (rfl)

/-- The complex-linear extension sends `x + i y` to `f x + i f y`. -/
@[simp]
theorem complexExtension_apply_symm (f : EuclideanSpace ℝ ι →L[ℝ] F)
    (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    complexExtension ι F f ((complexEuclideanEquivRealProd ι).symm p) =
      f p.1 + Complex.I • f p.2 := by
  rw [complexExtension_apply, ContinuousLinearEquiv.apply_symm_apply]

/-- On the real points `x + i 0` of `ℂⁿ`, the complex-linear extension of `f` is `f`. -/
theorem complexExtension_apply_symm_real (f : EuclideanSpace ℝ ι →L[ℝ] F)
    (x : EuclideanSpace ℝ ι) :
    complexExtension ι F f ((complexEuclideanEquivRealProd ι).symm (x, 0)) = f x := by
  simp

/-- Multiplication by `i` on `ℂⁿ` sends `x + i y` to `-y + i x`. -/
theorem _root_.TauCeti.complexEuclideanEquivRealProd_I_smul (z : EuclideanSpace ℂ ι) :
    complexEuclideanEquivRealProd ι (Complex.I • z) =
      (-(complexEuclideanEquivRealProd ι z).2, (complexEuclideanEquivRealProd ι z).1) := by
  ext i <;> simp

/-- The complex-linear extension of `f` commutes with multiplication by `i`. -/
theorem complexExtension_apply_I_smul (f : EuclideanSpace ℝ ι →L[ℝ] F)
    (z : EuclideanSpace ℂ ι) :
    complexExtension ι F f (Complex.I • z) = Complex.I • complexExtension ι F f z := by
  rw [complexExtension_apply, complexExtension_apply, complexEuclideanEquivRealProd_I_smul,
    map_neg, smul_add, smul_smul, Complex.I_mul_I, neg_one_smul, add_comm]

/-- The complex-linear extension of `f` is complex linear. -/
@[simp]
theorem complexExtension_apply_smul (f : EuclideanSpace ℝ ι →L[ℝ] F) (c : ℂ)
    (z : EuclideanSpace ℂ ι) :
    complexExtension ι F f (c • z) = c • complexExtension ι F f z :=
  (complexExtension ι F f).toLinearMap.map_smul_of_map_I_smul (complexExtension_apply_I_smul f) c z

/-- The complex-linear extension of `f` is the only real-linear map `ℂⁿ → F` that commutes with
multiplication by `i` and agrees with `f` on the real points `x + i 0`. -/
theorem complexExtension_unique (f : EuclideanSpace ℝ ι →L[ℝ] F)
    {g : EuclideanSpace ℂ ι →L[ℝ] F} (hg : ∀ z, g (Complex.I • z) = Complex.I • g z)
    (hgf : ∀ x, g ((complexEuclideanEquivRealProd ι).symm (x, 0)) = f x) :
    g = complexExtension ι F f := by
  ext z
  obtain ⟨p, rfl⟩ := (complexEuclideanEquivRealProd ι).symm.surjective z
  -- Split `x + i y` as `(x + i 0) + i (y + i 0)`.
  have hp : (complexEuclideanEquivRealProd ι).symm p =
      (complexEuclideanEquivRealProd ι).symm (p.1, 0) +
        Complex.I • (complexEuclideanEquivRealProd ι).symm (p.2, 0) := by
    apply (complexEuclideanEquivRealProd ι).injective
    simp [complexEuclideanEquivRealProd_I_smul]
  rw [complexExtension_apply_symm, hp, map_add, hg, hgf, hgf]

/-- A real-linear map `T : F → G` between complex normed spaces that commutes with multiplication
by `i` commutes with the complex-linear extension: `T ∘ f` extends to `T` composed with the
extension of `f`. -/
theorem comp_complexExtension (T : F →L[ℝ] G) (hT : ∀ v, T (Complex.I • v) = Complex.I • T v)
    (f : EuclideanSpace ℝ ι →L[ℝ] F) :
    T.comp (complexExtension ι F f) = complexExtension ι G (T.comp f) := by
  ext z
  simp [complexExtension_apply, hT]

/-- The complex-linear extension of an injective real-linear map `f : ℝⁿ → F` whose image is
totally real, that is meets its image under multiplication by `i` only in `0`, is injective. -/
theorem complexExtension_injective {f : EuclideanSpace ℝ ι →L[ℝ] F}
    (hf : Function.Injective f)
    (hfR : IsTotallyReal ((LinearMap.lsmul ℂ F Complex.I).restrictScalars ℝ)
      (LinearMap.range f.toLinearMap)) :
    Function.Injective (complexExtension ι F f) := by
  refine (injective_iff_map_eq_zero _).2 fun z hz ↦ ?_
  set p := complexEuclideanEquivRealProd ι z
  rw [complexExtension_apply] at hz
  -- `f x = -i f y` lies in the image and in its `i`-image, so it vanishes, and then so does `f y`.
  have h₁ : f p.1 = 0 := Submodule.disjoint_def.1 hfR.disjoint _ ⟨p.1, rfl⟩
    ⟨f (-p.2), ⟨-p.2, rfl⟩, by simpa using (eq_neg_of_add_eq_zero_left hz).symm⟩
  have h₂ : f p.2 = 0 := by
    rw [h₁, zero_add, smul_eq_zero] at hz
    exact hz.resolve_left Complex.I_ne_zero
  apply (complexEuclideanEquivRealProd ι).injective
  rw [map_zero]
  exact Prod.ext (hf (h₁.trans (map_zero f).symm)) (hf (h₂.trans (map_zero f).symm))

end ContinuousLinearMap
