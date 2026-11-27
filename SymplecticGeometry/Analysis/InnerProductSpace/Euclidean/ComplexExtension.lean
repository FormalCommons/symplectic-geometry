/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Algebra.Module.Multilinear.Basic
public import TauCeti.Analysis.InnerProductSpace.Euclidean.Complex
public import TauCeti.LinearAlgebra.TotallyReal.Basic
public import TauCeti.LinearAlgebra.TotallyReal.Euclidean

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
* `ContinuousMultilinearMap.eq_zero_of_map_update_I_smul`: a real-multilinear map on `ℂⁿ` that
  commutes with multiplication by `i` in each argument and vanishes on tuples of real points is
  zero.

Along the way, `TauCeti.complexEuclideanEquivRealProd_I_smul` and
`TauCeti.I_smul_complexEuclideanEquivRealProd_symm` say how multiplication by `i` acts on real
and imaginary parts, and `TauCeti.norm_complexEuclideanEquivRealProd_fst_le`,
`TauCeti.norm_complexEuclideanEquivRealProd_snd_le` bound their norms by that of the point, and
`TauCeti.norm_complexEuclideanEquivRealProd_symm_mk_zero` and
`TauCeti.norm_complexEuclideanEquivRealProd_symm_zero_mk` give the norms of the points `x + i 0`
and `0 + i y`. Finally `TauCeti.complexEuclideanEquivRealProd_snd_eq_zero_iff` says that the
points with imaginary part `0` are those of Tau Ceti's `TauCeti.realSubspace`,
`TauCeti.complexEuclideanEquivRealProd_symm_fst_zero_of_snd_eq_zero` that such a point is the
point `x + i 0` of its real part `x`, and
`TauCeti.complexEuclideanEquivRealProd_sumEquivProd_symm_snd_eq_zero_iff` reads this through
`EuclideanSpace.sumEquivProd` as the vanishing of the imaginary parts of all coordinates.

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

/-- Multiplication by `i` on `ℂⁿ` sends `x + i y` to `-y + i x`. -/
theorem _root_.TauCeti.I_smul_complexEuclideanEquivRealProd_symm
    (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    Complex.I • (complexEuclideanEquivRealProd ι).symm p =
      (complexEuclideanEquivRealProd ι).symm (-p.2, p.1) := by
  ext i
  simp
  linear_combination (↑(p.2.ofLp i) : ℂ) * Complex.I_sq

/-- The real part of a point of `ℂⁿ` has norm at most the norm of the point. -/
theorem _root_.TauCeti.norm_complexEuclideanEquivRealProd_fst_le (z : EuclideanSpace ℂ ι) :
    ‖(complexEuclideanEquivRealProd ι z).1‖ ≤ ‖z‖ := by
  have h := norm_complexEuclideanEquivRealProd_symm_sq (complexEuclideanEquivRealProd ι z)
  rw [ContinuousLinearEquiv.symm_apply_apply] at h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1
    (h ▸ le_add_of_nonneg_right (sq_nonneg _))

/-- The imaginary part of a point of `ℂⁿ` has norm at most the norm of the point. -/
theorem _root_.TauCeti.norm_complexEuclideanEquivRealProd_snd_le (z : EuclideanSpace ℂ ι) :
    ‖(complexEuclideanEquivRealProd ι z).2‖ ≤ ‖z‖ := by
  have h := norm_complexEuclideanEquivRealProd_symm_sq (complexEuclideanEquivRealProd ι z)
  rw [ContinuousLinearEquiv.symm_apply_apply] at h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1
    (h ▸ le_add_of_nonneg_left (sq_nonneg _))

/-- The real point `x + i 0` of `ℂⁿ` has the norm of `x`. -/
@[simp]
theorem _root_.TauCeti.norm_complexEuclideanEquivRealProd_symm_mk_zero
    (x : EuclideanSpace ℝ ι) : ‖(complexEuclideanEquivRealProd ι).symm (x, 0)‖ = ‖x‖ := by
  have h := norm_complexEuclideanEquivRealProd_symm_sq (ι := ι) (x, 0)
  rw [norm_zero, zero_pow two_ne_zero, add_zero] at h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

/-- The purely imaginary point `0 + i y` of `ℂⁿ` has the norm of `y`. -/
@[simp]
theorem _root_.TauCeti.norm_complexEuclideanEquivRealProd_symm_zero_mk
    (y : EuclideanSpace ℝ ι) : ‖(complexEuclideanEquivRealProd ι).symm (0, y)‖ = ‖y‖ := by
  have h := norm_complexEuclideanEquivRealProd_symm_sq (ι := ι) (0, y)
  rw [norm_zero, zero_pow two_ne_zero, zero_add] at h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

/-- A point of `ℂⁿ` has imaginary part `0` exactly when it lies in the real subspace `ℝⁿ`. -/
theorem _root_.TauCeti.complexEuclideanEquivRealProd_snd_eq_zero_iff {z : EuclideanSpace ℂ ι} :
    (complexEuclideanEquivRealProd ι z).2 = 0 ↔ z ∈ realSubspace ι := by
  simp [PiLp.ext_iff]

/-- A point `z` of `ℂⁿ` with imaginary part `0` is the point `x + i 0` of its real part `x`. -/
theorem _root_.TauCeti.complexEuclideanEquivRealProd_symm_fst_zero_of_snd_eq_zero
    {z : EuclideanSpace ℂ ι} (hz : (complexEuclideanEquivRealProd ι z).2 = 0) :
    (complexEuclideanEquivRealProd ι).symm ((complexEuclideanEquivRealProd ι z).1, 0) = z := by
  rw [← hz]
  simp

/-- The point of `EuclideanSpace ℂ (ι ⊕ κ)` that corresponds to `p = (z, w)` has imaginary part
`0` exactly when all coordinates of `z` and of `w` are real. -/
theorem _root_.TauCeti.complexEuclideanEquivRealProd_sumEquivProd_symm_snd_eq_zero_iff
    {κ : Type*} [Fintype κ] {p : EuclideanSpace ℂ ι × EuclideanSpace ℂ κ} :
    (complexEuclideanEquivRealProd _ (EuclideanSpace.sumEquivProd.symm p)).2 = 0 ↔
      (∀ i, (p.1 i).im = 0) ∧ ∀ j, (p.2 j).im = 0 := by
  simp [PiLp.ext_iff]

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

namespace ContinuousMultilinearMap

variable {ι : Type*} [Fintype ι] {κ : Type*} [Finite κ] [DecidableEq κ]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- A real-multilinear map on `ℂⁿ` with values in a complex normed space that commutes with
multiplication by `i` in each argument, and vanishes when all its arguments are real points
`x + i 0`, is zero. This is the multilinear form of
`ContinuousLinearMap.complexExtension_unique`. -/
theorem eq_zero_of_map_update_I_smul
    {P : ContinuousMultilinearMap ℝ (fun _ : κ ↦ EuclideanSpace ℂ ι) F}
    (hI : ∀ m i v, P (Function.update m i (Complex.I • v)) =
      Complex.I • P (Function.update m i v))
    (hre : ∀ x : κ → EuclideanSpace ℝ ι,
      P (fun i ↦ (complexEuclideanEquivRealProd ι).symm (x i, 0)) = 0) :
    P = 0 := by
  have := Fintype.ofFinite κ
  set e := complexEuclideanEquivRealProd ι
  -- Induction on a set of arguments outside which all arguments are real.
  suffices h : ∀ S : Finset κ, ∀ m : κ → EuclideanSpace ℂ ι, (∀ i ∉ S, (e (m i)).2 = 0) →
      P m = 0 by
    ext m
    exact h Finset.univ m (by simp)
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro m hm
    have hm' : m = fun i ↦ e.symm ((e (m i)).1, 0) := by
      funext i
      rw [← hm i (Finset.notMem_empty i)]
      simp
    rw [hm', hre]
  | insert i S hi ih =>
    intro m hm
    -- In the argument `i`, `P` is complex linear and vanishes on the real points.
    have hg : P.toContinuousLinearMap m i = 0 := by
      refine (ContinuousLinearMap.complexExtension_unique 0 (hI m i) fun x ↦ ?_).trans
        (ContinuousLinearMap.complexExtension ι F).map_zero
      refine (P.toContinuousLinearMap_apply m i _).trans (ih _ fun j hj ↦ ?_)
      rcases eq_or_ne j i with rfl | hji
      · simp [e]
      · rw [Function.update_of_ne hji]
        exact hm j (by simp [hji, hj])
    simpa using congr($hg (m i))

end ContinuousMultilinearMap
