/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
public import TauCeti.Geometry.Manifold.ContMDiffMap.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import SymplecticGeometry.Geometry.Manifold.ContMDiffMap.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
import TauCeti.Geometry.Manifold.DifferentialForm.ExtDeriv

/-!
# Smooth forms: bilinear forms of two-forms, multiplication by smooth functions, `0`-forms

Tau Ceti's `TauCeti.SmoothForm.bilinFormAt` reads the value at `x` of a real smooth two-form
`σ` on `M` as a bilinear form `σ_x` on the tangent space `T_x M`. This file shows that the map
`σ ↦ σ_x` is compatible with the module structure of the smooth two-forms: it sends sums,
real multiples, zero, negatives and differences of two-forms to the same operations on their
bilinear forms. All these lemmas are `@[simp]`.

The same family exists for the two-forms on a vector bundle of this library, in
`SymplecticGeometry/Geometry/Manifold/VectorBundle/Symplectic/Basic.lean`
(`SymplecticGeometry.ContMDiffTwoForm.bilinFormAt_add` and its neighbours).

The file also gives Tau Ceti's multiplication `TauCeti.SmoothForm.funSMulₗ g` of smooth forms by
a smooth real function `g` its behaviour in `g`: it is additive in `g`, the constant function `c`
acts as the scalar `c` (so `1` acts as the identity), and it commutes with pullback along a
smooth map `f`, where `g` becomes `g ∘ f`. The last is the smooth-form version of Tau Ceti's
`TauCeti.mpullback_fun_smul` for rough forms, from which it follows. The chain rule
`TauCeti.SmoothForm.mextDerivₗ_ofFunction_comp_of_hasDerivAt` writes the differential of
`g ∘ f` as `g' ∘ f` times the differential of `f`, by Tau Ceti's
`TauCeti.mextDeriv_ofFunction_comp_of_hasDerivAt`. These lemmas let proofs
about smooth forms stay with smooth forms instead of passing to the underlying rough forms.

Finally, the smooth `F`-valued `0`-forms are the smooth `F`-valued functions:
`TauCeti.SmoothForm.ofFunctionEquiv` is the linear equivalence that sends a function `f` to
Tau Ceti's `0`-form `TauCeti.SmoothForm.ofFunction f`, and whose inverse reads a `0`-form `α` as
the function `x ↦ α x 0`, which is smooth by `TauCeti.SmoothForm.contMDiff_apply_zero`. Its
construction follows that of Tau Ceti's `TauCeti.kerDelBarZeroEquiv`, which identifies the
`∂̄`-closed smooth `0`-forms with the holomorphic functions.

## Main results

* `TauCeti.SmoothForm.bilinFormAt_add`, `TauCeti.SmoothForm.bilinFormAt_smul`,
  `TauCeti.SmoothForm.bilinFormAt_zero`, `TauCeti.SmoothForm.bilinFormAt_neg`,
  `TauCeti.SmoothForm.bilinFormAt_sub`.
* `TauCeti.SmoothForm.funSMulₗ_add`, `TauCeti.SmoothForm.funSMulₗ_const`,
  `TauCeti.SmoothForm.funSMulₗ_one`, `TauCeti.SmoothForm.mpullback_funSMulₗ`.
* `TauCeti.SmoothForm.mextDerivₗ_ofFunction_comp_of_hasDerivAt`: `d (g ∘ f) = (g' ∘ f) df`.
* `TauCeti.SmoothForm.ofFunctionEquiv`, with `ofFunctionEquiv_apply`,
  `coe_ofFunctionEquiv_symm` and `ofFunctionEquiv_symm_apply`.
-/

public section

open scoped ContDiff Manifold

namespace TauCeti.SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H} [IsManifold I 1 M]

/-- The bilinear form of a sum of two-forms is the sum of their bilinear forms. -/
@[simp]
theorem bilinFormAt_add (σ τ : SmoothForm I M ℝ 2) (x : M) :
    (σ + τ).bilinFormAt x = σ.bilinFormAt x + τ.bilinFormAt x := by
  ext v w
  simp [SmoothBundleForm.eval₂_apply]

/-- The bilinear form of a real multiple of a two-form is the same multiple of its bilinear
form. -/
@[simp]
theorem bilinFormAt_smul (c : ℝ) (σ : SmoothForm I M ℝ 2) (x : M) :
    (c • σ).bilinFormAt x = c • σ.bilinFormAt x := by
  ext v w
  simp [SmoothBundleForm.eval₂_apply]

/-- The bilinear form of the zero two-form is zero. -/
@[simp]
theorem bilinFormAt_zero (x : M) : (0 : SmoothForm I M ℝ 2).bilinFormAt x = 0 := by
  ext v w
  simp [SmoothBundleForm.eval₂_apply]

/-- The bilinear form of the negative of a two-form is the negative of its bilinear form. -/
@[simp]
theorem bilinFormAt_neg (σ : SmoothForm I M ℝ 2) (x : M) :
    (-σ).bilinFormAt x = -σ.bilinFormAt x := by
  ext v w
  simp [SmoothBundleForm.eval₂_apply]

/-- The bilinear form of a difference of two-forms is the difference of their bilinear forms. -/
@[simp]
theorem bilinFormAt_sub (σ τ : SmoothForm I M ℝ 2) (x : M) :
    (σ - τ).bilinFormAt x = σ.bilinFormAt x - τ.bilinFormAt x := by
  ext v w
  simp [SmoothBundleForm.eval₂_apply]


section FunSMul

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- Multiplication of smooth forms by smooth functions is additive in the function. -/
@[simp]
theorem funSMulₗ_add (f g : C^∞⟮I, M; ℝ⟯) (φ : SmoothForm I M F k) :
    funSMulₗ (f + g) φ = funSMulₗ f φ + funSMulₗ g φ := by
  ext1
  simp [add_smul]

/-- Multiplying a smooth form by the zero function gives the zero form. -/
@[simp]
theorem funSMulₗ_zero (φ : SmoothForm I M F k) : funSMulₗ 0 φ = 0 := by
  ext1
  simp

/-- Multiplying a smooth form by the constant function `c` is multiplying it by the scalar `c`. -/
@[simp]
theorem funSMulₗ_const (c : ℝ) (φ : SmoothForm I M F k) :
    funSMulₗ (ContMDiffMap.const c) φ = c • φ := by
  ext1
  simp

/-- Multiplying a smooth form by the constant function `1` leaves it unchanged. -/
@[simp]
theorem funSMulₗ_one (φ : SmoothForm I M F k) : funSMulₗ 1 φ = φ := by
  ext1
  simp

/-- Multiplying the `0`-form of a smooth function `h` by a smooth function `g` gives the `0`-form
of the product `g * h`. -/
@[simp]
theorem funSMulₗ_ofFunction (g h : C^∞⟮I, M; ℝ⟯) :
    funSMulₗ g (ofFunction h) = ofFunction (g * h) := by
  ext x v
  simp [RoughForm.ofFunction_apply]

variable {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  [TopologicalSpace M'] [ChartedSpace H' M'] {I' : ModelWithCorners ℝ E' H'} [IsManifold I' 1 M']

/-- The pullback of `g φ` along a smooth map `f` is `(g ∘ f) (f^* φ)`: the smooth-form version of
`TauCeti.mpullback_fun_smul`. -/
@[simp]
theorem mpullback_funSMulₗ (f : M → M') (hf : ContMDiff I I' ∞ f) (g : C^∞⟮I', M'; ℝ⟯)
    (φ : SmoothForm I' M' F k) :
    mpullback f hf (funSMulₗ g φ) = funSMulₗ (g.comp ⟨f, hf⟩) (mpullback f hf φ) := by
  ext1
  simp [TauCeti.mpullback_fun_smul]

/-- **The chain rule for smooth functions read as `0`-forms.** If `h = g ∘ f` for a smooth
function `f` and a function `g : ℝ → ℝ` with derivative `g' x` at `f x` for every `x`, then
`d h = g' • d f`. -/
theorem mextDerivₗ_ofFunction_comp_of_hasDerivAt [IsManifold I 2 M] {g : ℝ → ℝ}
    {f h g' : C^∞⟮I, M; ℝ⟯} (hh : ∀ x, h x = g (f x)) (hg : ∀ x, HasDerivAt g (g' x) (f x)) :
    mextDerivₗ I 0 (ofFunction h) = funSMulₗ g' (mextDerivₗ I 0 (ofFunction f)) := by
  refine Subtype.ext (funext fun x ↦ ?_)
  have hfun : (h : M → ℝ) = fun y ↦ g (f y) := funext hh
  rw [coe_funSMulₗ, mextDerivₗ_apply, mextDerivₗ_apply, coe_ofFunction, coe_ofFunction, hfun]
  exact mextDeriv_ofFunction_comp_of_hasDerivAt
    (f.contMDiff.mdifferentiableAt (by simp)) (hg x)

end FunSMul

section ZeroForm

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The smooth `F`-valued functions on `M` are the smooth `F`-valued `0`-forms: a function `f` is
sent to its `0`-form `TauCeti.SmoothForm.ofFunction f`, and a `0`-form `α` to its value
`x ↦ α x 0` on the empty tuple of tangent vectors. -/
noncomputable def ofFunctionEquiv : C^∞⟮I, M; 𝓘(ℝ, F), F⟯ ≃ₗ[ℝ] SmoothForm I M F 0 :=
  LinearEquiv.symm
    { toFun α := (⟨fun x ↦ α.val x 0, contMDiff_apply_zero α⟩ : C^∞⟮I, M; 𝓘(ℝ, F), F⟯)
      invFun := ofFunction
      map_add' _ _ := rfl
      map_smul' _ _ := rfl
      left_inv α := Subtype.ext <| (coe_ofFunction _).trans <|
        (congrArg (RoughForm.ofFunction I) (ContMDiffMap.coeFn_mk _ _)).trans
          (RoughForm.eq_ofFunction (I := I) (F := F) α.val).symm
      right_inv f := ContMDiffMap.ext fun x ↦ congrFun (ofFunction_apply_zero f) x }

/-- `ofFunctionEquiv` sends a smooth function to its `0`-form. -/
@[simp]
theorem ofFunctionEquiv_apply (f : C^∞⟮I, M; 𝓘(ℝ, F), F⟯) : ofFunctionEquiv f = ofFunction f :=
  (rfl)

/-- Reading the `0`-form of a smooth function `f` back as a function gives `f`. -/
@[simp]
theorem ofFunctionEquiv_symm_ofFunction (f : C^∞⟮I, M; 𝓘(ℝ, F), F⟯) :
    ofFunctionEquiv.symm (ofFunction f) = f :=
  ofFunctionEquiv.symm_apply_apply f

/-- The `0`-form of the function of a smooth `0`-form `α` is `α`. -/
@[simp]
theorem ofFunction_ofFunctionEquiv_symm (α : SmoothForm I M F 0) :
    ofFunction (ofFunctionEquiv.symm α) = α :=
  ofFunctionEquiv.apply_symm_apply α

/-- The function of a smooth `0`-form `α` is `x ↦ α x 0`, the value of `α x` on the empty
tuple. -/
@[simp]
theorem coe_ofFunctionEquiv_symm (α : SmoothForm I M F 0) :
    ⇑(ofFunctionEquiv.symm α) = fun x ↦ α.val x 0 :=
  (rfl)

/-- The function of a smooth `0`-form `α` takes at `x` the value of `α x` on the empty tuple. -/
theorem ofFunctionEquiv_symm_apply (α : SmoothForm I M F 0) (x : M) :
    ofFunctionEquiv.symm α x = α.val x 0 :=
  (rfl)

end ZeroForm

end TauCeti.SmoothForm

end
