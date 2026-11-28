/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
public import TauCeti.Geometry.Manifold.ContMDiffMap.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
import SymplecticGeometry.Geometry.Manifold.ContMDiffMap.Basic
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Basic
import TauCeti.Geometry.Manifold.DifferentialForm.ExtDeriv

/-!
# Smooth forms: values at a point, bilinear forms of two-forms, function multiples, `0`-forms

A smooth bundle-valued form `φ : TauCeti.SmoothBundleForm I F V k` is an element of a submodule
of rough forms, and its value at `x` is `φ.val x`. The file starts with the value at `x` of
the zero form, of a sum, a scalar multiple, a negative, a difference and a finite sum of smooth
forms: `TauCeti.SmoothBundleForm.add_apply` and its neighbours, all `@[simp]`. They spare proofs
the passage through `Submodule.coe_add` and `Pi.add_apply`, and apply to the smooth forms
`TauCeti.SmoothForm` with fixed coefficients as well.

Tau Ceti's `TauCeti.SmoothForm.bilinFormAt` reads the value at `x` of a real smooth two-form
`σ` on `M` as a bilinear form `σ_x` on the tangent space `T_x M`. This file shows that the map
`σ ↦ σ_x` is compatible with the module structure of the smooth two-forms: it sends sums,
real multiples, zero, negatives and differences of two-forms to the same operations on their
bilinear forms. It also sends the pullback `f^* β` along a smooth map `f` to `β_{f x}` composed
with `d_x f` on both sides. All these lemmas are `@[simp]`. Before them,
`TauCeti.SmoothForm.bilinFormAt_def` states the definition of `σ_x`: the bilinear form of the
value `σ x`.

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

A smooth one-form evaluated on a vector field differentiable at `x`, and a smooth two-form
evaluated on two such vector fields, are functions differentiable at `x`
(`TauCeti.SmoothForm.mdifferentiableAt_apply_one`,
`TauCeti.SmoothForm.mdifferentiableAt_apply_two`), by
`TauCeti.RoughForm.mdifferentiableAt_apply_one` and
`TauCeti.RoughForm.mdifferentiableAt_apply_two` for the underlying rough form.

Finally, the smooth `F`-valued `0`-forms are the smooth `F`-valued functions:
`TauCeti.SmoothForm.ofFunctionEquiv` is the linear equivalence that sends a function `f` to
Tau Ceti's `0`-form `TauCeti.SmoothForm.ofFunction f`, and whose inverse reads a `0`-form `α` as
the function `x ↦ α x 0`, which is smooth by `TauCeti.SmoothForm.contMDiff_apply_zero`. Its
construction follows that of Tau Ceti's `TauCeti.kerDelBarZeroEquiv`, which identifies the
`∂̄`-closed smooth `0`-forms with the holomorphic functions.

## Main results

* `TauCeti.SmoothBundleForm.zero_apply`, `TauCeti.SmoothBundleForm.add_apply`,
  `TauCeti.SmoothBundleForm.smul_apply`, `TauCeti.SmoothBundleForm.neg_apply`,
  `TauCeti.SmoothBundleForm.sub_apply`, `TauCeti.SmoothBundleForm.sum_apply`: the value at a
  point of a combination of smooth forms.
* `TauCeti.SmoothForm.bilinFormAt_def`: `σ_x` is the bilinear form of `σ x`.
* `TauCeti.SmoothForm.bilinFormAt_add`, `TauCeti.SmoothForm.bilinFormAt_smul`,
  `TauCeti.SmoothForm.bilinFormAt_zero`, `TauCeti.SmoothForm.bilinFormAt_neg`,
  `TauCeti.SmoothForm.bilinFormAt_sub`.
* `TauCeti.SmoothForm.bilinFormAt_mpullback`: the bilinear form of `f^* β` at `x` is that of `β`
  at `f x` composed with `d_x f` on both sides.
* `TauCeti.SmoothForm.funSMulₗ_add`, `TauCeti.SmoothForm.funSMulₗ_const`,
  `TauCeti.SmoothForm.funSMulₗ_one`, `TauCeti.SmoothForm.mpullback_funSMulₗ`.
* `TauCeti.SmoothForm.mextDerivₗ_ofFunction_comp_of_hasDerivAt`: `d (g ∘ f) = (g' ∘ f) df`.
* `TauCeti.SmoothForm.mdifferentiableAt_apply_one`: a smooth one-form on a vector field
  differentiable at `x` is differentiable at `x`.
* `TauCeti.SmoothForm.mdifferentiableAt_apply_two`: a smooth two-form on two vector fields
  differentiable at `x` is differentiable at `x`.
* `TauCeti.SmoothForm.ofFunctionEquiv`, with `ofFunctionEquiv_apply`,
  `coe_ofFunctionEquiv_symm` and `ofFunctionEquiv_symm_apply`.
* `TauCeti.SmoothForm.ofFunction_zero`, `TauCeti.SmoothForm.ofFunction_add`,
  `TauCeti.SmoothForm.ofFunction_smul`: the `0`-form of the zero function, of a sum and of a real
  multiple of smooth functions.
-/

public section

open scoped ContDiff Manifold

namespace TauCeti.SmoothBundleForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (Bundle.TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)] {k : ℕ}

/-- The value at `x` of the zero form is zero. -/
@[simp]
theorem zero_apply (x : M) : (0 : SmoothBundleForm I F V k).val x = 0 :=
  (rfl)

/-- The value at `x` of a sum of smooth forms is the sum of their values at `x`. -/
@[simp]
theorem add_apply (φ ψ : SmoothBundleForm I F V k) (x : M) :
    (φ + ψ).val x = φ.val x + ψ.val x :=
  (rfl)

/-- The value at `x` of a scalar multiple `c • φ` of a smooth form is `c` times the value of `φ`
at `x`. The scalars `c` act through `ℝ`, so they may be real numbers or integers. -/
@[simp]
theorem smul_apply {S : Type*} [SMul S ℝ] [∀ x, SMul S (TangentSpace I x [⋀^Fin k]→L[ℝ] V x)]
    [IsScalarTower S ℝ (RoughBundleForm I M V k)] (c : S) (φ : SmoothBundleForm I F V k)
    (x : M) : (c • φ).val x = c • φ.val x :=
  (rfl)

/-- The value at `x` of the negative of a smooth form is the negative of its value at `x`. -/
@[simp]
theorem neg_apply (φ : SmoothBundleForm I F V k) (x : M) : (-φ).val x = -φ.val x :=
  (rfl)

/-- The value at `x` of a difference of smooth forms is the difference of their values at `x`. -/
@[simp]
theorem sub_apply (φ ψ : SmoothBundleForm I F V k) (x : M) :
    (φ - ψ).val x = φ.val x - ψ.val x :=
  (rfl)

/-- The value at `x` of a finite sum of smooth forms is the sum of their values at `x`. -/
@[simp]
theorem sum_apply {ι : Type*} (s : Finset ι) (φ : ι → SmoothBundleForm I F V k) (x : M) :
    (∑ i ∈ s, φ i).val x = ∑ i ∈ s, (φ i).val x := by
  rw [Submodule.coe_sum, Finset.sum_apply]

end TauCeti.SmoothBundleForm

namespace TauCeti.SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H} [IsManifold I 1 M]

/-- The bilinear form of a two-form `σ` at `x` is the bilinear form `(v, w) ↦ σ x ![v, w]` of
its value at `x`. -/
theorem bilinFormAt_def (σ : SmoothForm I M ℝ 2) (x : M) :
    σ.bilinFormAt x = MultilinearMap.toBilinMap (σ.val x).toMultilinearMap := by
  ext v w
  simp [SmoothBundleForm.eval₂_apply]

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

section Pullback

variable {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  [TopologicalSpace M'] [ChartedSpace H' M'] {I' : ModelWithCorners ℝ E' H'} [IsManifold I' 1 M']

/-- The bilinear form at `x` of the pullback `f^* β` of a two-form along a smooth map `f` is the
bilinear form of `β` at `f x` composed on both sides with the derivative `d_x f`. -/
@[simp]
theorem bilinFormAt_mpullback {f : M → M'} (hf : ContMDiff I I' ∞ f) (β : SmoothForm I' M' ℝ 2)
    (x : M) :
    (mpullback f hf β).bilinFormAt x = (β.bilinFormAt (f x)).comp
      (mfderiv I I' f x : TangentSpace I x →ₗ[ℝ] _) (mfderiv I I' f x) := by
  refine LinearMap.ext₂ fun v w ↦ ?_
  simp only [LinearMap.BilinForm.comp_apply, bilinFormAt_apply, eval₂_mpullback,
    ContinuousLinearMap.coe_coe]

end Pullback


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

section Evaluation

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Evaluating a smooth one-form `φ` on a vector field `Z` differentiable at `x` gives a function
`y ↦ φ y ![Z y]` differentiable at `x`. -/
theorem mdifferentiableAt_apply_one (φ : SmoothForm I M F 1)
    {Z : (y : M) → TangentSpace I y} {x : M}
    (hZ : MDifferentiableAt I I.tangent (fun y ↦ (Z y : TangentBundle I M)) x) :
    MDifferentiableAt I 𝓘(ℝ, F) (fun y ↦ φ.val y ![Z y]) x :=
  RoughForm.mdifferentiableAt_apply_one (φ.mdifferentiableAt x) hZ

/-- Evaluating a smooth two-form `φ` on two vector fields `A` and `B` differentiable at `x` gives
a function `y ↦ φ y (A y, B y)` differentiable at `x`. -/
theorem mdifferentiableAt_apply_two (φ : SmoothForm I M F 2)
    {A B : (y : M) → TangentSpace I y} {x : M}
    (hA : MDifferentiableAt I I.tangent (fun y ↦ (A y : TangentBundle I M)) x)
    (hB : MDifferentiableAt I I.tangent (fun y ↦ (B y : TangentBundle I M)) x) :
    MDifferentiableAt I 𝓘(ℝ, F) (fun y ↦ φ.val y ![A y, B y]) x :=
  RoughForm.mdifferentiableAt_apply_two (φ.mdifferentiableAt x) hA hB

end Evaluation

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
      left_inv α := (eq_ofFunction α).symm
      right_inv f := ContMDiffMap.ext fun x ↦ congrFun (ofFunction_apply_zero f) x }

/-- `ofFunctionEquiv` sends a smooth function to its `0`-form. -/
@[simp]
theorem ofFunctionEquiv_apply (f : C^∞⟮I, M; 𝓘(ℝ, F), F⟯) : ofFunctionEquiv f = ofFunction f :=
  (rfl)

/-- The `0`-form of the zero function is the zero form. -/
@[simp]
theorem ofFunction_zero : ofFunction (0 : C^∞⟮I, M; 𝓘(ℝ, F), F⟯) = 0 :=
  map_zero ofFunctionEquiv

/-- The `0`-form of a sum of smooth functions is the sum of their `0`-forms. -/
@[simp]
theorem ofFunction_add (f g : C^∞⟮I, M; 𝓘(ℝ, F), F⟯) :
    ofFunction (f + g) = ofFunction f + ofFunction g :=
  map_add ofFunctionEquiv f g

/-- The `0`-form of a real multiple `c • f` of a smooth function is `c` times the `0`-form of
`f`. -/
@[simp]
theorem ofFunction_smul (c : ℝ) (f : C^∞⟮I, M; 𝓘(ℝ, F), F⟯) :
    ofFunction (c • f) = c • ofFunction f :=
  map_smul ofFunctionEquiv c f

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
