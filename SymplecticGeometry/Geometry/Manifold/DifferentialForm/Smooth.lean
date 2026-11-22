/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
public import Mathlib.Geometry.Manifold.VectorBundle.ContinuousAlternatingMap
public import TauCeti.Geometry.Manifold.ContMDiffMap.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import SymplecticGeometry.Geometry.Manifold.ContMDiffMap.Basic

/-!
# Smooth forms: bilinear forms of two-forms, multiplication by smooth functions, evaluation

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
`TauCeti.mpullback_fun_smul` for rough forms, from which it follows. These lemmas let proofs
about smooth forms stay with smooth forms instead of passing to the underlying rough forms.

Finally, Tau Ceti's `TauCeti.SmoothForm.contMDiff_apply` says that evaluating a smooth
two-form along a map on two `C^n` tangent fields gives a `C^n` function; its version at a point,
for tangent fields that are `C^n` only there, is `TauCeti.SmoothForm.contMDiffAt_apply`, with the
same proof.

## Main results

* `TauCeti.SmoothForm.bilinFormAt_add`, `TauCeti.SmoothForm.bilinFormAt_smul`,
  `TauCeti.SmoothForm.bilinFormAt_zero`, `TauCeti.SmoothForm.bilinFormAt_neg`,
  `TauCeti.SmoothForm.bilinFormAt_sub`.
* `TauCeti.SmoothForm.funSMulₗ_add`, `TauCeti.SmoothForm.funSMulₗ_const`,
  `TauCeti.SmoothForm.funSMulₗ_one`, `TauCeti.SmoothForm.mpullback_funSMulₗ`.
* `TauCeti.SmoothForm.contMDiffAt_apply`.
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

end FunSMul

section Evaluation

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]

/-- Evaluating a smooth degree-two form along a map `b` on two tangent fields along `b` that are
`C^n` at `y₀`, as maps into the tangent bundle, gives a function that is `C^n` at `y₀`. This is
the version at a point of Tau Ceti's `TauCeti.SmoothForm.contMDiff_apply`. -/
theorem contMDiffAt_apply {n : WithTop ℕ∞} [ENat.LEInfty n] (form : SmoothForm I M F 2)
    {b : N → M} {y₀ : N} {V W : ∀ y : N, TangentSpace I (b y)}
    (hV : ContMDiffAt I' I.tangent n (fun y ↦ Bundle.TotalSpace.mk' E (b y) (V y)) y₀)
    (hW : ContMDiffAt I' I.tangent n (fun y ↦ Bundle.TotalSpace.mk' E (b y) (W y)) y₀) :
    ContMDiffAt I' 𝓘(ℝ, F) n (fun y ↦ form.eval₂ (b y) (V y) (W y)) y₀ := by
  have hb : ContMDiffAt I' I n b y₀ := (Bundle.contMDiffAt_totalSpace_iff.mp hV).1
  have h := (((form.contMDiff (b y₀)).of_le ENat.LEInfty.out).comp y₀
    hb).continuousAlternatingMap_bundle_apply (v := ![V, W])
    (fun i ↦ by fin_cases i <;> assumption)
  convert (Bundle.contMDiffAt_totalSpace_iff.mp h).2 using 2 with y
  simp only [Bundle.Trivial.fiberBundle_trivializationAt', Bundle.Trivial.trivialization_apply,
    SmoothBundleForm.eval₂_apply]
  congr 1
  ext i
  fin_cases i <;> simp

end Evaluation

end TauCeti.SmoothForm

end
