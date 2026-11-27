/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
public import SymplecticGeometry.Geometry.Manifold.Complex.JConvex.Hypersurface
public import SymplecticGeometry.Geometry.Manifold.Complex.JConvex.Surround.Attached
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import TauCeti.Geometry.Manifold.Complex.LeviForm
public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic
public import TauCeti.LinearAlgebra.TotallyReal.Euclidean

import SymplecticGeometry.Algebra.Order.Ring.Basic
import SymplecticGeometry.Analysis.Complex.LeviForm.Prod
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import TauCeti.Analysis.InnerProductSpace.Euclidean.Complex
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Complex.QuadraticLeviForm
import TauCeti.Analysis.Normed.Operator.Prod
import TauCeti.Geometry.Manifold.Morse.Examples.Saddle

/-!
# The model of the J-convex surrounding

This file sets up the model in which Cieliebak and Eliashberg compute the shapes of `i`-convex
hypersurfaces near an attached disc. The ambient space is
`V = EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)`, a complex manifold modelled on
itself, with points written `p = (x + i y, w)`.

## The model disc

The disc is the inclusion `ι₀ : ℝᵏ → V`, `x ↦ (x, 0)`, of the real points of the first factor,
that is the locus `y = 0`, `w = 0`.

* `SymplecticGeometry.modelDisc k m`: the inclusion `ι₀`, as a real continuous linear map
  (`SymplecticGeometry.modelDisc_apply`);
* `SymplecticGeometry.modelDiscProj k m`: the projection `π₀ : V → ℝᵏ`, `(x + i y, w) ↦ x`, a
  real continuous linear left inverse of `ι₀` (`SymplecticGeometry.leftInverse_modelDiscProj`),
  built from Tau Ceti's `TauCeti.complexEuclideanEquivRealProd`;
* `SymplecticGeometry.isSmoothEmbedding_modelDisc`: `ι₀` is a smooth embedding, by Tau Ceti's
  `ContinuousLinearMap.isSmoothEmbedding_of_injective`;
* `SymplecticGeometry.mfderiv_modelDisc`: its differential at every point is `ι₀` itself;
* `SymplecticGeometry.isTotallyReal_range_modelDisc`: its image `ℝᵏ × 0` is totally real for
  multiplication by `i` (Tau Ceti's `TauCeti.IsTotallyReal`), as the product of Tau Ceti's
  totally real `TauCeti.realSubspace` with the zero subspace (`TauCeti.IsTotallyReal.prod`);
* `SymplecticGeometry.isTotallyReal_range_mfderiv_modelDisc`: hence its tangent images are
  totally real for the complex structure of `V`.

When `m ≠ 0` the image has less than half the real dimension of `V`, so `ι₀` is not
a totally real embedding in Tau Ceti's stronger sense `TauCeti.IsTotallyRealEmbedding`, and the
weak form above is the one the surrounding uses.

## Shape functions

On `V`, the *shape coordinates* are `s = |x|²` and `t = |y|² + |w|²`. Functions of `(s, t)` are
the model functions with which the `J`-convex surrounding of a totally real disc is built: the
model disc is the locus `t = 0`. This part computes their Levi forms and gives a criterion for
the strict plurisubharmonicity of `f(s) + g(t)`.

* `SymplecticGeometry.shape p`: the pair `(s p, t p)`;
* `SymplecticGeometry.leviForm_shape_fst_apply`, `SymplecticGeometry.leviForm_shape_snd_apply`:
  the Levi forms of `s` and `t` are `⟪v₁, w₁⟫ / 2` and `⟪v₁, w₁⟫ / 2 + ⟪v₂, w₂⟫`. So the Levi form
  of `t` is positive definite (`SymplecticGeometry.re_leviForm_shape_snd_apply_self`,
  `SymplecticGeometry.re_leviForm_shape_snd_pos`), and its differential vanishes only where
  `t = 0` (`SymplecticGeometry.fderiv_shape_snd_ne_zero`).
* `SymplecticGeometry.re_leviForm_comp_shape_apply_self`: for `h` of class `C²`, the Levi form of
  `h ∘ shape` on `v` in terms of the partial derivatives of `h` and of
  `σ = ∑ⱼ xⱼ v₁ⱼ` and `τ = ⟪w, v₂⟫ - i ∑ⱼ yⱼ v₁ⱼ`, which are the Wirtinger derivatives
  `∂s v` and `∂t v`.
* `SymplecticGeometry.re_leviForm_comp_shape_apply_self_of_fderiv_eq_zero`: on a complex
  tangency `v` of a level of `h ∘ shape` at which `∂ₜh ≠ 0`, `τ = c σ` for the real `c` with
  `∂ₛh + c ∂ₜh = 0`, so that the real part of the Levi form is a multiple of `|σ|²` plus terms
  in `|v₁|²` and `|v₂|²`, and `|σ|²` has the Cauchy–Schwarz bounds `|σ|² ≤ s |v₁|²` and
  `(t + c² s) |σ|² ≤ s t |v|²`.
* `SymplecticGeometry.isManifoldStrictlyPlurisubharmonicAt_shape`: with `u⁻ = min u 0`, if
  `f' + g' + 2 f''⁻ s + 2 g''⁻ t > 0` and, when `m ≠ 0`, `g' + 2 g''⁻ t > 0`, then
  `f(s) + g(t)` is strictly plurisubharmonic. The flat form is
  `SymplecticGeometry.isStrictlyPlurisubharmonicAt_shape`.

The Levi form of `h ∘ shape` comes from `TauCeti.re_leviForm_comp_prodMk_apply_self` and the Levi
forms of `s` and `t`, which Tau Ceti's `TauCeti.leviForm_re_sq_comp_apply` and
`TauCeti.leviForm_norm_sq_comp_apply` give. The criterion follows from it by the Cauchy–Schwarz
bounds `|σ|² ≤ s |v₁|²` and `|τ|² ≤ t (|v₁|² + |v₂|²)`; the second is a case of
`SymplecticGeometry.norm_ofReal_mul_add_ofReal_mul_sq_le`, the bound
`|c₁ σ + c₂ τ|² ≤ (c₁² s + c₂² t) |v|²` for real `c₁`, `c₂`.

## Handles around the model disc

The sets `{t ≤ γ², s ≤ (1 + γ)²}` are the handles of width `γ` around `ι₀ (closedBall 0 1)`.

* `SymplecticGeometry.isCompact_setOf_shape_le`: the sets `{t ≤ a, s ≤ b}` are compact;
* `SymplecticGeometry.setOf_shape_le_subset_setOf_shape_le`: the handles grow with `γ`;
* `SymplecticGeometry.iInter_setOf_shape_le_eq`: the intersection of the handles for
  `0 < γ < 1` is the model disc `ι₀ (closedBall 0 1)`.

## The model handle function and the model level

* `SymplecticGeometry.modelHandle k m a b`: the model handle function `b t - a s`. For `0 < b`
  and `a < b` it is strictly plurisubharmonic everywhere
  (`SymplecticGeometry.isManifoldStrictlyPlurisubharmonicAt_modelHandle`, by the criterion with
  `f' + g' = b - a` and `g' = b`). For `0 < a` and `0 < b`, the real splitting
  `SymplecticGeometry.modelHandleSplitting`, `(x + i y, w) ↦ (√a x, √b (y, w))`, built from Tau
  Ceti's `TauCeti.complexEuclideanEquivRealProd`, carries it to Tau Ceti's quadratic model
  `(u, v) ↦ -‖u‖² + ‖v‖²` on `ℝᵏ × (ℝᵏ × ℂᵐ)` (`SymplecticGeometry.modelHandle_eq_comp`). The
  critical data of that model in Tau Ceti's `TauCeti.Geometry.Manifold.Morse.Examples.Saddle`
  and `TauCeti.Analysis.Calculus.Morse.NormSq` then give: its only critical point is `0`
  (`SymplecticGeometry.criticalPoints_modelHandle`, from
  `TauCeti.criticalPoints_neg_norm_sq_add_norm_sq` through Tau Ceti's
  `IsLocalDiffeomorphAt.mem_criticalPoints_comp_iff`), it is a Morse function
  (`SymplecticGeometry.isMorse_modelHandle`), and its Morse index at `0` is `k`
  (`SymplecticGeometry.manifoldMorseIndex_modelHandle`). The last two proofs follow that of Tau
  Ceti's `TauCeti.isMorse_neg_norm_sq_add_norm_sq`, through the change of coordinates
  `TauCeti.IsNondegenerateCriticalPoint.comp` and `TauCeti.morseIndex_comp`.
* `SymplecticGeometry.modelLevel k m`: the model level `φ₀ = 1 - s + 2 t`, which is `1` plus the
  model handle function with `a = 1` and `b = 2` (`SymplecticGeometry.modelLevel_eq`). It is
  strictly plurisubharmonic everywhere
  (`SymplecticGeometry.isManifoldStrictlyPlurisubharmonicAt_modelLevel`, by the criterion with
  `f' + g' = 1` and `g' = 2`). Its only critical point is `0`
  (`SymplecticGeometry.criticalPoints_modelLevel`), where it takes the value `1`
  (`SymplecticGeometry.modelLevel_zero`), so its zero level is a J-convex level
  (`SymplecticGeometry.isJConvexLevel_modelLevel`).
  The real part of its Levi form on `v = (v₁, v₂)` is `|v₁|² / 2 + 2 |v₂|²` at every point
  (`SymplecticGeometry.re_leviForm_modelLevel_apply_self`), while its first and second
  derivatives are bounded on bounded sets, so on such a set its Levi form is at least a fixed
  multiple of `max ‖D²φ₀‖ ‖Dφ₀‖ ‖v‖²`
  (`SymplecticGeometry.exists_pos_mul_max_norm_le_re_leviForm_modelLevel`), the kind of margin
  that `SymplecticGeometry.isManifoldStrictlyPlurisubharmonicAt_comp_modelChart_symm` takes.
* `SymplecticGeometry.isJOrthogonallyAttached_model`: the model disc is attached J-orthogonally
  to `{φ₀ ≤ 0}`, the model case of `SymplecticGeometry.IsJOrthogonallyAttached`. Along the disc
  `φ₀ (ι₀ x) = 1 - |x|²` (`SymplecticGeometry.modelLevel_modelDisc`), and the differential of
  `φ₀` there (`SymplecticGeometry.fderiv_modelLevel_apply`) only sees the real parts of the
  first factor, so it vanishes on `i` times the tangent vectors of the disc.
* `SymplecticGeometry.isJOrthogonallyAttached_modelLevel_comp_symm`: the same through a partial
  diffeomorphism `Φ` from `V` whose differential is complex linear along the sphere, such as
  the chart of `SymplecticGeometry.exists_modelChart`: `Φ ∘ ι₀` is attached J-orthogonally to
  `{φ₀ ∘ Φ.symm ≤ 0}`.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  Chapter 4 (shapes of `i`-convex hypersurfaces) and §7.9 (discs attached J-orthogonally).
-/

public section

noncomputable section

open Manifold
open scoped ContDiff

namespace SymplecticGeometry

open TauCeti

variable (k m : ℕ)

/-- The model disc `ι₀ : ℝᵏ → ℂᵏ × ℂᵐ`, `x ↦ (x, 0)`: the inclusion of the real points of the
first factor, as a real continuous linear map. -/
def modelDisc :
    EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m) :=
  (ContinuousLinearMap.inl ℝ _ _).comp
    ((complexEuclideanEquivRealProd (Fin k)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.inl ℝ _ _))

variable {k m}

/-- The model disc sends `x` to the point with coordinates `(x j : ℂ)` in the first factor and
`0` in the second. -/
theorem modelDisc_apply (x : EuclideanSpace ℝ (Fin k)) :
    modelDisc k m x = (WithLp.toLp 2 fun j ↦ (x j : ℂ), 0) := by
  ext j <;> simp [modelDisc]

/-- The `j`-th coordinate of the first component of `ι₀ x` is `x j`. -/
@[simp]
theorem modelDisc_apply_fst_apply (x : EuclideanSpace ℝ (Fin k)) (j : Fin k) :
    (modelDisc k m x).1 j = x j := by
  simp [modelDisc_apply]

/-- The second component of `ι₀ x` is `0`. -/
@[simp]
theorem modelDisc_apply_snd (x : EuclideanSpace ℝ (Fin k)) : (modelDisc k m x).2 = 0 := by
  simp [modelDisc_apply]

variable (k m) in
/-- The projection `π₀ : ℂᵏ × ℂᵐ → ℝᵏ`, `(z, w) ↦ Re z`, onto the core: the real part of the first
factor, as a real continuous linear map. It is a left inverse of the model disc
(`SymplecticGeometry.leftInverse_modelDiscProj`). -/
def modelDiscProj :
    EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin k) :=
  (ContinuousLinearMap.fst ℝ _ _).comp
    ((complexEuclideanEquivRealProd (Fin k)).toContinuousLinearMap.comp
      (ContinuousLinearMap.fst ℝ _ _))

/-- The projection `π₀` sends `(z, w)` to the real parts of the coordinates of `z`. -/
@[simp]
theorem modelDiscProj_apply (p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) :
    modelDiscProj k m p = WithLp.toLp 2 fun j ↦ (p.1 j).re := by
  ext j
  simp [modelDiscProj]

/-- The projection `π₀` is a left inverse of the model disc: `π₀ (ι₀ x) = x`. -/
theorem leftInverse_modelDiscProj : Function.LeftInverse (modelDiscProj k m) (modelDisc k m) :=
  fun x ↦ by ext j; simp

/-- The projection `π₀` composed with the model disc `ι₀` is the identity of `ℝᵏ`. -/
@[simp]
theorem modelDiscProj_comp_modelDisc :
    (modelDiscProj k m).comp (modelDisc k m) = ContinuousLinearMap.id ℝ _ :=
  ContinuousLinearMap.ext leftInverse_modelDiscProj

/-- The model disc is injective, since `π₀` is a left inverse of it. -/
theorem modelDisc_injective : Function.Injective (modelDisc k m) :=
  leftInverse_modelDiscProj.injective

/-- The image of the model disc is the product of the real subspace `ℝᵏ ⊆ ℂᵏ` with `0`. -/
theorem range_modelDisc :
    LinearMap.range (modelDisc k m).toLinearMap = (realSubspace (Fin k)).prod ⊥ := by
  ext ⟨z, w⟩
  simp only [LinearMap.mem_range, ContinuousLinearMap.coe_coe, Submodule.mem_prod,
    mem_realSubspace, Submodule.mem_bot]
  constructor
  · rintro ⟨x, hx⟩
    rw [modelDisc_apply, Prod.mk.injEq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    simp
  · rintro ⟨hz, rfl⟩
    refine ⟨modelDiscProj k m (z, 0), ?_⟩
    rw [modelDisc_apply]
    ext j
    · apply Complex.ext <;> simp [hz j]
    · simp

/-- The model disc is a smooth embedding, of any regularity. -/
theorem isSmoothEmbedding_modelDisc (n : WithTop ℕ∞) :
    IsSmoothEmbedding 𝓘(ℝ, EuclideanSpace ℝ (Fin k))
      𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) n (modelDisc k m) :=
  (modelDisc k m).isSmoothEmbedding_of_injective modelDisc_injective

/-- The differential of the linear map `ι₀` is `ι₀` at every point. -/
theorem mfderiv_modelDisc (x : EuclideanSpace ℝ (Fin k)) :
    mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin k))
      𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) (modelDisc k m) x =
      modelDisc k m :=
  (modelDisc k m).mfderiv_eq

/-- The image of the model disc is totally real for multiplication by `i` on `ℂᵏ × ℂᵐ`. -/
theorem isTotallyReal_range_modelDisc :
    IsTotallyReal ((LinearMap.lsmul ℂ
        (EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) Complex.I).restrictScalars ℝ)
      (LinearMap.range (modelDisc k m).toLinearMap) := by
  rw [range_modelDisc, LinearMap.lsmul_restrictScalars_prodMap]
  exact isMaximalTotallyReal_realSubspace.isTotallyReal.prod (IsTotallyReal.bot _)

/-- The tangent images of the model disc are totally real for the complex structure of
`ℂᵏ × ℂᵐ`, multiplication by `i`. -/
theorem isTotallyReal_range_mfderiv_modelDisc (x : EuclideanSpace ℝ (Fin k)) :
    IsTotallyReal
      ((SmoothAlmostComplexStructure.ofComplexManifold
        (EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m))
        (EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m))).toEndomorphism
          (modelDisc k m x)).toLinearMap
      (LinearMap.range (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin k))
        𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) (modelDisc k m)
          x).toLinearMap) := by
  rw [mfderiv_modelDisc, SmoothAlmostComplexStructure.toEndomorphism_ofComplexManifold]
  exact isTotallyReal_range_modelDisc

section Shape

open Complex ComplexConjugate
open scoped InnerProductSpace

/-- The **shape coordinates** on `ℂᵏ × ℂᵐ`: at `p = (x + i y, w)`, the pair `(s, t)` with
`s = |x|²` and `t = |y|² + |w|²`. -/
def shape (p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) : ℝ × ℝ :=
  (∑ j, (p.1 j).re ^ 2, ∑ j, (p.1 j).im ^ 2 + ‖p.2‖ ^ 2)

theorem shape_def (p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) :
    shape p = (∑ j, (p.1 j).re ^ 2, ∑ j, (p.1 j).im ^ 2 + ‖p.2‖ ^ 2) :=
  (rfl)

@[simp]
theorem shape_fst (p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) :
    (shape p).1 = ∑ j, (p.1 j).re ^ 2 := by
  rw [shape_def]

@[simp]
theorem shape_snd (p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) :
    (shape p).2 = ∑ j, (p.1 j).im ^ 2 + ‖p.2‖ ^ 2 := by
  rw [shape_def]

theorem shape_fst_nonneg (p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) :
    0 ≤ (shape p).1 := by
  rw [shape_fst]
  positivity

theorem shape_snd_nonneg (p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) :
    0 ≤ (shape p).2 := by
  rw [shape_snd]
  positivity

/-- The complex-linear functional `(z, w) ↦ c * z j` on `ℂᵏ × ℂᵐ`. -/
private def coordCLM (c : ℂ) (j : Fin k) :
    EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m) →L[ℂ] ℂ :=
  c • (EuclideanSpace.proj j ∘L ContinuousLinearMap.fst ℂ _ _)

private theorem coordCLM_apply (c : ℂ) (j : Fin k)
    (p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) :
    coordCLM c j p = c * p.1 j := by
  simp [coordCLM]

private theorem shape_fst_eq :
    (fun p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m) ↦ (shape p).1) =
      ∑ j, fun p ↦ (coordCLM 1 j p).re ^ 2 := by
  funext p
  simp [coordCLM_apply]

private theorem shape_snd_eq :
    (fun p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m) ↦ (shape p).2) =
      (∑ j, fun p ↦ (coordCLM (-I) j p).re ^ 2) +
        fun p ↦ ‖ContinuousLinearMap.snd ℂ _ _ p‖ ^ 2 := by
  funext p
  simp [coordCLM_apply]

private theorem contDiff_coordCLM_re_sq {n : WithTop ℕ∞} (c : ℂ) (j : Fin k) :
    ContDiff ℝ n fun p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m) ↦
      (coordCLM c j p).re ^ 2 :=
  ((reCLM.contDiff.comp ((coordCLM c j).restrictScalars ℝ).contDiff).pow 2)

private theorem contDiff_norm_sq_snd {n : WithTop ℕ∞} :
    ContDiff ℝ n fun p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m) ↦
      ‖ContinuousLinearMap.snd ℂ _ _ p‖ ^ 2 :=
  (contDiff_norm_sq ℝ).comp contDiff_snd

private theorem contDiff_sum_coordCLM_re_sq {n : WithTop ℕ∞} (c : ℂ) :
    ContDiff ℝ n (∑ j, fun p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m) ↦
      (coordCLM c j p).re ^ 2) := by
  rw [Finset.sum_fn]
  exact ContDiff.sum fun j _ ↦ contDiff_coordCLM_re_sq c j

/-- The shape coordinates are smooth. -/
theorem contDiff_shape {n : WithTop ℕ∞} :
    ContDiff ℝ n (shape : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m) → ℝ × ℝ) := by
  have h1 : ContDiff ℝ n fun p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m) ↦
      (shape p).1 := by
    rw [shape_fst_eq]
    exact contDiff_sum_coordCLM_re_sq 1
  have h2 : ContDiff ℝ n fun p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m) ↦
      (shape p).2 := by
    rw [shape_snd_eq]
    exact (contDiff_sum_coordCLM_re_sq (-I)).add contDiff_norm_sq_snd
  exact h1.prodMk h2

/-- The Levi form of `s = |x|²` on `ℂᵏ × ℂᵐ` is `⟪v₁, w₁⟫ / 2`. -/
theorem leviForm_shape_fst_apply (p v w : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) :
    leviForm (fun q ↦ (shape q).1) p v w = ⟪v.1, w.1⟫_ℂ / 2 := by
  rw [shape_fst_eq, leviForm_sum _ fun j _ ↦ (contDiff_coordCLM_re_sq 1 j).contDiffAt]
  simp only [LinearMap.sum_apply, leviForm_re_sq_comp_apply]
  simp [coordCLM_apply, PiLp.inner_apply, Finset.sum_div]

/-- The Levi form of `t = |y|² + |w|²` on `ℂᵏ × ℂᵐ` is `⟪v₁, w₁⟫ / 2 + ⟪v₂, w₂⟫`. -/
theorem leviForm_shape_snd_apply (p v w : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) :
    leviForm (fun q ↦ (shape q).2) p v w = ⟪v.1, w.1⟫_ℂ / 2 + ⟪v.2, w.2⟫_ℂ := by
  rw [shape_snd_eq, leviForm_add (contDiff_sum_coordCLM_re_sq (-I)).contDiffAt
    contDiff_norm_sq_snd.contDiffAt,
    leviForm_sum _ fun j _ ↦ (contDiff_coordCLM_re_sq (-I) j).contDiffAt]
  simp only [LinearMap.add_apply, LinearMap.sum_apply,
    leviForm_re_sq_comp_apply, leviForm_norm_sq_comp_apply]
  simp only [coordCLM_apply, PiLp.inner_apply, Finset.sum_div]
  congr 1
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [RCLike.inner_apply, map_mul, map_neg, conj_I]
  linear_combination (-(w.1 j * conj (v.1 j)) / 2) * I_sq

/-- The real part of the Levi form of `t = |y|² + |w|²` on `(v, v)` is `|v₁|² / 2 + |v₂|²`. -/
theorem re_leviForm_shape_snd_apply_self
    (p v : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) :
    (leviForm (fun q ↦ (shape q).2) p v v).re = ‖v.1‖ ^ 2 / 2 + ‖v.2‖ ^ 2 := by
  rw [leviForm_shape_snd_apply, add_re, div_ofNat_re, ← RCLike.re_to_complex,
    ← RCLike.re_to_complex, inner_self_eq_norm_sq, inner_self_eq_norm_sq]

/-- The Levi form of `t = |y|² + |w|²` is positive definite: its real part on `(v, v)` is
positive for `v ≠ 0`. -/
theorem re_leviForm_shape_snd_pos (p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m))
    {v : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)} (hv : v ≠ 0) :
    0 < (leviForm (fun q ↦ (shape q).2) p v v).re := by
  rw [re_leviForm_shape_snd_apply_self]
  by_contra hn
  refine hv (Prod.ext (norm_eq_zero.1 ?_) (norm_eq_zero.1 ?_)) <;>
    nlinarith [norm_nonneg v.1, norm_nonneg v.2]

/-- The differential of `s = |x|²` at `p = (x + i y, w)` is `v ↦ 2 ∑ⱼ xⱼ Re v₁ⱼ`. -/
theorem fderiv_shape_fst_apply (p v : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) :
    fderiv ℝ (fun q ↦ (shape q).1) p v = 2 * ∑ j, (p.1 j).re * (v.1 j).re := by
  have h (j : Fin k) : HasFDerivAt (fun q ↦ (coordCLM (m := m) 1 j q).re ^ 2)
      ((2 * (coordCLM 1 j p).re) • (reCLM.restrictScalars ℝ ∘L (coordCLM 1 j).restrictScalars ℝ))
      p := by
    simpa using ((reCLM.restrictScalars ℝ ∘L (coordCLM (m := m) 1 j).restrictScalars ℝ)
      |>.hasFDerivAt (x := p)).pow 2
  rw [shape_fst_eq, (HasFDerivAt.sum fun j _ ↦ h j).fderiv]
  simp [coordCLM_apply, Finset.mul_sum, mul_assoc]

/-- The differential of `t = |y|² + |w|²` at `p = (x + i y, w)` is
`v ↦ 2 (∑ⱼ yⱼ Im v₁ⱼ + Re ⟪w, v₂⟫)`. -/
theorem fderiv_shape_snd_apply (p v : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) :
    fderiv ℝ (fun q ↦ (shape q).2) p v =
      2 * (∑ j, (p.1 j).im * (v.1 j).im + (⟪p.2, v.2⟫_ℂ).re) := by
  have h (j : Fin k) : HasFDerivAt (fun q ↦ (coordCLM (m := m) (-I) j q).re ^ 2)
      ((2 * (coordCLM (-I) j p).re) •
        (reCLM.restrictScalars ℝ ∘L (coordCLM (-I) j).restrictScalars ℝ)) p := by
    simpa using ((reCLM.restrictScalars ℝ ∘L (coordCLM (m := m) (-I) j).restrictScalars ℝ)
      |>.hasFDerivAt (x := p)).pow 2
  have h₂ : HasFDerivAt (fun q ↦ ‖ContinuousLinearMap.snd ℂ (EuclideanSpace ℂ (Fin k))
      (EuclideanSpace ℂ (Fin m)) q‖ ^ 2)
      ((2 : ℕ) • (innerSL ℝ p.2 ∘L ContinuousLinearMap.snd ℝ _ _)) p := by
    simpa using (hasFDerivAt_snd (𝕜 := ℝ) (p := p)).norm_sq
  rw [shape_snd_eq, ((HasFDerivAt.sum fun j _ ↦ h j).add h₂).fderiv]
  simp [coordCLM_apply, PiLp.inner_apply, Complex.re_sum, Finset.mul_sum, mul_add, mul_assoc]

/-- The differential of `t = |y|² + |w|²` at `p` is nonzero where `t p ≠ 0`: it takes the value
`2 t p` on `p`. -/
theorem fderiv_shape_snd_ne_zero {p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)}
    (hp : (shape p).2 ≠ 0) : fderiv ℝ (fun q ↦ (shape q).2) p ≠ 0 := by
  intro h0
  have h := fderiv_shape_snd_apply p p
  rw [h0, zero_apply, ← RCLike.re_to_complex, inner_self_eq_norm_sq] at h
  have ht := shape_snd p
  simp only [← sq] at h
  exact hp (by linarith)

/-- The differential of `shape` at `p` is the pair of the differentials of `s` and of `t`. -/
theorem fderiv_shape_apply (p v : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) :
    fderiv ℝ shape p v =
      (fderiv ℝ (fun q ↦ (shape q).1) p v, fderiv ℝ (fun q ↦ (shape q).2) p v) := by
  have hd : DifferentiableAt ℝ shape p := (contDiff_shape (n := 1)).differentiable one_ne_zero p
  rw [fderiv.fst hd, fderiv.snd hd, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']

/-- The chain rule for a function of the shape coordinates: for `H : ℝ × ℝ → ℝ` differentiable
at `shape p`, the differential of `H ∘ shape` at `p` is `v ↦ dH (ds_p v, dt_p v)`. -/
theorem fderiv_comp_shape_apply {H : ℝ × ℝ → ℝ}
    {p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)}
    (hH : DifferentiableAt ℝ H (shape p))
    (v : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) :
    fderiv ℝ (H ∘ shape) p v =
      fderiv ℝ H (shape p) (fderiv ℝ (fun q ↦ (shape q).1) p v,
        fderiv ℝ (fun q ↦ (shape q).2) p v) := by
  rw [fderiv_comp p hH ((contDiff_shape (n := 1)).differentiable one_ne_zero p),
    ContinuousLinearMap.comp_apply, fderiv_shape_apply]

/-- **The Levi form of a function of the shape coordinates.** Let `h : ℝ × ℝ → ℝ` be `C²` at
`(s, t) = shape p`, with `p = (x + i y, w)`, and write `hₛ`, `hₜ` for its first and `hₛₛ`, `hₛₜ`,
`hₜₜ` for its second partial derivatives there. For `v = (v₁, v₂)`, put `σ = ∑ⱼ xⱼ v₁ⱼ` and
`τ = ⟪w, v₂⟫ - i ∑ⱼ yⱼ v₁ⱼ`. Then the real part of the Levi form of `h ∘ shape` at `p` on `v` is
`hₛ |v₁|² / 2 + hₜ (|v₁|² / 2 + |v₂|²) + hₛₛ |σ|² + 2 hₛₜ Re (conj σ τ) + hₜₜ |τ|²`. -/
theorem re_leviForm_comp_shape_apply_self {h : ℝ × ℝ → ℝ}
    {p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)} (hh : ContDiffAt ℝ 2 h (shape p))
    (v : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) :
    (leviForm (h ∘ shape) p v v).re =
      fderiv ℝ h (shape p) (1, 0) * (‖v.1‖ ^ 2 / 2) +
        fderiv ℝ h (shape p) (0, 1) * (‖v.1‖ ^ 2 / 2 + ‖v.2‖ ^ 2) +
        fderiv ℝ (fderiv ℝ h) (shape p) (1, 0) (1, 0) * ‖∑ j, ((p.1 j).re : ℂ) * v.1 j‖ ^ 2 +
        2 * fderiv ℝ (fderiv ℝ h) (shape p) (1, 0) (0, 1) *
          (conj (∑ j, ((p.1 j).re : ℂ) * v.1 j) *
            (⟪p.2, v.2⟫_ℂ - I * ∑ j, ((p.1 j).im : ℂ) * v.1 j)).re +
        fderiv ℝ (fderiv ℝ h) (shape p) (0, 1) (0, 1) *
          ‖⟪p.2, v.2⟫_ℂ - I * ∑ j, ((p.1 j).im : ℂ) * v.1 j‖ ^ 2 := by
  have hcomp : h ∘ shape = fun q : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m) ↦
      h ((shape q).1, (shape q).2) := by
    funext q
    simp only [Function.comp_apply, Prod.mk.eta]
  -- The second derivative of `h` is symmetric, so on `(a, b)` it is `a² hₛₛ + 2 a b hₛₜ + b² hₜₜ`.
  have hsymm := hh.isSymmSndFDerivAt (by simp)
  have hB (a b : ℝ) : fderiv ℝ (fderiv ℝ h) (shape p) (a, b) (a, b) =
      a ^ 2 * fderiv ℝ (fderiv ℝ h) (shape p) (1, 0) (1, 0) +
        2 * a * b * fderiv ℝ (fderiv ℝ h) (shape p) (1, 0) (0, 1) +
        b ^ 2 * fderiv ℝ (fderiv ℝ h) (shape p) (0, 1) (0, 1) := by
    set B := fderiv ℝ (fderiv ℝ h) (shape p)
    rw [B.apply_mk_eq_smul_add_smul, add_apply, smul_apply, smul_apply,
      (B (1, 0)).apply_mk_eq_smul_add_smul a b, (B (0, 1)).apply_mk_eq_smul_add_smul a b]
    simp only [smul_eq_mul]
    rw [hsymm (0, 1) (1, 0)]
    ring
  have hre {n : ℕ} (u : EuclideanSpace ℂ (Fin n)) : (⟪u, u⟫_ℂ).re = ‖u‖ ^ 2 := by
    simpa using inner_self_eq_norm_sq (𝕜 := ℂ) u
  rw [hcomp, re_leviForm_comp_prodMk_apply_self (by rwa [Prod.mk.eta])
    (contDiff_shape.fst.contDiffAt) (contDiff_shape.snd.contDiffAt) v]
  simp only [Prod.mk.eta, leviForm_shape_fst_apply, leviForm_shape_snd_apply]
  rw [hB (fderiv ℝ (fun q ↦ (shape q).1) p v),
    hB (fderiv ℝ (fun q ↦ (shape q).1) p (I • v)),
    fderiv_shape_fst_apply, fderiv_shape_fst_apply, fderiv_shape_snd_apply,
    fderiv_shape_snd_apply]
  simp only [Prod.smul_fst, Prod.smul_snd, PiLp.smul_apply, smul_eq_mul, inner_smul_right,
    hre, Complex.sq_norm, normSq_apply, mul_re, mul_im, sub_re, sub_im,
    conj_re, conj_im, re_sum, im_sum, ofReal_re, ofReal_im, I_re, I_im, add_re, div_ofNat_re,
    zero_mul, one_mul, zero_sub, sub_zero, mul_neg, Finset.sum_neg_distrib]
  ring_nf

/-- The bound `|σ|² ≤ s |v₁|²` for `σ = ∑ⱼ xⱼ v₁ⱼ`, by Cauchy–Schwarz. -/
theorem norm_sum_re_mul_sq_le (p v : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) :
    ‖∑ j, ((p.1 j).re : ℂ) * v.1 j‖ ^ 2 ≤ (shape p).1 * ‖v.1‖ ^ 2 := by
  let X := (modelDisc k m (modelDiscProj k m p)).1
  have hX : ⟪X, v.1⟫_ℂ = ∑ j, ((p.1 j).re : ℂ) * v.1 j := by
    simp [X, PiLp.inner_apply, mul_comm]
  have hXn : ‖X‖ ^ 2 = (shape p).1 := by
    simp [X, EuclideanSpace.norm_sq_eq]
  rw [← hX, ← hXn, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm X v.1) 2

/-- The Cauchy–Schwarz bound `|c₁ σ + c₂ τ|² ≤ (c₁² s + c₂² t) |v|²` for real `c₁`, `c₂`, where
`σ = ∑ⱼ xⱼ v₁ⱼ` and `τ = ⟪w, v₂⟫ - i ∑ⱼ yⱼ v₁ⱼ` at `p = (x + i y, w)`: the combination is the
inner product of `v` with `(c₁ x + i c₂ y, c₂ w)`, whose real and imaginary parts are
orthogonal. -/
theorem norm_ofReal_mul_add_ofReal_mul_sq_le (c₁ c₂ : ℝ)
    (p v : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) :
    ‖(c₁ : ℂ) * ∑ j, ((p.1 j).re : ℂ) * v.1 j +
        (c₂ : ℂ) * (⟪p.2, v.2⟫_ℂ - I * ∑ j, ((p.1 j).im : ℂ) * v.1 j)‖ ^ 2 ≤
      (c₁ ^ 2 * (shape p).1 + c₂ ^ 2 * (shape p).2) * (‖v.1‖ ^ 2 + ‖v.2‖ ^ 2) := by
  let Y : EuclideanSpace ℂ (Fin k) :=
    WithLp.toLp 2 fun j ↦ (c₁ : ℂ) * ((p.1 j).re : ℂ) + I * ((c₂ : ℂ) * ((p.1 j).im : ℂ))
  let X : WithLp 2 (EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) :=
    WithLp.toLp 2 (Y, (c₂ : ℂ) • p.2)
  let u : WithLp 2 (EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) := WithLp.toLp 2 v
  have hX : ⟪X, u⟫_ℂ = (c₁ : ℂ) * ∑ j, ((p.1 j).re : ℂ) * v.1 j +
      (c₂ : ℂ) * (⟪p.2, v.2⟫_ℂ - I * ∑ j, ((p.1 j).im : ℂ) * v.1 j) := by
    simp only [X, Y, u, WithLp.prod_inner_apply, PiLp.inner_apply, inner_smul_left,
      RCLike.inner_apply, map_add, map_mul, conj_ofReal, conj_I, Finset.mul_sum, mul_sub]
    have e : ∑ j, v.1 j * ((c₁ : ℂ) * ((p.1 j).re : ℂ) + -I * ((c₂ : ℂ) * ((p.1 j).im : ℂ))) =
        ∑ j, (c₁ : ℂ) * (((p.1 j).re : ℂ) * v.1 j) -
          ∑ j, (c₂ : ℂ) * (I * (((p.1 j).im : ℂ) * v.1 j)) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ ↦ by ring
    rw [e]
    ring
  have hXn : ‖X‖ ^ 2 = c₁ ^ 2 * (shape p).1 + c₂ ^ 2 * (shape p).2 := by
    simp only [X, Y, WithLp.prod_norm_sq_eq_of_L2, EuclideanSpace.norm_sq_eq, norm_smul,
      shape_fst, shape_snd, Complex.sq_norm, normSq_apply, mul_pow, Finset.mul_sum, mul_add,
      WithLp.toLp_fst, WithLp.toLp_snd, Real.norm_eq_abs, sq_abs,
      Complex.norm_real]
    rw [← add_assoc, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [add_re, add_im, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im]
    ring
  have hun : ‖u‖ ^ 2 = ‖v.1‖ ^ 2 + ‖v.2‖ ^ 2 := by
    simp [u, WithLp.prod_norm_sq_eq_of_L2]
  rw [← hX, ← hXn, ← hun, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm X u) 2

/-- On the vectors `v` with `α ds_p v + β dt_p v = 0` and `α ds_p (i v) + β dt_p (i v) = 0`, the
combination `α σ + β τ` vanishes, where `σ = ∑ⱼ xⱼ v₁ⱼ` and `τ = ⟪w, v₂⟫ - i ∑ⱼ yⱼ v₁ⱼ` at
`p = (x + i y, w)`: the two hypotheses are twice its real part and minus twice its imaginary
part. -/
theorem ofReal_mul_add_ofReal_mul_eq_zero_of_fderiv_shape {α β : ℝ}
    {p v : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)}
    (h₁ : α * fderiv ℝ (fun q ↦ (shape q).1) p v + β * fderiv ℝ (fun q ↦ (shape q).2) p v = 0)
    (h₂ : α * fderiv ℝ (fun q ↦ (shape q).1) p (I • v) +
      β * fderiv ℝ (fun q ↦ (shape q).2) p (I • v) = 0) :
    (α : ℂ) * ∑ j, ((p.1 j).re : ℂ) * v.1 j +
      (β : ℂ) * (⟪p.2, v.2⟫_ℂ - I * ∑ j, ((p.1 j).im : ℂ) * v.1 j) = 0 := by
  rw [fderiv_shape_fst_apply, fderiv_shape_snd_apply] at h₁ h₂
  simp only [Prod.smul_fst, Prod.smul_snd, PiLp.smul_apply, smul_eq_mul, inner_smul_right,
    mul_re, mul_im, I_re, I_im, zero_mul, one_mul, zero_sub, mul_neg, Finset.sum_neg_distrib,
    zero_add] at h₂
  apply Complex.ext
  · simp only [add_re, mul_re, ofReal_re, re_sum, ofReal_im, zero_mul, sub_zero, im_sum, mul_im,
      add_zero, sub_re, I_re, I_im, one_mul, zero_sub, sub_neg_eq_add, sub_im, zero_add, zero_re]
    linear_combination h₁ / 2
  · simp only [add_im, mul_im, ofReal_re, im_sum, ofReal_im, zero_mul, add_zero, re_sum, mul_re,
      sub_zero, sub_im, I_re, I_im, one_mul, zero_add, sub_re, zero_sub, sub_neg_eq_add, zero_im]
    linear_combination -h₂ / 2

/-- **The Levi form of a function of the shape coordinates on a complex tangency.** Let `H` be
`C²` at `(s, t) = shape p`, with `p = (x + i y, w)`, and write `Hₛ`, `Hₜ` for its first and
`Hₛₛ`, `Hₛₜ`, `Hₜₜ` for its second partial derivatives there. Let `Hₜ ≠ 0` and `Hₛ + c Hₜ = 0`,
and let `v` satisfy `d(H ∘ shape)_p v = 0` and `d(H ∘ shape)_p (i v) = 0`. With
`σ = ∑ⱼ xⱼ v₁ⱼ` and `τ = ⟪w, v₂⟫ - i ∑ⱼ yⱼ v₁ⱼ`, then `τ = c σ`, the real part of the Levi form
of `H ∘ shape` at `p` on `v` is
`Hₛ |v₁|² / 2 + Hₜ (|v₁|² / 2 + |v₂|²) + (Hₛₛ + 2 c Hₛₜ + c² Hₜₜ) |σ|²`, and `|σ|²` satisfies
the Cauchy–Schwarz bounds `|σ|² ≤ s |v₁|²` and `(t + c² s) |σ|² ≤ s t (|v₁|² + |v₂|²)`. -/
theorem re_leviForm_comp_shape_apply_self_of_fderiv_eq_zero {H : ℝ × ℝ → ℝ}
    {p v : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)} (hH : ContDiffAt ℝ 2 H (shape p))
    {c : ℝ} (hβ : fderiv ℝ H (shape p) (0, 1) ≠ 0)
    (hc : fderiv ℝ H (shape p) (1, 0) + c * fderiv ℝ H (shape p) (0, 1) = 0)
    (hv₁ : fderiv ℝ (H ∘ shape) p v = 0) (hv₂ : fderiv ℝ (H ∘ shape) p (I • v) = 0) :
    ⟪p.2, v.2⟫_ℂ - I * ∑ j, ((p.1 j).im : ℂ) * v.1 j = (c : ℂ) * ∑ j, ((p.1 j).re : ℂ) * v.1 j ∧
      (leviForm (H ∘ shape) p v v).re =
        fderiv ℝ H (shape p) (1, 0) * (‖v.1‖ ^ 2 / 2) +
          fderiv ℝ H (shape p) (0, 1) * (‖v.1‖ ^ 2 / 2 + ‖v.2‖ ^ 2) +
          (fderiv ℝ (fderiv ℝ H) (shape p) (1, 0) (1, 0) +
            2 * c * fderiv ℝ (fderiv ℝ H) (shape p) (1, 0) (0, 1) +
            c ^ 2 * fderiv ℝ (fderiv ℝ H) (shape p) (0, 1) (0, 1)) *
            ‖∑ j, ((p.1 j).re : ℂ) * v.1 j‖ ^ 2 ∧
      ‖∑ j, ((p.1 j).re : ℂ) * v.1 j‖ ^ 2 ≤ (shape p).1 * ‖v.1‖ ^ 2 ∧
      ((shape p).2 + c ^ 2 * (shape p).1) * ‖∑ j, ((p.1 j).re : ℂ) * v.1 j‖ ^ 2 ≤
        (shape p).1 * (shape p).2 * (‖v.1‖ ^ 2 + ‖v.2‖ ^ 2) := by
  set σ := ∑ j, ((p.1 j).re : ℂ) * v.1 j with hσ
  set τ := ⟪p.2, v.2⟫_ℂ - I * ∑ j, ((p.1 j).im : ℂ) * v.1 j with hτ
  set α := fderiv ℝ H (shape p) (1, 0)
  set β := fderiv ℝ H (shape p) (0, 1)
  have hlin (a b : ℝ) : fderiv ℝ H (shape p) (a, b) = α * a + β * b := by
    rw [ContinuousLinearMap.apply_mk_eq_smul_add_smul, smul_eq_mul, smul_eq_mul]
    ring
  have hd : DifferentiableAt ℝ H (shape p) := hH.differentiableAt (by norm_num)
  rw [fderiv_comp_shape_apply hd, hlin] at hv₁ hv₂
  -- The tangency gives `α σ + β τ = 0`, and `α = -c β`.
  have h := ofReal_mul_add_ofReal_mul_eq_zero_of_fderiv_shape hv₁ hv₂
  have hc' : (α : ℂ) + (c : ℂ) * (β : ℂ) = 0 := by exact_mod_cast hc
  have hτσ : τ = (c : ℂ) * σ := by
    have h0 : (β : ℂ) * (τ - (c : ℂ) * σ) = 0 := by linear_combination h - σ * hc'
    rcases mul_eq_zero.1 h0 with h0 | h0
    · exact absurd (ofReal_eq_zero.1 h0) hβ
    · exact sub_eq_zero.1 h0
  refine ⟨hτσ, ?_, norm_sum_re_mul_sq_le p v, ?_⟩
  · rw [re_leviForm_comp_shape_apply_self hH v, ← hσ, ← hτ, hτσ]
    have e₁ : (conj σ * ((c : ℂ) * σ)).re = c * ‖σ‖ ^ 2 := by
      rw [mul_left_comm, mul_comm (conj σ), Complex.mul_conj, ← ofReal_mul, ofReal_re,
        Complex.normSq_eq_norm_sq]
    have e₂ : ‖(c : ℂ) * σ‖ ^ 2 = c ^ 2 * ‖σ‖ ^ 2 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [e₁, e₂]
    ring
  · -- Cauchy–Schwarz for `t σ + c s τ = (t + c² s) σ`.
    have hCS := norm_ofReal_mul_add_ofReal_mul_sq_le (shape p).2 (c * (shape p).1) p v
    rw [← hσ, ← hτ, hτσ] at hCS
    have e : ((shape p).2 : ℂ) * σ + ((c * (shape p).1 : ℝ) : ℂ) * ((c : ℂ) * σ) =
        (((shape p).2 + c ^ 2 * (shape p).1 : ℝ) : ℂ) * σ := by
      push_cast
      ring
    rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs] at hCS
    have hs := shape_fst_nonneg p
    have ht := shape_snd_nonneg p
    have hq : 0 ≤ (shape p).2 + c ^ 2 * (shape p).1 := by positivity
    rcases hq.eq_or_lt with hq | hq
    · rw [← hq, zero_mul]
      positivity
    · refine le_of_mul_le_mul_left ?_ hq
      calc ((shape p).2 + c ^ 2 * (shape p).1) * (((shape p).2 + c ^ 2 * (shape p).1) * ‖σ‖ ^ 2)
          = ((shape p).2 + c ^ 2 * (shape p).1) ^ 2 * ‖σ‖ ^ 2 := by ring
        _ ≤ ((shape p).2 ^ 2 * (shape p).1 + (c * (shape p).1) ^ 2 * (shape p).2) *
            (‖v.1‖ ^ 2 + ‖v.2‖ ^ 2) := hCS
        _ = ((shape p).2 + c ^ 2 * (shape p).1) *
            ((shape p).1 * (shape p).2 * (‖v.1‖ ^ 2 + ‖v.2‖ ^ 2)) := by ring

/-- **Strict plurisubharmonicity of `f(s) + g(t)`**, on `ℂᵏ × ℂᵐ`. Let `f` and `g` be `C²` at
`s = (shape p).1` and at `t = (shape p).2`, and write `u⁻ = min u 0`. If
`f'(s) + g'(t) + 2 f''(s)⁻ s + 2 g''(t)⁻ t > 0` and, when `m ≠ 0`, `g'(t) + 2 g''(t)⁻ t > 0`,
then `q ↦ f (s q) + g (t q)` is strictly plurisubharmonic at `p`. -/
theorem isStrictlyPlurisubharmonicAt_shape {f g : ℝ → ℝ}
    {p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)}
    (hf : ContDiffAt ℝ 2 f (shape p).1) (hg : ContDiffAt ℝ 2 g (shape p).2)
    (h₁ : 0 < deriv f (shape p).1 + deriv g (shape p).2 +
      2 * min (iteratedDeriv 2 f (shape p).1) 0 * (shape p).1 +
      2 * min (iteratedDeriv 2 g (shape p).2) 0 * (shape p).2)
    (h₂ : m ≠ 0 →
      0 < deriv g (shape p).2 + 2 * min (iteratedDeriv 2 g (shape p).2) 0 * (shape p).2) :
    IsStrictlyPlurisubharmonicAt (fun q ↦ f (shape q).1 + g (shape q).2) p := by
  set s := (shape p).1 with hs
  set t := (shape p).2 with ht
  have hp : shape p = (s, t) := by rw [hs, ht]
  have hcomp : (fun q : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m) ↦
      f (shape q).1 + g (shape q).2) = (f ∘ Prod.fst + g ∘ Prod.snd) ∘ shape := by
    funext q
    simp only [Function.comp_apply, Pi.add_apply]
  have hH : ContDiffAt ℝ 2 (f ∘ Prod.fst + g ∘ Prod.snd) (shape p) := by
    rw [hp]
    exact (hf.comp (s, t) contDiffAt_fst).add (hg.comp (s, t) contDiffAt_snd)
  rw [isStrictlyPlurisubharmonicAt_iff, hcomp]
  intro v hv
  rw [re_leviForm_comp_shape_apply_self hH v, hp,
    fderiv_comp_fst_add_comp_snd (hf.differentiableAt (by norm_num))
      (hg.differentiableAt (by norm_num)),
    fderiv_fderiv_comp_fst_add_comp_snd hf hg]
  have hf₂ : deriv (fderiv ℝ f) s 1 = iteratedDeriv 2 f s := by
    simpa using fderiv_fderiv_apply_eq_smul_iteratedDeriv f s 1 1
  have hg₂ : deriv (fderiv ℝ g) t 1 = iteratedDeriv 2 g t := by
    simpa using fderiv_fderiv_apply_eq_smul_iteratedDeriv g t 1 1
  have hS := norm_sum_re_mul_sq_le p v
  have hT : ‖⟪p.2, v.2⟫_ℂ - I * ∑ j, ((p.1 j).im : ℂ) * v.1 j‖ ^ 2 ≤
      (shape p).2 * (‖v.1‖ ^ 2 + ‖v.2‖ ^ 2) := by
    simpa using norm_ofReal_mul_add_ofReal_mul_sq_le 0 1 p v
  rw [← hs] at hS
  rw [← ht] at hT
  set S := ‖∑ j, ((p.1 j).re : ℂ) * v.1 j‖ ^ 2
  set T := ‖⟪p.2, v.2⟫_ℂ - I * ∑ j, ((p.1 j).im : ℂ) * v.1 j‖ ^ 2
  set a := ‖v.1‖ ^ 2 with ha
  set b := ‖v.2‖ ^ 2 with hb
  suffices H : 0 < deriv f s * (a / 2) + deriv g t * (a / 2 + b) + iteratedDeriv 2 f s * S +
      iteratedDeriv 2 g t * T by
    simpa [hf₂, hg₂] using H
  have hs₀ : 0 ≤ s := shape_fst_nonneg p
  have ht₀ : 0 ≤ t := shape_snd_nonneg p
  have ha₀ : 0 ≤ a := by positivity
  have hb₀ : 0 ≤ b := by positivity
  have hS₀ : 0 ≤ S := by positivity
  have hT₀ : 0 ≤ T := by positivity
  -- `f'' S ≥ f''⁻ s a` and `g'' T ≥ g''⁻ t (a + b)`.
  have hfS : min (iteratedDeriv 2 f s) 0 * s * a ≤ iteratedDeriv 2 f s * S :=
    mul_assoc (min _ 0) s a ▸ min_zero_mul_le_mul hS₀ hS
  have hgT : min (iteratedDeriv 2 g t) 0 * t * (a + b) ≤ iteratedDeriv 2 g t * T :=
    mul_assoc (min _ 0) t (a + b) ▸ min_zero_mul_le_mul hT₀ hT
  have hmg : min (iteratedDeriv 2 g t) 0 * t ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (min_le_right _ _) ht₀
  rcases hb₀.lt_or_eq with hb' | hb'
  · -- `v₂ ≠ 0`, so `m ≠ 0`.
    have hm : m ≠ 0 := by
      rintro rfl
      have h0 : v.2 = 0 := Subsingleton.elim _ _
      rw [hb, h0, norm_zero] at hb'
      norm_num at hb'
    nlinarith [mul_pos hb' (h₂ hm), mul_nonneg hb₀ (neg_nonneg.mpr hmg), mul_nonneg ha₀ h₁.le]
  · -- `v₂ = 0`, so `v₁ ≠ 0`.
    have ha' : 0 < a := by
      refine ha₀.lt_of_ne fun h ↦ hv ?_
      have h1 : v.1 = 0 := by simpa [ha] using h.symm
      have h2 : v.2 = 0 := by simpa [hb] using hb'.symm
      exact Prod.ext h1 h2
    rw [← hb'] at hgT ⊢
    nlinarith [mul_pos ha' h₁]

/-- **Strict plurisubharmonicity of `f(s) + g(t)`**, on `ℂᵏ × ℂᵐ` as a complex manifold modelled
on itself. Let `f` and `g` be `C²` at `s = (shape p).1` and at `t = (shape p).2`, and write
`u⁻ = min u 0`. If `f'(s) + g'(t) + 2 f''(s)⁻ s + 2 g''(t)⁻ t > 0` and, when `m ≠ 0`,
`g'(t) + 2 g''(t)⁻ t > 0`, then `q ↦ f (s q) + g (t q)` is strictly plurisubharmonic at `p`. -/
theorem isManifoldStrictlyPlurisubharmonicAt_shape {f g : ℝ → ℝ}
    {p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)}
    (hf : ContDiffAt ℝ 2 f (shape p).1) (hg : ContDiffAt ℝ 2 g (shape p).2)
    (h₁ : 0 < deriv f (shape p).1 + deriv g (shape p).2 +
      2 * min (iteratedDeriv 2 f (shape p).1) 0 * (shape p).1 +
      2 * min (iteratedDeriv 2 g (shape p).2) 0 * (shape p).2)
    (h₂ : m ≠ 0 →
      0 < deriv g (shape p).2 + 2 * min (iteratedDeriv 2 g (shape p).2) 0 * (shape p).2) :
    IsManifoldStrictlyPlurisubharmonicAt (EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m))
      (fun q ↦ f (shape q).1 + g (shape q).2) p := by
  rw [isManifoldStrictlyPlurisubharmonicAt_iff]
  simpa only [manifoldLeviForm_eq_leviForm, ← isStrictlyPlurisubharmonicAt_iff] using
    isStrictlyPlurisubharmonicAt_shape hf hg h₁ h₂

end Shape

/-! ### Handles around the model disc -/

section Handle

open Filter Metric Set

/-- The sets `{p | t p ≤ a ∧ s p ≤ b}` of the shape coordinates `(s, t) = shape p` are compact. -/
theorem isCompact_setOf_shape_le (a b : ℝ) :
    IsCompact {p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m) |
      (shape p).2 ≤ a ∧ (shape p).1 ≤ b} := by
  have hc := (contDiff_shape (k := k) (m := m) (n := 0)).continuous
  refine Metric.isCompact_of_isClosed_isBounded
    ((isClosed_le (continuous_snd.comp hc) continuous_const).inter
      (isClosed_le (continuous_fst.comp hc) continuous_const))
    ((isBounded_closedBall (x := 0) (r := √(|a| + |b|))).subset fun p hp ↦ ?_)
  obtain ⟨ha, hb⟩ := hp
  have hs := shape_fst_nonneg p
  have ht := shape_snd_nonneg p
  rw [shape_fst] at hs hb
  rw [shape_snd] at ht ha
  rw [mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff]
  constructor <;> refine Real.le_sqrt_of_sq_le ?_
  · have hn : ‖p.1‖ ^ 2 = ∑ j, ((p.1 j).re ^ 2 + (p.1 j).im ^ 2) := by
      rw [EuclideanSpace.norm_sq_eq]
      exact Finset.sum_congr rfl fun j _ ↦ by rw [Complex.sq_norm, Complex.normSq_apply]; ring
    rw [hn, Finset.sum_add_distrib]
    have : 0 ≤ ∑ j, (p.1 j).im ^ 2 := by positivity
    have : 0 ≤ ‖p.2‖ ^ 2 := by positivity
    linarith [le_abs_self a, le_abs_self b]
  · have : 0 ≤ ∑ j, (p.1 j).im ^ 2 := by positivity
    linarith [le_abs_self a, le_abs_self b, abs_nonneg a, abs_nonneg b]

/-- The handles `{p | t p ≤ γ ^ 2 ∧ s p ≤ (1 + γ) ^ 2}` grow with `γ ≥ 0`. -/
theorem setOf_shape_le_subset_setOf_shape_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    {p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m) |
      (shape p).2 ≤ a ^ 2 ∧ (shape p).1 ≤ (1 + a) ^ 2} ⊆
      {p | (shape p).2 ≤ b ^ 2 ∧ (shape p).1 ≤ (1 + b) ^ 2} :=
  fun _ hp ↦ ⟨hp.1.trans (by gcongr), hp.2.trans (by gcongr)⟩

/-- The handles `{p | t p ≤ γ ^ 2 ∧ s p ≤ (1 + γ) ^ 2}` for `0 < γ < 1` have the model disc
`ι₀ (closedBall 0 1)` as their intersection. -/
theorem iInter_setOf_shape_le_eq :
    ⋂ γ : Ioo (0 : ℝ) 1, {p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m) |
      (shape p).2 ≤ (γ : ℝ) ^ 2 ∧ (shape p).1 ≤ (1 + (γ : ℝ)) ^ 2} =
      modelDisc k m '' closedBall 0 1 := by
  -- A lower bound for a continuous `f` on `(0, 1)` is one for `f 0`.
  have hlim {f : ℝ → ℝ} (hf : Continuous f) {x : ℝ} (h : ∀ γ ∈ Ioo (0 : ℝ) 1, x ≤ f γ) :
      x ≤ f 0 :=
    haveI := left_nhdsWithin_Ioo_neBot (zero_lt_one' ℝ)
    ge_of_tendsto ((hf.tendsto 0).mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall h)
  ext p
  simp only [mem_iInter, mem_ofPred_eq, Subtype.forall]
  constructor
  · intro hp
    have ht : (shape p).2 ≤ 0 := by
      simpa using hlim (f := fun γ ↦ γ ^ 2) (by fun_prop) fun γ hγ ↦ (hp γ hγ).1
    have hs : (shape p).1 ≤ 1 := by
      simpa using hlim (f := fun γ ↦ (1 + γ) ^ 2) (by fun_prop) fun γ hγ ↦ (hp γ hγ).2
    rw [shape_snd] at ht
    have him : ∀ j, (p.1 j).im = 0 := fun j ↦ by
      have : (p.1 j).im ^ 2 ≤ ∑ i, (p.1 i).im ^ 2 :=
        Finset.single_le_sum (f := fun i ↦ (p.1 i).im ^ 2) (fun _ _ ↦ by positivity)
          (Finset.mem_univ j)
      have : 0 ≤ ‖p.2‖ ^ 2 := by positivity
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (by nlinarith [sq_nonneg (p.1 j).im])
    have h2 : p.2 = 0 := by
      have : 0 ≤ ∑ i, (p.1 i).im ^ 2 := by positivity
      exact norm_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1
        (le_antisymm (by linarith) (by positivity)))
    refine ⟨modelDiscProj k m p, ?_, ?_⟩
    · rw [mem_closedBall, dist_zero_right]
      refine (sq_le_one_iff₀ (norm_nonneg _)).1 ?_
      rw [EuclideanSpace.norm_sq_eq]
      simpa [shape_fst] using hs
    · ext j
      · exact Complex.ext (by simp) (by simp [him j])
      · simp [h2]
  · rintro ⟨x, hx, rfl⟩ γ hγ
    rw [mem_closedBall, dist_zero_right] at hx
    have hx2 : ∑ j, x j ^ 2 ≤ 1 := by
      have := pow_le_one₀ (n := 2) (norm_nonneg x) hx
      simpa [EuclideanSpace.norm_sq_eq] using this
    refine ⟨by simpa using sq_nonneg (γ : ℝ), ?_⟩
    simp only [shape_fst, modelDisc_apply_fst_apply, Complex.ofReal_re]
    nlinarith [hγ.1]

end Handle

/-! ### The model handle function and the model level -/

section Model

variable (k m) in
/-- The **model handle function** `b t - a s` on `ℂᵏ × ℂᵐ`, in the shape coordinates
`s = |x|²` and `t = |y|² + |w|²` of `p = (x + i y, w)`. -/
def modelHandle (a b : ℝ) (p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) : ℝ :=
  b * (shape p).2 - a * (shape p).1

theorem modelHandle_def (a b : ℝ) (p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) :
    modelHandle k m a b p = b * (shape p).2 - a * (shape p).1 :=
  (rfl)

/-- For `0 < b` and `a < b`, the model handle function `b t - a s` is strictly plurisubharmonic
at every point of `ℂᵏ × ℂᵐ`. -/
theorem isManifoldStrictlyPlurisubharmonicAt_modelHandle {a b : ℝ} (hb : 0 < b) (hab : a < b)
    (p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) :
    IsManifoldStrictlyPlurisubharmonicAt (EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m))
      (modelHandle k m a b) p := by
  have h := isManifoldStrictlyPlurisubharmonicAt_shape (f := fun s ↦ -a * s)
    (g := fun t ↦ b * t) (p := p) (by fun_prop) (by fun_prop)
    (by simp [iteratedDeriv_succ]; linarith) (fun _ ↦ by simp [iteratedDeriv_succ]; linarith)
  have he : modelHandle k m a b = fun q ↦ -a * (shape q).1 + b * (shape q).2 := by
    funext q
    rw [modelHandle_def]
    ring
  rwa [he]

/-- The real splitting `(x + i y, w) ↦ (√a x, √b (y, w))` of `ℂᵏ × ℂᵐ` as `ℝᵏ × (ℝᵏ × ℂᵐ)`, the
second factor with its `L²` norm, for `0 < a` and `0 < b`. It carries the model handle function
`b t - a s` to Tau Ceti's quadratic model `(u, v) ↦ -‖u‖² + ‖v‖²`
(`SymplecticGeometry.modelHandle_eq_comp`). -/
def modelHandleSplitting {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin k) × WithLp 2 (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℂ (Fin m)) :=
  (((complexEuclideanEquivRealProd (Fin k)).prodCongr (.refl ℝ _)).trans
      (ContinuousLinearEquiv.prodAssoc ℝ _ _ _)).trans
    ((ContinuousLinearEquiv.smulLeft (Units.mk0 √a (Real.sqrt_pos.2 ha).ne')).prodCongr
      ((WithLp.prodContinuousLinearEquiv 2 ℝ _ _).symm.trans
        (ContinuousLinearEquiv.smulLeft (Units.mk0 √b (Real.sqrt_pos.2 hb).ne'))))

theorem modelHandleSplitting_apply {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) :
    modelHandleSplitting ha hb p = (√a • modelDiscProj k m p,
        √b • WithLp.toLp 2 (WithLp.toLp 2 fun j ↦ (p.1 j).im, p.2)) := by
  ext j
  · simp [modelHandleSplitting]
  · apply WithLp.ofLp_injective
    ext j <;> simp [modelHandleSplitting]

/-- For `0 < a` and `0 < b`, the model handle function `b t - a s` is Tau Ceti's quadratic model
`(u, v) ↦ -‖u‖² + ‖v‖²` read through the splitting `modelHandleSplitting`. -/
theorem modelHandle_eq_comp {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    modelHandle k m a b = (fun z ↦ -‖z.1‖ ^ 2 + ‖z.2‖ ^ 2) ∘ modelHandleSplitting ha hb := by
  funext p
  rw [Function.comp_apply, modelHandleSplitting_apply, norm_smul, norm_smul, mul_pow, mul_pow,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.norm_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt ha.le, Real.sq_sqrt hb.le, WithLp.prod_norm_sq_eq_of_L2, modelHandle_def,
    shape_fst, shape_snd]
  simp [EuclideanSpace.real_norm_sq_eq]
  ring

/-- The differential of the splitting is invertible at every point. -/
private theorem isInvertible_fderiv_modelHandleSplitting {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) :
    (fderiv ℝ (modelHandleSplitting ha hb) p).IsInvertible := by
  simp [ContinuousLinearEquiv.fderiv]

/-- For `0 < a` and `0 < b`, the only critical point of the model handle function `b t - a s` on
`ℂᵏ × ℂᵐ` is `0`. -/
theorem criticalPoints_modelHandle {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    criticalPoints 𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m))
      (modelHandle k m a b) = {0} := by
  ext p
  have h := ((modelHandleSplitting ha hb).toDiffeomorph.isLocalDiffeomorph p
    ).mem_criticalPoints_comp_iff (by simp) (f := fun z ↦ -‖z.1‖ ^ 2 + ‖z.2‖ ^ 2)
  rw [ContinuousLinearEquiv.coe_toDiffeomorph, criticalPoints_neg_norm_sq_add_norm_sq] at h
  rw [modelHandle_eq_comp ha hb, h]
  simp

/-- For `0 < a` and `0 < b`, the model handle function `b t - a s` is a Morse function on
`ℂᵏ × ℂᵐ`: its only critical point, `0`, is nondegenerate. -/
theorem isMorse_modelHandle {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IsMorse 𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) (modelHandle k m a b) := by
  have hq := isMorse_modelSpace_iff.1 (isMorse_neg_norm_sq_add_norm_sq
    (E := EuclideanSpace ℝ (Fin k))
    (F := WithLp 2 (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℂ (Fin m))))
  refine isMorse_modelSpace_iff.2 ⟨?_, hasNondegenerateCriticalPointsOn_iff.2 fun p _ hp ↦ ?_⟩
  · rw [modelHandle_eq_comp ha hb]
    exact hq.1.comp (modelHandleSplitting ha hb).contDiff
  · have hp0 : p = 0 := by
      simpa [criticalPoints_modelHandle ha hb] using
        (mem_criticalPoints_iff_fderiv_eq_zero (f := modelHandle k m a b)).2 hp
    subst hp0
    rw [modelHandle_eq_comp ha hb]
    refine IsNondegenerateCriticalPoint.comp ?_ (modelHandleSplitting ha hb).contDiff.contDiffAt
      (isInvertible_fderiv_modelHandleSplitting ha hb 0)
    rw [map_zero]
    exact isNondegenerateCriticalPoint_neg_norm_sq_add_norm_sq

/-- For `0 < a` and `0 < b`, the critical point `0` of the model handle function `b t - a s` on
`ℂᵏ × ℂᵐ` has Morse index `k`. -/
theorem manifoldMorseIndex_modelHandle {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    manifoldMorseIndex 𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m))
      (modelHandle k m a b) 0 = k := by
  have hq : IsNondegenerateCriticalPoint (fun z : EuclideanSpace ℝ (Fin k) ×
      WithLp 2 (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℂ (Fin m)) ↦ -‖z.1‖ ^ 2 + ‖z.2‖ ^ 2)
      (modelHandleSplitting ha hb 0) := by
    rw [map_zero]
    exact isNondegenerateCriticalPoint_neg_norm_sq_add_norm_sq
  rw [manifoldMorseIndex_modelSpace, modelHandle_eq_comp ha hb,
    morseIndex_comp hq.contDiffAt (modelHandleSplitting ha hb).contDiff.contDiffAt
      hq.fderiv_eq_zero (isInvertible_fderiv_modelHandleSplitting ha hb 0),
    morseIndex_neg_norm_sq_add_norm_sq, finrank_euclideanSpace_fin]


variable (k m) in
/-- The **model level** `φ₀ = 1 - s + 2 t` on `ℂᵏ × ℂᵐ`, in the shape coordinates `s = |x|²` and
`t = |y|² + |w|²` of `p = (x + i y, w)`. -/
def modelLevel (p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) : ℝ :=
  1 - (shape p).1 + 2 * (shape p).2

theorem modelLevel_def (p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) :
    modelLevel k m p = 1 - (shape p).1 + 2 * (shape p).2 :=
  (rfl)

/-- The model level is `1` plus the model handle function with `a = 1` and `b = 2`. -/
theorem modelLevel_eq : modelLevel k m = fun p ↦ 1 + modelHandle k m 1 2 p := by
  funext p
  rw [modelLevel_def, modelHandle_def]
  ring

/-- The model level is strictly plurisubharmonic at every point of `ℂᵏ × ℂᵐ`, as a function on a
complex vector space. -/
theorem isStrictlyPlurisubharmonicAt_modelLevel
    (p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) :
    IsStrictlyPlurisubharmonicAt (modelLevel k m) p := by
  have h := isStrictlyPlurisubharmonicAt_shape (f := fun s ↦ 1 - s)
    (g := fun t ↦ 2 * t) (p := p) (by fun_prop) (by fun_prop)
    (by simp [iteratedDeriv_succ]) (fun _ ↦ by simp [iteratedDeriv_succ])
  simpa only [funext modelLevel_def] using h

/-- The model level is strictly plurisubharmonic at every point of `ℂᵏ × ℂᵐ`. -/
theorem isManifoldStrictlyPlurisubharmonicAt_modelLevel
    (p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) :
    IsManifoldStrictlyPlurisubharmonicAt (EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m))
      (modelLevel k m) p := by
  rw [isManifoldStrictlyPlurisubharmonicAt_iff]
  simpa only [manifoldLeviForm_eq_leviForm, ← isStrictlyPlurisubharmonicAt_iff] using
    isStrictlyPlurisubharmonicAt_modelLevel p

/-- The only critical point of the model level on `ℂᵏ × ℂᵐ` is `0`. -/
theorem criticalPoints_modelLevel :
    criticalPoints 𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m))
      (modelLevel k m) = {0} := by
  rw [← criticalPoints_modelHandle one_pos two_pos]
  ext p
  simp only [mem_criticalPoints_iff_fderiv_eq_zero, modelLevel_eq, fderiv_const_add]

/-- The model level takes the value `1` at the origin. -/
theorem modelLevel_zero : modelLevel k m 0 = 1 := by
  simp [modelLevel_def, shape_fst, shape_snd]

/-- **The model level is a J-convex level**: `0` is a regular value of `φ₀ = 1 - s + 2 t` on
`ℂᵏ × ℂᵐ`, and `φ₀` is strictly plurisubharmonic on its zero level. -/
theorem isJConvexLevel_modelLevel :
    IsJConvexLevel (EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) (modelLevel k m) 0 := by
  refine ⟨isRegularValue_iff_notMem_image_criticalPoints.2 ?_,
    fun p _ ↦ isManifoldStrictlyPlurisubharmonicAt_modelLevel p⟩
  rintro ⟨p, hp, hp0⟩
  rw [criticalPoints_modelLevel, Set.mem_singleton_iff] at hp
  subst hp
  rw [modelLevel_zero] at hp0
  exact one_ne_zero hp0

/-- The model level is smooth. -/
theorem contDiff_modelLevel {n : WithTop ℕ∞} : ContDiff ℝ n (modelLevel k m) := by
  simp only [funext modelLevel_def]
  exact (contDiff_const.sub (contDiff_shape.fst)).add (contDiff_const.mul contDiff_shape.snd)

/-- The Levi form of the model level `φ₀ = 1 - s + 2 t` on `v = (v₁, v₂)` has real part
`|v₁|² / 2 + 2 |v₂|²`, at every point. -/
theorem re_leviForm_modelLevel_apply_self
    (p v : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) :
    (leviForm (modelLevel k m) p v v).re = ‖v.1‖ ^ 2 / 2 + 2 * ‖v.2‖ ^ 2 := by
  have h : modelLevel k m = (fun _ ↦ (1 : ℝ)) +
      (-(fun q ↦ (shape q).1) + (2 : ℝ) • fun q ↦ (shape q).2) := by
    funext q
    simp only [modelLevel_def, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have h₁ : ContDiffAt ℝ 2 (fun q : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m) ↦
      (shape q).1) p := contDiff_shape.fst.contDiffAt
  have h₂ : ContDiffAt ℝ 2 (fun q : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m) ↦
      (shape q).2) p := contDiff_shape.snd.contDiffAt
  have h₃ : ContDiffAt ℝ 2 (-(fun q ↦ (shape q).1) + (2 : ℝ) • fun q ↦ (shape q).2) p :=
    h₁.neg.add (h₂.const_smul (2 : ℝ))
  rw [h, leviForm_add contDiffAt_const h₃, leviForm_add (f := -(fun q ↦ (shape q).1))
    (g := (2 : ℝ) • fun q ↦ (shape q).2) h₁.neg (h₂.const_smul (2 : ℝ)),
    leviForm_const, leviForm_neg, leviForm_smul]
  have hs : (leviForm (fun q ↦ (shape q).1) p v v).re = ‖v.1‖ ^ 2 / 2 := by
    rw [leviForm_shape_fst_apply, Complex.div_ofNat_re, ← RCLike.re_to_complex,
      inner_self_eq_norm_sq]
  simp only [LinearMap.add_apply, LinearMap.neg_apply, LinearMap.smul_apply,
    zero_add, Complex.add_re, Complex.neg_re, smul_eq_mul,
    Complex.re_ofReal_mul, hs, re_leviForm_shape_snd_apply_self]
  ring

/-- **The margin of the model level on bounded sets.** For every `R` there is `c > 0` such that
at every point `p` with `‖p‖ ≤ R`, the real part of the Levi form of the model level is at
least `c max ‖D²φ₀ p‖ ‖Dφ₀ p‖ ‖v‖²`. -/
theorem exists_pos_mul_max_norm_le_re_leviForm_modelLevel (R : ℝ) :
    ∃ c > 0, ∀ p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m), ‖p‖ ≤ R → ∀ v,
      c * max ‖fderiv ℝ (fderiv ℝ (modelLevel k m)) p‖ ‖fderiv ℝ (modelLevel k m) p‖ *
        ‖v‖ ^ 2 ≤ (leviForm (modelLevel k m) p v v).re := by
  have h := contDiff_modelLevel (k := k) (m := m) (n := ∞)
  have hc : Continuous fun p ↦
      max ‖fderiv ℝ (fderiv ℝ (modelLevel k m)) p‖ ‖fderiv ℝ (modelLevel k m) p‖ :=
    ((h.fderiv_right (m := 1) (by simp)).continuous_fderiv (by simp)).norm.max
      (h.continuous_fderiv (by simp)).norm
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : EuclideanSpace ℂ (Fin k) ×
    EuclideanSpace ℂ (Fin m)) R).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨(2 * (|B| + 1))⁻¹, by positivity, fun p hp v ↦ ?_⟩
  have hpB := hB p (mem_closedBall_zero_iff.2 hp)
  rw [Real.norm_of_nonneg (le_max_of_le_right (norm_nonneg _))] at hpB
  have hmax : (2 * (|B| + 1))⁻¹ *
      max ‖fderiv ℝ (fderiv ℝ (modelLevel k m)) p‖ ‖fderiv ℝ (modelLevel k m) p‖ ≤ 1 / 2 := by
    rw [inv_mul_le_iff₀ (by positivity)]
    linarith [le_abs_self B]
  have hv : ‖v‖ ^ 2 ≤ ‖v.1‖ ^ 2 + ‖v.2‖ ^ 2 := by
    rw [Prod.norm_def]
    rcases max_cases ‖v.1‖ ‖v.2‖ with ⟨h', -⟩ | ⟨h', -⟩ <;> rw [h'] <;>
      nlinarith [sq_nonneg ‖v.1‖, sq_nonneg ‖v.2‖]
  rw [re_leviForm_modelLevel_apply_self]
  nlinarith [mul_le_mul_of_nonneg_right hmax (sq_nonneg ‖v‖), sq_nonneg ‖v.2‖]

/-- On the model disc, the model level is `φ₀ (ι₀ x) = 1 - |x|²`. -/
theorem modelLevel_modelDisc (x : EuclideanSpace ℝ (Fin k)) :
    modelLevel k m (modelDisc k m x) = 1 - ‖x‖ ^ 2 := by
  simp [modelLevel_def, EuclideanSpace.real_norm_sq_eq]

open scoped InnerProductSpace in
/-- The differential of the model level `φ₀ = 1 - s + 2 t` at `p = (x + i y, w)` is
`v ↦ -2 ∑ⱼ xⱼ Re v₁ⱼ + 4 (∑ⱼ yⱼ Im v₁ⱼ + Re ⟪w, v₂⟫)`. -/
theorem fderiv_modelLevel_apply (p v : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) :
    fderiv ℝ (modelLevel k m) p v = -(2 * ∑ j, (p.1 j).re * (v.1 j).re) +
      2 * (2 * (∑ j, (p.1 j).im * (v.1 j).im + (⟪p.2, v.2⟫_ℂ).re)) := by
  have h1 : DifferentiableAt ℝ (fun q ↦ (shape q).1) p :=
    (contDiff_fst.comp (contDiff_shape (n := 1))).differentiable one_ne_zero p
  have h2 : DifferentiableAt ℝ (fun q ↦ (shape q).2) p :=
    (contDiff_snd.comp (contDiff_shape (n := 1))).differentiable one_ne_zero p
  have h : HasFDerivAt (modelLevel k m)
      (-fderiv ℝ (fun q ↦ (shape q).1) p + (2 : ℝ) • fderiv ℝ (fun q ↦ (shape q).2) p) p := by
    refine ((((hasFDerivAt_const (1 : ℝ) p).sub h1.hasFDerivAt).add
      (h2.hasFDerivAt.const_mul (2 : ℝ))).congr_of_eventuallyEq
        (.of_forall fun q ↦ ?_)).congr_fderiv (by rw [zero_sub])
    simp only [Pi.add_apply, Pi.sub_apply, modelLevel_def]
  rw [h.fderiv, add_apply, neg_apply, smul_apply, smul_eq_mul, fderiv_shape_fst_apply,
    fderiv_shape_snd_apply]

/-- **The model of a J-orthogonally attached disc.** The model disc `ι₀ : x ↦ (x, 0)` of
`ℂᵏ × ℂᵐ` is attached J-orthogonally to the domain `{φ₀ ≤ 0}` of the model level
`φ₀ = 1 - |x|² + 2 (|y|² + |w|²)`, at `p = (x + i y, w)`. -/
theorem isJOrthogonallyAttached_model :
    IsJOrthogonallyAttached (EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m))
      (modelLevel k m) (modelDisc k m) := by
  refine ⟨fun x hx ↦ ?_, fun x hx ↦ ?_, fun x hx ↦ ?_, fun x _ v ↦ ?_⟩
  · rw [modelLevel_modelDisc]
    nlinarith [norm_nonneg x]
  · rw [modelLevel_modelDisc, hx]
    norm_num
  · -- The radial derivative is `-2 |x|²`.
    have key : mvfderiv 𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m))
        (modelLevel k m) (modelDisc k m x) (modelDisc k m x) = -2 := by
      refine (mvfderiv_eq_fderiv_apply _ _ _).trans ((fderiv_modelLevel_apply _ _).trans ?_)
      simp [← sq, ← EuclideanSpace.real_norm_sq_eq, hx]
    rw [mfderiv_modelDisc]
    exact key.trans_lt (by norm_num)
  · -- The differential at `ι₀ x` only sees the real parts of the first factor.
    have key : mvfderiv 𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m))
        (modelLevel k m) (modelDisc k m x) (Complex.I • modelDisc k m v) = 0 := by
      refine (mvfderiv_eq_fderiv_apply _ _ _).trans ((fderiv_modelLevel_apply _ _).trans ?_)
      simp
    rw [mfderiv_modelDisc]
    exact key

/-- **The model carried through a chart.** Let `Φ` be a partial diffeomorphism from `ℂᵏ × ℂᵐ`
to a complex manifold `M`, defined on the model disc `ι₀ (closedBall 0 1)`, whose differential
commutes with multiplication by `i` at the points of the boundary sphere. Then `Φ ∘ ι₀` is
attached J-orthogonally to the domain `{φ₀ ∘ Φ.symm ≤ 0}` of the model level read through `Φ`. -/
theorem isJOrthogonallyAttached_modelLevel_comp_symm {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M] {n : WithTop ℕ∞}
    (hn : n ≠ 0) (Φ : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m))
      𝓘(ℝ, E) (EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) M n)
    (hsrc : modelDisc k m '' Metric.closedBall 0 1 ⊆ Φ.source)
    (hI : ∀ x : EuclideanSpace ℝ (Fin k), ‖x‖ = 1 →
      ∀ v : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m),
        mfderiv 𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) 𝓘(ℝ, E) Φ
          (modelDisc k m x) (Complex.I • v) =
        Complex.I • (show E from mfderiv 𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m))
          𝓘(ℝ, E) Φ (modelDisc k m x) v)) :
    IsJOrthogonallyAttached E (modelLevel k m ∘ Φ.symm) (Φ ∘ modelDisc k m) :=
  isJOrthogonallyAttached_model.map_partialDiffeomorph hn Φ hsrc hI

end Model

end SymplecticGeometry

end
