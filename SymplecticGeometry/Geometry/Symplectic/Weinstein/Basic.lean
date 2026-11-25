/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Morse.BirthDeath
public import SymplecticGeometry.Geometry.Manifold.Morse.GradientLike
public import TauCeti.Geometry.Manifold.Flow.Complete
public import TauCeti.Geometry.Symplectic.Liouville.VectorField
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
import Mathlib.Geometry.Manifold.Riemannian.Basic
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.Calculus.Morse.ShapeOperator
import TauCeti.Geometry.Manifold.Flow.NormedSpace
import TauCeti.Geometry.Manifold.Riemannian.Gradient.NormedSpace
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Basic
import TauCeti.Geometry.Symplectic.Liouville.Radial.Basic
import TauCeti.Topology.Maps.Proper.Metric

/-!
# Weinstein structures

A *Weinstein structure* on a boundaryless manifold `M` is a triple `(ω, X, f)`: a symplectic
form `ω`, a smooth complete Liouville vector field `X` of `ω` (so `L_X ω = ω`), and a proper
generalized Morse function `f : M → ℝ`, bounded below, for which `X` is gradient-like in the
quantitative sense of `TauCeti.IsGradientLike`. The primitive `λ = ι_X ω` is not part of the data:
it satisfies `dλ = ω` (`SymplecticGeometry.IsWeinsteinStructure.mextDeriv_interior`).

## Main declarations

* `SymplecticGeometry.IsWeinsteinStructure`: the predicate on a triple `(ω, X, f)`, with
  `SymplecticGeometry.isWeinsteinStructure_iff`.
* `SymplecticGeometry.IsWeinsteinStructure.mextDeriv_interior`: `d(ι_X ω) = ω`.
* `SymplecticGeometry.IsWeinsteinStructure.comp`: `(ω, X, h ∘ f)` is a Weinstein structure for a
  smooth `h` with `h' > 0` on the values of `f`, as long as `h ∘ f` stays proper and bounded
  below.
* `SymplecticGeometry.isWeinsteinStructure_constSmooth_norm_sq`: a linear symplectic form on a
  finite-dimensional real inner product space, with the radial field `x ↦ x / 2` and the function
  `x ↦ ‖x‖ ^ 2`, is a Weinstein structure; for instance `ℂⁿ` with its standard form and `|z|²`.

## Implementation notes

As in Cieliebak–Eliashberg, the field is part of the data, and not an existential, since the
gradient-like condition and Weinstein homotopies both mention it. The function is a plain
`M → ℝ`, the representation that `SymplecticGeometry.IsSteinFunction` uses.

The example follows Tau Ceti's `TauCeti.SymplecticForm.isLiouvilleDomain_closedBall` for the
Liouville part (the field `x / 2` and the primitive `TauCeti.SymplecticForm.radialPrimitive`). The
field `x / 2` is a quarter of the gradient `2 x` of `‖x‖ ^ 2` for the flat metric
`riemannianMetricVectorSpace`, so it is gradient-like by `TauCeti.isGradientLike_mgradient` and
`TauCeti.IsGradientLike.smul`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Definitions 7.4.5 and 7.4.7
* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  Chapter 11
-/

public section

open Bundle Set TauCeti TauCeti.Manifold
open scoped Manifold

namespace SymplecticGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) (⊤ : ℕ∞) M]

/-- A **Weinstein structure** on `M` is a triple `(ω, X, f)` of a symplectic form `ω`, a smooth
complete Liouville vector field `X` of `ω`, and a proper generalized Morse function `f`, bounded
below, for which `X` is gradient-like. -/
structure IsWeinsteinStructure (ω : SmoothTwoForm 𝓘(ℝ, E) M)
    (X : (x : M) → TangentSpace 𝓘(ℝ, E) x) (f : M → ℝ) : Prop where
  /-- The form is symplectic. -/
  isSymplectic : ω.IsSymplectic
  /-- The vector field is smooth. -/
  contMDiff_field : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent (⊤ : ℕ∞) (T% X)
  /-- The vector field is a Liouville field of the form: `L_X ω = ω`. -/
  isLiouvilleVectorField : IsLiouvilleVectorField ω.val X
  /-- The vector field is complete. -/
  isCompleteVectorField : IsCompleteVectorField X
  /-- The function is proper. -/
  isProperMap : IsProperMap f
  /-- The function is bounded below. -/
  bddBelow : BddBelow (range f)
  /-- The function is a generalized Morse function. -/
  isGeneralizedMorse : IsGeneralizedMorse E f
  /-- The vector field is gradient-like for the function. -/
  isGradientLike : IsGradientLike f X

variable {ω : SmoothTwoForm 𝓘(ℝ, E) M} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ}

/-- The conditions of `SymplecticGeometry.IsWeinsteinStructure`, as a conjunction. -/
theorem isWeinsteinStructure_iff :
    IsWeinsteinStructure ω X f ↔
      ω.IsSymplectic ∧ ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent (⊤ : ℕ∞) (T% X) ∧
        IsLiouvilleVectorField ω.val X ∧ IsCompleteVectorField X ∧ IsProperMap f ∧
          BddBelow (range f) ∧ IsGeneralizedMorse E f ∧ IsGradientLike f X :=
  ⟨fun h ↦ ⟨h.isSymplectic, h.contMDiff_field, h.isLiouvilleVectorField, h.isCompleteVectorField,
      h.isProperMap, h.bddBelow, h.isGeneralizedMorse, h.isGradientLike⟩,
    fun ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩ ↦ ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩⟩

namespace IsWeinsteinStructure

/-- The one-form `λ = ι_X ω` of a Weinstein structure is a primitive of `ω`: `dλ = ω`. -/
theorem mextDeriv_interior (hW : IsWeinsteinStructure ω X f) :
    mextDeriv (RoughForm.interior X ω.val) = ω.val :=
  (isLiouvilleVectorField_iff_mextDeriv_interior_eq ω.mdifferentiable
    (hW.contMDiff_field.mdifferentiable (by simp))
    ((SmoothForm.isClosed_def _).1 hW.isSymplectic.isClosed)).1
    hW.isLiouvilleVectorField

/-- Reparametrizing the function of a Weinstein structure `(ω, X, f)` by a smooth `h : ℝ → ℝ`
with `h' > 0` at every value of `f` gives a Weinstein structure `(ω, X, h ∘ f)`, as long as
`h ∘ f` is proper and bounded below. -/
theorem comp (hW : IsWeinsteinStructure ω X f) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hpos : ∀ x, 0 < deriv h (f x)) (hp : IsProperMap (h ∘ f)) (hb : BddBelow (range (h ∘ f))) :
    IsWeinsteinStructure ω X (h ∘ f) where
  isSymplectic := hW.isSymplectic
  contMDiff_field := hW.contMDiff_field
  isLiouvilleVectorField := hW.isLiouvilleVectorField
  isCompleteVectorField := hW.isCompleteVectorField
  isProperMap := hp
  bddBelow := hb
  isGeneralizedMorse := hW.isGeneralizedMorse.comp hh hpos
  isGradientLike := hW.isGradientLike.comp (hW.isGeneralizedMorse.contMDiff.mdifferentiable
    (by simp)) (hh.of_le (by simp)) hpos

end IsWeinsteinStructure

/-! ### The radial Weinstein structure of a symplectic vector space -/

section Radial

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- **The radial Weinstein structure.** On a finite-dimensional real inner product space `V` with
a linear symplectic form `ω`, the constant form `ω`, the radial field `x ↦ x / 2` and the
function `x ↦ ‖x‖ ^ 2` form a Weinstein structure. -/
theorem isWeinsteinStructure_constSmooth_norm_sq (ω : SymplecticForm V) :
    IsWeinsteinStructure ω.constSmooth (fun x : V ↦ (2⁻¹ : ℝ) • x) (fun x ↦ ‖x‖ ^ 2) where
  isSymplectic := ω.isSymplectic_constSmooth
  contMDiff_field := contMDiff_dilation _ _
  isLiouvilleVectorField := by
    rw [isLiouvilleVectorField_iff_mextDeriv_interior_eq ω.constSmooth.mdifferentiable
      ((contMDiff_dilation _ 1).mdifferentiable one_ne_zero)
      ((SmoothForm.isClosed_def _).1 ω.isClosed_constSmooth),
      ω.constSmooth_interior_two_inv_smul, ω.mextDeriv_radialPrimitive]
  isCompleteVectorField := isCompleteVectorField_dilation _
  isProperMap := by simpa using isProperMap_norm_sq_sub (0 : V)
  bddBelow := ⟨0, by rintro _ ⟨x, rfl⟩; positivity⟩
  isGeneralizedMorse := by
    refine IsMorse.isGeneralizedMorse (isMorse_modelSpace_iff.2
      ⟨contDiff_norm_sq ℝ, hasNondegenerateCriticalPointsOn_iff.2 fun x _ hx ↦ ?_⟩)
    have hid : Function.Injective (fderiv ℝ (id : V → V) x) := by simp [Function.injective_id]
    have key := isNondegenerateCriticalPoint_norm_sq_sub_comp_iff (a := (0 : V))
      (contDiffAt_id (𝕜 := ℝ) (x := x)) hid
    have hx' := (fderiv_norm_sq_sub_comp_eq_zero_iff (a := (0 : V))
      (differentiableAt_id (𝕜 := ℝ) (x := x))).1 (by simpa using hx)
    simp only [id_eq, sub_zero] at key hx'
    refine key.2 ⟨hx', ?_⟩
    have hx0 : x = 0 := by simpa using hx'
    subst hx0
    simp only [sub_self, shapeOperator_zero, Module.End.hasEigenvalue_iff, not_not]
    ext v
    simp [eq_comm]
  isGradientLike := by
    have hg := (isGradientLike_mgradient ((riemannianMetricVectorSpace V).ofLE le_top)
      (fun x : V ↦ ‖x‖ ^ 2)).smul (a := fun _ ↦ (4 : ℝ)⁻¹) continuous_const
      (fun _ ↦ by norm_num)
    refine (congrArg (IsGradientLike _) (funext fun x ↦ ?_)).mpr hg
    have h2 : gradient (fun y : V ↦ ‖y‖ ^ 2) x = (2 : ℝ) • x := by
      simpa using gradient_norm_sq_sub (0 : V) x
    rw [mgradient_eq_gradient_of_eq
      (inst := ⟨((riemannianMetricVectorSpace V).ofLE le_top).toRiemannianMetric⟩)
      (ContMDiffRiemannianMetric.toRiemannianMetric_ofLE _ _), h2]
    -- The two sides live in `TangentSpace 𝓘(ℝ, V) x`, which is `V` only up to unfolding, so
    -- `smul_smul` is applied to the statement in `V`.
    exact (by rw [smul_smul]; norm_num : (2⁻¹ : ℝ) • x = (4⁻¹ : ℝ) • (2 : ℝ) • x)

end Radial

end SymplecticGeometry

end
