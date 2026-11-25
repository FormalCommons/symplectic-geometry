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
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.LocalDiffeomorph
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.Calculus.Morse.NormSq
import TauCeti.Geometry.Manifold.Flow.Diffeomorph
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
* `SymplecticGeometry.IsWeinsteinStructure.pullback`: a diffeomorphism `Φ : M' → M` pulls a
  Weinstein structure `(ω, X, f)` back to `(Φ^* ω, Φ^* X, f ∘ Φ)`.
* `SymplecticGeometry.isWeinsteinStructure_constSmooth_norm_sq`: a linear symplectic form on a real
  inner product space of finite dimension, with the radial field `x ↦ x / 2` and the function
  `x ↦ ‖x‖ ^ 2`, is a Weinstein structure; for instance `ℂⁿ` with its standard form and `|z|²`.

## Implementation notes

As in Cieliebak–Eliashberg, the field is part of the data, and not an existential, since the
gradient-like condition and Weinstein homotopies both mention it. The function is a plain
`M → ℝ`, the representation that `SymplecticGeometry.IsSteinFunction` uses.

For the pull-back, the form stays symplectic by Tau Ceti's
`IsLocalDiffeomorph.isSymplectic_mpullback_iff`, and the field stays Liouville by the pointwise
naturality of the Lie derivative of a closed two-form,
`IsLocalDiffeomorphAt.mlieDerivForm_apply_eq_iff`. The field stays complete because `Φ⁻¹` carries
`X` to it (`Diffeomorph.mfderiv_symm_apply_eq_of_mfderiv_apply_eq`,
`MDifferentiable.isCompleteVectorField_of_surjective`); the function and the field remain
generalized Morse and gradient-like by `TauCeti.IsGeneralizedMorse.comp_diffeomorph`
and `TauCeti.IsGradientLike.mpullback`.

The example follows Tau Ceti's `TauCeti.SymplecticForm.isLiouvilleDomain_closedBall` for the
Liouville part (the field `x / 2` and the primitive `TauCeti.SymplecticForm.radialPrimitive`). The
origin is the only critical point of `‖x‖ ^ 2`, and it is nondegenerate, by
`TauCeti.fderiv_norm_sq_eq_zero_iff` and `TauCeti.isNondegenerateCriticalPoint_norm_sq`. The
field `x / 2` is a quarter of the gradient `2 x` of `‖x‖ ^ 2` for the flat metric
`riemannianMetricVectorSpace`, so it is gradient-like by `TauCeti.isGradientLike_mgradient` and
`TauCeti.IsGradientLike.smul`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Definition 7.4.5
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

/-- **Weinstein structures pull back along diffeomorphisms.** If `(ω, X, f)` is a Weinstein
structure on `M` and `Φ : M' → M` is a diffeomorphism, then the pulled-back form `Φ^* ω`, the
pulled-back field `VectorField.mpullback Φ X x = (dΦ_x)⁻¹ (X (Φ x))` and the function `f ∘ Φ` form
a Weinstein structure on `M'`. -/
theorem pullback (hW : IsWeinsteinStructure ω X f) {M' : Type*} [TopologicalSpace M']
    [ChartedSpace E M'] [IsManifold 𝓘(ℝ, E) (⊤ : ℕ∞) M']
    (Φ : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M' M (⊤ : ℕ∞)) :
    IsWeinsteinStructure (SmoothForm.mpullback Φ Φ.contMDiff ω)
      (VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) Φ X) (f ∘ Φ) := by
  have hsymp : SmoothTwoForm.IsSymplectic (SmoothForm.mpullback Φ Φ.contMDiff ω) :=
    (Φ.isLocalDiffeomorph.isSymplectic_mpullback_iff Φ.surjective).2 hW.isSymplectic
  have hX : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent (⊤ : ℕ∞)
      (T% (VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) Φ X)) :=
    hW.contMDiff_field.mpullback_vectorField Φ.contMDiff
      (fun _ ↦ Φ.isInvertible_mfderiv (by simp)) le_rfl
  have hΦX := Φ.mfderiv_apply_mpullback (by simp) X
  refine ⟨hsymp, hX, ?_, ?_, hW.isProperMap.comp Φ.toHomeomorph.isProperMap, ?_,
    hW.isGeneralizedMorse.comp_diffeomorph Φ,
    hW.isGradientLike.mpullback Φ.contMDiff fun _ ↦ Φ.isInvertible_mfderiv (by simp)⟩
  · -- Pointwise, `L_{Φ^* X} Φ^* ω = Φ^* ω` at `x` is `L_X ω = ω` at `Φ x`.
    refine isLiouvilleVectorField_iff.2 (funext fun x ↦ ?_)
    have h := ((Φ.isLocalDiffeomorph x).mlieDerivForm_apply_eq_iff
      (η := SmoothForm.mpullback Φ Φ.contMDiff ω)
      (.of_forall fun _ ↦ by rw [SmoothForm.coe_mpullback]) ((hX x).of_le (by simp))
      ((hW.contMDiff_field (Φ x)).of_le (by simp)) (.of_forall hΦX)
      (congrFun ((SmoothForm.isClosed_def _).1 hW.isSymplectic.isClosed) (Φ x))).1
      (congrFun (isLiouvilleVectorField_iff.1 hW.isLiouvilleVectorField) (Φ x))
    simpa only [SmoothForm.coe_mpullback] using h
  · -- `Φ⁻¹` carries `X` to the pulled-back field, so it carries integral curves to integral curves.
    exact MDifferentiable.isCompleteVectorField_of_surjective
      (Φ.symm.contMDiff.mdifferentiable (by simp)) Φ.symm.surjective
      (Φ.mfderiv_symm_apply_eq_of_mfderiv_apply_eq (by simp) hΦX) hW.isCompleteVectorField
  · simpa [range_comp] using hW.bddBelow

end IsWeinsteinStructure

/-! ### The radial Weinstein structure of a symplectic vector space -/

section Radial

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- **The radial Weinstein structure.** Let `V` be a real inner product space of finite
dimension, with a linear symplectic form `ω`. Then the constant form `ω`, the radial field
`x ↦ x / 2` and the function `x ↦ ‖x‖ ^ 2` form a Weinstein structure. -/
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
  isGeneralizedMorse := IsMorse.isGeneralizedMorse (isMorse_modelSpace_iff.2
    ⟨contDiff_norm_sq ℝ, hasNondegenerateCriticalPointsOn_iff.2 fun _ _ hx ↦
      fderiv_norm_sq_eq_zero_iff.1 hx ▸ isNondegenerateCriticalPoint_norm_sq⟩)
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
