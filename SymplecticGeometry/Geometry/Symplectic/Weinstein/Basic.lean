/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Morse.BirthDeath
public import SymplecticGeometry.Geometry.Manifold.Morse.GradientLike
public import SymplecticGeometry.Geometry.Symplectic.Liouville.Filling
public import SymplecticGeometry.Geometry.Symplectic.Liouville.Sublevel
public import TauCeti.Geometry.Manifold.Boundary.Interior
public import TauCeti.Geometry.Manifold.Flow.Complete
public import TauCeti.Geometry.Manifold.RegularValue.NormSq
public import TauCeti.Geometry.Symplectic.Liouville.VectorField
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
import Mathlib.Geometry.Manifold.Riemannian.Basic
import SymplecticGeometry.Geometry.Manifold.Boundary.Interior
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.LocalDiffeomorph
import SymplecticGeometry.Geometry.Manifold.VectorField.Pullback
import SymplecticGeometry.Topology.Maps.Proper
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

A *Weinstein domain* `(W, σ, Y, f)` lives on a manifold `W` with boundary over the
half-space `𝓡∂ (n + 1)`: `(σ, Y)` is a Liouville domain (`SymplecticGeometry.IsStrongFilling` with
the field Liouville on all of `W`), and `f` is smooth, constant equal to `c` on `∂W`, below `c`
elsewhere, and increasing along `Y` at the boundary; on the interior of `W`, as a boundaryless
manifold over `ℝⁿ⁺¹`, `f` is generalized Morse and `Y` gradient-like for it. A Weinstein
domain is compact; the predicate leaves that to the instance `CompactSpace W`, which the
results that need it take.

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
* `SymplecticGeometry.IsWeinsteinDomain`: the predicate on `(σ, Y, f, c)`, with
  `SymplecticGeometry.isWeinsteinDomain_iff`.
* `SymplecticGeometry.IsWeinsteinDomain.le`,
  `SymplecticGeometry.IsWeinsteinDomain.preimage_singleton_eq_boundary` and
  `SymplecticGeometry.IsWeinsteinDomain.level_unique`: `f ≤ c`, the boundary is the level
  `f ⁻¹' {c}`, and `f` determines `c` when the boundary is nonempty.
* `SymplecticGeometry.IsWeinsteinDomain.criticalPoints_subset_interior` and
  `SymplecticGeometry.IsWeinsteinDomain.finite_criticalPoints`: the critical points of `f` are
  interior points, and there are finitely many of them.
* `SymplecticGeometry.IsWeinsteinStructure.compactSpace_sublevel` and
  `SymplecticGeometry.IsWeinsteinStructure.isWeinsteinDomain_scalarRegularSublevel`: a sublevel
  `{f ≤ c}` of a Weinstein structure at a regular value `c` is compact, and with the pulled-back
  form and field it is a Weinstein domain.
* `SymplecticGeometry.isWeinsteinDomain_norm_sq_le_one`: the closed unit ball of a symplectic
  inner product space is a Weinstein domain.

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

For a Weinstein domain the interior of `W` is Tau Ceti's charted interior
`(𝓡∂ (n + 1)).interior W` (`ModelWithCorners.instChartedSpaceInterior`), whose charts are the
extended charts of `W`; its tangent spaces and those of `W` are both `ℝⁿ⁺¹`, so `Y` restricts
to it without change. Compactness of `W` is an instance argument rather than a field, as in
`SymplecticGeometry.IsStrongFilling.isLiouvilleCompletion_completion`. The derivative of
`f` along `Y` is positive on `∂W`, so the critical points of `f` are interior points; they form a
closed, hence compact, subset of `W`. The inclusion of the interior is a local diffeomorphism
(`ModelWithCorners.isLocalDiffeomorph_subtypeVal_interior`), so they are critical points of the
restriction of `f`, in a compact subset of the interior, and so finitely many by
`TauCeti.IsGeneralizedMorse.finite_criticalPoints_inter`.

For a regular sublevel `W = {f ≤ c}` of a Weinstein structure, Tau Ceti's
`TauCeti.boundary_scalarRegularSublevel` and `TauCeti.interior_scalarRegularSublevel` identify
`∂W` with the level and the interior with `{f < c}`. The level is regular, so `df ≠ 0` there and
the gradient-like field increases `f` along it
(`TauCeti.IsGradientLike.mvfderiv_apply_pos_of_isRegularValue`);
this gives the boundary condition and, through
`SymplecticGeometry.isStrongFilling_scalarRegularSublevel`, the Liouville domain. On the interior,
the inclusion into `M` is the inclusion into `W` after that of the interior, whose differential is
the identity (`ModelWithCorners.mfderiv_subtypeVal_interior`). So its differentials are invertible
(`TauCeti.isInvertible_mfderiv_subtypeVal_scalarRegularSublevel`), it is a local diffeomorphism by
the inverse function theorem `TauCeti.isLocalDiffeomorph_of_mfderiv_eq`, and the restricted
function and field stay generalized Morse and gradient-like by
`TauCeti.IsGeneralizedMorse.comp_isLocalDiffeomorph` and `TauCeti.IsGradientLike.mpullback`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Definition 7.4.5 (Weinstein manifolds and domains)
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

/-! ### Weinstein domains -/

section Domain

open scoped ContDiff

variable {n : ℕ} {W : Type*} [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
  [IsManifold (𝓡∂ (n + 1)) ∞ W]

/-- A **Weinstein domain** `(W, σ, Y, f)` with top level `c`, on a manifold `W` with
boundary (compact in the definition; results that need it take `CompactSpace W`): `(σ, Y)`
makes it a Liouville domain (a strong filling whose field is Liouville everywhere), and
`f : W → ℝ` is smooth, equal to `c` on the boundary and less than `c` at interior points, with
`df(Y) > 0` along the boundary. On the interior of `W`, a boundaryless manifold over
`ℝⁿ⁺¹` (Tau Ceti's `ModelWithCorners.instChartedSpaceInterior`), `f` is generalized Morse and `Y`
is gradient-like for `f`.

The level `c` is a parameter, although `f` determines it as soon as the boundary is nonempty. -/
structure IsWeinsteinDomain (σ : SmoothTwoForm (𝓡∂ (n + 1)) W)
    (Y : (x : W) → TangentSpace (𝓡∂ (n + 1)) x) (f : W → ℝ) (c : ℝ) : Prop where
  /-- The form and the field make `W` a Liouville domain. -/
  isStrongFilling : IsStrongFilling σ univ Y
  /-- The function is smooth. -/
  contMDiff : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ f
  /-- The function is `c` on the boundary. -/
  eq_of_mem_boundary : ∀ x ∈ (𝓡∂ (n + 1)).boundary W, f x = c
  /-- The function is less than `c` at interior points. -/
  lt_of_mem_interior : ∀ x ∈ (𝓡∂ (n + 1)).interior W, f x < c
  /-- The field increases the function along the boundary. -/
  mvfderiv_pos : ∀ x ∈ (𝓡∂ (n + 1)).boundary W, 0 < mvfderiv (𝓡∂ (n + 1)) f x (Y x)
  /-- On the interior, the function is generalized Morse. -/
  isGeneralizedMorse :
    IsGeneralizedMorse (EuclideanSpace ℝ (Fin (n + 1))) fun x : (𝓡∂ (n + 1)).interior W ↦ f x
  /-- On the interior, the field is gradient-like for the function. -/
  isGradientLike : IsGradientLike (fun x : (𝓡∂ (n + 1)).interior W ↦ f x)
    fun x ↦ (Y x : EuclideanSpace ℝ (Fin (n + 1)))

variable {σ : SmoothTwoForm (𝓡∂ (n + 1)) W} {Y : (x : W) → TangentSpace (𝓡∂ (n + 1)) x}
  {f : W → ℝ} {c : ℝ}

/-- The conditions of `SymplecticGeometry.IsWeinsteinDomain`, as a conjunction. -/
theorem isWeinsteinDomain_iff :
    IsWeinsteinDomain σ Y f c ↔
      IsStrongFilling σ univ Y ∧ ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ f ∧
        (∀ x ∈ (𝓡∂ (n + 1)).boundary W, f x = c) ∧
        (∀ x ∈ (𝓡∂ (n + 1)).interior W, f x < c) ∧
        (∀ x ∈ (𝓡∂ (n + 1)).boundary W, 0 < mvfderiv (𝓡∂ (n + 1)) f x (Y x)) ∧
        IsGeneralizedMorse (EuclideanSpace ℝ (Fin (n + 1)))
          (fun x : (𝓡∂ (n + 1)).interior W ↦ f x) ∧
        IsGradientLike (fun x : (𝓡∂ (n + 1)).interior W ↦ f x)
          (fun x ↦ (Y x : EuclideanSpace ℝ (Fin (n + 1)))) :=
  ⟨fun h ↦ ⟨h.isStrongFilling, h.contMDiff, h.eq_of_mem_boundary, h.lt_of_mem_interior,
      h.mvfderiv_pos, h.isGeneralizedMorse, h.isGradientLike⟩,
    fun ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ ↦ ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩⟩

namespace IsWeinsteinDomain

/-- The function of a Weinstein domain is at most its top level. -/
theorem le (h : IsWeinsteinDomain σ Y f c) (x : W) : f x ≤ c := by
  by_cases hx : x ∈ (𝓡∂ (n + 1)).interior W
  · exact (h.lt_of_mem_interior x hx).le
  · rw [← mem_compl_iff, ModelWithCorners.compl_interior] at hx
    exact (h.eq_of_mem_boundary x hx).le

/-- The boundary of a Weinstein domain is the level set of its function at the top level. -/
theorem preimage_singleton_eq_boundary (h : IsWeinsteinDomain σ Y f c) :
    f ⁻¹' {c} = (𝓡∂ (n + 1)).boundary W := by
  refine Subset.antisymm (fun x hx ↦ ?_) fun x hx ↦ h.eq_of_mem_boundary x hx
  rw [← ModelWithCorners.compl_interior]
  exact fun hxi ↦ (h.lt_of_mem_interior x hxi).ne hx

/-- The top level of a Weinstein domain with nonempty boundary is determined by the function. -/
theorem level_unique {c' : ℝ} (h : IsWeinsteinDomain σ Y f c) (h' : IsWeinsteinDomain σ Y f c')
    (hb : ((𝓡∂ (n + 1)).boundary W).Nonempty) : c = c' := by
  obtain ⟨x, hx⟩ := hb
  rw [← h.eq_of_mem_boundary x hx, h'.eq_of_mem_boundary x hx]

/-- The critical points of the function of a Weinstein domain are interior points. -/
theorem criticalPoints_subset_interior (h : IsWeinsteinDomain σ Y f c) :
    criticalPoints (𝓡∂ (n + 1)) f ⊆ (𝓡∂ (n + 1)).interior W := by
  intro x hx
  by_contra hxi
  rw [← mem_compl_iff, ModelWithCorners.compl_interior] at hxi
  have hpos := h.mvfderiv_pos x hxi
  rw [mem_criticalPoints.1 hx] at hpos
  exact hpos.false

/-- The function of a Weinstein domain on a compact manifold has only finitely many critical
points. -/
theorem finite_criticalPoints [CompactSpace W] (h : IsWeinsteinDomain σ Y f c) :
    (criticalPoints (𝓡∂ (n + 1)) f).Finite := by
  have hsub := h.criticalPoints_subset_interior
  have hS : IsOpen ((𝓡∂ (n + 1)).interior W) := (𝓡∂ (n + 1)).isOpen_interior one_ne_zero
  -- The critical set is closed in the compact `W`, and lies in the open interior.
  have hK : IsCompact (Subtype.val ⁻¹' criticalPoints (𝓡∂ (n + 1)) f :
      Set ((𝓡∂ (n + 1)).interior W)) :=
    (hS.isOpenEmbedding_subtypeVal.isCompact_preimage_iff (by simpa using hsub)).2
      (isClosed_criticalPoints (h.contMDiff.of_le (by simp))).isCompact
  -- The inclusion of the interior is a local diffeomorphism, so it preserves critical points.
  have hcrit : (Subtype.val ⁻¹' criticalPoints (𝓡∂ (n + 1)) f : Set ((𝓡∂ (n + 1)).interior W)) ⊆
      criticalPoints 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
        (fun x : (𝓡∂ (n + 1)).interior W ↦ f x) := fun x hx ↦
    (ModelWithCorners.isLocalDiffeomorph_subtypeVal_interior (n := 1) x
      |>.mem_criticalPoints_comp_iff le_rfl).2 hx
  have hfin := (h.isGeneralizedMorse.finite_criticalPoints_inter hK).image Subtype.val
  rwa [inter_eq_right.2 hcrit, image_preimage_eq_of_subset (by simpa using hsub)] at hfin

end IsWeinsteinDomain

end Domain

/-! ### Regular sublevels of Weinstein structures -/

section Sublevel

open Module

namespace IsWeinsteinStructure

/-- The sublevel `{x | f x ≤ c}` of the function of a Weinstein structure is compact, since the
function is proper and bounded below. -/
theorem compactSpace_sublevel (hW : IsWeinsteinStructure ω X f) (c : ℝ) :
    CompactSpace {x | f x ≤ c} :=
  isCompact_iff_compactSpace.1 (hW.isProperMap.isCompact_preimage_Iic hW.bddBelow c)

/-- **A regular sublevel of a Weinstein structure is a Weinstein domain.** Let `(ω, X, f)` be a
Weinstein structure on a manifold `M` of dimension `n + 1` and `c` a regular value of `f`. Then the
sublevel `W = {x | f x ≤ c}`, a manifold with boundary for Tau Ceti's atlas
`TauCeti.scalarRegularSublevelChartedSpace`, with the pull-back of `ω` along the inclusion
`ι : W → M`, the pull-back `x ↦ (dι_x)⁻¹ (X x)` of `X`, the restriction of `f` and the level `c`,
is a Weinstein domain. It is compact by `IsWeinsteinStructure.compactSpace_sublevel`. -/
theorem isWeinsteinDomain_scalarRegularSublevel {n : ℕ} (hn : finrank ℝ E = n + 1)
    (hW : IsWeinsteinStructure ω X f) {c : ℝ} (hc : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f c) :
    letI := scalarRegularSublevelChartedSpace
      (hW.isGeneralizedMorse.contMDiff.of_le (by simp)) hc hn
    haveI := isManifold_scalarRegularSublevel hc hn (by simp) hW.isGeneralizedMorse.contMDiff
    IsWeinsteinDomain
      (SmoothForm.mpullback Subtype.val (contMDiff_subtypeVal_scalarRegularSublevel hc hn
        (by simp) hW.isGeneralizedMorse.contMDiff) ω)
      (VectorField.mpullback (𝓡∂ (n + 1)) 𝓘(ℝ, E) Subtype.val X)
      (fun x : {x | f x ≤ c} ↦ f x) c := by
  have hf := hW.isGeneralizedMorse.contMDiff
  let := scalarRegularSublevelChartedSpace (hf.of_le (by simp)) hc hn
  have := isManifold_scalarRegularSublevel hc hn (by simp) hf
  have hι := contMDiff_subtypeVal_scalarRegularSublevel hc hn (by simp) hf
  have hinv := isInvertible_mfderiv_subtypeVal_scalarRegularSublevel (hf.of_le (by simp)) hc hn
  -- On the level `f⁻¹(c)` the differential of `f` is nonzero, so `X` increases `f` there.
  have hpos (x : M) (hx : f x = c) : 0 < mvfderiv 𝓘(ℝ, E) f x (X x) :=
    hW.isGradientLike.mvfderiv_apply_pos_of_isRegularValue hc hx
  have hbd := boundary_scalarRegularSublevel hc hn (by simp) hf
  -- The inclusion `Φ` of the interior of the sublevel into `M`; its differential is that of `ι`.
  set Φ : (𝓡∂ (n + 1)).interior {x | f x ≤ c} → M := fun x ↦ ((x : {x | f x ≤ c}) : M)
  have hΦ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, E) (⊤ : ℕ∞) Φ :=
    hι.comp (𝓡∂ (n + 1)).contMDiff_subtypeVal_interior
  have hdΦ (x) : mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, E) Φ x =
      mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, E) Subtype.val (x : {x | f x ≤ c}) := by
    exact ModelWithCorners.mfderiv_comp_subtypeVal_interior x ((hι _).mdifferentiableAt (by simp))
  have hΦinv (x) :
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, E) Φ x).IsInvertible := by
    rw [hdΦ]
    exact hinv _
  refine ⟨isStrongFilling_scalarRegularSublevel hn hW.isSymplectic hW.contMDiff_field
      hW.isLiouvilleVectorField hf hc hpos, hf.comp hι, fun x hx ↦ by rwa [hbd] at hx,
    fun x hx ↦ ?_, fun x hx ↦ ?_, hW.isGeneralizedMorse.comp_isLocalDiffeomorph
      (isLocalDiffeomorph_of_mfderiv_eq hΦ (by simp) hΦinv), ?_⟩
  · rwa [interior_scalarRegularSublevel hc hn (by simp) hf] at hx
  · rw [hbd] at hx
    rw [← Function.comp_def f Subtype.val, VectorField.mvfderiv_comp_apply_mpullback
      ((hf x).mdifferentiableAt (by simp)) (hinv x)]
    exact hpos x hx
  · refine (congrArg (IsGradientLike _) (funext fun x ↦ ?_)).mpr
      (hW.isGradientLike.mpullback hΦ hΦinv)
    rw [VectorField.mpullback_apply, VectorField.mpullback_apply, hdΦ]
    -- The two sides are typed in `TangentSpace 𝓘(ℝ, ℝⁿ⁺¹) x` and `TangentSpace (𝓡∂ (n + 1)) x`,
    -- which are both `ℝⁿ⁺¹`.
    rfl

end IsWeinsteinStructure

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- **The closed unit ball is a Weinstein domain.** Let `V` be a real inner product space of
dimension `n + 1` with a linear symplectic form `ω`. The closed unit ball `{x | ‖x‖ ^ 2 ≤ 1}`, a
manifold with boundary for Tau Ceti's atlas `TauCeti.scalarRegularSublevelChartedSpace`, with the
pull-back of the constant form `ω`, the pull-back of the radial field `x ↦ x / 2`, the function
`x ↦ ‖x‖ ^ 2` and the level `1`, is a Weinstein domain; for instance the unit ball of `ℂⁿ`. -/
theorem isWeinsteinDomain_norm_sq_le_one {n : ℕ} (hn : finrank ℝ V = n + 1)
    (ω : SymplecticForm V) :
    letI := scalarRegularSublevelChartedSpace (contDiff_norm_sq ℝ).contMDiff
      (isRegularValue_norm_sq (E := V) one_ne_zero) hn
    haveI := isManifold_scalarRegularSublevel (isRegularValue_norm_sq (E := V) one_ne_zero) hn
      (m := (⊤ : ℕ∞)) (by simp) (contDiff_norm_sq ℝ).contMDiff
    IsWeinsteinDomain
      (SmoothForm.mpullback Subtype.val (contMDiff_subtypeVal_scalarRegularSublevel
        (isRegularValue_norm_sq one_ne_zero) hn (m := (⊤ : ℕ∞)) (by simp)
        (contDiff_norm_sq ℝ).contMDiff) ω.constSmooth)
      (VectorField.mpullback (𝓡∂ (n + 1)) 𝓘(ℝ, V) Subtype.val fun x : V ↦ (2⁻¹ : ℝ) • x)
      (fun x : {x : V | ‖x‖ ^ 2 ≤ 1} ↦ ‖(x : V)‖ ^ 2) 1 :=
  (isWeinsteinStructure_constSmooth_norm_sq ω).isWeinsteinDomain_scalarRegularSublevel hn
    (isRegularValue_norm_sq one_ne_zero)

end Sublevel

end SymplecticGeometry

end
