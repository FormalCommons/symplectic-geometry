/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Fibration.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Closed
public import TauCeti.Geometry.Manifold.Submersion.EhresmannConnection.Basic
import SymplecticGeometry.Geometry.Manifold.Distribution.Orthogonal
import SymplecticGeometry.LinearAlgebra.BilinearForm.Orthogonal
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
import TauCeti.Geometry.Manifold.Distribution.Submersion
import TauCeti.Geometry.Symplectic.Manifold.Flat

/-!
# The connection of a vertically nondegenerate two-form

Let `proj : M → B` be a map and `τ` a two-form on `M`. The *vertical space* at `x` is the kernel
of the derivative of `proj` at `x`. This file defines the *horizontal space* of `τ` at `x` as the
`τ`-orthogonal of the vertical space, and shows that for a smooth submersion and a vertically
nondegenerate `τ` these spaces form a smooth Ehresmann connection, the connection `Γ_τ` of `τ`.
It also defines vertically closed forms: those whose exterior derivative vanishes as soon as two
of its three arguments are vertical.

## Main definitions

* `TauCeti.SmoothTwoForm.IsVerticallyClosed IB proj τ`: the exterior derivative of `τ` vanishes
  on every triple `(η₁, η₂, v)` with `η₁` and `η₂` vertical.
* `TauCeti.SmoothTwoForm.horizontalDistribution IB proj τ`: the `τ`-orthogonal of the vertical
  spaces.

## Main results

* `TauCeti.SmoothTwoForm.isVerticallyClosed_mpullback`: the pull-back of a two-form on the base
  is vertically closed, so adding it does not change vertical closedness
  (`isVerticallyClosed_add_mpullback_iff`).
* `TauCeti.SmoothTwoForm.convex_setOfPred_restrictsTo_isVerticallyClosed`: the vertically closed
  two-forms that restrict to a given form on the fibre along an atlas form a convex set.
* `IsVerticallyNondegenerate.isContMDiffDistribution_horizontalDistribution`:
  for a smooth submersion, the horizontal spaces of a vertically nondegenerate form are a smooth
  distribution of the rank of the base.
* `TauCeti.SmoothTwoForm.IsVerticallyNondegenerate.isEhresmannConnection`: for a smooth
  submersion, the horizontal spaces of a vertically nondegenerate form are a smooth Ehresmann
  connection.
* `TauCeti.SmoothTwoForm.horizontalDistribution_eq_iff`: two forms that agree on pairs of
  vertical vectors, the first of them vertically nondegenerate, have the same horizontal spaces
  exactly when they agree on every pair of a vertical vector and any vector.

## Implementation notes

The proof that the horizontal spaces form a smooth distribution has the shape of Tau Ceti's
`Manifold.IsSubmersion.isContMDiffDistribution_orthogonal_ker_mfderiv`, with the flat map of `τ`
in place of a Riemannian metric: the vertical spaces form a smooth distribution (Tau Ceti's
`Manifold.IsSubmersion.isContMDiffDistribution_ker_mfderiv`), and the orthogonals of a smooth
distribution for a smooth field of nondegenerate reflexive forms form one too
(`TauCeti.IsContMDiffDistribution.bilinFormOrthogonal`).

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §6.3.
-/

public section

noncomputable section

open Bundle Function Module Set
open scoped Manifold ContDiff

namespace TauCeti.SmoothTwoForm

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] {HB : Type*}
  [TopologicalSpace HB] (IB : ModelWithCorners ℝ EB HB) {B : Type*} [TopologicalSpace B]
  [ChartedSpace HB B]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners ℝ EM HM} {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  [IsManifold IM ∞ M]
  {proj : M → B} {τ τ₁ τ₂ : SmoothTwoForm IM M}

/-! ### Vertically closed two-forms -/

/-- A two-form `τ` on `M` is *vertically closed* for a map `proj : M → B` when its exterior
derivative vanishes on `(η₁, η₂, v)` at every point `x`, for all vectors `η₁` and `η₂` of the
kernel of the derivative of `proj` at `x` and every tangent vector `v`. -/
def IsVerticallyClosed (proj : M → B) (τ : SmoothTwoForm IM M) : Prop :=
  ∀ x, ∀ η₁ ∈ (mfderiv IM IB proj x).ker, ∀ η₂ ∈ (mfderiv IM IB proj x).ker,
    ∀ v : TangentSpace IM x, mextDeriv τ.val x ![η₁, η₂, v] = 0

variable {IB}

theorem isVerticallyClosed_iff :
    IsVerticallyClosed IB proj τ ↔
      ∀ x, ∀ η₁ ∈ (mfderiv IM IB proj x).ker, ∀ η₂ ∈ (mfderiv IM IB proj x).ker,
        ∀ v : TangentSpace IM x, mextDeriv τ.val x ![η₁, η₂, v] = 0 :=
  Iff.rfl

/-- A closed two-form is vertically closed for every map. -/
theorem _root_.TauCeti.SmoothForm.IsClosed.isVerticallyClosed (h : τ.IsClosed) :
    IsVerticallyClosed IB proj τ := fun x _ _ _ _ _ ↦ by
  rw [(SmoothForm.isClosed_def τ).1 h, Pi.zero_apply,
    ContinuousAlternatingMap.coe_zero, Pi.zero_apply]

/-- The sum of two vertically closed two-forms is vertically closed. -/
theorem IsVerticallyClosed.add (h₁ : IsVerticallyClosed IB proj τ₁)
    (h₂ : IsVerticallyClosed IB proj τ₂) : IsVerticallyClosed IB proj (τ₁ + τ₂) := by
  intro x η₁ hη₁ η₂ hη₂ v
  rw [← mextDerivₗ_apply, map_add, Submodule.coe_add, mextDerivₗ_apply,
    mextDerivₗ_apply, Pi.add_apply, ContinuousAlternatingMap.add_apply,
    h₁ x η₁ hη₁ η₂ hη₂ v, h₂ x η₁ hη₁ η₂ hη₂ v, add_zero]

/-- A scalar multiple of a vertically closed two-form is vertically closed. -/
theorem IsVerticallyClosed.smul (h : IsVerticallyClosed IB proj τ) (c : ℝ) :
    IsVerticallyClosed IB proj (c • τ) := by
  intro x η₁ hη₁ η₂ hη₂ v
  rw [Submodule.coe_smul, mextDeriv_smul, Pi.smul_apply,
    ContinuousAlternatingMap.smul_apply, h x η₁ hη₁ η₂ hη₂ v, smul_zero]

/-- Adding a vertically closed two-form does not change vertical closedness. -/
theorem IsVerticallyClosed.add_right_iff (h : IsVerticallyClosed IB proj τ₂) :
    IsVerticallyClosed IB proj (τ₁ + τ₂) ↔ IsVerticallyClosed IB proj τ₁ := by
  refine ⟨fun h₁₂ ↦ ?_, fun h₁ ↦ h₁.add h⟩
  have := h₁₂.add (h.smul (-1))
  rwa [neg_one_smul ℝ τ₂, add_neg_cancel_right] at this

/-- The exterior derivative of the pull-back `proj^* β` of a two-form on the base vanishes on
`(η₁, η₂, v)` as soon as `η₁` is vertical, since `d(proj^* β) = proj^* dβ`. -/
theorem mextDeriv_mpullback_apply_eq_zero [IsManifold IB ∞ B]
    (hproj : ContMDiff IM IB ∞ proj) (β : SmoothTwoForm IB B) {x : M}
    {η₁ : TangentSpace IM x} (hη₁ : η₁ ∈ (mfderiv IM IB proj x).ker) (η₂ v : TangentSpace IM x) :
    mextDeriv (SmoothForm.mpullback proj hproj β).val x ![η₁, η₂, v] = 0 := by
  rw [← mextDerivₗ_apply, SmoothForm.mextDerivₗ_mpullback, SmoothForm.mpullback_apply]
  refine ContinuousAlternatingMap.map_coord_zero _ 0 ?_
  simpa using hη₁

/-- The pull-back `proj^* β` of a two-form on the base is vertically closed. -/
theorem isVerticallyClosed_mpullback [IsManifold IB ∞ B] (hproj : ContMDiff IM IB ∞ proj)
    (β : SmoothTwoForm IB B) : IsVerticallyClosed IB proj (SmoothForm.mpullback proj hproj β) :=
  fun _ _ hη₁ η₂ _ v ↦ mextDeriv_mpullback_apply_eq_zero hproj β hη₁ η₂ v

/-- Adding the pull-back `proj^* β` of a two-form on the base does not change vertical
closedness. -/
theorem isVerticallyClosed_add_mpullback_iff [IsManifold IB ∞ B]
    (hproj : ContMDiff IM IB ∞ proj) (β : SmoothTwoForm IB B) :
    IsVerticallyClosed IB proj (τ + SmoothForm.mpullback proj hproj β) ↔
      IsVerticallyClosed IB proj τ :=
  (isVerticallyClosed_mpullback hproj β).add_right_iff

section RestrictsTo

variable {EF : Type*} [NormedAddCommGroup EF] [NormedSpace ℝ EF] {HF : Type*}
  [TopologicalSpace HF] {IF : ModelWithCorners ℝ EF HF} {F : Type*} [TopologicalSpace F]
  [ChartedSpace HF F] [IsManifold IF ∞ F]

variable (IB) in
/-- The two-forms on `M` that restrict to `σ` along an atlas `A` of `proj` and are vertically
closed form a convex set. -/
theorem convex_setOfPred_restrictsTo_isVerticallyClosed (A : MapFiber.Atlas F proj)
    (σ : SmoothTwoForm IF F) :
    Convex ℝ {τ : SmoothTwoForm IM M | A.RestrictsTo σ τ ∧ IsVerticallyClosed IB proj τ} :=
  fun _ (h₁ : _ ∧ _) _ (h₂ : _ ∧ _) _ _ ha hb hab ↦
    ⟨MapFiber.Atlas.convex_setOfPred_restrictsTo A σ h₁.1 h₂.1 ha hb hab,
      (h₁.2.smul _).add (h₂.2.smul _)⟩

end RestrictsTo

/-! ### The horizontal spaces of a two-form -/

variable (IB) in
/-- The *horizontal space* of a two-form `τ` at `x` for a map `proj`: the `τ`-orthogonal of the
kernel of the derivative of `proj` at `x`. -/
def horizontalDistribution (proj : M → B) (τ : SmoothTwoForm IM M) (x : M) :
    Submodule ℝ (TangentSpace IM x) :=
  (τ.bilinFormAt x).orthogonal (mfderiv IM IB proj x).ker

theorem horizontalDistribution_def (x : M) :
    horizontalDistribution IB proj τ x = (τ.bilinFormAt x).orthogonal (mfderiv IM IB proj x).ker :=
  (rfl)

/-- A tangent vector is horizontal for `τ` when `τ` pairs every vertical vector with it to
zero. -/
theorem mem_horizontalDistribution_iff {x : M} {v : TangentSpace IM x} :
    v ∈ horizontalDistribution IB proj τ x ↔
      ∀ η ∈ (mfderiv IM IB proj x).ker, τ.bilinFormAt x η v = 0 := by
  rw [horizontalDistribution_def, LinearMap.BilinForm.mem_orthogonal_iff]

/-- For a vertically nondegenerate two-form, the horizontal space at every point is a
complement of the vertical space. -/
theorem IsVerticallyNondegenerate.isCompl_horizontalDistribution [FiniteDimensional ℝ EM]
    (hτ : IsVerticallyNondegenerate IB proj τ) (x : M) :
    IsCompl (horizontalDistribution IB proj τ x) (mfderiv IM IB proj x).ker := by
  have : FiniteDimensional ℝ (TangentSpace IM x) := inferInstanceAs (FiniteDimensional ℝ EM)
  exact (LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate
    (SmoothForm.isAlt_bilinFormAt τ x).isRefl (isVerticallyNondegenerate_iff.1 hτ x)).symm

/-- For a smooth submersion `proj` from a manifold modelled on a finite-dimensional space and a
vertically nondegenerate two-form `τ`, the horizontal spaces of `τ` form a smooth distribution
whose rank is the dimension of the model space of the base. -/
theorem IsVerticallyNondegenerate.isContMDiffDistribution_horizontalDistribution
    [FiniteDimensional ℝ EM] (hτ : IsVerticallyNondegenerate IB proj τ)
    (hproj : Manifold.IsSubmersion IM IB ∞ proj) :
    IsContMDiffDistribution IM ∞ (finrank ℝ EB) (horizontalDistribution IB proj τ) := by
  rcases isEmpty_or_nonempty M with hM | hM
  · exact isContMDiffDistribution_iff.2 fun x ↦ isEmptyElim x
  have x : M := Classical.arbitrary M
  have : FiniteDimensional ℝ EB := Module.Finite.of_surjective
    (mfderiv IM IB proj x : TangentSpace IM x →ₗ[ℝ] TangentSpace IB (proj x))
    (hproj.surjective_mfderiv (by simp) x)
  -- Mathlib defines `ContinuousLinearMap.toBilinForm` as `toLinearMap₁₂`, the form that
  -- `IsContMDiffDistribution.bilinFormOrthogonal` uses.
  have hflat (y : M) : (τ.flat y).toLinearMap₁₂ = τ.bilinFormAt y := τ.toBilinForm_flat y
  -- The vertical spaces form a smooth distribution, and so do their `τ`-orthogonals.
  have hH := (hproj.isContMDiffDistribution_ker_mfderiv (m := ∞) (by simp)).bilinFormOrthogonal
    (β := τ.flat) τ.contMDiff_flat
    (fun y ↦ hflat y ▸ (SmoothForm.isAlt_bilinFormAt τ y).isRefl)
    fun y ↦ hflat y ▸ isVerticallyNondegenerate_iff.1 hτ y
  rw [Nat.sub_sub_self (hproj.finrank_le (by simp))] at hH
  simpa only [hflat, ← horizontalDistribution_def] using hH

/-- **The connection of a two-form.** For a smooth submersion `proj` from a manifold modelled on
a finite-dimensional space and a vertically nondegenerate two-form `τ`, the horizontal spaces of
`τ` form a smooth Ehresmann connection on `proj`. -/
theorem IsVerticallyNondegenerate.isEhresmannConnection [FiniteDimensional ℝ EM]
    (hτ : IsVerticallyNondegenerate IB proj τ) (hproj : Manifold.IsSubmersion IM IB ∞ proj) :
    IsEhresmannConnection IM IB ∞ proj (horizontalDistribution IB proj τ) where
  mdifferentiable := hproj.contMDiff.mdifferentiable (by simp)
  isCompl_ker := hτ.isCompl_horizontalDistribution
  surjective_mfderiv := hproj.surjective_mfderiv (by simp)
  isContMDiffDistribution := hτ.isContMDiffDistribution_horizontalDistribution hproj

/-- **Forms with the same connection.** Let `τ₁` and `τ₂` be two-forms that agree on pairs of
vertical vectors, with `τ₁` vertically nondegenerate. They have the same horizontal spaces
exactly when they agree on `(η, v)` for every vertical vector `η` and every tangent vector `v`. -/
theorem horizontalDistribution_eq_iff [FiniteDimensional ℝ EM]
    (hτ₁ : IsVerticallyNondegenerate IB proj τ₁)
    (h : ∀ x, ∀ η₁ ∈ (mfderiv IM IB proj x).ker, ∀ η₂ ∈ (mfderiv IM IB proj x).ker,
      τ₁.bilinFormAt x η₁ η₂ = τ₂.bilinFormAt x η₁ η₂) :
    horizontalDistribution IB proj τ₁ = horizontalDistribution IB proj τ₂ ↔
      ∀ x, ∀ η ∈ (mfderiv IM IB proj x).ker, ∀ v : TangentSpace IM x,
        τ₁.bilinFormAt x η v = τ₂.bilinFormAt x η v := by
  rw [funext_iff]
  exact forall_congr' fun x ↦ LinearMap.BilinForm.orthogonal_eq_orthogonal_iff (h x)
    (hτ₁.isCompl_horizontalDistribution x).symm.codisjoint

end TauCeti.SmoothTwoForm

end

end
