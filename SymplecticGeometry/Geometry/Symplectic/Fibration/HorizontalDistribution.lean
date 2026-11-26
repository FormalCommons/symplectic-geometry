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
import SymplecticGeometry.Geometry.Manifold.Submersion.VerticalProjection
import SymplecticGeometry.LinearAlgebra.BilinearForm.Orthogonal
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.PartitionOfUnity
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Semibasic
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
* `TauCeti.RoughForm.IsVerticallyClosedOn IB proj τ s`: the same condition at the points of a
  set `s`, for a two-form of any regularity; on the whole space it is vertical closedness
  (`TauCeti.SmoothTwoForm.isVerticallyClosedOn_univ_iff`).
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
* `TauCeti.SmoothTwoForm.exists_restrictsTo_horizontalDistribution_eq`: for a smooth atlas whose
  coordinate changes preserve a nondegenerate form `σ` on the fibre, every smooth Ehresmann
  connection is the connection of a two-form that restricts to `σ`.
* `TauCeti.SmoothTwoForm.exists_restrictsTo_isVerticallyClosed`: for a smooth atlas over a
  Hausdorff, σ-compact base whose coordinate changes preserve a closed form `σ` on the fibre, some
  vertically closed two-form restricts to `σ`.

## Implementation notes

The proof that the horizontal spaces form a smooth distribution has the shape of Tau Ceti's
`Manifold.IsSubmersion.isContMDiffDistribution_orthogonal_ker_mfderiv`, with the flat map of `τ`
in place of a Riemannian metric: the vertical spaces form a smooth distribution (Tau Ceti's
`Manifold.IsSubmersion.isContMDiffDistribution_ker_mfderiv`), and the orthogonals of a smooth
distribution for a smooth field of nondegenerate reflexive forms form one too
(`TauCeti.IsContMDiffDistribution.bilinFormOrthogonal`).

The two-form with a given connection `D` is built pointwise: at `x`, it is the pull-back of the
fibre form along the fibre coordinate of the chart at `proj x`, precomposed with the vertical
projection along `D`. Since the coordinate changes preserve the fibre form, any chart whose base
set contains `proj x` gives the same value on vertical vectors
(`TauCeti.MapFiber.Atlas.mpullback_snd_trivAt_apply_eq`), so near each point the form is read in
a single chart, where it is smooth by
`TauCeti.IsEhresmannConnection.contMDiffOn_compContinuousLinearMap_verticalProjection`.

The vertically closed form is glued from the pull-backs `θ_i` of `σ` along the fibre coordinates
of the charts by a partition of unity `ρ` of the base, and is smooth by Tau Ceti's
`TauCeti.isSmoothForm_sum_finsupport_smul_mpullback`. As `σ` is closed, the derivative of the sum
at `x` is `∑ᵢ d(ρᵢ ∘ proj) ∧ θ_i` (`TauCeti.mextDeriv_sum_finsupport_smul_mpullback_apply`). On
two vertical vectors each `θ_i` takes the value of the pull-back along the chart at `proj x`, and
the one-forms `d(ρᵢ ∘ proj)` are semibasic and sum to zero, which gives vertical closedness.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §6.3, Exercise 6.3.6.
* [V. Guillemin, E. Lerman, S. Sternberg, *Symplectic Fibrations and Multiplicity
  Diagrams*][GuilleminLermanSternberg1996], Theorem 1.2.5.
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

omit [IsManifold IM ∞ M] in
/-- A two-form `τ` on `M`, of any regularity, is *vertically closed on* a set `s` for a map
`proj : M → B` when its exterior derivative vanishes on `(η₁, η₂, v)` at every point `x ∈ s`, for
all vectors `η₁` and `η₂` of the kernel of the derivative of `proj` at `x` and every tangent
vector `v`. -/
def _root_.TauCeti.RoughForm.IsVerticallyClosedOn (proj : M → B) (τ : RoughForm IM M ℝ 2)
    (s : Set M) : Prop :=
  ∀ x ∈ s, ∀ η₁ ∈ (mfderiv IM IB proj x).ker, ∀ η₂ ∈ (mfderiv IM IB proj x).ker,
    ∀ v : TangentSpace IM x, mextDeriv τ x ![η₁, η₂, v] = 0

variable {IB}

theorem isVerticallyClosed_iff :
    IsVerticallyClosed IB proj τ ↔
      ∀ x, ∀ η₁ ∈ (mfderiv IM IB proj x).ker, ∀ η₂ ∈ (mfderiv IM IB proj x).ker,
        ∀ v : TangentSpace IM x, mextDeriv τ.val x ![η₁, η₂, v] = 0 :=
  Iff.rfl

omit [IsManifold IM ∞ M] in
theorem _root_.TauCeti.RoughForm.isVerticallyClosedOn_iff {τ : RoughForm IM M ℝ 2} {s : Set M} :
    τ.IsVerticallyClosedOn IB proj s ↔
      ∀ x ∈ s, ∀ η₁ ∈ (mfderiv IM IB proj x).ker, ∀ η₂ ∈ (mfderiv IM IB proj x).ker,
        ∀ v : TangentSpace IM x, mextDeriv τ x ![η₁, η₂, v] = 0 :=
  Iff.rfl

omit [IsManifold IM ∞ M] in
theorem _root_.TauCeti.RoughForm.IsVerticallyClosedOn.mono {τ : RoughForm IM M ℝ 2}
    {s t : Set M} (h : τ.IsVerticallyClosedOn IB proj s) (hts : t ⊆ s) :
    τ.IsVerticallyClosedOn IB proj t :=
  fun x hx ↦ h x (hts hx)

/-- A smooth two-form is vertically closed exactly when it is vertically closed on the whole
space. -/
theorem isVerticallyClosedOn_univ_iff :
    RoughForm.IsVerticallyClosedOn IB proj τ.val univ ↔ IsVerticallyClosed IB proj τ :=
  ⟨fun h x ↦ h x (mem_univ x), fun h x _ ↦ h x⟩

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

/-! ### A form with a given connection -/

section GivenConnection

variable {EF : Type*} [NormedAddCommGroup EF] [NormedSpace ℝ EF] {HF : Type*}
  [TopologicalSpace HF] {IF : ModelWithCorners ℝ EF HF} {F : Type*} [TopologicalSpace F]
  [ChartedSpace HF F] [IsManifold IF ∞ F]
  {A : MapFiber.Atlas F proj} {σ : SmoothTwoForm IF F}
  {D : Π x : M, Submodule ℝ (TangentSpace IM x)} (hD : IsEhresmannConnection IM IB ∞ proj D)

variable (A σ) in
/-- The form of `exists_restrictsTo_horizontalDistribution_eq`: at `x`, the pull-back of `σ`
along the fibre coordinate of the chart `A.trivAt (proj x)`, precomposed with the vertical
projection of `D`. -/
private def formOfConnection : RoughForm IM M ℝ 2 := fun x ↦
  (TauCeti.mpullback IM IF (fun y ↦ (A.trivAt (proj x) y).2) σ.val x).compContinuousLinearMap
    (hD.verticalProjection x)

private theorem formOfConnection_apply (x : M) (u : Fin 2 → TangentSpace IM x) :
    formOfConnection A σ hD x u =
      TauCeti.mpullback IM IF (fun y ↦ (A.trivAt (proj x) y).2) σ.val x
        (fun i ↦ hD.verticalProjection x (u i)) :=
  (rfl)

/-- Near a point, the chart at `proj x` in `formOfConnection` may be replaced by any chart whose
base set contains `proj x`. -/
private theorem formOfConnection_eq (hA : A.IsContMDiff ∞ IB IF IM)
    (hH : A.HasStructureGroup (SmoothForm.diffeomorphStabilizer σ)) {b : B} {x : M}
    (hx : proj x ∈ (A.trivAt b).baseSet) :
    formOfConnection A σ hD x =
      (TauCeti.mpullback IM IF (fun y ↦ (A.trivAt b y).2) σ.val x).compContinuousLinearMap
        (hD.verticalProjection x) := by
  ext u
  rw [formOfConnection_apply, ContinuousAlternatingMap.compContinuousLinearMap_apply]
  exact MapFiber.Atlas.mpullback_snd_trivAt_apply_eq hA hH (A.mem_baseSet_trivAt _) hx
    fun i ↦ hD.verticalProjection_apply_mem x (u i)

private theorem isSmoothForm_formOfConnection [IsManifold IB 1 B] [FiniteDimensional ℝ EM]
    (hA : A.IsContMDiff ∞ IB IF IM)
    (hH : A.HasStructureGroup (SmoothForm.diffeomorphStabilizer σ)) :
    IsSmoothForm IM ∞ (formOfConnection A σ hD) := by
  have hproj : ContMDiff IM IB (∞ + 1) proj := by simpa using hA.contMDiff_proj
  refine (isSmoothForm_def _ _).2 fun x₀ ↦ ?_
  -- Near `x₀`, the form is read in the single chart `e` at `proj x₀`.
  set e := A.trivAt (proj x₀)
  have hU := e.open_source
  have hθ : ContMDiffOn IM (IM.prod 𝓘(ℝ, EM [⋀^Fin 2]→L[ℝ] ℝ)) ∞
      (fun y ↦ TotalSpace.mk' (EM [⋀^Fin 2]→L[ℝ] ℝ) y
        (TauCeti.mpullback IM IF (fun y ↦ (e y).2) σ.val y)) e.source := fun y hy ↦
    (ContMDiffAt.mpullback_form (σ.contMDiff _) (hA.contMDiffAt_snd_trivAt (e.mem_source.1 hy))
      (by simp)).contMDiffWithinAt
  have hx₀ : e.source ∈ nhds x₀ := hU.mem_nhds (e.mem_source.2 (A.mem_baseSet_trivAt _))
  refine ((hD.contMDiffOn_compContinuousLinearMap_verticalProjection hproj (m := ⊤) le_rfl
    hθ).contMDiffAt hx₀).congr_of_eventuallyEq ?_
  filter_upwards [hx₀] with y hy
  rw [formOfConnection_eq hD hA hH (e.mem_source.1 hy)]

private theorem restrictsTo_formOfConnection (hA : A.IsContMDiff ∞ IB IF IM)
    (hH : A.HasStructureGroup (SmoothForm.diffeomorphStabilizer σ))
    {τ : SmoothTwoForm IM M} (hτ : τ.val = formOfConnection A σ hD) : A.RestrictsTo σ τ := by
  refine MapFiber.Atlas.restrictsTo_iff.2 fun b b' hb' ↦ funext fun v ↦ ?_
  ext w
  set ι := (A.trivAt b).fiberInclusionMap hb'
  -- The derivative of `ι` takes values in the vertical spaces, which the projection fixes.
  have hvert (i : Fin 2) : mfderiv IF IM ι v (w i) ∈ (mfderiv IM IB proj (ι v)).ker := by
    rw [← (A.trivAt b).range_mfderiv_fiberInclusionMap (hA.mdifferentiable_trivAt (by simp) b)]
    exact LinearMap.mem_range_self _ _
  have hb₀ : b' ∈ (A.trivAt (proj (ι v))).baseSet :=
    Set.mem_of_eq_of_mem ((A.trivAt b).proj_fiberInclusionMap hb' v).symm
      (A.mem_baseSet_trivAt _)
  rw [TauCeti.mpullback_apply, ← MapFiber.Atlas.mpullback_fiberInclusionMap_mpullback_snd_trivAt
    hA hH hb₀ hb', TauCeti.mpullback_apply, hτ, formOfConnection_apply]
  simp only [hD.verticalProjection_apply_of_mem_ker (hvert _)]
  -- The two sides differ only in that `ι` is unfolded on the right.
  rfl

private theorem le_horizontalDistribution_formOfConnection {τ : SmoothTwoForm IM M}
    (hτ : τ.val = formOfConnection A σ hD) (x : M) : D x ≤ horizontalDistribution IB proj τ x :=
  fun v hv ↦ mem_horizontalDistribution_iff.2 fun η _ ↦ by
    rw [SmoothForm.bilinFormAt_apply, SmoothBundleForm.eval₂_apply, hτ, formOfConnection_apply]
    refine ContinuousAlternatingMap.map_coord_zero _ 1 ?_
    simpa using hD.verticalProjection_apply_eq_zero_of_mem hv

/-- **A form with a given connection.** Let `A` be a smooth atlas of `proj` whose coordinate
changes preserve a nondegenerate two-form `σ` on the model fibre, and let `D` be a smooth
Ehresmann connection on `proj`. Then some two-form `τ` on `M` restricts to `σ` along `A` and has
the spaces of `D` as its horizontal spaces. -/
theorem exists_restrictsTo_horizontalDistribution_eq [IsManifold IB 1 B] [FiniteDimensional ℝ EM]
    (hA : A.IsContMDiff ∞ IB IF IM)
    (hH : A.HasStructureGroup (SmoothForm.diffeomorphStabilizer σ)) (hσ : σ.IsNondegenerate)
    (hD : IsEhresmannConnection IM IB ∞ proj D) :
    ∃ τ : SmoothTwoForm IM M, A.RestrictsTo σ τ ∧ horizontalDistribution IB proj τ = D := by
  -- At `x`, `τ` is the pull-back of `σ` along the fibre coordinate of the chart at `proj x`,
  -- evaluated on the vertical parts of its arguments along `D`.
  let τ : SmoothTwoForm IM M :=
    ⟨formOfConnection A σ hD, (isSmoothForm_formOfConnection hD hA hH).mem_smoothBundleForms⟩
  have hτ : A.RestrictsTo σ τ := restrictsTo_formOfConnection hD hA hH rfl
  refine ⟨τ, hτ, funext fun x ↦ ?_⟩
  -- `D x` lies in the horizontal space of `τ`, and both are complements of the vertical space.
  have hτv := (hτ.isVerticallyNondegenerate hA hσ).isCompl_horizontalDistribution x
  exact (eq_of_le_of_inf_le_of_le_sup (le_horizontalDistribution_formOfConnection hD rfl x)
    (hτv.disjoint.le_bot.trans bot_le)
    (le_top.trans (hD.isCompl_ker x).codisjoint.top_le)).symm

end GivenConnection

/-! ### Connection two-forms -/

section ConnectionTwoForm

variable {EF : Type*} [NormedAddCommGroup EF] [NormedSpace ℝ EF] {HF : Type*}
  [TopologicalSpace HF] {IF : ModelWithCorners ℝ EF HF} {F : Type*} [TopologicalSpace F]
  [ChartedSpace HF F] [IsManifold IF ∞ F]
  {A : MapFiber.Atlas F proj} {σ : SmoothTwoForm IF F}

variable (A σ) in
/-- The form of `exists_restrictsTo_isVerticallyClosed`: the sum, over a partition of unity `ρ`
of the base, of the pull-backs of `σ` along the fibre coordinates of the charts `A.trivAt i`,
weighted by `ρ i ∘ proj`. -/
private def connectionForm (ρ : SmoothPartitionOfUnity B IB B univ) : RoughForm IM M ℝ 2 :=
  fun x ↦ ∑ i ∈ ρ.finsupport (proj x),
    ρ i (proj x) • TauCeti.mpullback IM IF (fun y ↦ (A.trivAt i y).2) σ.val x

omit [IsManifold IM ∞ M] in
private theorem connectionForm_apply (ρ : SmoothPartitionOfUnity B IB B univ) (x : M) :
    connectionForm A σ ρ x = ∑ i ∈ ρ.finsupport (proj x),
      ρ i (proj x) • TauCeti.mpullback IM IF (fun y ↦ (A.trivAt i y).2) σ.val x :=
  (rfl)

private theorem isSmoothForm_connectionForm [IsManifold IB ∞ B] (hA : A.IsContMDiff ∞ IB IF IM)
    {ρ : SmoothPartitionOfUnity B IB B univ}
    (hρ : ρ.IsSubordinate fun i ↦ (A.trivAt i).baseSet) :
    IsSmoothForm IM ∞ (connectionForm A σ ρ) :=
  isSmoothForm_sum_finsupport_smul_mpullback hρ (fun i ↦ (A.trivAt i).open_baseSet)
    hA.contMDiff_proj (fun _ _ ↦ hA.contMDiffAt_snd_trivAt) σ

private theorem restrictsTo_connectionForm (hA : A.IsContMDiff ∞ IB IF IM)
    (hH : A.HasStructureGroup (SmoothForm.diffeomorphStabilizer σ))
    {ρ : SmoothPartitionOfUnity B IB B univ}
    (hρ : ρ.IsSubordinate fun i ↦ (A.trivAt i).baseSet) {τ : SmoothTwoForm IM M}
    (hτ : τ.val = connectionForm A σ ρ) : A.RestrictsTo σ τ := by
  refine MapFiber.Atlas.restrictsTo_iff.2 fun b b' hb' ↦ funext fun v ↦ ?_
  ext w
  set ι := (A.trivAt b).fiberInclusionMap hb'
  have hp : proj (ι v) = b' := (A.trivAt b).proj_fiberInclusionMap hb' v
  rw [TauCeti.mpullback_apply, hτ, connectionForm_apply, hp, ContinuousAlternatingMap.sum_apply]
  -- Each chart of the sum pulls back to `σ` along `ι`, and the weights sum to one.
  have hterm : ∀ i ∈ ρ.finsupport b',
      (ρ i b' • TauCeti.mpullback IM IF (fun y ↦ (A.trivAt i y).2) σ.val (ι v))
        (fun j ↦ mfderiv IF IM ι v (w j)) = ρ i b' • σ.val v w := fun i hi ↦ by
    rw [ContinuousAlternatingMap.smul_apply, ← TauCeti.mpullback_apply,
      MapFiber.Atlas.mpullback_fiberInclusionMap_mpullback_snd_trivAt hA hH
        (hρ i (subset_tsupport _ ((ρ.mem_finsupport b').1 hi))) hb']
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_smul, ρ.sum_finsupport (x₀ := b') (mem_univ _),
    one_smul]

private theorem isVerticallyClosed_connectionForm [IsManifold IB ∞ B]
    (hA : A.IsContMDiff ∞ IB IF IM)
    (hH : A.HasStructureGroup (SmoothForm.diffeomorphStabilizer σ)) (hσ : σ.IsClosed)
    {ρ : SmoothPartitionOfUnity B IB B univ}
    (hρ : ρ.IsSubordinate fun i ↦ (A.trivAt i).baseSet) {τ : SmoothTwoForm IM M}
    (hτ : τ.val = connectionForm A σ ρ) : IsVerticallyClosed IB proj τ := by
  intro x η₁ hη₁ η₂ hη₂ v
  have hproj : ContMDiff IM IB ∞ proj := hA.contMDiff_proj
  set θ : B → RoughForm IM M ℝ 2 := fun i ↦
    TauCeti.mpullback IM IF (fun y ↦ (A.trivAt i y).2) σ.val
  set dρ : B → RoughForm IM M ℝ (0 + 1) := fun i ↦
    mextDeriv (RoughForm.ofFunction IM (ρ i ∘ proj))
  rw [hτ, funext (connectionForm_apply ρ), mextDeriv_sum_finsupport_smul_mpullback_apply hρ
    (fun i ↦ (A.trivAt i).open_baseSet) hproj (g := fun i y ↦ (A.trivAt i y).2)
    (fun _ _ ↦ hA.contMDiffAt_snd_trivAt)
    σ.isSmoothForm ((SmoothForm.isClosed_def σ).1 hσ) x]
  -- In each term, `θ i` may be replaced by the pull-back `θ₀` along the chart at `proj x`: the
  -- two agree on vertical pairs, and `dρ i` is semibasic.
  set θ₀ := θ (proj x)
  have hterm : ∀ i ∈ ρ.fintsupport (proj x),
      (dρ i).wedge (θ i) x ![η₁, η₂, v] = (dρ i).wedge θ₀ x ![η₁, η₂, v] := fun i hi ↦ by
    have hψ : ∀ u w : TangentSpace IM x, mfderiv IM IB proj x u = 0 →
        mfderiv IM IB proj x w = 0 → (θ i - θ₀) x ![u, w] = 0 := fun u w hu hw ↦ by
      rw [Pi.sub_apply, ContinuousAlternatingMap.sub_apply, sub_eq_zero]
      exact MapFiber.Atlas.mpullback_snd_trivAt_apply_eq hA hH
        (hρ i ((ρ.mem_fintsupport_iff (proj x) i).1 hi)) (A.mem_baseSet_trivAt _)
        (Fin.forall_fin_two.2 ⟨hu, hw⟩)
    have hφ := RoughForm.isSemibasicAt_mextDeriv_ofFunction_comp
      (((ρ i).contMDiff.mdifferentiable (by simp)) (proj x)) (hproj.mdifferentiable (by simp) x)
    rw [← sub_add_cancel (θ i) θ₀, RoughForm.wedge_add_right, Pi.add_apply,
      ContinuousAlternatingMap.add_apply, hφ.wedge_apply_eq_zero hψ hη₁ hη₂ v, zero_add]
  -- The derivative formula reads the arguments in degree `0 + 1 + 2`, through `Fin.cast`.
  change ∑ i ∈ ρ.fintsupport (proj x), (dρ i).wedge (θ i) x ![η₁, η₂, v] = 0
  rw [Finset.sum_congr rfl hterm]
  simp only [RoughForm.wedge_def, RoughForm.wedgeWith_apply']
  rw [← ContinuousAlternatingMap.sum_apply, ← ContinuousAlternatingMap.pairedWedge_sum_left,
    SmoothPartitionOfUnity.sum_fintsupport_mextDeriv_ofFunction_comp (hproj.of_le (by simp))]
  simp

/-- **Connection two-forms.** Let `A` be a smooth atlas of `proj` whose coordinate changes
preserve a closed two-form `σ` on the model fibre, over a Hausdorff, σ-compact base modelled on a
finite-dimensional space. Then some two-form `τ` on `M` restricts to `σ` along `A` and is
vertically closed. -/
theorem exists_restrictsTo_isVerticallyClosed [IsManifold IB ∞ B] [FiniteDimensional ℝ EB]
    [T2Space B] [SigmaCompactSpace B] (hA : A.IsContMDiff ∞ IB IF IM)
    (hH : A.HasStructureGroup (SmoothForm.diffeomorphStabilizer σ)) (hσ : σ.IsClosed) :
    ∃ τ : SmoothTwoForm IM M, A.RestrictsTo σ τ ∧ IsVerticallyClosed IB proj τ := by
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate IB isClosed_univ
    (fun i ↦ (A.trivAt i).baseSet) (fun i ↦ (A.trivAt i).open_baseSet)
    fun b _ ↦ mem_iUnion.2 ⟨b, A.mem_baseSet_trivAt b⟩
  let τ : SmoothTwoForm IM M :=
    ⟨connectionForm A σ ρ, (isSmoothForm_connectionForm hA hρ).mem_smoothBundleForms⟩
  exact ⟨τ, restrictsTo_connectionForm hA hH hρ rfl,
    isVerticallyClosed_connectionForm hA hH hσ hρ rfl⟩

end ConnectionTwoForm

end TauCeti.SmoothTwoForm

end

end
