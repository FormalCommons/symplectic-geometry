/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.FiberBundle.RestrictsTo
public import SymplecticGeometry.Geometry.Manifold.FiberBundle.StructureGroup
public import SymplecticGeometry.Geometry.Symplectic.Fibration.HorizontalDistribution
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.TopForm
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Descent
public import TauCeti.Geometry.Manifold.Submersion.EhresmannConnection.Basic
public import TauCeti.Geometry.Symplectic.Manifold.Volume
import SymplecticGeometry.Geometry.Manifold.FiberBundle.MapFiber
import SymplecticGeometry.Geometry.Manifold.Submersion.HorizontalLiftField
import SymplecticGeometry.Geometry.Symplectic.Fibration.Curvature
import SymplecticGeometry.Geometry.Symplectic.Manifold.Volume
import SymplecticGeometry.Topology.FiberBundle.Basic
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.ChangeOfVariables
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Regularity
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Coupling forms: fibre integrals on horizontal lifts, and closed forms with the same connection

This file gathers two ingredients of the coupling forms of McDuff–Salamon [McDuffSalamon2017],
§6.4, and Guillemin–Lerman–Sternberg [GuilleminLermanSternberg1996], §1.4.

## The fibre integral of a two-form on horizontal lifts

Let `proj : M → B` carry an Ehresmann connection `hD` and an atlas `A` with model fibre `F`, and let
`σ` be a nondegenerate two-form on `F`, of dimension `2 * k`, with symplectic orientation `o`. For
a two-form `τ` on `M`, a point `b` and tangent vectors `w₁ w₂` at `b`, the number
`TauCeti.IsEhresmannConnection.fiberMean hD A hσ hk τ b w₁ w₂` is the integral over `F`, against
the symplectic volume form `σᵏ / k!` and the orientation `o`, of the function
`y ↦ τ(w₁♯, w₂♯)` at `e⁻¹ (b, y)`, where `e = A.trivAt b` and `wᵢ♯` is the horizontal lift of `wᵢ`
at that point. It is not divided by the symplectic volume of `F`. It serves to state the
normalization of coupling forms of McDuff–Salamon [McDuffSalamon2017], equations
(6.4.3)–(6.4.5).

If the coordinate changes of `A` preserve `σ`, the integral may be read through any chart of `A`
whose base set contains `b` (`fiberMean_coordChange`): the coordinate change is a diffeomorphism
of `F` that preserves `σ`, so it preserves the volume form (Tau Ceti's
`TauCeti.SmoothTwoForm.mpullback_volumeForm`) and the orientation
(`TauCeti.SmoothForm.diffeomorphStabilizer_le_orientationPreservingSubgroup`), and Tau Ceti's
change of variables
`Topology.IsOpenEmbedding.integralTopForm_mpullback_of_isOrientationPreservingAt` applies. The
argument is that of `TauCeti.MapFiber.Atlas.integralTopForm_fiberIntegrand_trivAt`, with this
integrand.

For compact `F`, the integral is additive in `τ` (`fiberMean_add`), and adding the pull-back of a
two-form `β` on `B` adds `V • β(w₁, w₂)`, where `V` is the integral of `σᵏ / k!` over `F`
(`fiberMean_add_mpullback`), since the horizontal lifts project to `w₁` and `w₂`; `V` is positive
when `F` is nonempty (`TauCeti.SmoothTwoForm.IsNondegenerate.integralTopForm_volumeForm_pos`).

## Closed forms with the same fibres and connection

Let `A` be a smooth atlas of `proj : M → B` with model fibre `F`, and let `τ` and `τ'` be closed
two-forms on `M` that both restrict to a nondegenerate form `σ` on `F` along `A` and have the same
horizontal spaces. Their difference `τ' - τ` is then semibasic for `proj`
(`TauCeti.MapFiber.Atlas.isSemibasic_sub_of_horizontalDistribution_eq`), and, when `F` is
preconnected, basic for `proj`, in the sense of Tau Ceti's `TauCeti.RoughForm.IsBasic`
(`TauCeti.MapFiber.Atlas.isBasic_sub_of_horizontalDistribution_eq`): its value at a point
depends only on the image of the point under `proj` and on the images of its arguments under the
derivative of `proj`. This is a step of the uniqueness of coupling forms, McDuff–Salamon
[McDuffSalamon2017], Theorem 6.4.1.

The argument:

* The two forms agree on pairs of vertical vectors, since both pull back to `σ` on each fibre
  (`TauCeti.MapFiber.Atlas.RestrictsTo.apply_eq`). Having the same horizontal
  spaces, they then agree on `(η, v)` for every vertical `η`
  (`TauCeti.SmoothTwoForm.horizontalDistribution_eq_iff`). So `τ' - τ` is semibasic, and at each
  point its value only depends on the images of its arguments under the derivative of `proj`
  (`TauCeti.RoughForm.IsSemibasicAt.apply_eq_of_mfderiv_eq`).
* Hence it is enough to compare its values on horizontal lifts `w₁♯, w₂♯` of fields `w₁ w₂` on
  `B` that are smooth at a point `b`, at two points over `b`. The functions `τ(w₁♯, w₂♯)` and
  `τ'(w₁♯, w₂♯)` have the same derivative along vertical vectors
  (`TauCeti.IsEhresmannConnection.mvfderiv_val_horizontalLiftField_eq_of_isClosed`), so their
  difference is constant along the fibre over `b`, which is preconnected
  (`TauCeti.MapFiber.Atlas.apply_eq_of_mfderiv_eq_zero_of_proj_eq`).

## Main definitions

* `TauCeti.IsEhresmannConnection.fiberMean`: the fibre integral of `τ(w₁♯, w₂♯) σᵏ / k!`.

## Main results

* `TauCeti.IsEhresmannConnection.fiberMean_coordChange`: for an atlas whose coordinate changes
  preserve `σ`, the integral through any chart at `b`.
* `TauCeti.IsEhresmannConnection.continuous_apply_horizontalLift`: the coefficient of the integrand
  is continuous.
* `TauCeti.IsEhresmannConnection.fiberMean_add`: additivity in `τ`.
* `TauCeti.IsEhresmannConnection.fiberMean_add_mpullback`: the effect of adding a pull-back from
  the base.
* `TauCeti.MapFiber.Atlas.isSemibasic_sub_of_horizontalDistribution_eq`: the difference of two
  forms with the same restriction to the fibres and the same connection is semibasic.
* `TauCeti.MapFiber.Atlas.isBasic_sub_of_horizontalDistribution_eq`: the difference of two closed
  forms with the same restriction to the fibres and the same connection is basic.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §6.4, equations (6.4.3)–(6.4.5) and Theorem 6.4.1.
* [D. McDuff, D. Salamon, errata to the third edition][McDuffSalamon2019Errata], the entries for
  §6.4.
* [V. Guillemin, E. Lerman, S. Sternberg, *Symplectic Fibrations and Multiplicity
  Diagrams*][GuilleminLermanSternberg1996], §1.4.
-/

public section

noncomputable section

open Bundle Module
open scoped Manifold ContDiff

namespace TauCeti.IsEhresmannConnection

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] {HB : Type*}
  [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {B : Type*} [TopologicalSpace B]
  [ChartedSpace HB B]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] {HM : Type*}
  [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM} {M : Type*} [TopologicalSpace M]
  [ChartedSpace HM M] [IsManifold IM ∞ M]
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace ℝ EF] [FiniteDimensional ℝ EF] {HF : Type*}
  [TopologicalSpace HF] {IF : ModelWithCorners ℝ EF HF} {F : Type*} [TopologicalSpace F]
  [ChartedSpace HF F] [IsManifold IF ∞ F]
  {proj : M → B} {D : Π x : M, Submodule ℝ (TangentSpace IM x)} {n : ℕ∞ω}
  {σ : SmoothTwoForm IF F} {k : ℕ}

/-- **The fibre integral of a two-form on horizontal lifts.** For an Ehresmann connection `hD` on
`proj : M → B`, an atlas `A` of `proj` with model fibre `F`, a nondegenerate two-form `σ` on `F` of
dimension `2 * k`, a two-form `τ` on `M`, a point `b` and tangent vectors `w₁ w₂` at `b`: the
integral over `F`, against the symplectic orientation of `σ`, of the top form
`y ↦ τ(w₁♯, w₂♯) • σᵏ / k!`, where `τ` and the horizontal lifts `wᵢ♯` are taken at `e⁻¹ (b, y)`
for the chart `e = A.trivAt b`. This is an integral, not a mean: it is not divided by the
symplectic volume of `F`. -/
def fiberMean (hD : IsEhresmannConnection IM IB n proj D) (A : MapFiber.Atlas F proj)
    (hσ : σ.IsNondegenerate) (hk : finrank ℝ EF = 2 * k) (τ : SmoothTwoForm IM M) (b : B)
    (w₁ w₂ : TangentSpace IB b) : ℝ :=
  integralTopForm (hσ.volumeOrientation hk) fun y ↦
    τ.val ((A.trivAt b).toOpenPartialHomeomorph.symm (b, y))
        ![(hD.horizontalLift _ w₁).val, (hD.horizontalLift _ w₂).val] •
      (σ.volumeForm k).val y

theorem fiberMean_def (hD : IsEhresmannConnection IM IB n proj D) (A : MapFiber.Atlas F proj)
    (hσ : σ.IsNondegenerate) (hk : finrank ℝ EF = 2 * k) (τ : SmoothTwoForm IM M) (b : B)
    (w₁ w₂ : TangentSpace IB b) :
    hD.fiberMean A hσ hk τ b w₁ w₂ = integralTopForm (hσ.volumeOrientation hk) fun y ↦
      τ.val ((A.trivAt b).toOpenPartialHomeomorph.symm (b, y))
          ![(hD.horizontalLift _ w₁).val, (hD.horizontalLift _ w₂).val] •
        (σ.volumeForm k).val y :=
  (rfl)

variable [IsManifold IB 1 B] (hD : IsEhresmannConnection IM IB n proj D)

variable (IF) in
include IF in
omit [FiniteDimensional ℝ EF] [IsManifold IF ∞ F] in
/-- **The coefficient of the integrand of `fiberMean` is continuous.** Along a fibre inclusion
`y ↦ e⁻¹ (b, y)` of a trivialization of a `C^1` map `proj`, the function `y ↦ τ(w₁♯, w₂♯)` on
`F`, with `τ` and the horizontal lifts of two fixed tangent vectors at `b` taken at
`e⁻¹ (b, y)`, is continuous. -/
theorem continuous_apply_horizontalLift (hproj : ContMDiff IM IB 1 proj)
    (τ : SmoothTwoForm IM M) (e : Trivialization F proj) {b : B} (hb : b ∈ e.baseSet)
    (w₁ w₂ : TangentSpace IB b) :
    Continuous fun y : F ↦ τ.val (e.toOpenPartialHomeomorph.symm (b, y))
      ![(hD.horizontalLift _ w₁).val, (hD.horizontalLift _ w₂).val] := by
  have hg : ContMDiff IF IM 0 fun y : F ↦ e.toOpenPartialHomeomorph.symm (b, y) :=
    contMDiff_zero_iff.2 (e.coe_fiberInclusionMap hb ▸ (e.fiberInclusionMap hb).continuous)
  have hproj₀ : ContMDiff IM IB (0 + 1) proj := by simpa using hproj
  have h₁ := (hD.of_le (zero_le (a := n))).contMDiff_horizontalLift
    (w := fun _ ↦ (⟨b, w₁⟩ : TangentBundle IB B))
    (fun _ ↦ (e.proj_symm_apply' hb).symm) hproj₀ hg contMDiff_const
  have h₂ := (hD.of_le (zero_le (a := n))).contMDiff_horizontalLift
    (w := fun _ ↦ (⟨b, w₂⟩ : TangentBundle IB B))
    (fun _ ↦ (e.proj_symm_apply' hb).symm) hproj₀ hg contMDiff_const
  have h := contMDiff_zero_iff.1 (SmoothForm.contMDiff_apply τ h₁ h₂)
  simp only [SmoothBundleForm.eval₂_apply] at h
  convert h using 6 <;> rw [horizontalLift_of_le hD (zero_le (a := n))]

omit [IsManifold IB 1 B] in
/-- **The fibre integral through any chart.** Let the coordinate changes of the atlas `A` preserve
`σ`. For every chart `e = A.trivAt b'` whose base set contains `b`, `fiberMean` is the integral of
`y ↦ τ(w₁♯, w₂♯) • σᵏ / k!` with `τ` and the lifts taken at `e⁻¹ (b, y)`. -/
theorem fiberMean_coordChange {A : MapFiber.Atlas F proj}
    (hA : A.HasStructureGroup (SmoothForm.diffeomorphStabilizer σ)) (hσ : σ.IsNondegenerate)
    (hk : finrank ℝ EF = 2 * k) (τ : SmoothTwoForm IM M) {b b' : B}
    (hb : b ∈ (A.trivAt b').baseSet) (w₁ w₂ : TangentSpace IB b) :
    hD.fiberMean A hσ hk τ b w₁ w₂ = integralTopForm (hσ.volumeOrientation hk) fun y ↦
      τ.val ((A.trivAt b').toOpenPartialHomeomorph.symm (b, y))
          ![(hD.horizontalLift _ w₁).val, (hD.horizontalLift _ w₂).val] •
        (σ.volumeForm k).val y := by
  obtain ⟨φ, hφ, hφe⟩ :=
    MapFiber.Atlas.hasStructureGroup_iff.1 hA b' b b hb (A.mem_baseSet_trivAt b)
  have hvol : mpullback IF IF φ (σ.volumeForm k).val = (σ.volumeForm k).val :=
    SmoothTwoForm.mpullback_volumeForm
      (funext (SmoothForm.mem_diffeomorphStabilizer_iff_forall.1 hφ))
  -- The point `e'⁻¹ (b, y)` is `e⁻¹ (b, φ y)`, for `e = A.trivAt b` and `e' = A.trivAt b'`.
  have hpt (y : F) : (A.trivAt b').toOpenPartialHomeomorph.symm (b, y) =
      (A.trivAt b).toOpenPartialHomeomorph.symm (b, φ y) := by
    rw [hφe, ← Trivialization.fiberInclusionMap_apply _ (A.mem_baseSet_trivAt b),
      Trivialization.fiberInclusionMap_coordChange _ _ hb, Trivialization.fiberInclusionMap_apply]
  -- `rw` cannot move the point alone: the lifted vectors live in the tangent space at it.
  have hval {x x' : M} (h : x = x') :
      τ.val x ![(hD.horizontalLift x w₁).val, (hD.horizontalLift x w₂).val] =
        τ.val x' ![(hD.horizontalLift x' w₁).val, (hD.horizontalLift x' w₂).val] := by
    subst h
    rfl
  have he := φ.toHomeomorph.isOpenEmbedding
  rw [fiberMean_def, ← he.integralTopForm_mpullback_of_isOrientationPreservingAt
    (Diffeomorph.mem_orientationPreservingSubgroup_iff.mp
      (SmoothForm.diffeomorphStabilizer_le_orientationPreservingSubgroup hσ hk hφ)) (by simp)]
  congr 1
  funext y
  ext v
  rw [mpullback_apply, ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.smul_apply,
    ← mpullback_apply, Diffeomorph.coe_toHomeomorph, hvol, hval (hpt y)]

/-- **`fiberMean` is additive in the two-form**, for a compact model fibre and a `C^1` map
`proj`. -/
theorem fiberMean_add [CompactSpace F] (hproj : ContMDiff IM IB 1 proj) (A : MapFiber.Atlas F proj)
    (hσ : σ.IsNondegenerate) (hk : finrank ℝ EF = 2 * k) (τ τ' : SmoothTwoForm IM M) (b : B)
    (w₁ w₂ : TangentSpace IB b) :
    hD.fiberMean A hσ hk (τ + τ') b w₁ w₂ =
      hD.fiberMean A hσ hk τ b w₁ w₂ + hD.fiberMean A hσ hk τ' b w₁ w₂ := by
  simp only [fiberMean_def]
  rw [← integralTopForm_add_smul_of_compactSpace _ (σ.volumeForm k).isSmoothForm
    (hD.continuous_apply_horizontalLift IF hproj τ _ (A.mem_baseSet_trivAt b) w₁ w₂)
    (hD.continuous_apply_horizontalLift IF hproj τ' _ (A.mem_baseSet_trivAt b) w₁ w₂)]
  rfl

/-- **Adding a pull-back from the base.** For a compact model fibre, a smooth map `proj` and a
two-form `β` on `B`, adding the pull-back of `β` to `τ` adds `V * β(w₁, w₂)` to `fiberMean`,
where `V` is the integral over `F` of the symplectic volume form `σᵏ / k!`, the symplectic volume
of `F` (positive when `F` is nonempty, by
`TauCeti.SmoothTwoForm.IsNondegenerate.integralTopForm_volumeForm_pos`). -/
theorem fiberMean_add_mpullback [CompactSpace F] [IsManifold IB ∞ B]
    (hproj : ContMDiff IM IB ∞ proj) (A : MapFiber.Atlas F proj) (hσ : σ.IsNondegenerate)
    (hk : finrank ℝ EF = 2 * k) (τ : SmoothTwoForm IM M) (β : SmoothTwoForm IB B) (b : B)
    (w₁ w₂ : TangentSpace IB b) :
    hD.fiberMean A hσ hk (τ + SmoothForm.mpullback proj hproj β) b w₁ w₂ =
      hD.fiberMean A hσ hk τ b w₁ w₂ +
        integralTopForm (hσ.volumeOrientation hk) (σ.volumeForm k).val * β.val b ![w₁, w₂] := by
  have hβ (y : F) :
      (SmoothForm.mpullback proj hproj β).val ((A.trivAt b).toOpenPartialHomeomorph.symm (b, y))
          ![(hD.horizontalLift _ w₁).val, (hD.horizontalLift _ w₂).val] = β.val b ![w₁, w₂] := by
    -- As above, `rw` cannot move the base point alone, since `w₁` and `w₂` are read at it.
    have hb {p : B} (h : p = b) : β.val p ![w₁, w₂] = β.val b ![w₁, w₂] := by
      subst h
      rfl
    rw [SmoothForm.coe_mpullback, mpullback_apply_pair, hD.mfderiv_horizontalLift _ w₁,
      hD.mfderiv_horizontalLift _ w₂]
    exact hb ((A.trivAt b).proj_symm_apply' (A.mem_baseSet_trivAt b))
  rw [fiberMean_add hD (hproj.of_le (by simp)), mul_comm, ← integralTopForm_smul]
  congr 1
  rw [fiberMean_def]
  congr 1
  funext y
  rw [hβ, Pi.smul_apply]

end TauCeti.IsEhresmannConnection

namespace TauCeti.MapFiber.Atlas

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {B : Type*}
  [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB ∞ B]
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace ℝ EF] {HF : Type*} [TopologicalSpace HF]
  {IF : ModelWithCorners ℝ EF HF} {F : Type*} [TopologicalSpace F] [ChartedSpace HF F]
  [IsManifold IF ∞ F]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [FiniteDimensional ℝ EM] {HM : Type*}
  [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM} [IM.Boundaryless] {M : Type*}
  [TopologicalSpace M] [ChartedSpace HM M] [IsManifold IM ∞ M]
  {proj : M → B} {A : Atlas F proj} {σ : SmoothTwoForm IF F} {τ τ' : SmoothTwoForm IM M}

omit [FiniteDimensional ℝ EB] [IsManifold IB ∞ B] [IM.Boundaryless] in
/-- **Forms with the same fibres and connection differ by a semibasic form.** Let `A` be a
smooth atlas of `proj : M → B`, and let `τ` and `τ'` be two-forms on `M` that restrict to the same
nondegenerate form `σ` on the model fibre and have the same horizontal spaces. Then `τ' - τ` is
semibasic for `proj`: it vanishes as soon as one of its arguments is vertical. -/
theorem isSemibasic_sub_of_horizontalDistribution_eq (hA : A.IsContMDiff ∞ IB IF IM)
    (hσ : σ.IsNondegenerate) (hτ : A.RestrictsTo σ τ) (hτ' : A.RestrictsTo σ τ')
    (hD : SmoothTwoForm.horizontalDistribution IB proj τ =
      SmoothTwoForm.horizontalDistribution IB proj τ') :
    RoughForm.IsSemibasic IB proj (τ' - τ).val := by
  -- The forms agree as soon as one argument is vertical.
  have hmix := (SmoothTwoForm.horizontalDistribution_eq_iff (hτ.isVerticallyNondegenerate hA hσ)
    fun x η₁ hη₁ η₂ hη₂ ↦ by
      simp only [SmoothForm.bilinFormAt_apply, SmoothBundleForm.eval₂_apply]
      exact hτ.apply_eq hA hτ' (Fin.forall_fin_two.2 ⟨hη₁, hη₂⟩)).1 hD
  refine SmoothForm.isSemibasic_iff_ker_mfderiv_le.2 fun x η hη ↦ ?_
  ext v
  have h := hmix x η hη v
  simp only [SmoothForm.bilinFormAt_apply, SmoothBundleForm.eval₂_apply] at h
  simp only [SmoothForm.bilinFormAt_apply, LinearMap.zero_apply, SmoothBundleForm.eval₂_apply,
    Submodule.coe_sub, Pi.sub_apply, ContinuousAlternatingMap.sub_apply, h, sub_self]

/-- **Closed forms with the same fibres and connection differ by a basic form.** Let `A` be a
smooth atlas of `proj : M → B` with preconnected model fibre `F`, and let `τ` and `τ'` be closed
two-forms on `M` that restrict to the same nondegenerate form `σ` on `F` and have the same
horizontal spaces. Then `τ' - τ` is basic for `proj`: `(τ' - τ)_x(v) = (τ' - τ)_y(w)` whenever
`proj x = proj y` and the derivatives of `proj` send `v` and `w` to the same vectors. -/
theorem isBasic_sub_of_horizontalDistribution_eq [PreconnectedSpace F]
    (hA : A.IsContMDiff ∞ IB IF IM) (hσ : σ.IsNondegenerate) (hτc : τ.IsClosed)
    (hτ'c : τ'.IsClosed) (hτ : A.RestrictsTo σ τ) (hτ' : A.RestrictsTo σ τ')
    (hD : SmoothTwoForm.horizontalDistribution IB proj τ =
      SmoothTwoForm.horizontalDistribution IB proj τ') :
    RoughForm.IsBasic IB proj (τ' - τ).val := by
  have hE := (hτ.isVerticallyNondegenerate hA hσ).isEhresmannConnection
    (hA.isSubmersion ENat.LEInfty.out)
  have hproj : ContMDiff IM IB 2 proj := (hA.isSubmersion ENat.LEInfty.out).contMDiff.of_le
    (by simp)
  have hsemi := isSemibasic_sub_of_horizontalDistribution_eq hA hσ hτ hτ' hD
  -- The forms agree as soon as one argument is vertical.
  have hmix : ∀ x, ∀ η ∈ (mfderiv IM IB proj x).ker, ∀ v : TangentSpace IM x,
      τ.bilinFormAt x η v = τ'.bilinFormAt x η v := fun x η hη v ↦ by
    have h := LinearMap.congr_fun (SmoothForm.isSemibasic_iff_ker_mfderiv_le.1 hsemi x hη) v
    simp only [SmoothForm.bilinFormAt_apply, LinearMap.zero_apply, SmoothBundleForm.eval₂_apply,
      Submodule.coe_sub, Pi.sub_apply, ContinuousAlternatingMap.sub_apply, sub_eq_zero] at h ⊢
    exact h.symm
  refine RoughForm.isBasic_iff.2 fun x y hxy v w hvw ↦ ?_
  -- Extend the images of the arguments to fields on `B`, smooth at `proj x`.
  let U₁ := FiberBundle.extend EB (mfderiv IM IB proj x (v 0))
  let U₂ := FiberBundle.extend EB (mfderiv IM IB proj x (v 1))
  -- The values of two-forms on the horizontal lifts of `U₁` and `U₂`.
  let G : SmoothTwoForm IM M → M → ℝ := fun ρ z ↦
    ρ.val z ![hE.horizontalLiftField U₁ z, hE.horizontalLiftField U₂ z]
  let g : M → ℝ := G τ' - G τ
  -- At any point over `proj x`, the value of `τ' - τ` on lifts of the images of `v` is that of `g`.
  have hlift : ∀ z, proj z = proj x → ∀ u : Fin 2 → TangentSpace IM z,
      (∀ i, mfderiv IM IB proj z (u i) = mfderiv IM IB proj x (v i)) → (τ' - τ).val z u = g z := by
    intro z hz u hu
    refine ((RoughForm.isSemibasic_def.1 hsemi z).apply_eq_of_mfderiv_eq
      (w := ![hE.horizontalLiftField U₁ z, hE.horizontalLiftField U₂ z]) fun i ↦ ?_).trans ?_
    swap
    · simp only [g, G, Submodule.coe_sub, Pi.sub_apply, ContinuousAlternatingMap.sub_apply]
    rw [hu i]
    -- The fields `U₁` and `U₂` take the prescribed values over `proj z = proj x`.
    fin_cases i <;>
      exact (eq_of_heq ((congr_arg_heq _ hz).trans
        (heq_of_eq (FiberBundle.extend_apply_self _ _)))).symm.trans
          (hE.mfderiv_horizontalLiftField _ z).symm
  have hU₁ : ContMDiffAt IB IB.tangent 1 (T% U₁) (proj x) :=
    FiberBundle.contMDiffAt_extend (I := IB) EB _
  have hU₂ : ContMDiffAt IB IB.tangent 1 (T% U₂) (proj x) :=
    FiberBundle.contMDiffAt_extend (I := IB) EB _
  -- At each point over `proj x`, the two functions making up `g` are differentiable.
  have hdiff : ∀ z, proj z = proj x → ∀ ρ : SmoothTwoForm IM M,
      MDifferentiableAt IM 𝓘(ℝ, ℝ) (G ρ) z := by
    intro z hz ρ
    have h₁ := hE.mdifferentiableAt_horizontalLiftField (by simp) (hproj z) (hz ▸ hU₁)
    have h₂ := hE.mdifferentiableAt_horizontalLiftField (by simp) (hproj z) (hz ▸ hU₂)
    convert ρ.mdifferentiableAt_apply_vectorField
      (V := ![hE.horizontalLiftField U₁, hE.horizontalLiftField U₂])
      (fun i ↦ by fin_cases i <;> assumption) using 3 with z
    ext i
    fin_cases i <;> simp
  -- `g` is constant on the fibre over `proj x`: along vertical vectors, its two halves have the
  -- same derivative.
  have hconst : g x = g y := by
    refine apply_eq_of_mfderiv_eq_zero_of_proj_eq hA (by simp) hxy
      (fun z hz ↦ (hdiff z hz τ').sub (hdiff z hz τ)) fun z hz η hη ↦ ?_
    rw [← mvfderiv_apply_eq_mfderiv_apply, mvfderiv_sub (hdiff _ hz τ') (hdiff _ hz τ), sub_apply]
    refine sub_eq_zero.2 ?_
    exact TauCeti.IsEhresmannConnection.mvfderiv_val_horizontalLiftField_eq_of_isClosed hE
      (by simp) hproj hτc hτ'c hmix (by rwa [hz]) (by rwa [hz]) hη
  refine (hlift x rfl v fun _ ↦ rfl).trans (hconst.trans (hlift y hxy.symm w fun i ↦ ?_).symm)
  -- The images of `w` and `v` agree, read over `proj y = proj x`.
  exact eq_of_heq ((heq_tangentSpaceCast hxy.symm _).symm.trans (heq_of_eq (hvw i).symm))

end TauCeti.MapFiber.Atlas
