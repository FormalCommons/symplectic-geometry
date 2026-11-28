/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.FiberBundle.StructureGroup
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.TopForm
public import TauCeti.Geometry.Manifold.Submersion.EhresmannConnection.Basic
public import TauCeti.Geometry.Symplectic.Manifold.Volume
import SymplecticGeometry.Geometry.Manifold.Submersion.HorizontalLiftField
import SymplecticGeometry.Geometry.Symplectic.Manifold.Volume
import SymplecticGeometry.Topology.FiberBundle.Basic
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.ChangeOfVariables
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Regularity

/-!
# Coupling forms: the fibre integral of a two-form on horizontal lifts

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

## Main definitions

* `TauCeti.IsEhresmannConnection.fiberMean`: the fibre integral of `τ(w₁♯, w₂♯) σᵏ / k!`.

## Main results

* `TauCeti.IsEhresmannConnection.fiberMean_coordChange`: for an atlas whose coordinate changes
  preserve `σ`, the integral through any chart at `b`.
* `TauCeti.IsEhresmannConnection.isSmoothForm_apply_horizontalLift_smul_volumeForm`: the integrand
  is continuous.
* `TauCeti.IsEhresmannConnection.fiberMean_add`: additivity in `τ`.
* `TauCeti.IsEhresmannConnection.fiberMean_add_mpullback`: the effect of adding a pull-back from
  the base.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §6.4, equations (6.4.3)–(6.4.5).
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

omit [FiniteDimensional ℝ EF] in
/-- **The integrand of `fiberMean` is continuous.** Along a fibre inclusion `y ↦ e⁻¹ (b, y)`
of a trivialization of a `C^1` map `proj`, the top form `y ↦ τ(w₁♯, w₂♯) • σᵏ / k!` on `F`, with
`τ` and the horizontal lifts of two fixed tangent vectors at `b` taken at `e⁻¹ (b, y)`, is
continuous. -/
theorem isSmoothForm_apply_horizontalLift_smul_volumeForm (hproj : ContMDiff IM IB 1 proj)
    (τ : SmoothTwoForm IM M) (e : Trivialization F proj) {b : B} (hb : b ∈ e.baseSet)
    (w₁ w₂ : TangentSpace IB b) :
    IsSmoothForm IF 0 fun y ↦ τ.val (e.toOpenPartialHomeomorph.symm (b, y))
      ![(hD.horizontalLift _ w₁).val, (hD.horizontalLift _ w₂).val] • (σ.volumeForm k).val y := by
  refine (σ.volumeForm k).isSmoothForm.fun_smul_of_continuous ?_
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
  rw [← integralTopForm_add_of_compactSpace _
    (hD.isSmoothForm_apply_horizontalLift_smul_volumeForm hproj τ _ (A.mem_baseSet_trivAt b) w₁ w₂)
    (hD.isSmoothForm_apply_horizontalLift_smul_volumeForm hproj τ' _ (A.mem_baseSet_trivAt b) w₁
      w₂)]
  congr 1
  funext y
  rw [Pi.add_apply, ← add_smul, Submodule.coe_add, Pi.add_apply,
    ContinuousAlternatingMap.add_apply]

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
