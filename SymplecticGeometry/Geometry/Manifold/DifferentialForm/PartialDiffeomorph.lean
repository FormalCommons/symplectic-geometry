/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Topology.VectorBundle.Riemannian
public import TauCeti.Geometry.Manifold.DifferentialForm.AlmostComplexType
public import TauCeti.Geometry.Manifold.DifferentialForm.ExtDeriv
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Smooth.Basic
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Chart
import SymplecticGeometry.Analysis.Normed.Module.Alternating.Derivation
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.LocalDiffeomorph
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.Chart
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Analysis.Calculus.DifferentialForm.Wedge
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.ModelSpace

/-!
# Differential forms read through a partial diffeomorphism onto a normed space

Let `ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞` be a chart of `M` with values in its model vector
space. A form `φ` on `M` is read in `ψ` as the flat form `mpullback 𝓘(ℝ, E) I ψ.symm φ` on `E`,
which is meaningful on `ψ.target`.

## Main declarations

* `TauCeti.mpullback_symm_eq_inChartAt`: for the restricted extended chart
  `TauCeti.extChartPartialDiffeomorph I n x`, this reading is Tau Ceti's coordinate expression
  `RoughForm.inChartAt` at `x`, at every point of the target, with no assumption on the boundary
  of the model: that target lies in the interior of `range I`.
* `TauCeti.mpullback_symm_mextDerivₗ`: on the target, the reading of `dφ` is the flat exterior
  derivative `extDeriv` of the reading of `φ`.
* `TauCeti.mpullback_symm_realAlternatingDerivation`: the reading of the real derivation
  `J.toEndomorphism.realAlternatingDerivation φ` of a smooth form along an almost complex
  structure `J` is the derivation of the reading of `φ` along the pushed-forward structure
  `J.chartPushforward`.
* `TauCeti.mpullback_symm_compContinuousLinearMap_mfderiv`,
  `TauCeti.fderiv_mpullback_symm_wedge_apply` and
  `TauCeti.fderiv_mpullback_symm_realAlternatingDerivation_apply`: a form at `ψ.symm y` is its
  reading at `y` pulled back along the differential of `ψ`; and the derivatives of the readings
  of `β ∧ σ` and of `𝒥 φ` are given by the Leibniz rule and, in a chart in which `J` is constant,
  by the derivation of that constant.
* `TauCeti.symbolInChart ψ φ y`: the derivative at `y` of the reading of `φ`, carried to the
  tangent space at `ψ.symm y` along the differential of `ψ`. The value of `dφ` at `ψ.symm y` is
  its alternation (`TauCeti.val_mextDerivₗ_symm_eq_alternatizeUncurryFin_symbolInChart`), and in
  a chart in which `J` is constant it carries `𝒥 φ` to the derivation of `J (ψ.symm y)`
  (`TauCeti.symbolInChart_realAlternatingDerivation_apply`).
* `TauCeti.RoughForm.extendByZeroAlong ψ a`: the form on `M` that is the pullback along `ψ` of a
  flat form `a` on the source of `ψ`, and zero elsewhere; `TauCeti.mpullback_symm_extendByZeroAlong`
  recovers `a` on `ψ.target`. When `a` is smooth with compact support in `ψ.target`, the
  extension is smooth (`TauCeti.IsSmoothForm.extendByZeroAlong`), and bundled as
  `TauCeti.SmoothForm.extendByZeroAlong`. Both versions are linear in `a`
  (`extendByZeroAlong_zero`, `_add`, `_smul`, `_neg` and `_sub`).
* `TauCeti.SmoothForm.localize ψ χ α`: in the other direction, the flat form on `E` that is the
  reading of a smooth form `α` in `ψ`, scaled by `χ ∘ ψ.symm` for a cutoff `χ` on `M`, on
  `ψ.target`, and zero elsewhere. It is continuous with compact support when `χ` is continuous
  with compact support in `ψ.source` (`TauCeti.SmoothForm.continuous_localize`,
  `TauCeti.SmoothForm.hasCompactSupport_localize`), and smooth when `χ` is smooth
  (`TauCeti.SmoothForm.contDiff_localize`).
* `TauCeti.SmoothForm.sum_extendByZeroAlong_localize`: the two constructions are inverse to each
  other up to the cutoff (`TauCeti.SmoothForm.extendByZeroAlong_localize_apply`), so a smooth form
  is the sum of the extensions by zero of its localizations to finitely many charts, with a smooth
  partition of unity subordinate to their sources as cutoffs.
* `TauCeti.SmoothForm.contDiffAt_mpullback_symm` and
  `TauCeti.SmoothForm.differentiableAt_mpullback_symm`: the reading of a smooth form in `ψ` is
  smooth, hence differentiable, at each point of `ψ.target`.
* `TauCeti.SmoothForm.contDiffOn_fderiv_mpullback_symm_apply`: the partial derivatives of the
  reading of a smooth form in `ψ` are smooth on `ψ.target`.

The proof of `TauCeti.mpullback_symm_eq_inChartAt` is the pointwise form of the argument of Tau
Ceti's `TauCeti.RoughForm.inChartAt_ae_eq_mpullback`, which proves the same equality almost
everywhere on the target of the extended chart. The statements and docstrings of
`TauCeti.RoughForm.extendByZeroAlong_zero`, `_add` and `_smul` follow those of Tau Ceti's
`TauCeti.RoughForm.extendByZero_zero`, `extendByZero_add` and `extendByZero_smul`.

## References

* [P. Griffiths, J. Harris, *Principles of Algebraic Geometry*][GriffithsHarris1978],
  Chapter 0, §6.
-/

public section

noncomputable section

open Set Filter
open scoped Manifold Topology ContDiff

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-! ### The atlas chart -/

/-- On the target of the restricted extended chart at `x`, reading a form through the inverse of
that chart gives its coordinate expression `inChartAt` at `x`. -/
theorem mpullback_symm_eq_inChartAt {n : WithTop ℕ∞} [IsManifold I n M] (φ : RoughForm I M F k)
    (x : M) {y : E} (hy : y ∈ (extChartPartialDiffeomorph I n x).target) :
    (mpullback 𝓘(ℝ, E) I (extChartPartialDiffeomorph I n x).symm φ y : E [⋀^Fin k]→L[ℝ] F) =
      φ.inChartAt x y := by
  have hsymm : ⇑(extChartPartialDiffeomorph I n x).symm = (extChartAt I x).symm :=
    funext (extChartPartialDiffeomorph_symm_apply I n x)
  rw [extChartPartialDiffeomorph_target] at hy
  have hI : range I ∈ 𝓝 y := mem_interior_iff_mem_nhds.mp
    (interior_mono (extChartAt_target_subset_range x) hy)
  have hd := mfderivWithin_of_mem_nhds (I := 𝓘(ℝ, E)) (I' := I) (f := (extChartAt I x).symm) hI
  ext v
  rw [hsymm]
  exact (mpullback_apply _ φ y v).trans ((congrArg (fun L : TangentSpace 𝓘(ℝ, E) y →L[ℝ]
    TangentSpace I ((extChartAt I x).symm y) ↦ φ _ fun i ↦ L (v i)) hd.symm).trans
      (RoughForm.inChartAt_apply φ x y v).symm)

/-! ### The exterior derivative -/

/-- On the target of a partial diffeomorphism `ψ` onto an open subset of `E`, the exterior
derivative of a smooth form, read through `ψ`, is the flat exterior derivative of its reading. -/
theorem mpullback_symm_mextDerivₗ [IsManifold I ∞ M] (ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞)
    (φ : SmoothForm I M F k) {y : E} (hy : y ∈ ψ.target) :
    (mpullback 𝓘(ℝ, E) I ψ.symm (mextDerivₗ I k φ).val y : E [⋀^Fin (k + 1)]→L[ℝ] F) =
      extDeriv (mpullback 𝓘(ℝ, E) I ψ.symm φ.val : E → E [⋀^Fin k]→L[ℝ] F) y := by
  rw [mextDerivₗ_apply, mpullback_mextDeriv_at
    ((ψ.symm.contMDiffOn.contMDiffAt (ψ.open_target.mem_nhds hy)).of_le (by simp))
    ((φ.contMDiff _).of_le (by simp)), mextDeriv_eq_extDeriv]

/-! ### The derivation along an almost complex structure -/

/-- Read through a chart `ψ` with values in the model space, the real derivation of a smooth form
`φ` along an almost complex structure `J` is the derivation of the reading of `φ` along the
structure `J.chartPushforward` that `J` induces on `ψ.target`. -/
theorem mpullback_symm_realAlternatingDerivation [IsManifold I ∞ M]
    (J : SmoothAlmostComplexStructure I M) (ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞)
    (φ : SmoothForm I M ℝ k) {y : E} (hy : y ∈ ψ.target)
    (v : Fin k → TangentSpace 𝓘(ℝ, E) y) :
    mpullback 𝓘(ℝ, E) I ψ.symm (J.toEndomorphism.realAlternatingDerivation φ).val y v =
      ∑ i, mpullback 𝓘(ℝ, E) I ψ.symm φ.val y
        (Function.update v i (J.chartPushforward ψ.toOpenPartialHomeomorph y (v i))) := by
  have hJ := J.mfderiv_symm_apply_chartPushforward_apply ψ hy
  simp only [mpullback_apply, ContMDiffSection.realAlternatingDerivation_apply]
  refine Finset.sum_congr rfl fun i _ ↦ congrArg (φ.val (ψ.symm y)) (funext fun j ↦ ?_)
  rcases eq_or_ne j i with rfl | hj
  · rw [Function.update_self]
    exact (hJ (v j)).symm.trans (congrArg _ (Function.update_self j _ v).symm)
  · rw [Function.update_of_ne hj]
    exact congrArg _ (Function.update_of_ne hj _ v).symm

/-! ### Values and derivatives of forms read in a chart -/

section Readings

/-- A form at `ψ.symm y` is recovered from its reading in the chart at `y` by pulling back along
the differential of `ψ`. This is `PartialDiffeomorph.mpullback_mpullback_symm_apply` at `ψ.symm y`,
with the reading taken at `y` rather than at `ψ (ψ.symm y)`. -/
theorem mpullback_symm_compContinuousLinearMap_mfderiv {n : WithTop ℕ∞}
    (ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E n) (hn : n ≠ 0) (φ : RoughForm I M F k) {y : E}
    (hy : y ∈ ψ.target) :
    (mpullback 𝓘(ℝ, E) I ψ.symm φ y : E [⋀^Fin k]→L[ℝ] F).compContinuousLinearMap
        (mfderiv I 𝓘(ℝ, E) ψ (ψ.symm y) : TangentSpace I (ψ.symm y) →L[ℝ] E) =
      φ (ψ.symm y) := by
  ext v
  -- The left side evaluated at `v` is the pullback evaluated at the images of `v`.
  refine (mpullback_apply _ φ y _).trans ?_
  exact congrArg (φ (ψ.symm y))
    (funext fun i ↦ ψ.mfderiv_symm_apply_mfderiv_apply_of_mem_target hn hy (v i))

/-- The derivative at `y` of the reading of a form `φ` in the chart `ψ`, carried to the tangent
space at `ψ.symm y` along the differential of `ψ`: the continuous linear map that sends `v` to the
derivative of the reading in the direction `dψ v`, pulled back along `dψ`. At `ψ.symm y`, the
exterior derivative `dφ` is its alternation
(`TauCeti.val_mextDerivₗ_symm_eq_alternatizeUncurryFin_symbolInChart`). -/
def symbolInChart (ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞) (φ : RoughForm I M F k) (y : E) :
    TangentSpace I (ψ.symm y) →L[ℝ] TangentSpace I (ψ.symm y) [⋀^Fin k]→L[ℝ] F :=
  ContinuousAlternatingMap.compContinuousLinearMapCLM
      (mfderiv I 𝓘(ℝ, E) ψ (ψ.symm y) : TangentSpace I (ψ.symm y) →L[ℝ] E) ∘L
    fderiv ℝ (F := E [⋀^Fin k]→L[ℝ] F) (mpullback 𝓘(ℝ, E) I ψ.symm φ) y ∘L
      (mfderiv I 𝓘(ℝ, E) ψ (ψ.symm y) : TangentSpace I (ψ.symm y) →L[ℝ] E)

theorem symbolInChart_def (ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞) (φ : RoughForm I M F k)
    (y : E) :
    symbolInChart ψ φ y =
      ContinuousAlternatingMap.compContinuousLinearMapCLM
          (mfderiv I 𝓘(ℝ, E) ψ (ψ.symm y) : TangentSpace I (ψ.symm y) →L[ℝ] E) ∘L
        fderiv ℝ (F := E [⋀^Fin k]→L[ℝ] F) (mpullback 𝓘(ℝ, E) I ψ.symm φ) y ∘L
          (mfderiv I 𝓘(ℝ, E) ψ (ψ.symm y) : TangentSpace I (ψ.symm y) →L[ℝ] E) :=
  (rfl)

theorem symbolInChart_apply (ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞) (φ : RoughForm I M F k)
    (y : E) (v : TangentSpace I (ψ.symm y)) :
    symbolInChart ψ φ y v =
      (fderiv ℝ (F := E [⋀^Fin k]→L[ℝ] F) (mpullback 𝓘(ℝ, E) I ψ.symm φ) y
        (mfderiv I 𝓘(ℝ, E) ψ (ψ.symm y) v)).compContinuousLinearMap
        (mfderiv I 𝓘(ℝ, E) ψ (ψ.symm y) : TangentSpace I (ψ.symm y) →L[ℝ] E) :=
  (rfl)

variable [IsManifold I ∞ M]

/-- **The Leibniz rule in a chart**: on the target of a chart, the derivative of the reading of
`β ∧ σ` is `Dβ ∧ σ + β ∧ Dσ`, in terms of the readings of `β` and `σ`. -/
theorem fderiv_mpullback_symm_wedge_apply {l : ℕ} (ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞)
    (β : SmoothForm I M ℝ k) (σ : SmoothForm I M ℝ l) {y : E} (hy : y ∈ ψ.target) (v : E) :
    fderiv ℝ (F := E [⋀^Fin (k + l)]→L[ℝ] ℝ)
        (mpullback 𝓘(ℝ, E) I ψ.symm (SmoothForm.wedge β σ).val) y v =
      ContinuousAlternatingMap.wedge
          (fderiv ℝ (F := E [⋀^Fin k]→L[ℝ] ℝ) (mpullback 𝓘(ℝ, E) I ψ.symm β.val) y v)
          (mpullback 𝓘(ℝ, E) I ψ.symm σ.val y : E [⋀^Fin l]→L[ℝ] ℝ) +
        ContinuousAlternatingMap.wedge (mpullback 𝓘(ℝ, E) I ψ.symm β.val y : E [⋀^Fin k]→L[ℝ] ℝ)
          (fderiv ℝ (F := E [⋀^Fin l]→L[ℝ] ℝ) (mpullback 𝓘(ℝ, E) I ψ.symm σ.val) y v) := by
  have hT := ψ.open_target.mem_nhds hy
  have hd {j : ℕ} (φ : SmoothForm I M ℝ j) : DifferentiableAt ℝ (F := E [⋀^Fin j]→L[ℝ] ℝ)
      (mpullback 𝓘(ℝ, E) I ψ.symm φ.val) y :=
    ((φ.contDiffOn_mpullback ψ.open_target ψ.symm.contMDiffOn).contDiffAt hT).differentiableAt
      (by simp)
  rw [SmoothForm.coe_wedge, mpullback_wedge, RoughForm.wedge_def,
    show RoughForm.wedgeWith (ContinuousLinearMap.mul ℝ ℝ) (mpullback 𝓘(ℝ, E) I ψ.symm β.val)
      (mpullback 𝓘(ℝ, E) I ψ.symm σ.val) = fun z ↦ _ from
      funext (RoughForm.wedgeWith_apply' _ _ _)]
  refine (fderiv_pairedWedge_apply (μ := fun _ : E ↦ ContinuousLinearMap.mul ℝ ℝ)
      (differentiableAt_const _) (hd β) (hd σ) v).trans ?_
  simp only [fderiv_fun_const, Pi.zero_apply, zero_apply]
  -- The forms read in the chart have the fibres of the pullback as their types, so the term of
  -- the constant pairing is cleared up to that identification of types.
  erw [ContinuousAlternatingMap.pairedWedge_zero_pairing, zero_add]
  exact (congrArg₂ (· + ·) (ContinuousAlternatingMap.wedge_def _ _)
    (ContinuousAlternatingMap.wedge_def _ _)).symm

/-- In a chart in which `J` is a constant endomorphism `A₀`, the derivative of the reading of
`𝒥 φ` is `D_{A₀}` applied to the derivative of the reading of `φ`, where `D_{A₀}` is the
derivation of `A₀` on forms. -/
theorem fderiv_mpullback_symm_realAlternatingDerivation_apply
    (J : SmoothAlmostComplexStructure I M) (ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞)
    {A₀ : E →L[ℝ] E}
    (hψ : ∀ p ∈ ψ.target, ∀ w, J.chartPushforward ψ.toOpenPartialHomeomorph p w = A₀ w)
    (φ : SmoothForm I M ℝ k) {y : E} (hy : y ∈ ψ.target) (v : E) :
    fderiv ℝ (F := E [⋀^Fin k]→L[ℝ] ℝ)
        (mpullback 𝓘(ℝ, E) I ψ.symm (J.toEndomorphism.realAlternatingDerivation φ).val) y v =
      (fderiv ℝ (F := E [⋀^Fin k]→L[ℝ] ℝ) (mpullback 𝓘(ℝ, E) I ψ.symm φ.val) y
        v).fderivCompContinuousLinearMap (.id ℝ E) A₀ := by
  set L := (ContinuousAlternatingMap.fderivCompContinuousLinearMapCLM ℝ (ι := Fin k)
    (.id ℝ E)).flip A₀
  have hT := ψ.open_target.mem_nhds hy
  have hd : DifferentiableAt ℝ (F := E [⋀^Fin k]→L[ℝ] ℝ)
      (mpullback 𝓘(ℝ, E) I ψ.symm φ.val) y :=
    ((φ.contDiffOn_mpullback ψ.open_target ψ.symm.contMDiffOn).contDiffAt hT).differentiableAt
      (by simp)
  have hev : (fun z ↦ L (mpullback 𝓘(ℝ, E) I ψ.symm φ.val z)) =ᶠ[𝓝 y]
      (mpullback 𝓘(ℝ, E) I ψ.symm (J.toEndomorphism.realAlternatingDerivation φ).val :
        E → E [⋀^Fin k]→L[ℝ] ℝ) := by
    filter_upwards [hT] with z hz
    ext w
    refine Eq.trans ?_ (mpullback_symm_realAlternatingDerivation J ψ φ hz w).symm
    simp only [hψ z hz]
    -- The two sides differ only in the fibre type in which the form is read.
    exact ContinuousAlternatingMap.fderivCompContinuousLinearMap_id_apply _ _ _
  rw [((L.hasFDerivAt.comp y hd.hasFDerivAt).congr_of_eventuallyEq hev.symm).fderiv]
  simp [L]

-- The alternation and the derivation of forms on the tangent space below use its norm, which the
-- metric gives.
open Bundle
variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- At `ψ.symm y`, the exterior derivative of a smooth form is the alternation of the derivative
of its reading in the chart, carried to the tangent space by `symbolInChart`. -/
theorem val_mextDerivₗ_symm_eq_alternatizeUncurryFin_symbolInChart
    (ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞) (φ : SmoothForm I M F k) {y : E}
    (hy : y ∈ ψ.target) :
    (mextDerivₗ I k φ).val (ψ.symm y) =
      ContinuousAlternatingMap.alternatizeUncurryFin (symbolInChart ψ φ.val y) := by
  rw [← mpullback_symm_compContinuousLinearMap_mfderiv ψ (by simp) (mextDerivₗ I k φ).val hy,
    mpullback_symm_mextDerivₗ ψ φ hy]
  -- `extDeriv` is the alternation of the derivative.
  exact ContinuousAlternatingMap.alternatizeUncurryFin_compContinuousLinearMap (𝕜 := ℝ) (E := E)
    (fderiv ℝ (F := E [⋀^Fin k]→L[ℝ] F) (mpullback 𝓘(ℝ, E) I ψ.symm φ.val) y) _

/-- In a chart in which `J` is a constant endomorphism `A₀`, `symbolInChart` carries `𝒥 φ` to
the derivation of `J (ψ.symm y)` applied to `symbolInChart` of `φ`. -/
theorem symbolInChart_realAlternatingDerivation_apply
    (J : SmoothAlmostComplexStructure I M) (ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞)
    {A₀ : E →L[ℝ] E}
    (hψ : ∀ p ∈ ψ.target, ∀ w, J.chartPushforward ψ.toOpenPartialHomeomorph p w = A₀ w)
    (φ : SmoothForm I M ℝ k) {y : E} (hy : y ∈ ψ.target) (v : TangentSpace I (ψ.symm y)) :
    symbolInChart ψ (J.toEndomorphism.realAlternatingDerivation φ).val y v =
      (symbolInChart ψ φ.val y v).fderivCompContinuousLinearMap (.id ℝ _)
        (J.toEndomorphism (ψ.symm y)) := by
  -- The step on `E`, for a map `T` that intertwines `A₀` and `J`.
  have key (T : TangentSpace I (ψ.symm y) →L[ℝ] E)
      (hT : A₀ ∘L T = T ∘L J.toEndomorphism (ψ.symm y)) (D D' : E →L[ℝ] E [⋀^Fin k]→L[ℝ] ℝ)
      (hD : ∀ u, D' u = (D u).fderivCompContinuousLinearMap (.id ℝ E) A₀) :
      (D' (T v)).compContinuousLinearMap T =
        ((D (T v)).compContinuousLinearMap T).fderivCompContinuousLinearMap (.id ℝ _)
          (J.toEndomorphism (ψ.symm y)) := by
    rw [hD, ContinuousAlternatingMap.compContinuousLinearMap_fderivCompContinuousLinearMap_id _ hT]
  rw [symbolInChart_apply, symbolInChart_apply]
  refine key _ ?_ _ _ (fderiv_mpullback_symm_realAlternatingDerivation_apply J ψ hψ φ hy)
  ext u
  set e := ψ.mfderivSymmEquiv (by simp) hy
  have h1 := (congrArg (mfderiv 𝓘(ℝ, E) I ψ.symm y) (hψ y hy (e.symm u))).symm.trans
    (J.mfderiv_symm_apply_chartPushforward_apply ψ hy (e.symm u))
  rw [← ψ.coe_mfderivSymmEquiv (by simp) hy] at h1
  have hT (w : TangentSpace I (ψ.symm y)) : mfderiv I 𝓘(ℝ, E) ψ (ψ.symm y) w = e.symm w :=
    (congrFun (ψ.coe_mfderivSymmEquiv_symm (by simp) hy) w).symm
  exact (congrArg A₀ (hT u)).trans (((e.symm_apply_apply _).symm.trans
    (congrArg e.symm (h1.trans (congrArg _ (e.apply_symm_apply u))))).trans (hT _).symm)

end Readings


/-! ### Extension by zero along a chart -/

section ExtendByZero

variable {n : WithTop ℕ∞} (ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E n)
  (a : E → E [⋀^Fin k]→L[ℝ] F)

open Classical in
/-- The extension by zero along a partial diffeomorphism `ψ` from `M` to `E` of a flat form `a`
on `E`: on the source of `ψ` it is the pullback of `a` along `ψ`, and outside it is zero. -/
def RoughForm.extendByZeroAlong : RoughForm I M F k :=
  ψ.source.piecewise (mpullback I 𝓘(ℝ, E) ψ a) 0

namespace RoughForm

open Classical in
theorem extendByZeroAlong_def :
    extendByZeroAlong ψ a = ψ.source.piecewise (mpullback I 𝓘(ℝ, E) ψ a) 0 :=
  (rfl)

variable {ψ} {x : M}

theorem extendByZeroAlong_apply_of_mem (hx : x ∈ ψ.source) :
    extendByZeroAlong ψ a x = mpullback I 𝓘(ℝ, E) ψ a x := by
  classical
  exact Set.piecewise_eq_of_mem _ _ _ hx

theorem extendByZeroAlong_apply_of_notMem (hx : x ∉ ψ.source) :
    extendByZeroAlong ψ a x = 0 := by
  classical
  exact Set.piecewise_eq_of_notMem _ _ _ hx

/-- The extension by zero of the zero flat form is zero. -/
@[simp]
theorem extendByZeroAlong_zero :
    extendByZeroAlong ψ (0 : E → E [⋀^Fin k]→L[ℝ] F) = (0 : RoughForm I M F k) := by
  classical
  rw [extendByZeroAlong_def]
  exact (congrArg (ψ.source.piecewise · (0 : RoughForm I M F k))
    (mpullback_zero (I := I) (I' := 𝓘(ℝ, E)) (F := F) (k := k) ψ)).trans
    (Set.piecewise_same ψ.source (0 : RoughForm I M F k))

/-- Extension by zero along `ψ` is additive. -/
@[simp]
theorem extendByZeroAlong_add (b : E → E [⋀^Fin k]→L[ℝ] F) :
    extendByZeroAlong ψ (a + b) =
      (extendByZeroAlong ψ a + extendByZeroAlong ψ b : RoughForm I M F k) := by
  classical
  rw [extendByZeroAlong_def, extendByZeroAlong_def, extendByZeroAlong_def,
    ← Set.piecewise_add, add_zero]
  exact congrArg (ψ.source.piecewise · (0 : RoughForm I M F k))
    (mpullback_add (I := I) (I' := 𝓘(ℝ, E)) ψ (a : RoughForm 𝓘(ℝ, E) E F k) b)

/-- Extension by zero along `ψ` commutes with multiplication by a real constant. -/
@[simp]
theorem extendByZeroAlong_smul (c : ℝ) :
    extendByZeroAlong ψ (c • a) = (c • extendByZeroAlong ψ a : RoughForm I M F k) := by
  classical
  rw [extendByZeroAlong_def, extendByZeroAlong_def, ← Set.piecewise_smul, smul_zero]
  exact congrArg (ψ.source.piecewise · (0 : RoughForm I M F k))
    (mpullback_smul (I := I) (I' := 𝓘(ℝ, E)) ψ c (a : RoughForm 𝓘(ℝ, E) E F k))

/-- Extension by zero along `ψ` commutes with negation. -/
@[simp]
theorem extendByZeroAlong_neg :
    extendByZeroAlong ψ (-a) = (-extendByZeroAlong ψ a : RoughForm I M F k) := by
  rw [← neg_one_smul ℝ a, extendByZeroAlong_smul, neg_one_smul]

/-- Extension by zero along `ψ` commutes with subtraction. -/
@[simp]
theorem extendByZeroAlong_sub (b : E → E [⋀^Fin k]→L[ℝ] F) :
    extendByZeroAlong ψ (a - b) =
      (extendByZeroAlong ψ a - extendByZeroAlong ψ b : RoughForm I M F k) := by
  rw [sub_eq_add_neg, extendByZeroAlong_add, extendByZeroAlong_neg, ← sub_eq_add_neg]

/-- The extension by zero of `a` along `ψ` vanishes outside the image under `ψ.symm` of the
support of `a`. -/
theorem extendByZeroAlong_apply_of_notMem_image
    (hx : x ∉ ψ.symm '' tsupport a) :
    extendByZeroAlong ψ a x = 0 := by
  by_cases hxs : x ∈ ψ.source
  · rw [extendByZeroAlong_apply_of_mem a hxs]
    refine mpullback_apply_eq_zero (image_eq_zero_of_notMem_tsupport fun h ↦ hx ?_)
    exact ⟨ψ x, h, ψ.left_inv hxs⟩
  · exact extendByZeroAlong_apply_of_notMem a hxs

/-- On a Hausdorff manifold, the extension by zero of a compactly supported flat form `a` whose
support lies in the target of `ψ` is supported in the image under `ψ.symm` of the support of `a`.
-/
theorem tsupport_extendByZeroAlong_subset [T2Space M]
    (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ ψ.target) :
    tsupport (α := E [⋀^Fin k]→L[ℝ] F) (extendByZeroAlong ψ a) ⊆
      ψ.symm '' tsupport a := by
  have hK : IsCompact (ψ.symm '' tsupport a) :=
    hc.image_of_continuousOn (ψ.contMDiffOn_invFun.continuousOn.mono hs)
  refine closure_minimal (fun x hx ↦ ?_) hK.isClosed
  by_contra h
  exact hx (extendByZeroAlong_apply_of_notMem_image a h)

/-- On a Hausdorff manifold, the extension by zero of a compactly supported flat form whose
support lies in the target of `ψ` is compactly supported. -/
theorem isCompact_tsupport_extendByZeroAlong [T2Space M]
    (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ ψ.target) :
    IsCompact (tsupport (α := E [⋀^Fin k]→L[ℝ] F) (extendByZeroAlong ψ a)) :=
  (hc.image_of_continuousOn (ψ.contMDiffOn_invFun.continuousOn.mono hs)).of_isClosed_subset
    (isClosed_tsupport _) (tsupport_extendByZeroAlong_subset a hc hs)

end RoughForm

/-- Read through `ψ`, the extension by zero of `a` along `ψ` is `a` on the target of `ψ`. -/
theorem mpullback_symm_extendByZeroAlong (hn : n ≠ 0) {y : E} (hy : y ∈ ψ.target) :
    (mpullback 𝓘(ℝ, E) I ψ.symm (RoughForm.extendByZeroAlong ψ a) y :
      E [⋀^Fin k]→L[ℝ] F) = a y := by
  have hx : ψ.symm y ∈ ψ.source := ψ.map_target hy
  have h : mpullback 𝓘(ℝ, E) I ψ.symm (RoughForm.extendByZeroAlong ψ a) y =
      mpullback 𝓘(ℝ, E) I ψ.symm (mpullback I 𝓘(ℝ, E) ψ (a : RoughForm 𝓘(ℝ, E) E F k)) y := by
    ext v
    simp only [mpullback_apply, RoughForm.extendByZeroAlong_apply_of_mem a hx]
  rw [h]
  exact ψ.mpullback_symm_mpullback_apply hn _ hy

/-- On a Hausdorff manifold, the extension by zero along a smooth chart `ψ` of a smooth flat form
with compact support in the target of `ψ` is smooth. -/
theorem IsSmoothForm.extendByZeroAlong [T2Space M] [IsManifold I ∞ M]
    {ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞} {a : E → E [⋀^Fin k]→L[ℝ] F}
    (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ ψ.target) :
    IsSmoothForm I ∞ (RoughForm.extendByZeroAlong ψ a) := by
  rw [isSmoothForm_def]
  intro x
  by_cases hx : x ∈ ψ.source
  · have ha' : IsSmoothForm 𝓘(ℝ, E) ∞ (a : RoughForm 𝓘(ℝ, E) E F k) :=
      isSmoothForm_modelSpace_iff.mpr ha
    refine ContMDiffAt.congr_of_eventuallyEq (((isSmoothForm_def _ _).mp ha' (ψ x)).mpullback_form
      (ψ.contMDiffOn.contMDiffAt (ψ.open_source.mem_nhds hx)) (by simp)) ?_
    filter_upwards [ψ.open_source.mem_nhds hx] with z hz
    rw [RoughForm.extendByZeroAlong_apply_of_mem a hz]
  · have hK : IsClosed (ψ.symm '' tsupport a) :=
      (hc.image_of_continuousOn (ψ.contMDiffOn_invFun.continuousOn.mono hs)).isClosed
    have hxK : x ∉ ψ.symm '' tsupport a := by
      rintro ⟨z, hz, rfl⟩
      exact hx (ψ.map_target (hs hz))
    refine ContMDiffAt.congr_of_eventuallyEq
      ((isSmoothForm_def _ _).mp (IsSmoothForm.zero (I := I) (M := M) (F := F) (k := k) ∞) x) ?_
    filter_upwards [hK.isOpen_compl.mem_nhds hxK] with z hz
    rw [RoughForm.extendByZeroAlong_apply_of_notMem_image a hz, Pi.zero_apply]

/-- The extension by zero along a smooth chart `ψ`, on a Hausdorff manifold, of a smooth flat form
`a` with compact support in the target of `ψ`, as a smooth form. -/
def SmoothForm.extendByZeroAlong [T2Space M] [IsManifold I ∞ M]
    (ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞) (a : E → E [⋀^Fin k]→L[ℝ] F)
    (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ ψ.target) : SmoothForm I M F k :=
  ⟨RoughForm.extendByZeroAlong ψ a, (IsSmoothForm.extendByZeroAlong ha hc hs).mem_smoothBundleForms⟩

@[simp]
theorem SmoothForm.coe_extendByZeroAlong [T2Space M] [IsManifold I ∞ M]
    (ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞) (a : E → E [⋀^Fin k]→L[ℝ] F)
    (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ ψ.target) :
    (SmoothForm.extendByZeroAlong ψ a ha hc hs).val = RoughForm.extendByZeroAlong ψ a :=
  (rfl)

section SmoothForm

variable [T2Space M] [IsManifold I ∞ M] {ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞}
  {a b : E → E [⋀^Fin k]→L[ℝ] F}

/-- The extension by zero along `ψ` of the zero flat form is the zero smooth form. -/
@[simp]
theorem SmoothForm.extendByZeroAlong_zero (h : ContDiff ℝ ∞ (0 : E → E [⋀^Fin k]→L[ℝ] F))
    (hc : HasCompactSupport (0 : E → E [⋀^Fin k]→L[ℝ] F))
    (hs : tsupport (0 : E → E [⋀^Fin k]→L[ℝ] F) ⊆ ψ.target) :
    SmoothForm.extendByZeroAlong ψ 0 h hc hs = 0 :=
  Subtype.ext RoughForm.extendByZeroAlong_zero

/-- Extension by zero along `ψ` of smooth forms is additive. -/
theorem SmoothForm.extendByZeroAlong_add (ha : ContDiff ℝ ∞ a) (hac : HasCompactSupport a)
    (has : tsupport a ⊆ ψ.target) (hb : ContDiff ℝ ∞ b) (hbc : HasCompactSupport b)
    (hbs : tsupport b ⊆ ψ.target) (hab : ContDiff ℝ ∞ (a + b))
    (habc : HasCompactSupport (a + b)) (habs : tsupport (a + b) ⊆ ψ.target) :
    SmoothForm.extendByZeroAlong ψ (a + b) hab habc habs =
      SmoothForm.extendByZeroAlong ψ a ha hac has + SmoothForm.extendByZeroAlong ψ b hb hbc hbs :=
  Subtype.ext (RoughForm.extendByZeroAlong_add a b)

/-- Extension by zero along `ψ` of smooth forms commutes with multiplication by a real constant. -/
theorem SmoothForm.extendByZeroAlong_smul (c : ℝ) (ha : ContDiff ℝ ∞ a)
    (hac : HasCompactSupport a) (has : tsupport a ⊆ ψ.target) (hca : ContDiff ℝ ∞ (c • a))
    (hcac : HasCompactSupport (c • a)) (hcas : tsupport (c • a) ⊆ ψ.target) :
    SmoothForm.extendByZeroAlong ψ (c • a) hca hcac hcas =
      c • SmoothForm.extendByZeroAlong ψ a ha hac has :=
  Subtype.ext (RoughForm.extendByZeroAlong_smul a c)

/-- Extension by zero along `ψ` of smooth forms commutes with negation. -/
theorem SmoothForm.extendByZeroAlong_neg (ha : ContDiff ℝ ∞ a) (hac : HasCompactSupport a)
    (has : tsupport a ⊆ ψ.target) (hna : ContDiff ℝ ∞ (-a)) (hnac : HasCompactSupport (-a))
    (hnas : tsupport (-a) ⊆ ψ.target) :
    SmoothForm.extendByZeroAlong ψ (-a) hna hnac hnas =
      -SmoothForm.extendByZeroAlong ψ a ha hac has :=
  Subtype.ext (RoughForm.extendByZeroAlong_neg a)

/-- Extension by zero along `ψ` of smooth forms commutes with subtraction. -/
theorem SmoothForm.extendByZeroAlong_sub (ha : ContDiff ℝ ∞ a) (hac : HasCompactSupport a)
    (has : tsupport a ⊆ ψ.target) (hb : ContDiff ℝ ∞ b) (hbc : HasCompactSupport b)
    (hbs : tsupport b ⊆ ψ.target) (hab : ContDiff ℝ ∞ (a - b))
    (habc : HasCompactSupport (a - b)) (habs : tsupport (a - b) ⊆ ψ.target) :
    SmoothForm.extendByZeroAlong ψ (a - b) hab habc habs =
      SmoothForm.extendByZeroAlong ψ a ha hac has - SmoothForm.extendByZeroAlong ψ b hb hbc hbs :=
  Subtype.ext (RoughForm.extendByZeroAlong_sub a b)

end SmoothForm

end ExtendByZero

/-! ### Localization of a smooth form to a chart -/

namespace SmoothForm

section Localize

variable [IsManifold I ∞ M]

/-- The **localization** of a smooth `k`-form `α` to a chart `ψ : M → E` with a cutoff
`χ : M → ℝ`: the flat form on `E` that sends a point `y` of `ψ.target` to
`χ (ψ.symm y) • (ψ.symm)^* α (y)`, the reading of `α` in `ψ` at `y` scaled by `χ (ψ.symm y)`,
and every other point to `0`. -/
def localize (ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞) (χ : M → ℝ) (α : SmoothForm I M F k) :
    E → E [⋀^Fin k]→L[ℝ] F :=
  ψ.target.indicator fun y ↦ χ (ψ.symm y) • TauCeti.mpullback 𝓘(ℝ, E) I ψ.symm α.val y

variable (ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞) (χ : M → ℝ) (α β : SmoothForm I M F k)

theorem localize_def :
    α.localize ψ χ =
      ψ.target.indicator fun y ↦ χ (ψ.symm y) • TauCeti.mpullback 𝓘(ℝ, E) I ψ.symm α.val y :=
  (rfl)

/-- On the target of the chart, the localization of `α` is the reading of `α` in the chart,
scaled by `χ ∘ ψ.symm`. -/
theorem localize_of_mem {y : E} (hy : y ∈ ψ.target) :
    α.localize ψ χ y = χ (ψ.symm y) • TauCeti.mpullback 𝓘(ℝ, E) I ψ.symm α.val y := by
  rw [localize_def]
  exact Set.indicator_of_mem hy _

/-- On the target of the chart, the localization of `α` evaluated on vectors `v` is `χ (ψ⁻¹ y)`
times `α` at `ψ⁻¹ y` evaluated on the images of `v` under the differential of `ψ.symm`. -/
theorem localize_apply_of_mem {y : E} (hy : y ∈ ψ.target) (v : Fin k → E) :
    α.localize ψ χ y v =
      χ (ψ.symm y) • α.val (ψ.symm y) (fun i ↦ mfderiv 𝓘(ℝ, E) I ψ.symm y (v i)) := by
  refine (congrArg (fun f : E [⋀^Fin k]→L[ℝ] F ↦ f v) (localize_of_mem _ _ _ hy)).trans ?_
  refine (ContinuousAlternatingMap.smul_apply (R' := ℝ)
    (TauCeti.mpullback (F := F) 𝓘(ℝ, E) I ψ.symm α.val y) _ v).trans ?_
  exact congrArg _ (TauCeti.mpullback_apply _ _ _ v)

/-- On the target of the chart, the localization of `α` at `y` is `χ (ψ⁻¹ y)` times `α` at
`ψ⁻¹ y` composed with the differential of `ψ.symm` at `y`, as a form on `E`. -/
theorem localize_of_mem_eq_smul_compContinuousLinearMap {y : E} (hy : y ∈ ψ.target) :
    α.localize ψ χ y = χ (ψ.symm y) • (show E [⋀^Fin k]→L[ℝ] F from
      (α.val (ψ.symm y)).compContinuousLinearMap (mfderiv 𝓘(ℝ, E) I ψ.symm y)) := by
  -- The `show` reads the composite, whose domain is `TangentSpace 𝓘(ℝ, E) y`, in
  -- `E [⋀^Fin k]→L[ℝ] F`, so that the smul and the norm are those of forms on `E`. The closing
  -- `rfl` unfolds `TangentSpace 𝓘(ℝ, E) y` to `E`, which no lemma rewrites.
  ext v
  rw [localize_apply_of_mem _ _ _ hy]
  rfl

/-- Off the target of the chart, the localization vanishes. -/
theorem localize_apply_of_notMem {y : E} (hy : y ∉ ψ.target) : α.localize ψ χ y = 0 := by
  rw [localize_def]
  exact Set.indicator_of_notMem hy _

/-- The localization of the zero form is zero. -/
@[simp]
theorem localize_zero : (0 : SmoothForm I M F k).localize ψ χ = 0 := by
  ext y v
  by_cases hy : y ∈ ψ.target
  · simp [localize_apply_of_mem _ _ _ hy]
  · simp [localize_apply_of_notMem _ _ _ hy]

/-- The localization vanishes off the image `ψ '' tsupport χ` of the support of the cutoff. -/
theorem localize_apply_eq_zero_of_notMem {y : E} (hy : y ∉ ψ '' tsupport χ) :
    α.localize ψ χ y = 0 := by
  by_cases hyt : y ∈ ψ.target
  · ext v
    rw [localize_apply_of_mem _ _ _ hyt, image_eq_zero_of_notMem_tsupport (f := χ), zero_smul,
      ContinuousAlternatingMap.coe_zero, Pi.zero_apply]
    exact fun h ↦ hy ⟨_, h, ψ.right_inv hyt⟩
  · exact localize_apply_of_notMem _ _ _ hyt

/-- The localization is additive in the form. -/
@[simp]
theorem localize_add : (α + β).localize ψ χ = α.localize ψ χ + β.localize ψ χ := by
  ext y v
  by_cases hy : y ∈ ψ.target
  · simp [localize_apply_of_mem _ _ _ hy, smul_add]
  · simp [localize_apply_of_notMem _ _ _ hy]

/-- The localization is homogeneous in the form. -/
@[simp]
theorem localize_smul (c : ℝ) : (c • α).localize ψ χ = c • α.localize ψ χ := by
  ext y v
  by_cases hy : y ∈ ψ.target
  · simp [localize_apply_of_mem _ _ _ hy, smul_comm c]
  · simp [localize_apply_of_notMem _ _ _ hy]

variable {χ}

/-- If the cutoff has compact support in the source of the chart, the localization is supported
in the image of that support under the chart. -/
theorem tsupport_localize_subset (hK : IsCompact (tsupport χ)) (hχ : tsupport χ ⊆ ψ.source) :
    tsupport (α.localize ψ χ) ⊆ ψ '' tsupport χ :=
  closure_minimal (Function.support_subset_iff'.2 fun _ hy ↦
    localize_apply_eq_zero_of_notMem _ _ _ hy)
    (hK.image_of_continuousOn (ψ.contMDiffOn.continuousOn.mono hχ)).isClosed

/-- If the cutoff has compact support in the source of the chart, so does the localization. -/
theorem hasCompactSupport_localize (hK : IsCompact (tsupport χ)) (hχ : tsupport χ ⊆ ψ.source) :
    HasCompactSupport (α.localize ψ χ) :=
  (hK.image_of_continuousOn (ψ.contMDiffOn.continuousOn.mono hχ)).of_isClosed_subset
    (isClosed_tsupport _) (α.tsupport_localize_subset ψ hK hχ)

/-- The localization of a smooth form with a continuous cutoff whose support is compact and lies
in the source of the chart is continuous. -/
theorem continuous_localize (hχc : Continuous χ) (hK : IsCompact (tsupport χ))
    (hχ : tsupport χ ⊆ ψ.source) : Continuous (α.localize ψ χ) := by
  have hon : ContinuousOn (α.localize ψ χ) ψ.target :=
    ((hχc.comp_continuousOn ψ.symm.contMDiffOn.continuousOn).smul
      (α.contDiffOn_mpullback ψ.open_target ψ.symm.contMDiffOn).continuousOn).congr
        fun y hy ↦ localize_of_mem _ _ _ hy
  exact hon.continuous_of_tsupport_subset ψ.open_target
    ((α.tsupport_localize_subset ψ hK hχ).trans (ψ.mapsTo.mono_left hχ).image_subset)

/-- The localization of a smooth form with a smooth cutoff whose support is compact and lies in
the source of the chart is smooth. -/
theorem contDiff_localize (hχc : ContMDiff I 𝓘(ℝ) ∞ χ) (hK : IsCompact (tsupport χ))
    (hχ : tsupport χ ⊆ ψ.source) : ContDiff ℝ ∞ (α.localize ψ χ) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y ∈ ψ.target
  · have hon :=
      (contMDiffOn_iff_contDiffOn.1 (hχc.comp_contMDiffOn ψ.symm.contMDiffOn)).smul
        (α.contDiffOn_mpullback ψ.open_target ψ.symm.contMDiffOn)
    refine (hon.contDiffAt (ψ.open_target.mem_nhds hy)).congr_of_eventuallyEq ?_
    filter_upwards [ψ.open_target.mem_nhds hy] with z hz
    exact localize_of_mem _ _ _ hz
  · have hK' : _root_.IsClosed (ψ '' tsupport χ) :=
      (hK.image_of_continuousOn (ψ.contMDiffOn.continuousOn.mono hχ)).isClosed
    have hyK : y ∉ ψ '' tsupport χ := fun h ↦ hy ((ψ.mapsTo.mono_left hχ).image_subset h)
    refine (contDiffAt_const (c := (0 : E [⋀^Fin k]→L[ℝ] F))).congr_of_eventuallyEq ?_
    filter_upwards [hK'.isOpen_compl.mem_nhds hyK] with z hz
    exact localize_apply_eq_zero_of_notMem _ _ _ hz

/-- Extending the localization of `α` by zero along the chart gives back `χ • α`, when the
support of the cutoff `χ` lies in the source of the chart. -/
theorem extendByZeroAlong_localize_apply (hχ : tsupport χ ⊆ ψ.source) (x : M) :
    RoughForm.extendByZeroAlong ψ (α.localize ψ χ) x = χ x • α.val x := by
  by_cases hx : x ∈ ψ.source
  · rw [RoughForm.extendByZeroAlong_apply_of_mem _ hx]
    ext v
    have h := congrArg (fun f ↦ f v) (ψ.mpullback_mpullback_symm_apply (by simp) α.val hx)
    simp only [TauCeti.mpullback_apply] at h
    refine (TauCeti.mpullback_apply (I := I) (I' := 𝓘(ℝ, E)) ψ
      (α.localize ψ χ : RoughForm 𝓘(ℝ, E) E F k) x v).trans ?_
    refine (localize_apply_of_mem _ _ _ (ψ.map_source hx) _).trans ?_
    rw [h]
    exact (congrArg (· • α.val x v) (congrArg χ (ψ.left_inv hx))).trans
      (ContinuousAlternatingMap.smul_apply (R' := ℝ) _ _ v).symm
  · rw [RoughForm.extendByZeroAlong_apply_of_notMem _ hx,
      image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hχ h)), zero_smul]

/-- A smooth form is the sum of the extensions by zero of its localizations to finitely many
charts, with cutoffs a smooth partition of unity subordinate to their sources. -/
theorem sum_extendByZeroAlong_localize [T2Space M] {ι : Type*} [Fintype ι]
    (ψ : ι → PartialDiffeomorph I 𝓘(ℝ, E) M E ∞) (ρ : SmoothPartitionOfUnity ι I M univ)
    (hρ : ρ.IsSubordinate fun i ↦ (ψ i).source) (hK : ∀ i, IsCompact (tsupport (ρ i))) :
    ∑ i, SmoothForm.extendByZeroAlong (ψ i) (α.localize (ψ i) (ρ i))
      (α.contDiff_localize (ψ i) (ρ i).contMDiff (hK i) (hρ i))
      (α.hasCompactSupport_localize (ψ i) (hK i) (hρ i))
      ((α.tsupport_localize_subset (ψ i) (hK i) (hρ i)).trans
        ((ψ i).mapsTo.mono_left (hρ i)).image_subset) = α := by
  refine Subtype.ext (funext fun x ↦ ?_)
  rw [Submodule.coe_sum, Finset.sum_apply]
  simp only [SmoothForm.coe_extendByZeroAlong]
  rw [Finset.sum_congr rfl fun i _ ↦ extendByZeroAlong_localize_apply (ψ i) α (hρ i) x,
    ← Finset.sum_smul, ← finsum_eq_sum_of_fintype, ρ.sum_eq_one (mem_univ x), one_smul]

end Localize

/-! ### Partial derivatives in a chart -/

/-- The reading `(ψ.symm)^* α` of a smooth form in a chart `ψ` is smooth at every point of the
target of the chart. -/
theorem contDiffAt_mpullback_symm [IsManifold I ∞ M] (α : SmoothForm I M F k)
    (ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞) {y : E} (hy : y ∈ ψ.target) :
    ContDiffAt ℝ (E := E) (F := E [⋀^Fin k]→L[ℝ] F) ∞
      (TauCeti.mpullback 𝓘(ℝ, E) I ψ.symm α.val) y :=
  (α.contDiffOn_mpullback ψ.open_target ψ.symm.contMDiffOn).contDiffAt
    (ψ.open_target.mem_nhds hy)

/-- The reading `(ψ.symm)^* α` of a smooth form in a chart `ψ` is differentiable at every point
of the target of the chart. -/
theorem differentiableAt_mpullback_symm [IsManifold I ∞ M] (α : SmoothForm I M F k)
    (ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞) {y : E} (hy : y ∈ ψ.target) :
    DifferentiableAt ℝ (E := E) (F := E [⋀^Fin k]→L[ℝ] F)
      (TauCeti.mpullback 𝓘(ℝ, E) I ψ.symm α.val) y :=
  (α.contDiffAt_mpullback_symm ψ hy).differentiableAt (by simp)

/-- The partial derivative `∂_v` of the reading `(ψ.symm)^* α` of a smooth form in a chart `ψ` is
smooth on the target of the chart. -/
theorem contDiffOn_fderiv_mpullback_symm_apply [IsManifold I ∞ M]
    (α : SmoothForm I M F k) (ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞) (v : E) :
    ContDiffOn ℝ ∞ (fun z ↦ fderiv ℝ (F := E [⋀^Fin k]→L[ℝ] F)
      (TauCeti.mpullback 𝓘(ℝ, E) I ψ.symm α.val) z v) ψ.target :=
  ((α.contDiffOn_mpullback ψ.open_target ψ.symm.contMDiffOn).fderiv_of_isOpen ψ.open_target
    (m := ∞) (by simp)).clm_apply contDiffOn_const

end SmoothForm

end TauCeti

end
