/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Symplectic.Basic
public import SymplecticGeometry.Geometry.Manifold.Instances.SymplecticGroup.Basic
public import SymplecticGeometry.Topology.VectorBundle.Core.TwoChart
public import TauCeti.Analysis.Matrix.EuclideanLin
public import TauCeti.Geometry.Manifold.Instances.SymplecticGroup
public import SymplecticGeometry.Topology.VectorBundle.Core.Basic
import SymplecticGeometry.Geometry.Manifold.VectorBundle.Core.TwoChart
import SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Matrix

/-!
# Symplectic vector bundles from a clutching map

Let `U₁` and `U₂` be open sets that cover a manifold `M`, and `T : M → Sp(2k)` a map into the
group `Matrix.symplecticGroup κ ℝ` of real symplectic matrices that is smooth on `U₁ ∩ U₂`. This
file glues the trivial bundles `U₁ × ℝ²ᵏ` and `U₂ × ℝ²ᵏ` along `T`: a vector `v` over `x` in the
chart of `U₂` is the vector `T x v` in the chart of `U₁`. Since the coordinate changes are
symplectic, the standard form `stdForm κ` of each chart is the same form on the fibre, so the
bundle is a symplectic vector bundle, and each chart gives a symplectic frame of it over its set.

The bundle is the two-chart core `twoChartCore` of `Topology/VectorBundle/Core/TwoChart.lean`,
for the action of the symplectic group on `StdSpace κ` by `toEuclideanCLM`. The coordinate change
from the chart `i` to the chart `j` (`true` for `U₁`, `false` for `U₂`) is the power
`T x ^ (j - i)` (`twoChartCocycle`), a symplectic matrix at every point, not only on `U₁ ∩ U₂`.
So the frames `symplecticClutchingFrame b` are defined as linear isomorphisms at every point, and
the relation between the two frames holds at every point, although only its values on `U₁ ∩ U₂`
carry information.

## Main definitions

* `SymplecticGeometry.Bundle.symplecticClutchingCore U₁ U₂ T`: the vector bundle core with fibre
  `StdSpace κ`, two charts over `U₁` and `U₂`, and coordinate change `T` from the second to the
  first. Its fibres are identified with `StdSpace κ` by `VectorBundleCore.fiberEquiv`.
* `SymplecticGeometry.Bundle.symplecticClutchingForm`: the two-form that is `stdForm κ` in every
  chart.
* `SymplecticGeometry.Bundle.symplecticClutchingFrame b`: the frame of the chart `b`, which is the
  inverse of the chart over its base set.

## Main results

* `SymplecticGeometry.Bundle.isContMDiff_symplecticClutchingCore`: the bundle is smooth.
* `SymplecticGeometry.Bundle.isNondegenerate_symplecticClutchingForm`: the form is nondegenerate.
* `SymplecticGeometry.Bundle.isSymplecticFrameOn_symplecticClutchingFrame`: the frame of the chart
  `b` is a symplectic frame for `stdForm κ` over the base set of that chart.
* `SymplecticGeometry.Bundle.symplecticClutchingFrame_false_apply`: the frame of `U₂` at `v` is the
  frame of `U₁` at `T x v`.

## Implementation notes

The form is smooth because, read in any chart, it is the constant `stdForm κ`
(`contMDiff_continuousAlternatingMap_bundle_of_inCoordinates_eq_const`); the smoothness of
`T` is used through `Matrix.SymplecticGroup.contMDiff_toEuclideanCLM`. As in
`Geometry/Manifold/Instances/SymplecticGroup/Basic.lean`, the smooth structure of the symplectic
group is that of Tau Ceti, for the topology `Matrix.linftyOpTopologicalSpace` on matrices.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.6
  (symplectic vector bundles and their transition maps) and §2.7 (bundles over a surface given by
  a clutching map).
-/

public section

noncomputable section

open Bundle Set Matrix
open scoped Manifold ContDiff Matrix.Norms.Operator

attribute [local instance] Matrix.linftyOpTopologicalSpace

namespace SymplecticGeometry

namespace Bundle

variable {EM HM M : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [TopologicalSpace HM]
  {IM : ModelWithCorners ℝ EM HM} [TopologicalSpace M] [ChartedSpace HM M]
  {κ : Type*} [Fintype κ] [DecidableEq κ]

/-! ### The bundle -/

section Core

variable (U₁ U₂ : Set M) (T : M → symplecticGroup κ ℝ) (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂)
  (hU : U₁ ∪ U₂ = univ)
  (hT : ContMDiffOn IM 𝓘(ℝ, TauCeti.Lie.SymplecticGroupModel κ ℝ) ∞ T (U₁ ∩ U₂))

/-- **The bundle clutched by `T`.** Over open sets `U₁` and `U₂` covering `M`, the vector bundle
core with fibre `StdSpace κ` and two charts, `true` over `U₁` and `false` over `U₂`, whose
coordinate change from the second chart to the first is `T x`, a symplectic matrix that depends
smoothly on `x ∈ U₁ ∩ U₂`. The preferred chart at `x` is the first one when `x ∈ U₁`. -/
abbrev symplecticClutchingCore : VectorBundleCore ℝ M (StdSpace κ) Bool :=
  twoChartCore U₁ U₂
    ((toEuclideanCLM (𝕜 := ℝ) (n := κ ⊕ κ) : Matrix (κ ⊕ κ) (κ ⊕ κ) ℝ →* _).comp
      (symplecticGroup κ ℝ).subtype) T hU₁ hU₂ hU
    ((Matrix.SymplecticGroup.contMDiff_toEuclideanCLM.comp_contMDiffOn hT).continuousOn)

/-- The coordinate change of the clutched bundle from the chart `i` to the chart `j` is the
matrix `T x ^ (j - i)`. -/
theorem coordChange_symplecticClutchingCore (i j : Bool) (x : M) :
    (symplecticClutchingCore U₁ U₂ T hU₁ hU₂ hU hT).coordChange i j x =
      toEuclideanCLM (𝕜 := ℝ) (↑(twoChartCocycle T i j x) : Matrix (κ ⊕ κ) (κ ⊕ κ) ℝ) :=
  coordChange_twoChartCore ..

/-- **The clutched bundle is smooth**: its coordinate changes are `Cⁿ` for every `n ≤ ∞`. -/
instance isContMDiff_symplecticClutchingCore (n : ℕ∞) :
    (symplecticClutchingCore U₁ U₂ T hU₁ hU₂ hU hT).IsContMDiff IM n :=
  isContMDiff_twoChartCore _ hU₁ hU₂ hU _
    ((Matrix.SymplecticGroup.contMDiff_toEuclideanCLM.comp_contMDiffOn hT).of_le
      (by exact_mod_cast le_top))

/-! ### The symplectic form -/

/-- **The symplectic form of the clutched bundle**: the standard form `stdForm κ` on every fibre,
read in any chart. It is smooth because the coordinate changes are symplectic. -/
def symplecticClutchingForm (n : ℕ∞) :
    ContMDiffTwoForm IM n (StdSpace κ) (symplecticClutchingCore U₁ U₂ T hU₁ hU₂ hU hT).Fiber where
  toFun x := (AlternatingMap.toContinuousAlternatingMap
      (stdForm κ).isAlt.toAlternatingMap).compContinuousLinearMap
    ((symplecticClutchingCore U₁ U₂ T hU₁ hU₂ hU hT).fiberEquiv x : _ →L[ℝ] StdSpace κ)
  contMDiff_toFun := contMDiff_continuousAlternatingMap_bundle_of_inCoordinates_eq_const
      (c := fun _ ↦ AlternatingMap.toContinuousAlternatingMap
        (stdForm κ).isAlt.toAlternatingMap) fun _ x hx _ ↦ by
    ext v
    simp only [ContinuousAlternatingMap.inCoordinates, Trivial.eq_trivialization M ℝ,
      Trivial.continuousLinearMapAt_trivialization,
      ContinuousLinearMap.compContinuousAlternatingMap_coe, Function.comp_apply,
      ContinuousAlternatingMap.compContinuousLinearMap_apply, ContinuousLinearMap.id_apply,
      AlternatingMap.coe_toContinuousAlternatingMap]
    rw [LinearMap.IsAlt.toAlternatingMap_apply (stdForm κ).isAlt,
      LinearMap.IsAlt.toAlternatingMap_apply (stdForm κ).isAlt]
    simp only [Function.comp_apply, ContinuousLinearEquiv.coe_coe]
    rw [Trivialization.symmL_apply _ hx, Trivialization.symmL_apply _ hx,
      VectorBundleCore.fiberEquiv_trivializationAt_symm _ hx,
      VectorBundleCore.fiberEquiv_trivializationAt_symm _ hx, coordChange_symplecticClutchingCore]
    exact mem_symplecticGroup_iff_forall_stdForm_toEuclideanCLM.1 (Subtype.prop _) (v 0) (v 1)

theorem symplecticClutchingForm_def (n : ℕ∞) (x : M) :
    symplecticClutchingForm (IM := IM) U₁ U₂ T hU₁ hU₂ hU hT n x =
      (AlternatingMap.toContinuousAlternatingMap
        (stdForm κ).isAlt.toAlternatingMap).compContinuousLinearMap
          ((symplecticClutchingCore U₁ U₂ T hU₁ hU₂ hU hT).fiberEquiv x : _ →L[ℝ] StdSpace κ) :=
  (rfl)

/-- The form of the clutched bundle takes the value `stdForm κ (v 0) (v 1)` on `v`, read in
`StdSpace κ`. -/
@[simp]
theorem symplecticClutchingForm_apply (n : ℕ∞) (x : M)
    (v : Fin 2 → (symplecticClutchingCore U₁ U₂ T hU₁ hU₂ hU hT).Fiber x) :
    symplecticClutchingForm (IM := IM) U₁ U₂ T hU₁ hU₂ hU hT n x v =
      stdForm κ ((symplecticClutchingCore U₁ U₂ T hU₁ hU₂ hU hT).fiberEquiv x (v 0))
        ((symplecticClutchingCore U₁ U₂ T hU₁ hU₂ hU hT).fiberEquiv x (v 1)) := by
  rw [symplecticClutchingForm_def, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    AlternatingMap.coe_toContinuousAlternatingMap,
    LinearMap.IsAlt.toAlternatingMap_apply (stdForm κ).isAlt]
  simp only [Function.comp_apply, ContinuousLinearEquiv.coe_coe]

/-- The bilinear form of the form of the clutched bundle is `stdForm κ` on every fibre. -/
theorem bilinFormAt_symplecticClutchingForm (n : ℕ∞) (x : M)
    (v w : (symplecticClutchingCore U₁ U₂ T hU₁ hU₂ hU hT).Fiber x) :
    (symplecticClutchingForm (IM := IM) U₁ U₂ T hU₁ hU₂ hU hT n).bilinFormAt x v w =
      stdForm κ ((symplecticClutchingCore U₁ U₂ T hU₁ hU₂ hU hT).fiberEquiv x v)
        ((symplecticClutchingCore U₁ U₂ T hU₁ hU₂ hU hT).fiberEquiv x w) := by
  simp

/-! ### The frames of the charts -/

/-- **The frame of the chart `b`** of the clutched bundle at `x`: the matrix `T x ^ (j - b)`,
where `j` is the preferred chart at `x`, followed by the identification of `StdSpace κ` with the
fibre. Over the base set of the chart it is the inverse of the chart
(`symplecticClutchingFrame_apply_of_mem`), and a symplectic frame
(`isSymplecticFrameOn_symplecticClutchingFrame`). -/
def symplecticClutchingFrame (b : Bool) (x : M) :
    StdSpace κ ≃L[ℝ] (symplecticClutchingCore U₁ U₂ T hU₁ hU₂ hU hT).Fiber x :=
  (toEuclideanCLE (↑(twoChartCocycle T b
      ((symplecticClutchingCore U₁ U₂ T hU₁ hU₂ hU hT).indexAt x) x) : Matrix (κ ⊕ κ) (κ ⊕ κ) ℝ)
    (SymplecticGroup.symplectic_det (Subtype.prop _)).ne_zero).trans
    ((symplecticClutchingCore U₁ U₂ T hU₁ hU₂ hU hT).fiberEquiv x).symm

theorem symplecticClutchingFrame_def (b : Bool) (x : M) :
    symplecticClutchingFrame U₁ U₂ T hU₁ hU₂ hU hT b x =
      (toEuclideanCLE (↑(twoChartCocycle T b
          ((symplecticClutchingCore U₁ U₂ T hU₁ hU₂ hU hT).indexAt x) x) :
            Matrix (κ ⊕ κ) (κ ⊕ κ) ℝ)
        (SymplecticGroup.symplectic_det (Subtype.prop _)).ne_zero).trans
        ((symplecticClutchingCore U₁ U₂ T hU₁ hU₂ hU hT).fiberEquiv x).symm :=
  (rfl)

/-- Read in `StdSpace κ`, the frame of the chart `b` at `x` is the matrix `T x ^ (j - b)`, where
`j` is the preferred chart at `x`. -/
@[simp]
theorem fiberEquiv_symplecticClutchingFrame (b : Bool) (x : M)
    (v : StdSpace κ) :
    (symplecticClutchingCore U₁ U₂ T hU₁ hU₂ hU hT).fiberEquiv x
        (symplecticClutchingFrame U₁ U₂ T hU₁ hU₂ hU hT b x v) =
      toEuclideanCLM (𝕜 := ℝ) (↑(twoChartCocycle T b
        ((symplecticClutchingCore U₁ U₂ T hU₁ hU₂ hU hT).indexAt x) x) :
          Matrix (κ ⊕ κ) (κ ⊕ κ) ℝ) v := by
  simp [symplecticClutchingFrame_def]

/-- Over the base set of the chart `b`, its frame is the inverse of the chart. -/
theorem symplecticClutchingFrame_apply_of_mem {b : Bool} {x : M}
    (hx : x ∈ (symplecticClutchingCore U₁ U₂ T hU₁ hU₂ hU hT).baseSet b) (v : StdSpace κ) :
    symplecticClutchingFrame U₁ U₂ T hU₁ hU₂ hU hT b x v =
      ((symplecticClutchingCore U₁ U₂ T hU₁ hU₂ hU hT).localTriv b).symm x v := by
  apply ((symplecticClutchingCore U₁ U₂ T hU₁ hU₂ hU hT).fiberEquiv x).injective
  rw [fiberEquiv_symplecticClutchingFrame,
    VectorBundleCore.fiberEquiv_localTriv_symm _ b (by rwa [← VectorBundleCore.baseSet_at]),
    coordChange_symplecticClutchingCore]

/-- **The two frames differ by `T`**: the frame of `U₂` at `v` is the frame of `U₁` at `T x v`. -/
theorem symplecticClutchingFrame_false_apply (x : M) (v : StdSpace κ) :
    symplecticClutchingFrame U₁ U₂ T hU₁ hU₂ hU hT false x v =
      symplecticClutchingFrame U₁ U₂ T hU₁ hU₂ hU hT true x
        (toEuclideanCLM (𝕜 := ℝ) (T x : Matrix (κ ⊕ κ) (κ ⊕ κ) ℝ) v) := by
  apply ((symplecticClutchingCore U₁ U₂ T hU₁ hU₂ hU hT).fiberEquiv x).injective
  rw [fiberEquiv_symplecticClutchingFrame,
    fiberEquiv_symplecticClutchingFrame,
    ← twoChartCocycle_false_true T x, ← mul_apply_eq_comp, ← map_mul,
    ← Submonoid.coe_mul, twoChartCocycle_mul]

/-- **The frames of the charts are symplectic**: the frame of the chart `b` is a symplectic frame
of the form of the clutched bundle for `stdForm κ`, over the base set of the chart, `U₁` for
`b = true` and `U₂` for `b = false`. -/
theorem isSymplecticFrameOn_symplecticClutchingFrame (n : ℕ∞) (b : Bool) :
    (symplecticClutchingForm (IM := IM) U₁ U₂ T hU₁ hU₂ hU hT n).IsSymplecticFrameOn (stdForm κ)
      ((symplecticClutchingCore U₁ U₂ T hU₁ hU₂ hU hT).baseSet b)
      (symplecticClutchingFrame U₁ U₂ T hU₁ hU₂ hU hT b) := by
  have : MemTrivializationAtlas ((symplecticClutchingCore U₁ U₂ T hU₁ hU₂ hU hT).localTriv b) :=
    ⟨⟨b, rfl⟩⟩
  refine ⟨?_, fun x _ v w ↦ ?_⟩
  · have h := ((symplecticClutchingCore U₁ U₂ T hU₁ hU₂ hU hT).localTriv b).contMDiffOn_symm
      (IB := IM) (n := n)
    rw [Trivialization.target_eq, ← VectorBundleCore.baseSet_at] at h
    refine h.congr fun p hp ↦ ?_
    rw [symplecticClutchingFrame_apply_of_mem _ _ _ _ _ _ _ hp.1]
    exact Trivialization.mk_symm _ (by rw [← VectorBundleCore.baseSet_at]; exact hp.1) p.2
  · rw [bilinFormAt_symplecticClutchingForm, fiberEquiv_symplecticClutchingFrame,
      fiberEquiv_symplecticClutchingFrame]
    exact mem_symplecticGroup_iff_forall_stdForm_toEuclideanCLM.1 (Subtype.prop _) v w

/-- **The form of the clutched bundle is nondegenerate.** -/
theorem isNondegenerate_symplecticClutchingForm (n : ℕ∞) :
    (symplecticClutchingForm (IM := IM) U₁ U₂ T hU₁ hU₂ hU hT n).IsNondegenerate :=
  ContMDiffTwoForm.isNondegenerate_def.2 fun x ↦
    (isSymplecticFrameOn_symplecticClutchingFrame U₁ U₂ T hU₁ hU₂ hU hT n _
      ).nondegenerate_bilinFormAt
      ((symplecticClutchingCore U₁ U₂ T hU₁ hU₂ hU hT).mem_baseSet_at x)

end Core

end Bundle

end SymplecticGeometry

end
