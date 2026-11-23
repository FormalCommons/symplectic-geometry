/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Symplectic.Basic
public import SymplecticGeometry.Geometry.Manifold.Instances.SymplecticGroup
import TauCeti.Analysis.Matrix.EuclideanLin
import SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Matrix
import TauCeti.Geometry.Manifold.Algebra.LieGroup

/-!
# Symplectic vector bundles from a clutching map

Let `U₁` and `U₂` be open sets that cover a manifold `M`, and `T : M → Sp(2k)` a map into the
group `Matrix.symplecticGroup κ ℝ` of real symplectic matrices that is smooth on `U₁ ∩ U₂`. This
file glues the trivial bundles `U₁ × ℝ²ᵏ` and `U₂ × ℝ²ᵏ` along `T`: a vector `v` over `x` in the
chart of `U₂` is the vector `T x v` in the chart of `U₁`. Since the coordinate changes are
symplectic, the standard form `stdForm κ` of each chart is the same form on the fibre, so the
bundle is a symplectic vector bundle, and each chart gives a symplectic frame of it over its set.

The coordinate change from the chart `i` to the chart `j` (`true` for `U₁`, `false` for `U₂`) is
the power `T x ^ (j - i)` (`symplecticClutchingMatrix`), a symplectic matrix at every point, not
only on `U₁ ∩ U₂`. So the frames `symplecticClutchingFrame b` are defined as linear isomorphisms
at every point, and the relation between the two frames holds at every point, although only its
values on `U₁ ∩ U₂` carry information.

## Main definitions

* `SymplecticGeometry.Bundle.symplecticClutchingMatrix T i j x`: the coordinate change from the
  chart `i` to the chart `j` at `x`, `T x ^ (j - i)`.
* `SymplecticGeometry.Bundle.symplecticClutchingCore U₁ U₂ T`: the vector bundle core with fibre
  `StdSpace κ`, two charts over `U₁` and `U₂`, and coordinate change `T` from the second to the
  first.
* `SymplecticGeometry.Bundle.symplecticClutchingFiberEquiv`: the identification of each fibre with
  `StdSpace κ`.
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

The construction follows that of the line bundle `clutchingLineBundle` in
`ChernNumber/Gluing.lean`, with two charts indexed by `Bool`. The form is smooth because, read in
any chart, it is the constant `stdForm κ`; the smoothness of `T` is used through
`Matrix.SymplecticGroup.contMDiff_toEuclideanCLM`. As in
`Geometry/Manifold/Instances/SymplecticGroup.lean`, the smooth structure of the symplectic group
is that of Tau Ceti, for the topology `Matrix.linftyOpTopologicalSpace` on matrices.

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

/-! ### The coordinate changes -/

section Matrix

variable {X : Type*} (T : X → symplecticGroup κ ℝ)

/-- The coordinate change of the clutched bundle from the chart `i` to the chart `j` at `x`:
`T x ^ (j - i)`, where the chart `true` lies over `U₁` and the chart `false` over `U₂`. -/
def symplecticClutchingMatrix (i j : Bool) (x : X) : symplecticGroup κ ℝ :=
  T x ^ ((j.toNat : ℤ) - i.toNat)

theorem symplecticClutchingMatrix_def (i j : Bool) (x : X) :
    symplecticClutchingMatrix T i j x = T x ^ ((j.toNat : ℤ) - i.toNat) :=
  (rfl)

@[simp]
theorem symplecticClutchingMatrix_self (i : Bool) (x : X) :
    symplecticClutchingMatrix T i i x = 1 := by
  simp [symplecticClutchingMatrix_def]

/-- From the chart of `U₂` to the chart of `U₁`, the coordinate change is `T`. -/
@[simp]
theorem symplecticClutchingMatrix_false_true (x : X) :
    symplecticClutchingMatrix T false true x = T x := by
  simp [symplecticClutchingMatrix_def]

/-- From the chart of `U₁` to the chart of `U₂`, the coordinate change is `T⁻¹`. -/
@[simp]
theorem symplecticClutchingMatrix_true_false (x : X) :
    symplecticClutchingMatrix T true false x = (T x)⁻¹ := by
  simp [symplecticClutchingMatrix_def]

/-- The coordinate changes compose: from `i` to `j`, then from `j` to `l`, is from `i` to `l`. -/
theorem symplecticClutchingMatrix_mul (i j l : Bool) (x : X) :
    symplecticClutchingMatrix T j l x * symplecticClutchingMatrix T i j x =
      symplecticClutchingMatrix T i l x := by
  rw [symplecticClutchingMatrix_def, symplecticClutchingMatrix_def,
    symplecticClutchingMatrix_def, ← _root_.zpow_add]
  congr 1
  ring

end Matrix

/-! ### The bundle -/

section Core

variable (U₁ U₂ : Set M) (T : M → symplecticGroup κ ℝ) (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂)
  (hU : U₁ ∪ U₂ = univ)
  (hT : ContMDiffOn IM 𝓘(ℝ, TauCeti.Lie.SymplecticGroupModel κ ℝ) ∞ T (U₁ ∩ U₂))

include hT in
/-- The coordinate changes `x ↦ T x ^ (j - i)` are smooth where both charts are defined. -/
private theorem contMDiffOn_toEuclideanCLM_symplecticClutchingMatrix (i j : Bool) :
    ContMDiffOn IM 𝓘(ℝ, StdSpace κ →L[ℝ] StdSpace κ) ∞
      (fun x ↦ toEuclideanCLM (𝕜 := ℝ)
        (symplecticClutchingMatrix T i j x : Matrix (κ ⊕ κ) (κ ⊕ κ) ℝ))
      ((bif i then U₁ else U₂) ∩ (bif j then U₁ else U₂)) := by
  have h (k : ℤ) := (Matrix.SymplecticGroup.contMDiff_toEuclideanCLM (κ := κ)).comp_contMDiffOn
    ((TauCeti.contMDiff_zpow k).comp_contMDiffOn hT)
  cases i <;> cases j
  · simpa using contMDiffOn_const
  · exact (h _).mono (inter_comm _ _).subset
  · exact h _
  · simpa using contMDiffOn_const

open scoped Classical in
/-- **The bundle clutched by `T`.** Over open sets `U₁` and `U₂` covering `M`, the vector bundle
core with fibre `StdSpace κ` and two charts, `true` over `U₁` and `false` over `U₂`, whose
coordinate change from the second chart to the first is `T x`, a symplectic matrix that depends
smoothly on `x ∈ U₁ ∩ U₂`. The preferred chart at `x` is the first one when `x ∈ U₁`. -/
def symplecticClutchingCore : VectorBundleCore ℝ M (StdSpace κ) Bool where
  baseSet b := bif b then U₁ else U₂
  isOpen_baseSet b := by cases b <;> assumption
  indexAt x := decide (x ∈ U₁)
  mem_baseSet_at x := by
    by_cases hx : x ∈ U₁
    · simp [hx]
    · simpa [hx] using (hU.symm ▸ mem_univ x : x ∈ U₁ ∪ U₂).resolve_left hx
  coordChange i j x := toEuclideanCLM (𝕜 := ℝ)
    (symplecticClutchingMatrix T i j x : Matrix (κ ⊕ κ) (κ ⊕ κ) ℝ)
  coordChange_self i x _ v := by simp
  continuousOn_coordChange i j :=
    (contMDiffOn_toEuclideanCLM_symplecticClutchingMatrix U₁ U₂ T hT i j).continuousOn
  coordChange_comp i j l x _ v := by
    rw [← mul_apply_eq_comp, ← map_mul, ← Submonoid.coe_mul,
      symplecticClutchingMatrix_mul]

/-- The first chart of the clutched bundle lies over `U₁`. -/
@[simp]
theorem baseSet_localTriv_symplecticClutchingCore_true :
    ((symplecticClutchingCore U₁ U₂ T hU₁ hU₂ hU hT).localTriv true).baseSet = U₁ :=
  (rfl)

/-- The second chart of the clutched bundle lies over `U₂`. -/
@[simp]
theorem baseSet_localTriv_symplecticClutchingCore_false :
    ((symplecticClutchingCore U₁ U₂ T hU₁ hU₂ hU hT).localTriv false).baseSet = U₂ :=
  (rfl)

open scoped Classical in
/-- The preferred chart of the clutched bundle at `x` is the first one exactly when `x ∈ U₁`. -/
@[simp]
theorem indexAt_symplecticClutchingCore (x : M) :
    (symplecticClutchingCore U₁ U₂ T hU₁ hU₂ hU hT).indexAt x = decide (x ∈ U₁) :=
  (rfl)

/-- The coordinate change of the clutched bundle from the chart `i` to the chart `j` is the
matrix `T x ^ (j - i)`. -/
@[simp]
theorem coordChange_symplecticClutchingCore (i j : Bool) (x : M) :
    (symplecticClutchingCore U₁ U₂ T hU₁ hU₂ hU hT).coordChange i j x =
      toEuclideanCLM (𝕜 := ℝ) (symplecticClutchingMatrix T i j x : Matrix (κ ⊕ κ) (κ ⊕ κ) ℝ) :=
  (rfl)

/-- **The clutched bundle is smooth**: its coordinate changes are `Cⁿ` for every `n ≤ ∞`. -/
instance isContMDiff_symplecticClutchingCore (n : ℕ∞) :
    (symplecticClutchingCore U₁ U₂ T hU₁ hU₂ hU hT).IsContMDiff IM n where
  contMDiffOn_coordChange i j :=
    (contMDiffOn_toEuclideanCLM_symplecticClutchingMatrix U₁ U₂ T hT i j).of_le
      (by exact_mod_cast le_top)

/-- The fibres of the clutched bundle are `StdSpace κ`: the identity, as a continuous linear
equivalence. -/
def symplecticClutchingFiberEquiv (x : M) :
    (symplecticClutchingCore U₁ U₂ T hU₁ hU₂ hU hT).Fiber x ≃L[ℝ] StdSpace κ :=
  ContinuousLinearEquiv.refl ℝ (StdSpace κ)

/-- The point `v` of the chart `i` is the point `T x ^ (j - i) v` of the fibre, where `j` is the
preferred chart at `x`. -/
theorem symplecticClutchingFiberEquiv_localTriv_symm (i : Bool) {x : M}
    (hx : x ∈ (symplecticClutchingCore U₁ U₂ T hU₁ hU₂ hU hT).baseSet i) (v : StdSpace κ) :
    symplecticClutchingFiberEquiv U₁ U₂ T hU₁ hU₂ hU hT x
        (((symplecticClutchingCore U₁ U₂ T hU₁ hU₂ hU hT).localTriv i).symm x v) =
      toEuclideanCLM (𝕜 := ℝ) (symplecticClutchingMatrix T i
        ((symplecticClutchingCore U₁ U₂ T hU₁ hU₂ hU hT).indexAt x) x :
          Matrix (κ ⊕ κ) (κ ⊕ κ) ℝ) v :=
  congrArg (symplecticClutchingFiberEquiv U₁ U₂ T hU₁ hU₂ hU hT x)
    ((symplecticClutchingCore U₁ U₂ T hU₁ hU₂ hU hT).localTriv_symm_apply i
      (by rwa [← VectorBundleCore.baseSet_at]) v)

/-! ### The symplectic form -/

/-- **The symplectic form of the clutched bundle**: the standard form `stdForm κ` on every fibre,
read in any chart. It is smooth because the coordinate changes are symplectic. -/
def symplecticClutchingForm (n : ℕ∞) :
    ContMDiffTwoForm IM n (StdSpace κ) (symplecticClutchingCore U₁ U₂ T hU₁ hU₂ hU hT).Fiber where
  toFun x := (AlternatingMap.toContinuousAlternatingMap
      (stdForm κ).isAlt.toAlternatingMap).compContinuousLinearMap
    (symplecticClutchingFiberEquiv U₁ U₂ T hU₁ hU₂ hU hT x : _ →L[ℝ] StdSpace κ)
  contMDiff_toFun x₀ := by
    rw [contMDiffAt_continuousAlternatingMap_bundle]
    refine ⟨contMDiffAt_id, (contMDiffAt_const (c := AlternatingMap.toContinuousAlternatingMap
      (stdForm κ).isAlt.toAlternatingMap)).congr_of_eventuallyEq ?_⟩
    filter_upwards [((symplecticClutchingCore U₁ U₂ T hU₁ hU₂ hU hT).isOpen_baseSet _).mem_nhds
      ((symplecticClutchingCore U₁ U₂ T hU₁ hU₂ hU hT).mem_baseSet_at x₀)] with x hx
    ext v
    have hx' : x ∈ (trivializationAt (StdSpace κ)
        (symplecticClutchingCore U₁ U₂ T hU₁ hU₂ hU hT).Fiber x₀).baseSet := by
      rwa [VectorBundleCore.trivializationAt, ← VectorBundleCore.localTrivAt_def,
        ← VectorBundleCore.baseSet_at]
    simp only [ContinuousAlternatingMap.inCoordinates, Trivial.eq_trivialization M ℝ,
      Trivial.continuousLinearMapAt_trivialization,
      ContinuousLinearMap.compContinuousAlternatingMap_coe, Function.comp_apply,
      ContinuousAlternatingMap.compContinuousLinearMap_apply, ContinuousLinearMap.id_apply,
      AlternatingMap.coe_toContinuousAlternatingMap]
    rw [LinearMap.IsAlt.toAlternatingMap_apply (stdForm κ).isAlt,
      LinearMap.IsAlt.toAlternatingMap_apply (stdForm κ).isAlt]
    simp only [Function.comp_apply, ContinuousLinearEquiv.coe_coe]
    rw [Trivialization.symmL_apply _ hx', Trivialization.symmL_apply _ hx']
    simp only [VectorBundleCore.trivializationAt, ← VectorBundleCore.localTrivAt_def,
      symplecticClutchingFiberEquiv_localTriv_symm U₁ U₂ T hU₁ hU₂ hU hT _ hx]
    rw [toEuclideanCLM_apply, toEuclideanCLM_apply]
    exact mem_symplecticGroup_iff_forall_stdForm.1 (Subtype.prop _) (v 0) (v 1)

theorem symplecticClutchingForm_def (n : ℕ∞) (x : M) :
    symplecticClutchingForm (IM := IM) U₁ U₂ T hU₁ hU₂ hU hT n x =
      (AlternatingMap.toContinuousAlternatingMap
        (stdForm κ).isAlt.toAlternatingMap).compContinuousLinearMap
          (symplecticClutchingFiberEquiv U₁ U₂ T hU₁ hU₂ hU hT x : _ →L[ℝ] StdSpace κ) :=
  (rfl)

/-- The form of the clutched bundle takes the value `stdForm κ (v 0) (v 1)` on `v`, read in
`StdSpace κ`. -/
@[simp]
theorem symplecticClutchingForm_apply (n : ℕ∞) (x : M)
    (v : Fin 2 → (symplecticClutchingCore U₁ U₂ T hU₁ hU₂ hU hT).Fiber x) :
    symplecticClutchingForm (IM := IM) U₁ U₂ T hU₁ hU₂ hU hT n x v =
      stdForm κ (symplecticClutchingFiberEquiv U₁ U₂ T hU₁ hU₂ hU hT x (v 0))
        (symplecticClutchingFiberEquiv U₁ U₂ T hU₁ hU₂ hU hT x (v 1)) := by
  rw [symplecticClutchingForm_def, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    AlternatingMap.coe_toContinuousAlternatingMap,
    LinearMap.IsAlt.toAlternatingMap_apply (stdForm κ).isAlt]
  simp only [Function.comp_apply, ContinuousLinearEquiv.coe_coe]

/-- The bilinear form of the form of the clutched bundle is `stdForm κ` on every fibre. -/
theorem bilinFormAt_symplecticClutchingForm (n : ℕ∞) (x : M)
    (v w : (symplecticClutchingCore U₁ U₂ T hU₁ hU₂ hU hT).Fiber x) :
    (symplecticClutchingForm (IM := IM) U₁ U₂ T hU₁ hU₂ hU hT n).bilinFormAt x v w =
      stdForm κ (symplecticClutchingFiberEquiv U₁ U₂ T hU₁ hU₂ hU hT x v)
        (symplecticClutchingFiberEquiv U₁ U₂ T hU₁ hU₂ hU hT x w) := by
  simp

/-! ### The frames of the charts -/

/-- **The frame of the chart `b`** of the clutched bundle at `x`: the matrix `T x ^ (j - b)`,
where `j` is the preferred chart at `x`, followed by the identification of `StdSpace κ` with the
fibre. Over the base set of the chart it is the inverse of the chart
(`symplecticClutchingFrame_apply_of_mem`), and a symplectic frame
(`isSymplecticFrameOn_symplecticClutchingFrame`). -/
def symplecticClutchingFrame (b : Bool) (x : M) :
    StdSpace κ ≃L[ℝ] (symplecticClutchingCore U₁ U₂ T hU₁ hU₂ hU hT).Fiber x :=
  (toEuclideanCLE (symplecticClutchingMatrix T b
      ((symplecticClutchingCore U₁ U₂ T hU₁ hU₂ hU hT).indexAt x) x : Matrix (κ ⊕ κ) (κ ⊕ κ) ℝ)
    (SymplecticGroup.symplectic_det (Subtype.prop _)).ne_zero).trans
    (symplecticClutchingFiberEquiv U₁ U₂ T hU₁ hU₂ hU hT x).symm

/-- Read in `StdSpace κ`, the frame of the chart `b` at `x` is the matrix `T x ^ (j - b)`, where
`j` is the preferred chart at `x`. -/
@[simp]
theorem symplecticClutchingFiberEquiv_symplecticClutchingFrame (b : Bool) (x : M)
    (v : StdSpace κ) :
    symplecticClutchingFiberEquiv U₁ U₂ T hU₁ hU₂ hU hT x
        (symplecticClutchingFrame U₁ U₂ T hU₁ hU₂ hU hT b x v) =
      toEuclideanCLM (𝕜 := ℝ) (symplecticClutchingMatrix T b
        ((symplecticClutchingCore U₁ U₂ T hU₁ hU₂ hU hT).indexAt x) x :
          Matrix (κ ⊕ κ) (κ ⊕ κ) ℝ) v := by
  simp [symplecticClutchingFrame]

/-- Over the base set of the chart `b`, its frame is the inverse of the chart. -/
theorem symplecticClutchingFrame_apply_of_mem {b : Bool} {x : M}
    (hx : x ∈ (symplecticClutchingCore U₁ U₂ T hU₁ hU₂ hU hT).baseSet b) (v : StdSpace κ) :
    symplecticClutchingFrame U₁ U₂ T hU₁ hU₂ hU hT b x v =
      ((symplecticClutchingCore U₁ U₂ T hU₁ hU₂ hU hT).localTriv b).symm x v := by
  apply (symplecticClutchingFiberEquiv U₁ U₂ T hU₁ hU₂ hU hT x).injective
  rw [symplecticClutchingFiberEquiv_symplecticClutchingFrame,
    symplecticClutchingFiberEquiv_localTriv_symm U₁ U₂ T hU₁ hU₂ hU hT b hx]

/-- **The two frames differ by `T`**: the frame of `U₂` at `v` is the frame of `U₁` at `T x v`. -/
theorem symplecticClutchingFrame_false_apply (x : M) (v : StdSpace κ) :
    symplecticClutchingFrame U₁ U₂ T hU₁ hU₂ hU hT false x v =
      symplecticClutchingFrame U₁ U₂ T hU₁ hU₂ hU hT true x
        (toEuclideanCLM (𝕜 := ℝ) (T x : Matrix (κ ⊕ κ) (κ ⊕ κ) ℝ) v) := by
  apply (symplecticClutchingFiberEquiv U₁ U₂ T hU₁ hU₂ hU hT x).injective
  rw [symplecticClutchingFiberEquiv_symplecticClutchingFrame,
    symplecticClutchingFiberEquiv_symplecticClutchingFrame,
    ← symplecticClutchingMatrix_false_true T x, ← mul_apply_eq_comp, ← map_mul,
    ← Submonoid.coe_mul, symplecticClutchingMatrix_mul]

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
  · rw [bilinFormAt_symplecticClutchingForm, symplecticClutchingFiberEquiv_symplecticClutchingFrame,
      symplecticClutchingFiberEquiv_symplecticClutchingFrame]
    rw [toEuclideanCLM_apply, toEuclideanCLM_apply]
    exact mem_symplecticGroup_iff_forall_stdForm.1 (Subtype.prop _) v w

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
