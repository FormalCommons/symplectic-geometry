/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.AlmostComplexType
public import TauCeti.Geometry.Manifold.DifferentialForm.ExtDeriv
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Chart
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.LocalDiffeomorph
import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.Chart

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
* `TauCeti.mpullback_symm_realAlternatingDerivation`: the reading of the real derivation
  `J.toEndomorphism.realAlternatingDerivation φ` of a smooth form along an almost complex
  structure `J` is the derivation of the reading of `φ` along the pushed-forward structure
  `J.chartPushforward`.
* `TauCeti.RoughForm.extendByZeroAlong ψ a`: the form on `M` that is the pullback along `ψ` of a
  flat form `a` on the source of `ψ`, and zero elsewhere; `TauCeti.mpullback_symm_extendByZeroAlong`
  recovers `a` on `ψ.target`. When `a` is smooth with compact support in `ψ.target`, the
  extension is smooth (`TauCeti.IsSmoothForm.extendByZeroAlong`), and bundled as
  `TauCeti.SmoothForm.extendByZeroAlong`.

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

end ExtendByZero

end TauCeti

end
