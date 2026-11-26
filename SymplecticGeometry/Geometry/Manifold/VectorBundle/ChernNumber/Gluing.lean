/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.VectorBundle.ChernNumber.Clutching
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Hermitian.Basic
public import SymplecticGeometry.Analysis.Complex.Circle
public import SymplecticGeometry.Topology.VectorBundle.Core.TwoChart
import Mathlib.Analysis.Complex.Isometry
import TauCeti.Geometry.Manifold.Algebra.LieGroup
import TauCeti.Topology.VectorBundle.RestrictScalars
import SymplecticGeometry.Analysis.Matrix.SymplecticGroup.Maslov
import SymplecticGeometry.Geometry.Manifold.ContMDiff.ExtendOverDisc
import SymplecticGeometry.Geometry.Manifold.VectorBundle.ChernNumber.DiscFrame
import SymplecticGeometry.Geometry.Manifold.VectorBundle.Core.TwoChart
import SymplecticGeometry.Geometry.Manifold.Instances.SymplecticGroup.Basic
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Integration.CoordinateDisc

/-!
# Bundles from clutching data, and isomorphisms from equal Maslov indices

Let `φ` be a coordinate disc of a surface `M` (`SymplecticGeometry.CoordinateDisc`) and `k` an
integer. This file builds the complex line bundle over `M` obtained by clutching two trivial line
bundles with the map `e^{ikθ}`, and proves that its first Chern number is `k`. Together with the
trivial bundles, these line bundles realize every value of the first Chern number.

The bundle `clutchingLineBundle φ k` is a Mathlib `VectorBundleCore` with fibre `ℂ` and two
charts: the open disc `φ '' {‖z‖ < 1}` (the chart `true`) and the complement of the closed disc
`φ '' {‖z‖ ≤ 1 / 2}` (the chart `false`). On the annulus where they overlap, the coordinate change
from the second chart to the first is multiplication by `e^{ikθ}`, where `e^{iθ}` is the angular
coordinate `φ.phase` of `φ` (`CoordinateDisc.phase`): `w / ‖w‖` for the coordinate
`w = φ.coord x`. The coordinate changes are complex linear, so the bundle is a complex vector
bundle, and they are smooth as soon as the coordinate of `φ` is
(`isContMDiff_clutchingLineBundle`), which holds for the coordinate discs of the charts of the
maximal atlas (`CoordinateDisc.contMDiffOn_coord_ofChart`). They have modulus one, so the real
part of the standard Hermitian product of `ℂ` is a smooth metric `clutchingMetric φ k n`,
invariant under multiplication by `Complex.I`. Its symplectic form is, as for every Hermitian
bundle, `(ContMDiffComplexStructure.ofComplexModule …).compatibleForm g` (`Hermitian/Basic.lean`).

Conversely, two symplectic bundles `(V₁, ω₁)` and `(V₂, ω₂)` of the same rank are isomorphic if
they have frames over a coordinate disc and over the complement of its open disc whose transition
loops on the boundary circle have the same Maslov index
(`exists_pushforward_eq_of_maslovIndex_eq`). Over a closed connected oriented surface, by the disc
clutching formula, this is the case when their first Chern numbers agree
(`exists_pushforward_eq_of_symplecticChernNumber_eq`).

## Main definitions

* `SymplecticGeometry.Bundle.clutchingLineBundle`: the clutching line bundle, the two-chart core
  `twoChartCore` for the action `Circle.lsmul` of the circle on `ℂ` and the map `e^{ikθ}`, with
  its complex structure (`VectorBundle ℂ ℂ`) and fibres of complex dimension one
  (`finrank_clutchingLineBundle`). Its fibres are identified with `ℂ` by
  `VectorBundleCore.fiberEquiv`.
* `SymplecticGeometry.Bundle.clutchingFrame`: the frames of the two charts, from the standard
  plane `StdSpace (Fin 1)`.
* `SymplecticGeometry.Bundle.clutchingMetric`: its Hermitian metric.

## Main results

* `SymplecticGeometry.Bundle.isContMDiff_clutchingLineBundle`: the bundle is `Cⁿ` when the
  coordinate of `φ` is.
* `SymplecticGeometry.Bundle.clutchingMetric_inner_I_smul`: the metric is Hermitian.
* `SymplecticGeometry.Bundle.bilinFormAt_clutchingFrame`: the frames of the charts are symplectic.
* `SymplecticGeometry.Bundle.symplecticChernNumber_clutchingLineBundle`: over a compact surface,
  the first Chern number of the bundle with the symplectic form of its metric is `k`.
* `SymplecticGeometry.Bundle.exists_pushforward_eq_of_maslovIndex_eq`: two symplectic bundles
  with frames over a coordinate disc and over its complement whose transition loops have the same
  Maslov index are isomorphic.
* `SymplecticGeometry.Bundle.exists_pushforward_eq_of_symplecticChernNumber_eq`: over a closed
  connected oriented surface, two symplectic bundles of the same rank with the same first Chern
  number are isomorphic.

## Proof

The disc clutching formula `symplecticChernNumber_eq_sum_maslovIndex_clutching`
(`ChernNumber/Clutching.lean`) is applied to one coordinate disc, `z ↦ φ (3 z / 4)`, whose closed
disc lies in the first chart and the complement of whose open disc lies in the second. The two
charts give frames there, read on the standard symplectic plane `StdSpace (Fin 1)` through
`(x, y) ↦ x + i y` (`StdSpace.equivComplex`). They are symplectic, since the coordinate changes
have modulus one, and on the boundary circle they differ by `ζ ↦ ζ ^ k`, the realification of a
loop of `1 × 1` unitary matrices (`circlePowLoop k`), whose Maslov index is `k`
(`maslovIndex_toBasedLoop_circlePowLoop`).

For `exists_pushforward_eq_of_maslovIndex_eq`, let `Tₖ = Φₖ⁻¹ ∘ Φₖ'` be the transitions of the
two bundles, defined near the boundary circle, on the image of an annulus `1 - ε < ‖z‖ < 1 + ε` of
the chart (`CoordinateDisc.exists_image_annulus_subset`). There `D = T₂ ∘ T₁⁻¹` is a smooth map into
`Matrix.symplecticGroup κ ℝ` (`Matrix.SymplecticGroup.exists_contMDiffOn_toEuclideanCLM_eq`),
and on the circle it is the loop `Ψ₂ Ψ₁⁻¹`, of Maslov index `μ(Ψ₂) - μ(Ψ₁) = 0` by the product
axiom (`TauCeti.GLSymplectic.maslovIndex_toBasedLoop_mul`). So it is null-homotopic
(`TauCeti.GLSymplectic.nullhomotopic_of_maslovIndex_toBasedLoop_eq_zero`), and agrees near the
circle with a smooth map `g` on the disc of radius `1 + ε`
(`ContMDiffOn.exists_contMDiffOn_ball_eq_of_nullhomotopic`). Over the image `W` of that disc, the
frame `Φ₂ ∘ g` of the second bundle has transition `T₁` to `Φ₂'` near the circle
(`ContMDiffTwoForm.IsSymplecticFrameOn.precomp_of_contMDiffOn`). The frames `Φ₁` and `Φ₂ ∘ g`
over `W`, and `Φ₁'` and `Φ₂'` away from a smaller closed disc, then glue to an isomorphism
(`ContMDiffTwoForm.exists_pushforward_eq_of_frameTransition_eq`). For
`exists_pushforward_eq_of_symplecticChernNumber_eq`, the frames come from
`ContMDiffTwoForm.IsNondegenerate.exists_isSymplecticFrameOn_disc_ofChart` and
`ContMDiffTwoForm.IsNondegenerate.exists_isSymplecticFrameOn_discComplement_ofChart`, their
transition loops from `ContMDiffTwoForm.IsSymplecticFrameOn.exists_frameTransition`, and the
disc clutching formula turns equal Chern numbers into equal Maslov indices.

## Implementation notes

The smoothness of `clutchingMetric` follows from Tau Ceti's
`TauCeti.contMDiff_hom_bundle_of_inCoordinates_eq_const`: read in the preferred chart at each
point, the metric is the constant inner product of `ℂ`. The complex vector bundle structure comes
from the complex linearity of the charts, by Tau Ceti's `VectorBundle.ofLinear`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.7,
  where vector bundles over a surface are described by trivializations over a disc and over its
  complement, and their first Chern number by the Maslov index of the transition loop
  (Theorem 2.7.1).
  The isomorphism property of the first Chern number in Theorem 2.7.1, that bundles of the same
  rank with the same number are isomorphic, is `exists_pushforward_eq_of_symplecticChernNumber_eq`.
-/

public section

noncomputable section

open Bundle Function Module Set TauCeti
open scoped Manifold ContDiff

namespace SymplecticGeometry

namespace Bundle

variable {M : Type} [TopologicalSpace M] [T2Space M] {EM : Type} [NormedAddCommGroup EM]
  [NormedSpace ℝ EM] [FiniteDimensional ℝ EM] [ChartedSpace EM M]
  {o : HomologicalOrientation M EM 2} (φ : CoordinateDisc o) (k : ℤ)

/-! ### The line bundle -/

/-- The overlap of the two charts of the clutching line bundle lies in the range of `φ`, off the
centre: there the coordinate of `φ` does not vanish. -/
private theorem inter_subset_coord_ne_zero :
    φ.openDisc ∩ (φ '' {z | ‖(z : ℂ)‖ ≤ 1 / 2})ᶜ ⊆ {x ∈ range φ | φ.coord x ≠ 0} := by
  rintro x ⟨h₁, h₂⟩
  obtain ⟨z, hz, rfl⟩ := φ.mem_openDisc_iff.1 h₁
  have hz' : 1 / 2 < ‖(z : ℂ)‖ := lt_of_not_ge fun h ↦ h₂ ⟨z, h, rfl⟩
  exact ⟨mem_range_self z, by rw [CoordinateDisc.coord_apply]; exact norm_pos_iff.1 (by linarith)⟩

/-- The two charts of the clutching line bundle cover `M`. -/
private theorem openDisc_union_compl_image :
    φ.openDisc ∪ (φ '' {z | ‖(z : ℂ)‖ ≤ 1 / 2})ᶜ = univ := by
  refine eq_univ_of_forall fun x ↦ or_iff_not_imp_left.2 fun hx ↦ ?_
  rintro ⟨z, hz, rfl⟩
  exact hx (φ.apply_mem_openDisc_iff.2 (by linarith [show ‖(z : ℂ)‖ ≤ 1 / 2 from hz]))

variable {φ} in
/-- On the overlap of the two charts the multiplication by `e^{ikθ}` is `Cⁿ` if the coordinate
of `φ` is. -/
private theorem contMDiffOn_lsmul_phase_zpow {n : WithTop ℕ∞}
    (hφ : ContMDiffOn 𝓘(ℝ, EM) 𝓘(ℝ, ℂ) n φ.coord (range φ)) :
    ContMDiffOn 𝓘(ℝ, EM) 𝓘(ℝ, ℂ →L[ℝ] ℂ) n (fun x ↦ Circle.lsmul (φ.phase x ^ k))
      (φ.openDisc ∩ (φ '' {z | ‖(z : ℂ)‖ ≤ 1 / 2})ᶜ) := by
  simp only [Circle.lsmul_def]
  have := finrank_real_complex_fact'
  refine (ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] ℂ →L[ℝ] ℂ).contMDiff.comp_contMDiffOn
    ((contMDiff_coe_sphere (E := ℂ) (n := 1)).comp_contMDiffOn ?_)
  exact ((TauCeti.contMDiff_zpow _).comp_contMDiffOn (φ.contMDiffOn_phase hφ)).mono
    (inter_subset_coord_ne_zero φ)

/-- **The clutching line bundle** of a coordinate disc `φ` and an integer `k`: the complex line
bundle glued from the trivial bundles with fibre `ℂ` over the open disc `φ '' {‖z‖ < 1}` (the
chart `true`) and over the complement of `φ '' {‖z‖ ≤ 1 / 2}` (the chart `false`), with
transition `v ↦ e^{ikθ} v` from the second to the first on the annulus where they overlap, `θ`
being the angle of the coordinate of `φ`. It is a real vector bundle core; its fibres are `ℂ`,
and the coordinate changes are complex linear. It is the two-chart core `twoChartCore` for the
action `Circle.lsmul` of the circle on `ℂ` and the map `x ↦ e^{ikθ}`. -/
abbrev clutchingLineBundle : VectorBundleCore ℝ M ℂ Bool :=
  twoChartCore φ.openDisc (φ '' {z | ‖(z : ℂ)‖ ≤ 1 / 2})ᶜ Circle.lsmul (fun x ↦ φ.phase x ^ k)
    φ.isOpen_openDisc (φ.isCompact_image_closedBall (by norm_num)).isClosed.isOpen_compl
    (by exact openDisc_union_compl_image φ)
    (by exact contMDiffOn_zero_iff.1 (contMDiffOn_lsmul_phase_zpow k
      (contMDiffOn_zero_iff.2 φ.continuousOn_coord)))

/-- The fibres of the clutching line bundle are complex vector spaces: they are `ℂ`. -/
instance (x : M) : Module ℂ ((clutchingLineBundle φ k).Fiber x) :=
  inferInstanceAs (Module ℂ ℂ)

instance (x : M) : IsScalarTower ℝ ℂ ((clutchingLineBundle φ k).Fiber x) :=
  inferInstanceAs (IsScalarTower ℝ ℂ ℂ)

instance (x : M) : ContinuousConstSMul ℂ ((clutchingLineBundle φ k).Fiber x) :=
  inferInstanceAs (ContinuousConstSMul ℂ ℂ)

/-- The fibres of the clutching line bundle are complex lines. -/
theorem finrank_clutchingLineBundle (x : M) :
    finrank ℂ ((clutchingLineBundle φ k).Fiber x) = 1 :=
  Module.finrank_self ℂ

/-- The charts of the clutching line bundle are complex linear: its coordinate changes are
multiplications by complex scalars. -/
instance (i : Bool) : ((clutchingLineBundle φ k).localTriv i).IsLinear ℂ where
  linear x _ :=
    ⟨fun v w ↦ map_add ((clutchingLineBundle φ k).coordChange _ i x) v w,
      fun c v ↦ by
        simp only [VectorBundleCore.localTriv_apply, coordChange_twoChartCore]
        exact (Circle.lsmul_apply _ _).trans ((mul_left_comm _ c (v : ℂ)).trans
          (congrArg (c * ·) (Circle.lsmul_apply _ _).symm))⟩

/-- The clutching line bundle is a complex vector bundle. -/
instance : VectorBundle ℂ ℂ (clutchingLineBundle φ k).Fiber :=
  VectorBundle.ofLinear ℝ ℂ ℂ _ fun _ ⟨i, h⟩ ↦
    h ▸ inferInstanceAs (((clutchingLineBundle φ k).localTriv i).IsLinear ℂ)

variable {φ} in
/-- **Smoothness of the clutching line bundle.** If the coordinate of `φ` is `Cⁿ` on the range of
`φ`, for instance for the coordinate disc `CoordinateDisc.ofChart` of a chart of the maximal
atlas (`CoordinateDisc.contMDiffOn_coord_ofChart`), then the coordinate changes of the clutching
line bundle are `Cⁿ`. -/
theorem isContMDiff_clutchingLineBundle {n : WithTop ℕ∞}
    (hφ : ContMDiffOn 𝓘(ℝ, EM) 𝓘(ℝ, ℂ) n φ.coord (range φ)) :
    (clutchingLineBundle φ k).IsContMDiff 𝓘(ℝ, EM) n :=
  isContMDiff_twoChartCore _ _ _ _ _ (contMDiffOn_lsmul_phase_zpow k hφ)

/-! ### The Hermitian metric and the symplectic form -/

/-- The identification `VectorBundleCore.fiberEquiv` of the fibres of the clutching line bundle
with `ℂ` is complex linear. -/
@[simp]
theorem fiberEquiv_clutchingLineBundle_smul (x : M) (c : ℂ)
    (v : (clutchingLineBundle φ k).Fiber x) :
    (clutchingLineBundle φ k).fiberEquiv x (c • v) =
      c * (clutchingLineBundle φ k).fiberEquiv x v := by
  simp only [VectorBundleCore.fiberEquiv_def]
  -- The action of `ℂ` on the fibre is, by the instance above, multiplication in `ℂ`.
  rfl

/-- **The Hermitian metric of the clutching line bundle**: on every fibre `ℂ`, the real part
`⟪v, w⟫_ℝ = Re (conj v * w)` of the standard Hermitian product. The coordinate changes are
multiplications by complex numbers of modulus one, so it is constant in every chart, hence
smooth. -/
def clutchingMetric (n : WithTop ℕ∞) :
    ContMDiffRiemannianMetric 𝓘(ℝ, EM) n ℂ (clutchingLineBundle φ k).Fiber where
  inner x :=
    (ContinuousLinearMap.precomp ℝ ((clutchingLineBundle φ k).fiberEquiv x : _ →L[ℝ] ℂ)).comp
      ((innerSL ℝ).comp ((clutchingLineBundle φ k).fiberEquiv x : _ →L[ℝ] ℂ))
  symm _ v w := by
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.precomp_apply,
      innerSL_apply_apply, ContinuousLinearEquiv.coe_coe]
    exact real_inner_comm _ _
  pos _ v hv := by
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.precomp_apply,
      innerSL_apply_apply, ContinuousLinearEquiv.coe_coe]
    exact real_inner_self_pos.2 (by simpa using hv)
  isVonNBounded x := by
    have h := ((innerSL ℝ : ℂ →L[ℝ] ℂ →L[ℝ] ℝ).isVonNBounded_setOf_lt_one_of_pos fun v hv ↦ by
      rw [innerSL_apply_apply]
      exact real_inner_self_pos.2 hv).image
        (((clutchingLineBundle φ k).fiberEquiv x).symm : ℂ →L[ℝ] (clutchingLineBundle φ k).Fiber x)
    rw [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.image_symm_eq_preimage,
      Set.preimage_ofPred_eq] at h
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.precomp_apply,
      innerSL_apply_apply, ContinuousLinearEquiv.coe_coe] at h ⊢
    exact h
  contMDiff := contMDiff_hom_bundle_of_inCoordinates_eq_const (c := fun _ ↦ innerSL ℝ)
    fun a x hx _ ↦ by
      ext v w
      rw [inCoordinates_apply_eq₂ (E₃ := Trivial M ℝ) hx hx
        (by simp [Trivial.eq_trivialization M ℝ])]
      simp only [Trivial.eq_trivialization M ℝ, Trivial.linearMapAt_trivialization,
        LinearMap.id_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.precomp_apply,
        ContinuousLinearEquiv.coe_coe, VectorBundleCore.fiberEquiv_trivializationAt_symm _ hx,
        coordChange_twoChartCore, Circle.lsmul_apply,
        innerSL_apply_apply]
      rw [← rotation_apply, ← rotation_apply, LinearIsometryEquiv.inner_map_map]
      exact (innerSL_apply_apply ℝ v w).symm

/-- The metric `clutchingMetric` is the real inner product of `ℂ` on every fibre. -/
@[simp]
theorem clutchingMetric_inner (n : WithTop ℕ∞) (x : M)
    (v w : (clutchingLineBundle φ k).Fiber x) :
    (clutchingMetric φ k n).inner x v w =
      inner ℝ ((clutchingLineBundle φ k).fiberEquiv x v)
        ((clutchingLineBundle φ k).fiberEquiv x w) := by
  simp only [clutchingMetric, ContinuousLinearMap.comp_apply, ContinuousLinearMap.precomp_apply,
    innerSL_apply_apply, ContinuousLinearEquiv.coe_coe]

/-- Multiplication by `Complex.I` preserves the metric `clutchingMetric`: it is a Hermitian
metric. -/
theorem clutchingMetric_inner_I_smul (n : WithTop ℕ∞) (x : M)
    (v w : (clutchingLineBundle φ k).Fiber x) :
    (clutchingMetric φ k n).inner x (Complex.I • v) (Complex.I • w) =
      (clutchingMetric φ k n).inner x v w := by
  rw [clutchingMetric_inner, clutchingMetric_inner, fiberEquiv_clutchingLineBundle_smul,
    fiberEquiv_clutchingLineBundle_smul]
  simp [Complex.inner]

/-! ### The first Chern number -/

open CoordinateDisc in
/-- The coordinate disc `z ↦ φ (3 z / 4)`: its closed disc lies in the inner chart of the
clutching line bundle, and the complement of its open disc in the outer chart. -/
private def clutchingDisc : CoordinateDisc o :=
  φ.comp (affineBall 0 (r := 3 / 4) (add_mul_mem_ball (by norm_num) (by norm_num)))
    (isOpenEmbedding_affineBall _ _ (by norm_num))
    (comap_affineBall_complexHomologicalOrientation _ _ (by norm_num))

private theorem clutchingDisc_apply (z : CoordinateDisc.ball) :
    clutchingDisc φ z = φ (CoordinateDisc.affineBall 0 (r := 3 / 4)
      (CoordinateDisc.add_mul_mem_ball (by norm_num) (by norm_num)) z) :=
  φ.comp_apply _ _ _ z

private theorem disc_clutchingDisc_subset :
    (clutchingDisc φ).disc ⊆ (clutchingLineBundle φ k).baseSet true := by
  intro x hx
  obtain ⟨z, hz, rfl⟩ := (clutchingDisc φ).mem_disc_iff.1 hx
  rw [baseSet_twoChartCore_true, clutchingDisc_apply]
  refine φ.apply_mem_openDisc_iff.2 ?_
  rw [CoordinateDisc.coe_affineBall_apply, zero_add, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (by norm_num)]
  linarith

private theorem discComplement_clutchingDisc_subset :
    discComplement (fun _ : Unit ↦ clutchingDisc φ) ⊆
      (clutchingLineBundle φ k).baseSet false := by
  rw [baseSet_twoChartCore_false]
  rintro x hx ⟨w, hw, rfl⟩
  have hw' : ‖(w : ℂ)‖ ≤ 1 / 2 := hw
  have hb : (4 / 3 : ℂ) * w ∈ (CoordinateDisc.ball : Set ℂ) := by
    rw [SetLike.mem_coe, CoordinateDisc.mem_ball_iff, norm_mul]
    norm_num
    linarith
  refine (mem_discComplement_iff _).1 hx () ((clutchingDisc φ).mem_openDisc_iff.2
    ⟨⟨(4 / 3 : ℂ) * w, hb⟩, ?_, ?_⟩)
  · rw [norm_mul]
    norm_num
    linarith
  · rw [clutchingDisc_apply]
    congr 1
    ext
    rw [CoordinateDisc.coe_affineBall_apply, zero_add, ← mul_assoc]
    norm_num

private theorem phase_boundaryCircle_clutchingDisc (ζ : Circle) :
    φ.phase ((clutchingDisc φ).boundaryCircle ζ) = ζ := by
  rw [CoordinateDisc.boundaryCircle_apply, clutchingDisc_apply]
  exact φ.phase_apply_of_coe_eq_mul (r := 3 / 4) (by norm_num)
    (by rw [CoordinateDisc.coe_affineBall_apply, zero_add])

/-! ### The frames of the charts -/

open StdSpace

/-- The frame of the chart `i` of the clutching line bundle at a point `x` of its base set:
the standard plane `StdSpace (Fin 1)`, read as `ℂ` through `(x, y) ↦ x + i y`, followed by the
inverse of the chart at `x`. -/
def clutchingFrame (i : Bool) (x : M) (hx : x ∈ (clutchingLineBundle φ k).baseSet i) :
    StdSpace (Fin 1) ≃L[ℝ] (clutchingLineBundle φ k).Fiber x :=
  (equivComplex (Fin 1)).toContinuousLinearEquiv.trans
    (((clutchingLineBundle φ k).localTriv i).continuousLinearEquivAt ℝ x hx).symm

theorem clutchingFrame_apply (i : Bool) {x : M} (hx : x ∈ (clutchingLineBundle φ k).baseSet i)
    (v : StdSpace (Fin 1)) :
    clutchingFrame φ k i x hx v =
      ((clutchingLineBundle φ k).localTriv i).symm x (equivComplex (Fin 1) v) :=
  congrFun (((clutchingLineBundle φ k).localTriv i).continuousLinearEquivAt_symm_apply ℝ x hx) _

/-- Read in `ℂ`, the frame of the chart `i` at `x` is `v ↦ e^{ik(j - i)θ} v`, where `j` is the
chart that the core assigns to `x`. -/
theorem fiberEquiv_clutchingFrame (i : Bool) {x : M}
    (hx : x ∈ (clutchingLineBundle φ k).baseSet i) (v : StdSpace (Fin 1)) :
    (clutchingLineBundle φ k).fiberEquiv x (clutchingFrame φ k i x hx v) =
      (↑(twoChartCocycle (fun x ↦ φ.phase x ^ k) i ((clutchingLineBundle φ k).indexAt x) x) : ℂ) *
        equivComplex (Fin 1) v := by
  rw [clutchingFrame_apply, VectorBundleCore.fiberEquiv_localTriv_symm _ i hx,
    coordChange_twoChartCore, Circle.lsmul_apply]

/-- The frames of the charts are symplectic for the form of the Hermitian metric
`clutchingMetric φ k n`: they carry the standard form of the plane to it. -/
theorem bilinFormAt_clutchingFrame (n : ℕ∞) (i : Bool) {x : M}
    (hx : x ∈ (clutchingLineBundle φ k).baseSet i) (v w : StdSpace (Fin 1)) :
    ((ContMDiffComplexStructure.ofComplexModule 𝓘(ℝ, EM) n ℂ
        (clutchingLineBundle φ k).Fiber).compatibleForm (clutchingMetric φ k n)).bilinFormAt x
        (clutchingFrame φ k i x hx v) (clutchingFrame φ k i x hx w) =
      stdForm (Fin 1) v w := by
  rw [ContMDiffTwoForm.bilinFormAt_apply,
    ContMDiffComplexStructure.compatibleForm_ofComplexModule_apply _
      (clutchingMetric_inner_I_smul φ k n), clutchingMetric_inner,
    fiberEquiv_clutchingLineBundle_smul,
    fiberEquiv_clutchingFrame, fiberEquiv_clutchingFrame,
    stdForm_apply_eq_inner_equivComplex, mul_left_comm, ← rotation_apply, ← rotation_apply,
    LinearIsometryEquiv.inner_map_map]

/-- The frames of the chart `i` over a subset `S` of its base set form a continuous map
`S × StdSpace (Fin 1) → TotalSpace`. -/
theorem continuous_clutchingFrame (i : Bool) {S : Set M}
    (hS : S ⊆ (clutchingLineBundle φ k).baseSet i) :
    Continuous fun q : S × StdSpace (Fin 1) ↦
      TotalSpace.mk' ℂ (q.1 : M) (clutchingFrame φ k i q.1 (hS q.1.property) q.2) := by
  refine (((clutchingLineBundle φ k).localTriv i).continuousOn_symm.comp_continuous
    ((continuous_subtypeVal.comp continuous_fst).prodMk
      ((equivComplex (Fin 1)).continuous.comp continuous_snd))
    fun q ↦ ⟨hS q.1.property, trivial⟩).congr fun q ↦ ?_
  simp only [Function.comp_apply, clutchingFrame_apply]

/-! ### The first Chern number -/

variable [CompactSpace M] [IsManifold 𝓘(ℝ, EM) ((⊤ : ℕ∞) : WithTop ℕ∞) M]

open TauCeti.GLSymplectic in
variable {φ} in
/-- **The first Chern number of the clutching line bundle.** Let `φ` be a coordinate disc of a
compact surface `M` with a homological orientation `o`, whose coordinate is `Cⁿ` on its range,
and `k` an integer. With the symplectic form `ω = (ofComplexModule …).compatibleForm g` of its
Hermitian metric `g = clutchingMetric φ k n`, the clutching line bundle has first Chern number
`k`. -/
theorem symplecticChernNumber_clutchingLineBundle (hn : finrank ℝ EM = 2) {n : ℕ∞}
    (hφ : ContMDiffOn 𝓘(ℝ, EM) 𝓘(ℝ, ℂ) n φ.coord (range φ))
    (G : Type*) [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
    [Fact (finrank ℝ ℂ = 2 * finrank ℂ G)] :
    symplecticChernNumber o hn G
      ((ContMDiffComplexStructure.ofComplexModule 𝓘(ℝ, EM) n ℂ
        (clutchingLineBundle φ k).Fiber).compatibleForm (clutchingMetric φ k n)) = k := by
  have := isContMDiff_clutchingLineBundle k hφ
  rw [symplecticChernNumber_eq_sum_maslovIndex_clutching (φ := fun _ : Unit ↦ clutchingDisc φ)
    (Subsingleton.pairwise)
    (Φ := fun _ x ↦ clutchingFrame φ k true x (disc_clutchingDisc_subset φ k x.property))
    (Φout := fun x ↦ clutchingFrame φ k false x
      (discComplement_clutchingDisc_subset φ k x.property))
    (fun _ ↦ continuous_clutchingFrame φ k true (disc_clutchingDisc_subset φ k))
    (continuous_clutchingFrame φ k false (discComplement_clutchingDisc_subset φ k)) G hn
    (fun _ _ ↦ bilinFormAt_clutchingFrame φ k n true _)
    (fun _ ↦ bilinFormAt_clutchingFrame φ k n false _) (fun _ ↦ circlePowLoop k) ?_,
    Fintype.sum_unique, maslovIndex_toBasedLoop_circlePowLoop]
  -- On the boundary circle the frames differ by `ζ ↦ ζ ^ k`.
  intro _ ζ v
  apply ((clutchingLineBundle φ k).fiberEquiv _).injective
  rw [fiberEquiv_clutchingFrame, fiberEquiv_clutchingFrame,
    coe_circlePowLoop_apply, equivComplex_toEuclideanLin_realify_diagonal,
    ← twoChartCocycle_mul _ false true, twoChartCocycle_false_true,
    phase_boundaryCircle_clutchingDisc, Circle.coe_mul, Circle.coe_zpow]
  ring


/-! ### Isomorphisms from equal Maslov indices -/

section Iso

open Matrix TauCeti.GLSymplectic StdSpace ContMDiffTwoForm
open scoped ContDiff Matrix.Norms.Operator

variable {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) M] [T2Space M]
  {o : Manifold.Orientation (𝓡 2) M (Fin 2)}
  {e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))} {c : EuclideanSpace ℝ (Fin 2)} {r : ℝ}

variable {κ : Type*} [Fintype κ] [DecidableEq κ]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
  {V₁ : M → Type*} [∀ x, AddCommGroup (V₁ x)] [∀ x, Module ℝ (V₁ x)]
  [∀ x, TopologicalSpace (V₁ x)] [∀ x, IsTopologicalAddGroup (V₁ x)]
  [∀ x, ContinuousSMul ℝ (V₁ x)] [TopologicalSpace (TotalSpace F₁ V₁)]
  [FiberBundle F₁ V₁] [VectorBundle ℝ F₁ V₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  {V₂ : M → Type*} [∀ x, AddCommGroup (V₂ x)] [∀ x, Module ℝ (V₂ x)]
  [∀ x, TopologicalSpace (V₂ x)] [∀ x, IsTopologicalAddGroup (V₂ x)]
  [∀ x, ContinuousSMul ℝ (V₂ x)] [TopologicalSpace (TotalSpace F₂ V₂)]
  [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂]
  {ω₁ : ContMDiffTwoForm (𝓡 2) ⊤ F₁ V₁} {ω₂ : ContMDiffTwoForm (𝓡 2) ⊤ F₂ V₂}

omit [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) M] [T2Space M] [FiniteDimensional ℝ F₁]
  [∀ x, IsTopologicalAddGroup (V₁ x)] [∀ x, ContinuousSMul ℝ (V₁ x)]
  [∀ x, IsTopologicalAddGroup (V₂ x)] [∀ x, ContinuousSMul ℝ (V₂ x)] in
/-- At a point where the frames of the two bundles differ by the matrices `A₁` and `A₂`,
`Φₖ' = Φₖ ∘ Aₖ`, the change of frame `T₂ ∘ T₁⁻¹`, for the transitions `Tₖ = Φₖ⁻¹ ∘ Φₖ'`, is the
matrix `A₂ A₁⁻¹`. -/
private theorem frameTransition_trans_frameTransition_eq {x : M}
    {Φ₁ Φ₁' : ∀ x, StdSpace κ ≃L[ℝ] V₁ x} {Φ₂ Φ₂' : ∀ x, StdSpace κ ≃L[ℝ] V₂ x}
    {A₁ A₂ : GL (κ ⊕ κ) ℝ} (h₁ : ∀ v, Φ₁' x v = Φ₁ x (toEuclideanLin (A₁ : Matrix _ _ ℝ) v))
    (h₂ : ∀ v, Φ₂' x v = Φ₂ x (toEuclideanLin (A₂ : Matrix _ _ ℝ) v)) :
    ((frameTransition Φ₁ Φ₁' x).trans (frameTransition Φ₂' Φ₂ x) :
        StdSpace κ →L[ℝ] StdSpace κ) =
      toEuclideanCLM (𝕜 := ℝ) ((A₂ * A₁⁻¹ : GL (κ ⊕ κ) ℝ) : Matrix (κ ⊕ κ) (κ ⊕ κ) ℝ) := by
  ext1 v
  -- Write `v = T₁⁻¹ w = A₁ w`, so that both sides send it to `A₂ w`.
  obtain ⟨w, rfl⟩ := (frameTransition Φ₁' Φ₁ x).surjective v
  have hv : frameTransition Φ₁' Φ₁ x w = toEuclideanLin (A₁ : Matrix _ _ ℝ) w := by
    rw [frameTransition_apply, h₁, ContinuousLinearEquiv.symm_apply_apply]
  have hD : (frameTransition Φ₁ Φ₁' x).trans (frameTransition Φ₂' Φ₂ x)
      (frameTransition Φ₁' Φ₁ x w) = toEuclideanLin (A₂ : Matrix _ _ ℝ) w := by
    simp [frameTransition_apply, h₂]
  rw [ContinuousLinearEquiv.coe_coe, hD, hv, ← toEuclideanCLM_apply, ← toEuclideanCLM_apply,
    ← mul_apply_eq_comp, ← map_mul, Units.val_mul, Matrix.mul_assoc, ← Units.val_mul,
    inv_mul_cancel, Units.val_one, Matrix.mul_one]

/-- Let `D` be a smooth family of linear symplectomorphisms of `StdSpace κ` on an open set `O`
that contains the image of the annulus `1 - ε < ‖z‖ < 1 + ε` of the coordinate disc `φ` of a chart.
If on the boundary circle `D` is a loop of symplectic matrices of Maslov index `0`, then some
family `P` of linear symplectomorphisms, smooth on the image of the disc `‖z‖ < 1 + ε`, equals `D`
on the image of the annulus `1 - ε / 2 < ‖z‖ < 1 + ε`. -/
private theorem exists_extend_of_maslovIndex_eq_zero
    (hea : e ∈ IsManifold.maximalAtlas (𝓡 2) ∞ M) (hr : 0 < r) (hc : Metric.ball c r ⊆ e.target)
    (he : ∀ x ∈ e.source,
      o.IsOrientationPreservingAt (Manifold.Orientation.euclideanSpace 2) e x)
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) {O : Set M} (hO : IsOpen O)
    (hεO : ∀ z : CoordinateDisc.ball, 1 - ε < ‖(z : ℂ)‖ → ‖(z : ℂ)‖ < 1 + ε →
      CoordinateDisc.ofChart e hr hc he z ∈ O)
    {D : M → StdSpace κ ≃L[ℝ] StdSpace κ}
    (hD : ContMDiffOn (𝓡 2) 𝓘(ℝ, StdSpace κ →L[ℝ] StdSpace κ) ∞
      (fun x ↦ (D x : StdSpace κ →L[ℝ] StdSpace κ)) O)
    (hDσ : ∀ x ∈ O, (stdForm κ).IsSymplectomorphism (stdForm κ) (D x).toLinearEquiv)
    (Ψ : C(Circle, GLSymplectic κ ℝ)) (hΨ : maslovIndex Ψ.toBasedLoop = 0)
    (hDΨ : ∀ ζ, (D ((CoordinateDisc.ofChart e hr hc he).boundaryCircle ζ) :
        StdSpace κ →L[ℝ] StdSpace κ) =
      toEuclideanCLM (𝕜 := ℝ) ((Ψ ζ : GL (κ ⊕ κ) ℝ) : Matrix (κ ⊕ κ) (κ ⊕ κ) ℝ)) :
    ∃ P : M → StdSpace κ ≃L[ℝ] StdSpace κ,
      ContMDiffOn (𝓡 2) 𝓘(ℝ, StdSpace κ →L[ℝ] StdSpace κ) ∞
        (fun x ↦ (P x : StdSpace κ →L[ℝ] StdSpace κ))
        (CoordinateDisc.ofChart e hr hc he '' {z | ‖(z : ℂ)‖ < 1 + ε}) ∧
      (∀ x, (stdForm κ).IsSymplectomorphism (stdForm κ) (P x).toLinearEquiv) ∧
      ∀ z : CoordinateDisc.ball, 1 - ε / 2 < ‖(z : ℂ)‖ → ‖(z : ℂ)‖ < 1 + ε →
        P (CoordinateDisc.ofChart e hr hc he z) = D (CoordinateDisc.ofChart e hr hc he z) := by
  set φ := CoordinateDisc.ofChart e hr hc he
  set ψ : ℂ → M := fun z ↦ e.symm (c + (r / 2) • Complex.orthonormalBasisOneI.repr z)
  have hψ (z : CoordinateDisc.ball) : ψ z = φ z := (CoordinateDisc.ofChart_apply e hr hc he z).symm
  -- Tau Ceti's charts on the symplectic group are stated for the topology of the operator norm
  -- on matrices, which is the product topology (`Matrix.linftyOpTopologicalSpace_eq`), but not
  -- reducibly so.
  let : TopologicalSpace (Matrix (κ ⊕ κ) (κ ⊕ κ) ℝ) := Matrix.linftyOpTopologicalSpace _ _ _
  -- `D` is a smooth map `C` into the symplectic group on `O`.
  obtain ⟨C, hCs, hC⟩ := Matrix.SymplecticGroup.exists_contMDiffOn_toEuclideanCLM_eq hO hD
    fun x hx ↦ (toEuclideanCLM_symm_mem_symplecticGroup_iff (D x)).2 (hDσ x hx)
  -- So `C ∘ ψ` is smooth on the annulus `A` of the chart.
  set A : Set ℂ := (annulus ℂ (1 - ε) (1 + ε) : Set ℂ)
  have hψO (z : ℂ) (hz : z ∈ A) : ψ z ∈ O := by
    rw [SetLike.mem_coe, mem_annulus] at hz
    have hb : z ∈ CoordinateDisc.ball := CoordinateDisc.mem_ball_iff.2 (by linarith [hz.2])
    rw [show z = ((⟨z, hb⟩ : CoordinateDisc.ball) : ℂ) from rfl, hψ]
    exact hεO _ hz.1 hz.2
  have hf : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, TauCeti.Lie.SymplecticGroupModel κ ℝ) ∞
      (fun z ↦ C (ψ z)) A :=
    hCs.comp ((CoordinateDisc.contMDiffOn_symm_add_smul_orthonormalBasisOneI_repr e hr hc
      hea).mono fun z hz ↦ CoordinateDisc.mem_ball_iff.2 (by linarith [(mem_annulus.1 hz).2]))
      fun z hz ↦ hψO z hz
  -- On the circle, `C ∘ ψ` is the loop `Ψ`, which is null-homotopic.
  let γ : C(Circle, symplecticGroup κ ℝ) :=
    (ContinuousMap.mk _ (symplecticGroupContinuousMulEquiv κ ℝ).symm.continuous).comp Ψ
  have hγ (ζ : Circle) : γ ζ = C (ψ ζ) := by
    have hζ : (ζ : ℂ) ∈ A := by
      exact mem_annulus.2 ⟨by rw [Circle.norm_coe]; linarith, by rw [Circle.norm_coe]; linarith⟩
    have hb : ψ ζ = φ.boundaryCircle ζ := by rw [CoordinateDisc.boundaryCircle_apply, ← hψ]
    have hγζ : ((γ ζ : symplecticGroup κ ℝ) : Matrix (κ ⊕ κ) (κ ⊕ κ) ℝ) =
        ((Ψ ζ : GLSymplectic κ ℝ) : GL (κ ⊕ κ) ℝ) :=
      coe_symplecticGroupContinuousMulEquiv_symm κ ℝ _
    apply Subtype.ext
    refine EquivLike.injective (toEuclideanCLM (n := κ ⊕ κ) (𝕜 := ℝ)) ?_
    rw [hC _ (hψO _ hζ), hb, hDΨ, hγζ]
  have hγ0 : γ.Nullhomotopic :=
    ContinuousMap.Nullhomotopic.comp_right (nullhomotopic_of_maslovIndex_toBasedLoop_eq_zero hΨ) _
  -- Extend `C ∘ ψ` from the annulus to a smooth map `g` on the disc of radius `1 + ε`, and read
  -- it through the coordinate of `φ`.
  obtain ⟨g, hg, hgf⟩ := ContMDiffOn.exists_contMDiffOn_ball_eq_of_nullhomotopic (n := ⊤)
    (a := 1 - ε) (a' := 1 - ε / 2) (b := 1 + ε) (by linarith) (by linarith) (by linarith)
    (by linarith) hf γ hγ hγ0
  let P (x : M) : StdSpace κ ≃L[ℝ] StdSpace κ :=
    Matrix.GeneralLinearGroup.ofEuclideanCLE.symm (ofSymplecticGroup κ ℝ (g (φ.coord x)))
  have hP (x : M) : (P x : StdSpace κ →L[ℝ] StdSpace κ) =
      toEuclideanCLM (𝕜 := ℝ) (g (φ.coord x) : Matrix (κ ⊕ κ) (κ ⊕ κ) ℝ) := by
    simp only [P, Matrix.GeneralLinearGroup.ofEuclideanCLE_symm_apply, coe_toEuclideanCLE,
      coe_ofSymplecticGroup]
  refine ⟨P, ?_, fun x ↦ ?_, fun z hz₁ hz₂ ↦ ?_⟩
  · have hcoord := CoordinateDisc.contMDiffOn_coord_ofChart e hr hc he hea
    refine ContMDiffOn.congr ?_ fun x _ ↦ hP x
    refine (Matrix.SymplecticGroup.contMDiff_toEuclideanCLM (κ := κ)).comp_contMDiffOn
      (hg.comp (hcoord.mono ?_) ?_)
    · rintro _ ⟨z, -, rfl⟩
      exact Set.mem_range_self z
    · rintro _ ⟨z, hz, rfl⟩
      rw [Set.mem_preimage, CoordinateDisc.coord_apply]
      exact mem_ball_zero_iff.2 hz
  · rw [← toEuclideanCLM_symm_mem_symplecticGroup_iff, hP, StarAlgEquiv.symm_apply_apply]
    exact (g (φ.coord x)).property
  · have hgz : g (φ.coord (φ z)) = C (φ z) := by
      rw [CoordinateDisc.coord_apply, hgf z hz₁.le hz₂, hψ]
    refine ContinuousLinearEquiv.coe_injective ?_
    rw [hP, hgz, hC _ (hεO z (by linarith) hz₂)]

omit [DecidableEq κ] in
/-- If a family `P` of linear symplectomorphisms, smooth on the image `W` of the disc
`‖z‖ < 1 + ε` of `φ`, equals the change of frame `T₂ ∘ T₁⁻¹` near the boundary circle, then the
frames `Φ₁` and `Φ₂ ∘ P` over `W`, and `Φ₁'` and `Φ₂'` away from the closed disc
`‖z‖ ≤ 1 - ε / 2`, glue to a symplectic isomorphism. -/
private theorem exists_pushforward_eq_of_eq_frameTransition_trans (hr : 0 < r)
    (hc : Metric.ball c r ⊆ e.target)
    (he : ∀ x ∈ e.source,
      o.IsOrientationPreservingAt (Manifold.Orientation.euclideanSpace 2) e x)
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    {U₁ U₁' U₂ U₂' : Set M} (hU₁' : IsOpen U₁') (hU₂' : IsOpen U₂')
    (hDU₁ : (CoordinateDisc.ofChart e hr hc he).disc ⊆ U₁)
    (hDU₂ : (CoordinateDisc.ofChart e hr hc he).disc ⊆ U₂)
    (hDU₁' : discComplement (fun _ : Unit ↦ CoordinateDisc.ofChart e hr hc he) ⊆ U₁')
    (hDU₂' : discComplement (fun _ : Unit ↦ CoordinateDisc.ofChart e hr hc he) ⊆ U₂')
    (hεO : ∀ z : CoordinateDisc.ball, 1 - ε < ‖(z : ℂ)‖ → ‖(z : ℂ)‖ < 1 + ε →
      CoordinateDisc.ofChart e hr hc he z ∈ (U₁ ∩ U₁') ∩ (U₂ ∩ U₂'))
    {Φ₁ Φ₁' : ∀ x, StdSpace κ ≃L[ℝ] V₁ x} {Φ₂ Φ₂' : ∀ x, StdSpace κ ≃L[ℝ] V₂ x}
    (h₁ : ω₁.IsSymplecticFrameOn (stdForm κ) U₁ Φ₁)
    (h₁' : ω₁.IsSymplecticFrameOn (stdForm κ) U₁' Φ₁')
    (h₂ : ω₂.IsSymplecticFrameOn (stdForm κ) U₂ Φ₂)
    (h₂' : ω₂.IsSymplecticFrameOn (stdForm κ) U₂' Φ₂')
    {P : M → StdSpace κ ≃L[ℝ] StdSpace κ}
    (hP : ContMDiffOn (𝓡 2) 𝓘(ℝ, StdSpace κ →L[ℝ] StdSpace κ) ∞
      (fun x ↦ (P x : StdSpace κ →L[ℝ] StdSpace κ))
      (CoordinateDisc.ofChart e hr hc he '' {z | ‖(z : ℂ)‖ < 1 + ε}))
    (hPσ : ∀ x, (stdForm κ).IsSymplectomorphism (stdForm κ) (P x).toLinearEquiv)
    (hPD : ∀ z : CoordinateDisc.ball, 1 - ε / 2 < ‖(z : ℂ)‖ → ‖(z : ℂ)‖ < 1 + ε →
      P (CoordinateDisc.ofChart e hr hc he z) =
        (frameTransition Φ₁ Φ₁' (CoordinateDisc.ofChart e hr hc he z)).trans
          (frameTransition Φ₂' Φ₂ (CoordinateDisc.ofChart e hr hc he z))) :
    ∃ (Ψ : ∀ x, V₁ x ≃L[ℝ] V₂ x) (hΨ : ContMDiff ((𝓡 2).prod 𝓘(ℝ, F₁)) ((𝓡 2).prod 𝓘(ℝ, F₂)) ∞
      (fun p : TotalSpace F₁ V₁ ↦ TotalSpace.mk' F₂ p.proj (Ψ p.proj p.snd))),
      pushforward Ψ hΨ ω₁ = ω₂ := by
  set φ := CoordinateDisc.ofChart e hr hc he
  -- Over the image `W` of the disc of radius `1 + ε`, the frames `Φ₁` and `Φ₂ ∘ P`.
  set W := φ '' {z | ‖(z : ℂ)‖ < 1 + ε}
  have hW : IsOpen W :=
    φ.isOpenEmbedding.isOpenMap _ (isOpen_lt continuous_subtypeVal.norm continuous_const)
  have hWU : W ⊆ U₁ ∩ U₂ := by
    rintro _ ⟨z, hz, rfl⟩
    by_cases h : ‖(z : ℂ)‖ ≤ 1
    · exact ⟨hDU₁ (φ.apply_mem_disc_iff.2 h), hDU₂ (φ.apply_mem_disc_iff.2 h)⟩
    · have := hεO z (by linarith [not_le.1 h]) hz
      exact ⟨this.1.1, this.2.1⟩
  have hPs : ω₂.IsSymplecticFrameOn (stdForm κ) W fun x ↦ (P x).trans (Φ₂ x) :=
    (h₂.mono fun x hx ↦ (hWU hx).2).precomp_of_contMDiffOn hP fun x _ ↦ hPσ x
  -- Away from a smaller closed disc, the frames `Φ₁'` and `Φ₂'`.
  set U' := (U₁' ∩ U₂') ∩ (φ '' {z | ‖(z : ℂ)‖ ≤ 1 - ε / 2})ᶜ
  have hU' : IsOpen U' := (hU₁'.inter hU₂').inter
    (φ.isCompact_image_closedBall (by linarith)).isClosed.isOpen_compl
  have hcover : W ∪ U' = Set.univ := by
    refine Set.eq_univ_of_forall fun x ↦ ?_
    by_cases hx : x ∈ φ.openDisc
    · obtain ⟨z, hz, rfl⟩ := φ.mem_openDisc_iff.1 hx
      exact Or.inl ⟨z, show ‖(z : ℂ)‖ < 1 + ε by linarith, rfl⟩
    · have hxc : x ∈ discComplement (fun _ : Unit ↦ φ) := (mem_discComplement_iff _).2 fun _ ↦ hx
      refine Or.inr ⟨⟨hDU₁' hxc, hDU₂' hxc⟩, ?_⟩
      rintro ⟨z, hz, rfl⟩
      exact hx (φ.apply_mem_openDisc_iff.2 (by linarith [show ‖(z : ℂ)‖ ≤ 1 - ε / 2 from hz]))
  -- On the overlap, `P = T₂ ∘ T₁⁻¹`, so the frames of both bundles have the same transition.
  have htrans : ∀ x ∈ W ∩ U', frameTransition Φ₁' Φ₁ x =
      frameTransition Φ₂' (fun x ↦ (P x).trans (Φ₂ x)) x := by
    rintro x ⟨⟨z, hz, rfl⟩, -, hxz⟩
    have hz' : 1 - ε / 2 < ‖(z : ℂ)‖ := not_le.1 fun h ↦ hxz ⟨z, h, rfl⟩
    refine ContinuousLinearEquiv.ext (funext fun v ↦ ?_)
    rw [frameTransition_apply, frameTransition_apply, ContinuousLinearEquiv.eq_symm_apply,
      ContinuousLinearEquiv.trans_apply, hPD z hz' hz]
    simp [frameTransition_apply]
  obtain ⟨Ψ, hΨ, hpush, -, -⟩ := exists_pushforward_eq_of_frameTransition_eq
    (h₁.mono fun x hx ↦ (hWU hx).1) (h₁'.mono fun x (hx : x ∈ U') ↦ hx.1.1) hPs
    (h₂'.mono fun x (hx : x ∈ U') ↦ hx.1.2) hW hU' hcover htrans
  exact ⟨Ψ, hΨ, hpush⟩

/-- **Isomorphic bundles from equal Maslov indices.** Let `φ = CoordinateDisc.ofChart e hr hc he`
be the coordinate disc of a chart `e` of the smooth maximal atlas of a Hausdorff surface `M`, and
let `ω₁`, `ω₂` be smooth two-forms on smooth vector bundles `V₁`, `V₂` over `M`. For `k = 1, 2`,
let `Φₖ` be a symplectic frame of `ωₖ` for `stdForm κ` over an open set that contains the closed
disc of `φ`, `Φₖ'` one over an open set that contains the complement `discComplement` of its open
disc, and `Ψₖ` the loop of symplectic matrices with `Φₖ' = Φₖ ∘ Ψₖ` on the boundary circle. If
`Ψ₁` and `Ψ₂` have the same Maslov index, then `(V₁, ω₁)` and `(V₂, ω₂)` are isomorphic: some
fibrewise linear isomorphism `Ψ`, smooth on total spaces, carries `ω₁` to `ω₂`. -/
theorem exists_pushforward_eq_of_maslovIndex_eq (hea : e ∈ IsManifold.maximalAtlas (𝓡 2) ∞ M)
    (hr : 0 < r) (hc : Metric.ball c r ⊆ e.target)
    (he : ∀ x ∈ e.source,
      o.IsOrientationPreservingAt (Manifold.Orientation.euclideanSpace 2) e x)
    {U₁ U₁' U₂ U₂' : Set M} (hU₁ : IsOpen U₁) (hU₁' : IsOpen U₁') (hU₂ : IsOpen U₂)
    (hU₂' : IsOpen U₂') (hDU₁ : (CoordinateDisc.ofChart e hr hc he).disc ⊆ U₁)
    (hDU₂ : (CoordinateDisc.ofChart e hr hc he).disc ⊆ U₂)
    (hDU₁' : discComplement (fun _ : Unit ↦ CoordinateDisc.ofChart e hr hc he) ⊆ U₁')
    (hDU₂' : discComplement (fun _ : Unit ↦ CoordinateDisc.ofChart e hr hc he) ⊆ U₂')
    {Φ₁ Φ₁' : ∀ x, StdSpace κ ≃L[ℝ] V₁ x} {Φ₂ Φ₂' : ∀ x, StdSpace κ ≃L[ℝ] V₂ x}
    (h₁ : ω₁.IsSymplecticFrameOn (stdForm κ) U₁ Φ₁)
    (h₁' : ω₁.IsSymplecticFrameOn (stdForm κ) U₁' Φ₁')
    (h₂ : ω₂.IsSymplecticFrameOn (stdForm κ) U₂ Φ₂)
    (h₂' : ω₂.IsSymplecticFrameOn (stdForm κ) U₂' Φ₂')
    (Ψ₁ Ψ₂ : C(Circle, GLSymplectic κ ℝ))
    (hΨ₁ : ∀ ζ v, Φ₁' ((CoordinateDisc.ofChart e hr hc he).boundaryCircle ζ) v =
      Φ₁ ((CoordinateDisc.ofChart e hr hc he).boundaryCircle ζ)
        (toEuclideanLin (Ψ₁ ζ : GL (κ ⊕ κ) ℝ) v))
    (hΨ₂ : ∀ ζ v, Φ₂' ((CoordinateDisc.ofChart e hr hc he).boundaryCircle ζ) v =
      Φ₂ ((CoordinateDisc.ofChart e hr hc he).boundaryCircle ζ)
        (toEuclideanLin (Ψ₂ ζ : GL (κ ⊕ κ) ℝ) v))
    (hμ : maslovIndex Ψ₁.toBasedLoop = maslovIndex Ψ₂.toBasedLoop) :
    ∃ (Ψ : ∀ x, V₁ x ≃L[ℝ] V₂ x) (hΨ : ContMDiff ((𝓡 2).prod 𝓘(ℝ, F₁)) ((𝓡 2).prod 𝓘(ℝ, F₂)) ∞
      (fun p : TotalSpace F₁ V₁ ↦ TotalSpace.mk' F₂ p.proj (Ψ p.proj p.snd))),
      pushforward Ψ hΨ ω₁ = ω₂ := by
  set φ := CoordinateDisc.ofChart e hr hc he
  have hdisj : Pairwise (Disjoint on fun _ : Unit ↦ φ.disc) := Subsingleton.pairwise
  -- The four frames are defined near the boundary circle; around it, on an annulus of the chart.
  set O := (U₁ ∩ U₁') ∩ (U₂ ∩ U₂')
  have hO : IsOpen O := (hU₁.inter hU₁').inter (hU₂.inter hU₂')
  have hφO (ζ : Circle) : φ.boundaryCircle ζ ∈ O :=
    have hd := φ.boundaryCircle_mem_disc ζ
    have hd' := boundaryCircle_mem_discComplement _ hdisj () ζ
    ⟨⟨hDU₁ hd, hDU₁' hd'⟩, hDU₂ hd, hDU₂' hd'⟩
  obtain ⟨ε, hε, hε2, hεO⟩ := φ.exists_image_annulus_subset hO hφO
  -- The change of frame `D = T₂ ∘ T₁⁻¹`, from the transitions `Tₖ = Φₖ⁻¹ ∘ Φₖ'`, is smooth and
  -- symplectic on `O`.
  have hO₁ : ω₁.IsSymplecticFrameOn (stdForm κ) O Φ₁ := h₁.mono fun x hx ↦ hx.1.1
  have hO₁' : ω₁.IsSymplecticFrameOn (stdForm κ) O Φ₁' := h₁'.mono fun x hx ↦ hx.1.2
  have hO₂ : ω₂.IsSymplecticFrameOn (stdForm κ) O Φ₂ := h₂.mono fun x hx ↦ hx.2.1
  have hO₂' : ω₂.IsSymplecticFrameOn (stdForm κ) O Φ₂' := h₂'.mono fun x hx ↦ hx.2.2
  have hD : ContMDiffOn (𝓡 2) 𝓘(ℝ, StdSpace κ →L[ℝ] StdSpace κ) ∞
      (fun x ↦ ((frameTransition Φ₁ Φ₁' x).trans (frameTransition Φ₂' Φ₂ x) :
        StdSpace κ →L[ℝ] StdSpace κ)) O :=
    ((hO₂'.contMDiffOn_frameTransition hO₂ hO).clm_comp
      (hO₁.contMDiffOn_frameTransition hO₁' hO)).congr fun x _ ↦
        (ContinuousLinearEquiv.comp_coe _ _).symm
  have hDσ (x : M) (hx : x ∈ O) : (stdForm κ).IsSymplectomorphism (stdForm κ)
      ((frameTransition Φ₁ Φ₁' x).trans (frameTransition Φ₂' Φ₂ x)).toLinearEquiv :=
    (hO₁.isSymplectomorphism_frameTransition hO₁' hx).trans
      (hO₂'.isSymplectomorphism_frameTransition hO₂ hx)
  -- On the boundary circle, `D` is the loop `Ψ₂ Ψ₁⁻¹`, of Maslov index `0`.
  have hμ0 : maslovIndex (Ψ₂ * Ψ₁⁻¹).toBasedLoop = 0 := by
    have h := maslovIndex_toBasedLoop_mul (Ψ₂ * Ψ₁⁻¹) Ψ₁
    rw [inv_mul_cancel_right] at h
    linarith
  obtain ⟨P, hP, hPσ, hPD⟩ := exists_extend_of_maslovIndex_eq_zero hea hr hc he hε hε2 hO hεO hD
    hDσ (Ψ₂ * Ψ₁⁻¹) hμ0 fun ζ ↦ frameTransition_trans_frameTransition_eq (hΨ₁ ζ) (hΨ₂ ζ)
  exact exists_pushforward_eq_of_eq_frameTransition_trans hr hc he hε hε2 hU₁' hU₂' hDU₁ hDU₂
    hDU₁' hDU₂' hεO h₁ h₁' h₂ h₂' hP hPσ hPD

omit [DecidableEq κ] in
/-- **Isomorphic bundles from equal first Chern numbers.** Let `ω₁`, `ω₂` be nondegenerate smooth
two-forms on smooth vector bundles `V₁`, `V₂` of the same rank `2 |κ|` over a closed connected
surface `M` with a smooth orientation `o`. If their first Chern numbers `symplecticChernNumber`
agree, then `(V₁, ω₁)` and `(V₂, ω₂)` are isomorphic: some fibrewise linear isomorphism `Ψ`,
smooth on total spaces, carries `ω₁` to `ω₂`. -/
theorem exists_pushforward_eq_of_symplecticChernNumber_eq [CompactSpace M] [ConnectedSpace M]
    [FiniteDimensional ℝ F₂] [ContMDiffVectorBundle ((⊤ : ℕ∞) : WithTop ℕ∞) F₁ V₁ (𝓡 2)]
    [ContMDiffVectorBundle ((⊤ : ℕ∞) : WithTop ℕ∞) F₂ V₂ (𝓡 2)]
    (hω₁ : ω₁.IsNondegenerate) (hω₂ : ω₂.IsNondegenerate)
    (hF₁ : finrank ℝ F₁ = 2 * Fintype.card κ) (hF₂ : finrank ℝ F₂ = 2 * Fintype.card κ)
    (G₁ G₂ : Type*) [NormedAddCommGroup G₁] [NormedSpace ℂ G₁] [FiniteDimensional ℂ G₁]
    [NormedAddCommGroup G₂] [NormedSpace ℂ G₂] [FiniteDimensional ℂ G₂]
    [Fact (finrank ℝ F₁ = 2 * finrank ℂ G₁)] [Fact (finrank ℝ F₂ = 2 * finrank ℂ G₂)]
    (h : symplecticChernNumber (o.toHomologicalOrientation finrank_euclideanSpace_fin)
        finrank_euclideanSpace_fin G₁ ω₁ =
      symplecticChernNumber (o.toHomologicalOrientation finrank_euclideanSpace_fin)
        finrank_euclideanSpace_fin G₂ ω₂) :
    ∃ (Ψ : ∀ x, V₁ x ≃L[ℝ] V₂ x) (hΨ : ContMDiff ((𝓡 2).prod 𝓘(ℝ, F₁)) ((𝓡 2).prod 𝓘(ℝ, F₂)) ∞
      (fun p : TotalSpace F₁ V₁ ↦ TotalSpace.mk' F₂ p.proj (Ψ p.proj p.snd))),
      pushforward Ψ hΨ ω₁ = ω₂ := by
  classical
  rcases isEmpty_or_nonempty M with hM | ⟨⟨x₀⟩⟩
  · -- Over the empty surface any family is an isomorphism.
    refine ⟨fun x ↦ isEmptyElim x, fun p ↦ isEmptyElim p.proj, ?_⟩
    exact (pushforward_eq_iff _ _).2 fun x ↦ isEmptyElim x
  -- An oriented chart, its coordinate disc `φ`, and the frames of both bundles near the closed
  -- disc and near its complement.
  obtain ⟨e, r, hr, hc, he, hea, -⟩ := CoordinateDisc.exists_ofChart_pairwise_disjoint o
    (x := fun _ : Unit ↦ x₀) (Function.injective_of_subsingleton _) (U := fun _ ↦ Set.univ)
    fun _ ↦ Filter.univ_mem
  set φ := CoordinateDisc.ofChart (e ()) (hr ()) (hc ()) (he ())
  have hdisj : Pairwise (Disjoint on fun _ : Unit ↦ φ.disc) := Subsingleton.pairwise
  obtain ⟨U₁, hU₁, hD₁, Φ₁, h₁⟩ :=
    hω₁.exists_isSymplecticFrameOn_disc_ofChart (hea ()) (hr ()) (hc ()) (he ()) hF₁
  obtain ⟨U₁', hU₁', hD₁', Φ₁', h₁'⟩ :=
    hω₁.exists_isSymplecticFrameOn_discComplement_ofChart (hea ()) (hr ()) (hc ()) (he ()) hF₁
  obtain ⟨U₂, hU₂, hD₂, Φ₂, h₂⟩ :=
    hω₂.exists_isSymplecticFrameOn_disc_ofChart (hea ()) (hr ()) (hc ()) (he ()) hF₂
  obtain ⟨U₂', hU₂', hD₂', Φ₂', h₂'⟩ :=
    hω₂.exists_isSymplecticFrameOn_discComplement_ofChart (hea ()) (hr ()) (hc ()) (he ()) hF₂
  have hbc {U U' : Set M} (hD : φ.disc ⊆ U) (hD' : discComplement (fun _ : Unit ↦ φ) ⊆ U')
      (ζ : Circle) : φ.boundaryCircle ζ ∈ U ∩ U' :=
    ⟨hD (φ.boundaryCircle_mem_disc ζ), hD' (boundaryCircle_mem_discComplement _ hdisj () ζ)⟩
  obtain ⟨Ψ₁, hΨ₁⟩ := h₁.exists_frameTransition hU₁ hU₁' h₁' _ (hbc hD₁ hD₁')
  obtain ⟨Ψ₂, hΨ₂⟩ := h₂.exists_frameTransition hU₂ hU₂' h₂' _ (hbc hD₂ hD₂')
  refine exists_pushforward_eq_of_maslovIndex_eq (hea ()) (hr ()) (hc ()) (he ()) hU₁ hU₁' hU₂
    hU₂' hD₁ hD₂ hD₁' hD₂' h₁ h₁' h₂ h₂' Ψ₁ Ψ₂ hΨ₁ hΨ₂ ?_
  -- By the clutching formula, the Maslov indices are the Chern numbers.
  have hc₁ := symplecticChernNumber_eq_sum_maslovIndex_clutching hdisj
    (Φ := fun _ x ↦ Φ₁ x) (Φout := fun x ↦ Φ₁' x) (fun _ ↦ h₁.continuous_restrict hD₁)
    (h₁'.continuous_restrict hD₁') G₁ finrank_euclideanSpace_fin
    (fun _ x ↦ h₁.map_bilinFormAt x (hD₁ x.property))
    (fun x ↦ h₁'.map_bilinFormAt x (hD₁' x.property)) (fun _ ↦ Ψ₁) fun _ ↦ hΨ₁
  have hc₂ := symplecticChernNumber_eq_sum_maslovIndex_clutching hdisj
    (Φ := fun _ x ↦ Φ₂ x) (Φout := fun x ↦ Φ₂' x) (fun _ ↦ h₂.continuous_restrict hD₂)
    (h₂'.continuous_restrict hD₂') G₂ finrank_euclideanSpace_fin
    (fun _ x ↦ h₂.map_bilinFormAt x (hD₂ x.property))
    (fun x ↦ h₂'.map_bilinFormAt x (hD₂' x.property)) (fun _ ↦ Ψ₂) fun _ ↦ hΨ₂
  rw [hc₁, hc₂, Fintype.sum_unique, Fintype.sum_unique] at h
  exact h

end Iso

end Bundle

end SymplecticGeometry

end
