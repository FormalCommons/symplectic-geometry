/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.VectorBundle.ChernNumber.Clutching
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Hermitian.Basic
import Mathlib.Analysis.Complex.Isometry
import TauCeti.Analysis.Calculus.ContDiffZPow
import TauCeti.Topology.VectorBundle.RestrictScalars
import SymplecticGeometry.Analysis.Matrix.SymplecticGroup.Maslov

/-!
# The clutching line bundle

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

## Main definitions

* `SymplecticGeometry.Bundle.clutchingScalar`: the scalar coordinate changes of the bundle.
* `SymplecticGeometry.Bundle.clutchingLineBundle`: the clutching line bundle, with its complex
  structure (`VectorBundle ℂ ℂ`) and fibres of complex dimension one
  (`finrank_clutchingLineBundle`).
* `SymplecticGeometry.Bundle.clutchingFiberEquiv`: the identification of each fibre with `ℂ`.
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

## Proof

The disc clutching formula `symplecticChernNumber_eq_sum_maslovIndex_clutching`
(`ChernNumber/Clutching.lean`) is applied to one coordinate disc, `z ↦ φ (3 z / 4)`, whose closed
disc lies in the first chart and the complement of whose open disc lies in the second. The two
charts give frames there, read on the standard symplectic plane `StdSpace (Fin 1)` through
`(x, y) ↦ x + i y` (`StdSpace.equivComplex`). They are symplectic, since the coordinate changes
have modulus one, and on the boundary circle they differ by `ζ ↦ ζ ^ k`, the realification of a
loop of `1 × 1` unitary matrices (`circlePowLoop k`), whose Maslov index is `k`
(`maslovIndex_toBasedLoop_circlePowLoop`).

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

/-- The scalar transition function of the clutching line bundle, from chart `i` to chart `j`:
`e^{ik(j - i)θ}`, where the inner chart is `true` and the outer one `false`. -/
def clutchingScalar (i j : Bool) (x : M) : Circle :=
  φ.phase x ^ (k * ((j.toNat : ℤ) - i.toNat))

theorem clutchingScalar_def (i j : Bool) (x : M) :
    clutchingScalar φ k i j x = φ.phase x ^ (k * ((j.toNat : ℤ) - i.toNat)) :=
  (rfl)

@[simp]
theorem clutchingScalar_self (i : Bool) (x : M) : clutchingScalar φ k i i x = 1 := by
  simp [clutchingScalar_def]

/-- From the outer chart to the inner chart, the transition is `e^{ikθ}`. -/
@[simp]
theorem clutchingScalar_false_true (x : M) :
    clutchingScalar φ k false true x = φ.phase x ^ k := by
  simp [clutchingScalar_def]

theorem clutchingScalar_mul (i j l : Bool) (x : M) :
    clutchingScalar φ k j l x * clutchingScalar φ k i j x = clutchingScalar φ k i l x := by
  rw [clutchingScalar_def, clutchingScalar_def, clutchingScalar_def, ← zpow_add, ← mul_add]
  congr 2
  ring

/-- The overlap of the two charts of the clutching line bundle lies in the range of `φ`, off the
centre: there the coordinate of `φ` does not vanish. -/
private theorem inter_subset_coord_ne_zero :
    φ.openDisc ∩ (φ '' {z | ‖(z : ℂ)‖ ≤ 1 / 2})ᶜ ⊆ {x ∈ range φ | φ.coord x ≠ 0} := by
  rintro x ⟨h₁, h₂⟩
  obtain ⟨z, hz, rfl⟩ := φ.mem_openDisc_iff.1 h₁
  have hz' : 1 / 2 < ‖(z : ℂ)‖ := lt_of_not_ge fun h ↦ h₂ ⟨z, h, rfl⟩
  exact ⟨mem_range_self z, by rw [CoordinateDisc.coord_apply]; exact norm_pos_iff.1 (by linarith)⟩

variable {φ} in
/-- On the overlap of the two charts the scalar transition functions are `Cⁿ` if the coordinate
of `φ` is. -/
private theorem contMDiffOn_clutchingScalar {n : WithTop ℕ∞}
    (hφ : ContMDiffOn 𝓘(ℝ, EM) 𝓘(ℝ, ℂ) n φ.coord (range φ)) (i j : Bool) :
    ContMDiffOn 𝓘(ℝ, EM) 𝓘(ℝ, ℂ) n (fun x ↦ (clutchingScalar φ k i j x : ℂ))
      (φ.openDisc ∩ (φ '' {z | ‖(z : ℂ)‖ ≤ 1 / 2})ᶜ) := by
  intro x hx
  simp only [clutchingScalar_def, Circle.coe_zpow]
  have hs := (contDiffAt_id (𝕜 := ℝ) (n := n) (x := (φ.phase x : ℂ))).zpow
    (m := k * ((j.toNat : ℤ) - i.toNat)) (Or.inl (Circle.coe_ne_zero _))
  refine hs.comp_contMDiffWithinAt (f := fun y ↦ (φ.phase y : ℂ)) ?_
  exact (φ.contMDiffOn_coe_phase hφ).mono (inter_subset_coord_ne_zero φ) x hx

private theorem continuousOn_clutchingScalar (i j : Bool) :
    ContinuousOn (fun x ↦ (clutchingScalar φ k i j x : ℂ))
      (φ.openDisc ∩ (φ '' {z | ‖(z : ℂ)‖ ≤ 1 / 2})ᶜ) :=
  contMDiffOn_zero_iff.1
    (contMDiffOn_clutchingScalar k (contMDiffOn_zero_iff.2 φ.continuousOn_coord) i j)

open scoped Classical in
/-- **The clutching line bundle** of a coordinate disc `φ` and an integer `k`: the complex line
bundle glued from the trivial bundles with fibre `ℂ` over the open disc `φ '' {‖z‖ < 1}` (the
chart `true`) and over the complement of `φ '' {‖z‖ ≤ 1 / 2}` (the chart `false`), with
transition `v ↦ e^{ikθ} v` from the second to the first on the annulus where they overlap, `θ`
being the angle of the coordinate of `φ`. It is a real vector bundle core; its fibres are `ℂ`,
and the coordinate changes are complex linear. -/
def clutchingLineBundle : VectorBundleCore ℝ M ℂ Bool where
  baseSet b := if b then φ.openDisc else (φ '' {z | ‖(z : ℂ)‖ ≤ 1 / 2})ᶜ
  isOpen_baseSet b := by
    cases b
    · exact (φ.isCompact_image_closedBall (by norm_num)).isClosed.isOpen_compl
    · exact φ.isOpen_openDisc
  indexAt x := decide (x ∈ φ.openDisc)
  mem_baseSet_at x := by
    by_cases hx : x ∈ φ.openDisc
    · simp [hx]
    · simp only [hx, decide_false, Bool.false_eq_true, ↓reduceIte, mem_compl_iff]
      rintro ⟨z, hz, rfl⟩
      exact hx (φ.apply_mem_openDisc_iff.2 (by linarith [show ‖(z : ℂ)‖ ≤ 1 / 2 from hz]))
  coordChange i j x := ContinuousLinearMap.lsmul ℝ ℂ (clutchingScalar φ k i j x : ℂ)
  coordChange_self i x _ v := by simp
  continuousOn_coordChange i j := by
    refine (ContinuousLinearMap.lsmul ℝ ℂ).continuous.comp_continuousOn ?_
    cases i <;> cases j
    · simpa using continuousOn_const
    · exact (continuousOn_clutchingScalar φ k _ _).mono fun x hx ↦ ⟨by simpa using hx.2,
        by simpa using hx.1⟩
    · exact (continuousOn_clutchingScalar φ k _ _).mono fun x hx ↦ ⟨by simpa using hx.1,
        by simpa using hx.2⟩
    · simpa using continuousOn_const
  coordChange_comp i j l x _ v := by
    simp only [ContinuousLinearMap.lsmul_apply, smul_smul, ← Circle.coe_mul,
      clutchingScalar_mul]

/-- The inner chart of the clutching line bundle is the open disc of `φ`. -/
@[simp]
theorem baseSet_localTriv_clutchingLineBundle_true :
    ((clutchingLineBundle φ k).localTriv true).baseSet = φ.openDisc :=
  (rfl)

/-- The outer chart of the clutching line bundle is the complement of `φ '' {‖z‖ ≤ 1 / 2}`. -/
@[simp]
theorem baseSet_localTriv_clutchingLineBundle_false :
    ((clutchingLineBundle φ k).localTriv false).baseSet = (φ '' {z | ‖(z : ℂ)‖ ≤ 1 / 2})ᶜ :=
  (rfl)

open scoped Classical in
/-- The chart that the clutching line bundle assigns to a point is the inner one exactly on the
open disc of `φ`. -/
@[simp]
theorem indexAt_clutchingLineBundle (x : M) :
    (clutchingLineBundle φ k).indexAt x = decide (x ∈ φ.openDisc) :=
  (rfl)

@[simp]
theorem coordChange_clutchingLineBundle (i j : Bool) (x : M) (v : ℂ) :
    (clutchingLineBundle φ k).coordChange i j x v = (clutchingScalar φ k i j x : ℂ) * v :=
  (rfl)

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
      fun c v ↦ mul_left_comm (clutchingScalar φ k _ i x : ℂ) c (v : ℂ)⟩

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
    (clutchingLineBundle φ k).IsContMDiff 𝓘(ℝ, EM) n where
  contMDiffOn_coordChange i j := by
    refine (ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] ℂ →L[ℝ] ℂ).contMDiff.comp_contMDiffOn ?_
    cases i <;> cases j
    · simpa using contMDiffOn_const
    · exact (contMDiffOn_clutchingScalar k hφ _ _).mono fun x hx ↦ ⟨hx.2, hx.1⟩
    · exact (contMDiffOn_clutchingScalar k hφ _ _).mono fun x hx ↦ hx
    · simpa using contMDiffOn_const

/-! ### The Hermitian metric and the symplectic form -/

/-- The fibres of the clutching line bundle are `ℂ`: the identity, as a real linear
isomorphism. -/
def clutchingFiberEquiv (x : M) : (clutchingLineBundle φ k).Fiber x ≃L[ℝ] ℂ :=
  ContinuousLinearEquiv.refl ℝ ℂ

/-- The identification of the fibres with `ℂ` is complex linear. -/
@[simp]
theorem clutchingFiberEquiv_smul (x : M) (c : ℂ) (v : (clutchingLineBundle φ k).Fiber x) :
    clutchingFiberEquiv φ k x (c • v) = c * clutchingFiberEquiv φ k x v :=
  (rfl)

/-- The point `v` of `ℂ` in the chart `i` is the point `e^{ik(j - i)θ} v` of the fibre, where `j`
is the chart that the core assigns to the base point. -/
theorem clutchingFiberEquiv_localTriv_symm (i : Bool) {x : M}
    (hx : x ∈ ((clutchingLineBundle φ k).localTriv i).baseSet) (v : ℂ) :
    clutchingFiberEquiv φ k x (((clutchingLineBundle φ k).localTriv i).symm x v) =
      (clutchingScalar φ k i ((clutchingLineBundle φ k).indexAt x) x : ℂ) * v :=
  congrArg (clutchingFiberEquiv φ k x) ((clutchingLineBundle φ k).localTriv_symm_apply i hx v)

/-- The point `v` of `ℂ` in the preferred chart at `a` is the point `e^{ik(j - i)θ} v` of the
fibre. -/
theorem clutchingFiberEquiv_trivializationAt_symm {a x : M}
    (hx : x ∈ (trivializationAt ℂ (clutchingLineBundle φ k).Fiber a).baseSet) (v : ℂ) :
    clutchingFiberEquiv φ k x ((trivializationAt ℂ (clutchingLineBundle φ k).Fiber a).symm x v) =
      (clutchingScalar φ k ((clutchingLineBundle φ k).indexAt a)
        ((clutchingLineBundle φ k).indexAt x) x : ℂ) * v :=
  clutchingFiberEquiv_localTriv_symm φ k _ hx v

/-- **The Hermitian metric of the clutching line bundle**: on every fibre `ℂ`, the real part
`⟪v, w⟫_ℝ = Re (conj v * w)` of the standard Hermitian product. The coordinate changes are
multiplications by complex numbers of modulus one, so it is constant in every chart, hence
smooth. -/
def clutchingMetric (n : WithTop ℕ∞) :
    ContMDiffRiemannianMetric 𝓘(ℝ, EM) n ℂ (clutchingLineBundle φ k).Fiber where
  inner x := (ContinuousLinearMap.precomp ℝ (clutchingFiberEquiv φ k x : _ →L[ℝ] ℂ)).comp
    ((innerSL ℝ).comp (clutchingFiberEquiv φ k x : _ →L[ℝ] ℂ))
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
        ((clutchingFiberEquiv φ k x).symm : ℂ →L[ℝ] (clutchingLineBundle φ k).Fiber x)
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
        ContinuousLinearEquiv.coe_coe, clutchingFiberEquiv_trivializationAt_symm φ k hx,
        innerSL_apply_apply]
      rw [← rotation_apply, ← rotation_apply, LinearIsometryEquiv.inner_map_map]
      exact (innerSL_apply_apply ℝ v w).symm

/-- The metric `clutchingMetric` is the real inner product of `ℂ` on every fibre. -/
@[simp]
theorem clutchingMetric_inner (n : WithTop ℕ∞) (x : M)
    (v w : (clutchingLineBundle φ k).Fiber x) :
    (clutchingMetric φ k n).inner x v w =
      inner ℝ (clutchingFiberEquiv φ k x v) (clutchingFiberEquiv φ k x w) := by
  simp only [clutchingMetric, ContinuousLinearMap.comp_apply, ContinuousLinearMap.precomp_apply,
    innerSL_apply_apply, ContinuousLinearEquiv.coe_coe]

/-- Multiplication by `Complex.I` preserves the metric `clutchingMetric`: it is a Hermitian
metric. -/
theorem clutchingMetric_inner_I_smul (n : WithTop ℕ∞) (x : M)
    (v w : (clutchingLineBundle φ k).Fiber x) :
    (clutchingMetric φ k n).inner x (Complex.I • v) (Complex.I • w) =
      (clutchingMetric φ k n).inner x v w := by
  rw [clutchingMetric_inner, clutchingMetric_inner, clutchingFiberEquiv_smul,
    clutchingFiberEquiv_smul]
  simp [Complex.inner]

/-! ### The first Chern number -/

open CoordinateDisc in
/-- The coordinate disc `z ↦ φ (3 z / 4)`: its closed disc lies in the inner chart of the
clutching line bundle, and the complement of its open disc in the outer chart. -/
private def clutchingDisc : CoordinateDisc o :=
  φ.comp (affineBall 0 (r := 3 / 4) (by norm_num) (by norm_num))
    (isOpenEmbedding_affineBall _ _ _) (comap_affineBall_complexHomologicalOrientation _ _ _)

private theorem clutchingDisc_apply (z : CoordinateDisc.ball) :
    clutchingDisc φ z = φ (CoordinateDisc.affineBall 0 (r := 3 / 4) (by norm_num)
      (by norm_num) z) :=
  φ.comp_apply _ _ _ z

private theorem disc_clutchingDisc_subset :
    (clutchingDisc φ).disc ⊆ (clutchingLineBundle φ k).baseSet true := by
  intro x hx
  obtain ⟨z, hz, rfl⟩ := (clutchingDisc φ).mem_disc_iff.1 hx
  rw [clutchingDisc_apply]
  refine φ.apply_mem_openDisc_iff.2 ?_
  rw [CoordinateDisc.coe_affineBall_apply, zero_add, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (by norm_num)]
  linarith

private theorem discComplement_clutchingDisc_subset :
    discComplement (fun _ : Unit ↦ clutchingDisc φ) ⊆
      (clutchingLineBundle φ k).baseSet false := by
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
  (congrFun (((clutchingLineBundle φ k).localTriv i).symm_continuousLinearEquivAt_eq
    (R := ℝ) hx) _).trans (((clutchingLineBundle φ k).localTriv i).symmL_apply hx _)

/-- Read in `ℂ`, the frame of the chart `i` at `x` is `v ↦ e^{ik(j - i)θ} v`, where `j` is the
chart that the core assigns to `x`. -/
theorem clutchingFiberEquiv_clutchingFrame (i : Bool) {x : M}
    (hx : x ∈ (clutchingLineBundle φ k).baseSet i) (v : StdSpace (Fin 1)) :
    clutchingFiberEquiv φ k x (clutchingFrame φ k i x hx v) =
      (clutchingScalar φ k i ((clutchingLineBundle φ k).indexAt x) x : ℂ) *
        equivComplex (Fin 1) v := by
  rw [clutchingFrame_apply, clutchingFiberEquiv_localTriv_symm φ k i hx]

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
      (clutchingMetric_inner_I_smul φ k n), clutchingMetric_inner, clutchingFiberEquiv_smul,
    clutchingFiberEquiv_clutchingFrame, clutchingFiberEquiv_clutchingFrame,
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
  apply (clutchingFiberEquiv φ k _).injective
  rw [clutchingFiberEquiv_clutchingFrame, clutchingFiberEquiv_clutchingFrame,
    coe_circlePowLoop_apply, equivComplex_toEuclideanLin_realify_diagonal,
    ← clutchingScalar_mul φ k false true, clutchingScalar_false_true,
    phase_boundaryCircle_clutchingDisc, Circle.coe_mul, Circle.coe_zpow]
  ring

end Bundle

end SymplecticGeometry

end
