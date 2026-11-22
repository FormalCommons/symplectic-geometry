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
coordinate `clutchingPhase φ` of `φ`: `w / ‖w‖` for the coordinate `w = φ.coord x`. The coordinate
changes are complex linear, so the bundle is a complex vector bundle, and they are smooth as soon
as the coordinate of `φ` is (`isContMDiff_clutchingLineBundle`), which holds for the coordinate
discs of the charts of the maximal atlas (`CoordinateDisc.contMDiffOn_coord_ofChart`). They
have modulus one, so the real part of the standard Hermitian product of `ℂ` is a smooth metric
`clutchingMetric φ k n`, invariant under multiplication by `Complex.I`. Its symplectic form is,
as for every Hermitian bundle, `(ContMDiffComplexStructure.ofComplexModule …).compatibleForm g`
(`Hermitian/Basic.lean`).

## Main definitions

* `SymplecticGeometry.Bundle.clutchingPhase`: the angular coordinate of a coordinate disc.
* `SymplecticGeometry.Bundle.clutchingScalar`: the scalar coordinate changes of the bundle.
* `SymplecticGeometry.Bundle.clutchingLineBundle`: the clutching line bundle, with its complex
  structure (`VectorBundle ℂ ℂ`) and fibres of complex dimension one
  (`finrank_clutchingLineBundle`).
* `SymplecticGeometry.Bundle.clutchingFiberEquiv`: the identification of each fibre with `ℂ`.
* `SymplecticGeometry.Bundle.clutchingMetric`: its Hermitian metric.

## Main results

* `SymplecticGeometry.Bundle.isContMDiff_clutchingLineBundle`: the bundle is `Cⁿ` when the
  coordinate of `φ` is.
* `SymplecticGeometry.Bundle.clutchingMetric_inner_I_smul`: the metric is Hermitian.
* `SymplecticGeometry.Bundle.symplecticChernNumber_clutchingLineBundle`: over a compact surface,
  the first Chern number of the bundle with the symplectic form of its metric is `k`.

## Proof

The disc clutching formula `symplecticChernNumber_eq_sum_maslovIndex_clutching`
(`ChernNumber/Clutching.lean`) is applied to one coordinate disc, `z ↦ φ (3 z / 4)`, whose closed
disc lies in the first chart and the complement of whose open disc lies in the second. The two
charts give frames there, read on the standard symplectic plane `StdSpace Unit` through
`(x, y) ↦ x + i y`. They are symplectic, since the coordinate changes have modulus one, and on the
boundary circle they differ by `ζ ↦ ζ ^ k`, the realification of a loop of `1 × 1` unitary
matrices. Its Maslov index is the degree of `ζ ↦ ζ ^ k`, which is `k`.

## Implementation notes

The smoothness of `clutchingMetric` is proved as Tau Ceti's `TauCeti.contMDiff_const_bundlePairing`
is, for a constant pairing on a trivial bundle: read in the preferred chart at each point, the
metric is the constant inner product of `ℂ`. The computation of the Maslov index of `ζ ↦ ζ ^ k`
follows that of `SymplecticGeometry.maslovIndex_symplecticRotationLoop`.

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

/-! ### The angular coordinate of a coordinate disc -/

/-- The angular coordinate of the coordinate disc `φ`, as a point of the circle: `e^{iθ}` at
`φ (r e^{iθ})`, that is `w / ‖w‖` for `w = φ.coord x` when `w ≠ 0`. -/
def clutchingPhase (x : M) : Circle :=
  Circle.exp (Complex.arg (φ.coord x))

theorem clutchingPhase_def (x : M) : clutchingPhase φ x = Circle.exp (Complex.arg (φ.coord x)) :=
  (rfl)

theorem coe_clutchingPhase {x : M} (hx : φ.coord x ≠ 0) :
    (clutchingPhase φ x : ℂ) = φ.coord x / ‖φ.coord x‖ := by
  rw [clutchingPhase_def, Circle.coe_exp, eq_div_iff (by simpa using hx), mul_comm,
    Complex.norm_mul_exp_arg_mul_I]

/-- At `φ z`, the angular coordinate is `z / ‖z‖`. -/
theorem coe_clutchingPhase_apply {z : CoordinateDisc.ball} (hz : (z : ℂ) ≠ 0) :
    (clutchingPhase φ (φ z) : ℂ) = z / ‖(z : ℂ)‖ := by
  rw [coe_clutchingPhase φ (by rwa [CoordinateDisc.coord_apply]), CoordinateDisc.coord_apply]

/-! ### The line bundle -/

/-- The scalar transition function of the clutching line bundle, from chart `i` to chart `j`:
`e^{ik(j - i)θ}`, where the inner chart is `true` and the outer one `false`. -/
def clutchingScalar (i j : Bool) (x : M) : Circle :=
  clutchingPhase φ x ^ (k * ((j.toNat : ℤ) - i.toNat))

theorem clutchingScalar_def (i j : Bool) (x : M) :
    clutchingScalar φ k i j x = clutchingPhase φ x ^ (k * ((j.toNat : ℤ) - i.toNat)) :=
  (rfl)

@[simp]
theorem clutchingScalar_self (i : Bool) (x : M) : clutchingScalar φ k i i x = 1 := by
  simp [clutchingScalar_def]

/-- From the outer chart to the inner chart, the transition is `e^{ikθ}`. -/
@[simp]
theorem clutchingScalar_false_true (x : M) :
    clutchingScalar φ k false true x = clutchingPhase φ x ^ k := by
  simp [clutchingScalar_def]

theorem clutchingScalar_mul (i j l : Bool) (x : M) :
    clutchingScalar φ k j l x * clutchingScalar φ k i j x = clutchingScalar φ k i l x := by
  rw [clutchingScalar_def, clutchingScalar_def, clutchingScalar_def, ← zpow_add, ← mul_add]
  congr 2
  ring

/-- A point in both charts of the clutching line bundle is `φ z` with `1 / 2 < ‖z‖ < 1`. -/
private theorem exists_of_mem_inter {x : M} (h₁ : x ∈ φ.openDisc)
    (h₂ : x ∈ (φ '' {z | ‖(z : ℂ)‖ ≤ 1 / 2})ᶜ) :
    ∃ z : CoordinateDisc.ball, φ z = x ∧ 1 / 2 < ‖(z : ℂ)‖ ∧ ‖(z : ℂ)‖ < 1 := by
  obtain ⟨z, hz, rfl⟩ := φ.mem_openDisc_iff.1 h₁
  exact ⟨z, rfl, lt_of_not_ge fun h ↦ h₂ ⟨z, h, rfl⟩, hz⟩

/-- On the overlap of the two charts, the scalar transition function is
`(w / ‖w‖) ^ (k (j - i))` for `w = φ.coord x`. -/
private theorem coe_clutchingScalar_of_mem {x : M} (h₁ : x ∈ φ.openDisc)
    (h₂ : x ∈ (φ '' {z | ‖(z : ℂ)‖ ≤ 1 / 2})ᶜ) (i j : Bool) :
    (clutchingScalar φ k i j x : ℂ) =
      (φ.coord x / ‖φ.coord x‖) ^ (k * ((j.toNat : ℤ) - i.toNat)) := by
  obtain ⟨z, rfl, hz, -⟩ := exists_of_mem_inter φ h₁ h₂
  have hz0 : (z : ℂ) ≠ 0 := norm_pos_iff.1 (by linarith)
  rw [clutchingScalar_def, Circle.coe_zpow, coe_clutchingPhase φ (by simpa using hz0)]

variable {φ} in
/-- On the overlap of the two charts the scalar transition functions are `Cⁿ` if the coordinate
of `φ` is. -/
private theorem contMDiffOn_clutchingScalar {n : WithTop ℕ∞}
    (hφ : ContMDiffOn 𝓘(ℝ, EM) 𝓘(ℝ, ℂ) n φ.coord (range φ)) (i j : Bool) :
    ContMDiffOn 𝓘(ℝ, EM) 𝓘(ℝ, ℂ) n (fun x ↦ (clutchingScalar φ k i j x : ℂ))
      (φ.openDisc ∩ (φ '' {z | ‖(z : ℂ)‖ ≤ 1 / 2})ᶜ) := by
  intro x hx
  obtain ⟨z, rfl, hz, -⟩ := exists_of_mem_inter φ hx.1 hx.2
  have hz0 : φ.coord (φ z) ≠ 0 := by
    rw [CoordinateDisc.coord_apply]
    exact norm_pos_iff.1 (by linarith)
  -- The function `w ↦ (w / ‖w‖) ^ m` is smooth away from `0`.
  have hw : ((‖φ.coord (φ z)‖ : ℝ) : ℂ) ≠ 0 := by simpa using hz0
  have hs : ContDiffAt ℝ n (fun w : ℂ ↦ (w / ‖w‖) ^ (k * ((j.toNat : ℤ) - i.toNat)))
      (φ.coord (φ z)) := by
    simp only [div_eq_mul_inv]
    exact (contDiffAt_id.mul ((Complex.ofRealCLM.contDiff.contDiffAt.comp _
      (contDiffAt_norm ℝ hz0)).inv hw)).zpow (Or.inl (mul_ne_zero hz0 (inv_ne_zero hw)))
  refine (hs.comp_contMDiffWithinAt
    ((hφ _ (mem_range_self z)).mono fun y hy ↦ ?_)).congr (fun y hy ↦ ?_) ?_
  · obtain ⟨w, rfl, -⟩ := exists_of_mem_inter φ hy.1 hy.2
    exact mem_range_self w
  · exact coe_clutchingScalar_of_mem φ k hy.1 hy.2 i j
  · exact coe_clutchingScalar_of_mem φ k hx.1 hx.2 i j

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
instance : VectorBundle ℂ ℂ (clutchingLineBundle φ k).Fiber where
  trivialization_linear' := by
    rintro _ ⟨i, rfl⟩
    exact inferInstanceAs (((clutchingLineBundle φ k).localTriv i).IsLinear ℂ)
  continuousOn_coordChange' := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    refine ((ContinuousLinearMap.lsmul ℂ ℂ).continuous.comp_continuousOn
      (((ContinuousLinearMap.apply ℝ ℂ (1 : ℂ)).continuous.comp_continuousOn
        ((clutchingLineBundle φ k).continuousOn_coordChange i j)))).congr fun x hx ↦ ?_
    refine ContinuousLinearMap.ext fun v ↦ ?_
    have h := (clutchingLineBundle φ k).localTriv_coordChange_eq i j hx v
    rw [Trivialization.coordChangeL_apply' _ _ hx] at h
    exact (Trivialization.coordChangeL_apply' (R := ℂ) ((clutchingLineBundle φ k).localTriv i)
      ((clutchingLineBundle φ k).localTriv j) hx v).trans (h.trans (by simp [mul_comm]))

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
  contMDiff := by
    intro a
    let b : ℂ →L[ℝ] ℂ →L[ℝ] ℝ := innerSL ℝ
    rw [contMDiffAt_hom_bundle]
    refine ⟨contMDiffAt_id, (contMDiffAt_const (c := b)).congr_of_eventuallyEq ?_⟩
    filter_upwards [(trivializationAt ℂ (clutchingLineBundle φ k).Fiber a).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt ℂ _ a)] with x hx
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

private theorem clutchingPhase_boundaryCircle (ζ : Circle) :
    clutchingPhase φ ((clutchingDisc φ).boundaryCircle ζ) = ζ := by
  refine Circle.ext ?_
  rw [CoordinateDisc.boundaryCircle_apply, clutchingDisc_apply, coe_clutchingPhase_apply]
  · simp only [CoordinateDisc.coe_affineBall_apply, zero_add, norm_mul, Complex.norm_real,
      Circle.norm_coe, mul_one]
    norm_num
  · rw [CoordinateDisc.coe_affineBall_apply, zero_add]
    exact mul_ne_zero (by norm_num) (Circle.coe_ne_zero ζ)

/-- The identification `(x, y) ↦ x + i y` of the standard symplectic plane with `ℂ`. -/
private def stdLineEquiv : StdSpace Unit ≃L[ℝ] ℂ :=
  (complexToRealEuclidean Unit).symm.trans (ContinuousLinearEquiv.funUnique Unit ℝ ℂ)

/-- Read on `ℂ`, the standard form of `StdSpace Unit` is `ω₀(v, w) = ⟪i v, w⟫`. -/
private theorem stdForm_eq_inner_stdLineEquiv (v w : StdSpace Unit) :
    stdForm Unit v w = inner ℝ (Complex.I * stdLineEquiv v) (stdLineEquiv w) := by
  obtain ⟨v, rfl⟩ := (complexToRealEuclidean Unit).surjective v
  obtain ⟨w, rfl⟩ := (complexToRealEuclidean Unit).surjective w
  rw [stdForm_apply_eq_inner, stdComplexStructure_complexToRealEuclidean,
    inner_complexToRealEuclidean]
  simp [stdLineEquiv, Complex.inner, dotProduct, mul_comm]

/-- On `ℂ`, the realification of the `1 × 1` matrix `(c)` is multiplication by `c`. -/
private theorem stdLineEquiv_toEuclideanLin_realify (c : ℂ) (v : StdSpace Unit) :
    stdLineEquiv (Matrix.toEuclideanLin (Matrix.diagonal fun _ : Unit ↦ c).realify v) =
      c * stdLineEquiv v := by
  obtain ⟨v, rfl⟩ := (complexToRealEuclidean Unit).surjective v
  rw [← complexToRealEuclidean_mulVec]
  simp [stdLineEquiv]

variable [CompactSpace M] [IsManifold 𝓘(ℝ, EM) ((⊤ : ℕ∞) : WithTop ℕ∞) M]

open Matrix Matrix.UnitaryGroup TauCeti.GLSymplectic in
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
  set Z := clutchingLineBundle φ k
  set ψ := clutchingDisc φ
  set form := (ContMDiffComplexStructure.ofComplexModule 𝓘(ℝ, EM) n ℂ Z.Fiber).compatibleForm
    (clutchingMetric φ k n)
  -- The frame of the chart `i` at a point `x` of its base set: `v ↦ e_i⁻¹ (x, v)`, read on
  -- `StdSpace Unit` through `stdLineEquiv`.
  let frame (i : Bool) (x : M) (hx : x ∈ Z.baseSet i) : StdSpace Unit ≃L[ℝ] Z.Fiber x :=
    stdLineEquiv.trans ((Z.localTriv i).continuousLinearEquivAt ℝ x hx).symm
  have frame_apply (i : Bool) {x : M} (hx : x ∈ Z.baseSet i) (v : StdSpace Unit) :
      frame i x hx v = (Z.localTriv i).symm x (stdLineEquiv v) :=
    (congrFun ((Z.localTriv i).symm_continuousLinearEquivAt_eq (R := ℝ) hx) _).trans
      ((Z.localTriv i).symmL_apply hx _)
  have clutchingFiberEquiv_frame (i : Bool) {x : M} (hx : x ∈ Z.baseSet i)
      (v : StdSpace Unit) : clutchingFiberEquiv φ k x (frame i x hx v) =
        (clutchingScalar φ k i (Z.indexAt x) x : ℂ) * stdLineEquiv v := by
    rw [frame_apply, clutchingFiberEquiv_localTriv_symm φ k i hx]
  -- The frames are symplectic.
  have frame_symplectic (i : Bool) {x : M} (hx : x ∈ Z.baseSet i) (v w : StdSpace Unit) :
      form.bilinFormAt x (frame i x hx v) (frame i x hx w) = stdForm Unit v w := by
    rw [ContMDiffTwoForm.bilinFormAt_apply,
      ContMDiffComplexStructure.compatibleForm_ofComplexModule_apply _
        (clutchingMetric_inner_I_smul φ k n), clutchingMetric_inner, clutchingFiberEquiv_smul,
      clutchingFiberEquiv_frame, clutchingFiberEquiv_frame, stdForm_eq_inner_stdLineEquiv,
      mul_left_comm, ← rotation_apply, ← rotation_apply, LinearIsometryEquiv.inner_map_map]
  -- The frames are continuous on total spaces.
  have frame_continuous (i : Bool) {S : Set M} (hS : S ⊆ Z.baseSet i) :
      Continuous fun q : S × StdSpace Unit ↦
        TotalSpace.mk' ℂ (q.1 : M) (frame i q.1 (hS q.1.property) q.2) := by
    refine ((Z.localTriv i).continuousOn_symm.comp_continuous
      ((continuous_subtypeVal.comp continuous_fst).prodMk
        (stdLineEquiv.continuous.comp continuous_snd)) fun q ↦ ⟨hS q.1.property, trivial⟩).congr
      fun q ↦ ?_
    simp only [Function.comp_apply, frame_apply]
  -- The transition loop `ζ ↦ ζ ^ k`, as a loop of symplectic `2 × 2` matrices.
  let Ψ : C(Circle, GLSymplectic Unit ℝ) :=
    ⟨fun ζ ↦ ofUnitary (detSection Unit () (ζ ^ k)),
      continuous_ofUnitary.comp ((continuous_detSection ()).comp (continuous_zpow k))⟩
  have hΨ (ζ : Circle) (v : StdSpace Unit) :
      stdLineEquiv (Matrix.toEuclideanLin ((Ψ ζ : GL (Unit ⊕ Unit) ℝ) :
        Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) ℝ) v) = (ζ : ℂ) ^ k * stdLineEquiv v := by
    have hm : ((Ψ ζ : GL (Unit ⊕ Unit) ℝ) : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) ℝ) =
        (Matrix.diagonal fun _ : Unit ↦ (ζ : ℂ) ^ k).realify := by
      simp only [Ψ, ContinuousMap.coe_mk, coe_ofUnitary, coe_detSection]
      congr 2
    rw [hm, stdLineEquiv_toEuclideanLin_realify]
  have hindex : maslovIndex Ψ.toBasedLoop = k := by
    rw [maslovIndex_def]
    refine Circle.degree_eq_of_sub_eq _ (θ := fun t ↦ 2 * Real.pi * k * t) (by fun_prop)
      (fun t ↦ ?_) (by simp only [Set.Icc.coe_one, Set.Icc.coe_zero]; ring)
    rw [Path.map_coe, Function.comp_apply, ContinuousMap.toBasedLoop_apply]
    simp only [Ψ, ContinuousMap.coe_mk, maslovPhase_ofUnitary, detCircle_detSection,
      unitToCircle_apply, ← Circle.exp_zsmul, zsmul_eq_mul]
    ring_nf
  rw [symplecticChernNumber_eq_sum_maslovIndex_clutching (φ := fun _ : Unit ↦ ψ)
    (Subsingleton.pairwise) (Φ := fun _ x ↦ frame true x (disc_clutchingDisc_subset φ k x.property))
    (Φout := fun x ↦ frame false x (discComplement_clutchingDisc_subset φ k x.property))
    (fun _ ↦ frame_continuous true (disc_clutchingDisc_subset φ k))
    (frame_continuous false (discComplement_clutchingDisc_subset φ k)) G hn
    (fun _ x ↦ frame_symplectic true _) (fun x ↦ frame_symplectic false _) (fun _ ↦ Ψ) ?_,
    Fintype.sum_unique, hindex]
  intro _ ζ v
  apply (clutchingFiberEquiv φ k _).injective
  rw [clutchingFiberEquiv_frame, clutchingFiberEquiv_frame, hΨ,
    ← clutchingScalar_mul φ k false true, clutchingScalar_false_true, clutchingPhase_boundaryCircle,
    Circle.coe_mul, Circle.coe_zpow]
  ring

end Bundle

end SymplecticGeometry

end
