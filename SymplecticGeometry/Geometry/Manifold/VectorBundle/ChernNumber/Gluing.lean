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
import SymplecticGeometry.Geometry.Manifold.ContMDiff.ExtendOverDisc
import SymplecticGeometry.Geometry.Manifold.VectorBundle.ChernNumber.DiscFrame
import SymplecticGeometry.Geometry.Manifold.Instances.SymplecticGroup

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
loops on the boundary circle have the same Maslov index (`nonempty_iso_of_maslovIndex_eq`). Over a
closed connected oriented surface, by the disc clutching formula, this is the case when their first
Chern numbers agree (`nonempty_iso_of_symplecticChernNumber_eq`).

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
* `SymplecticGeometry.Bundle.nonempty_iso_of_maslovIndex_eq`: two symplectic bundles with frames
  over a coordinate disc and over its complement whose transition loops have the same Maslov index
  are isomorphic.
* `SymplecticGeometry.Bundle.nonempty_iso_of_symplecticChernNumber_eq`: over a closed connected
  oriented surface, two symplectic bundles of the same rank with the same first Chern number are
  isomorphic.

## Proof

The disc clutching formula `symplecticChernNumber_eq_sum_maslovIndex_clutching`
(`ChernNumber/Clutching.lean`) is applied to one coordinate disc, `z ↦ φ (3 z / 4)`, whose closed
disc lies in the first chart and the complement of whose open disc lies in the second. The two
charts give frames there, read on the standard symplectic plane `StdSpace (Fin 1)` through
`(x, y) ↦ x + i y` (`StdSpace.equivComplex`). They are symplectic, since the coordinate changes
have modulus one, and on the boundary circle they differ by `ζ ↦ ζ ^ k`, the realification of a
loop of `1 × 1` unitary matrices (`circlePowLoop k`), whose Maslov index is `k`
(`maslovIndex_toBasedLoop_circlePowLoop`).

For `nonempty_iso_of_maslovIndex_eq`, let `Tₖ = Φₖ⁻¹ ∘ Φₖ'` be the transitions of the two
bundles, defined near the boundary circle, on the image of an annulus `1 - ε < ‖z‖ < 1 + ε` of the
chart. There `D = T₂ ∘ T₁⁻¹` is a smooth map into `Matrix.symplecticGroup κ ℝ`
(`Matrix.SymplecticGroup.contMDiffAt_iff_toEuclideanCLM`), and on the circle it is the loop
`Ψ₂ Ψ₁⁻¹`, of Maslov index `μ(Ψ₂) - μ(Ψ₁) = 0` by the product axiom
(`TauCeti.GLSymplectic.maslovIndex_toBasedLoop_mul`). So it is null-homotopic
(`TauCeti.GLSymplectic.nullhomotopic_of_maslovIndex_toBasedLoop_eq_zero`), and agrees near the
circle with a smooth map `g` on the disc of radius `1 + ε`
(`ContMDiffOn.exists_contMDiffOn_ball_eq_of_nullhomotopic`). Over the image `W` of that disc, the
frame `Φ₂ ∘ g` of the second bundle has transition `T₁` to `Φ₂'` near the circle
(`ContMDiffTwoForm.IsSymplecticFrameOn.precomp_of_contMDiffOn`). The frames `Φ₁` and `Φ₂ ∘ g`
over `W`, and `Φ₁'` and `Φ₂'` away from a smaller closed disc, then glue to an isomorphism
(`ContMDiffTwoForm.exists_pushforward_eq_of_frameTransition_eq`). For
`nonempty_iso_of_symplecticChernNumber_eq`, the frames come from
`ContMDiffTwoForm.IsNondegenerate.exists_isSymplecticFrameOn_disc_ofChart` and
`ContMDiffTwoForm.IsNondegenerate.exists_isSymplecticFrameOn_discComplement_ofChart`, and the disc
clutching formula turns equal Chern numbers into equal Maslov indices.

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
  rank with the same number are isomorphic, is `nonempty_iso_of_symplecticChernNumber_eq`.
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


/-! ### Isomorphisms from equal Maslov indices -/

section Iso

open Matrix TauCeti.GLSymplectic StdSpace ContMDiffTwoForm
open scoped ContDiff Matrix.Norms.Operator

/-- An open set that contains the boundary circle of a coordinate disc contains the image of an
annulus `1 - ε < ‖z‖ < 1 + ε` of the chart, for some `0 < ε ≤ 1 / 2`. -/
private theorem exists_image_annulus_subset {M : Type} [TopologicalSpace M] [T2Space M]
    {EM : Type} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [FiniteDimensional ℝ EM]
    [ChartedSpace EM M] {o : HomologicalOrientation M EM 2} (φ : CoordinateDisc o) {O : Set M}
    (hO : IsOpen O) (hφO : ∀ ζ, φ.boundaryCircle ζ ∈ O) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 2 ∧
      ∀ z : CoordinateDisc.ball, 1 - ε < ‖(z : ℂ)‖ → ‖(z : ℂ)‖ < 1 + ε → φ z ∈ O := by
  -- The points of the ball that `φ` sends into `O`, as an open set of `ℂ`, contain the circle.
  have hS : IsOpen (Subtype.val '' (φ ⁻¹' O) : Set ℂ) :=
    CoordinateDisc.ball.isOpen.isOpenMap_subtypeVal _ (hO.preimage φ.continuous)
  have hsph : Metric.sphere (0 : ℂ) 1 ⊆ Subtype.val '' (φ ⁻¹' O) := fun z hz ↦
    ⟨⟨z, CoordinateDisc.mem_ball_of_norm_le_one (mem_sphere_zero_iff_norm.1 hz).le⟩,
      by have h := hφO (show Circle from ⟨z, hz⟩); rwa [CoordinateDisc.boundaryCircle_apply] at h,
      rfl⟩
  obtain ⟨δ, hδ, hδS⟩ := (isCompact_sphere (0 : ℂ) 1).exists_thickening_subset_open hS hsph
  refine ⟨min δ (1 / 2), lt_min hδ one_half_pos, min_le_right _ _, fun z h₁ h₂ ↦ ?_⟩
  have hn : 0 < ‖(z : ℂ)‖ := by linarith [min_le_right δ (1 / 2)]
  -- `z` is within `δ` of the point `z / ‖z‖` of the circle.
  have hd : dist (z : ℂ) (z / ‖(z : ℂ)‖) < δ := by
    have he : (z : ℂ) - z / ‖(z : ℂ)‖ = (((‖(z : ℂ)‖ - 1) / ‖(z : ℂ)‖ : ℝ) : ℂ) * z := by
      have : (‖(z : ℂ)‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hn.ne'
      push_cast
      field_simp
    rw [dist_eq_norm, he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div,
      abs_of_pos hn, div_mul_cancel₀ _ hn.ne']
    have := min_le_left δ (1 / 2)
    exact abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
  obtain ⟨w, hw, hwz⟩ := hδS (Metric.mem_thickening_iff.2
    ⟨(z : ℂ) / ‖(z : ℂ)‖, by simp [hn.ne'], hd⟩)
  rwa [Subtype.val_injective hwz] at hw

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

/-- **Isomorphic bundles from equal Maslov indices.** Let `φ = CoordinateDisc.ofChart e hr hc he`
be the coordinate disc of a chart `e` of the smooth maximal atlas of a Hausdorff surface `M`, and
let `ω₁`, `ω₂` be smooth two-forms on smooth vector bundles `V₁`, `V₂` over `M`. For `k = 1, 2`,
let `Φₖ` be a symplectic frame of `ωₖ` for `stdForm κ` over an open set that contains the closed
disc of `φ`, `Φₖ'` one over an open set that contains the complement `discComplement` of its open
disc, and `Ψₖ` the loop of symplectic matrices with `Φₖ' = Φₖ ∘ Ψₖ` on the boundary circle. If
`Ψ₁` and `Ψ₂` have the same Maslov index, then `(V₁, ω₁)` and `(V₂, ω₂)` are isomorphic: some
fibrewise linear isomorphism `Ψ`, smooth on total spaces, carries `ω₁` to `ω₂`. -/
theorem nonempty_iso_of_maslovIndex_eq (hea : e ∈ IsManifold.maximalAtlas (𝓡 2) ∞ M)
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
  set ψ : ℂ → M := fun z ↦ e.symm (c + (r / 2) • Complex.orthonormalBasisOneI.repr z)
  have hψ (z : CoordinateDisc.ball) : ψ z = φ z := (CoordinateDisc.ofChart_apply e hr hc he z).symm
  have hdisj : Pairwise (Disjoint on fun _ : Unit ↦ φ.disc) := Subsingleton.pairwise
  -- The four frames are defined near the boundary circle; around it, on an annulus of the chart.
  set O := (U₁ ∩ U₁') ∩ (U₂ ∩ U₂')
  have hO : IsOpen O := (hU₁.inter hU₁').inter (hU₂.inter hU₂')
  have hφO (ζ : Circle) : φ.boundaryCircle ζ ∈ O :=
    have hd := φ.boundaryCircle_mem_disc ζ
    have hd' := boundaryCircle_mem_discComplement _ hdisj () ζ
    ⟨⟨hDU₁ hd, hDU₁' hd'⟩, hDU₂ hd, hDU₂' hd'⟩
  obtain ⟨ε, hε, hε2, hεO⟩ := exists_image_annulus_subset φ hO hφO
  -- The change of frame `D = T₂ ∘ T₁⁻¹`, from the transitions `Tₖ = Φₖ⁻¹ ∘ Φₖ'`, as a smooth map
  -- into the symplectic group on `O`.
  let D (x : M) : StdSpace κ ≃L[ℝ] StdSpace κ :=
    (frameTransition Φ₁ Φ₁' x).trans (frameTransition Φ₂' Φ₂ x)
  have hD : ContMDiffOn (𝓡 2) 𝓘(ℝ, StdSpace κ →L[ℝ] StdSpace κ) ∞
      (fun x ↦ (D x : StdSpace κ →L[ℝ] StdSpace κ)) O := by
    have hT₁ := ((h₁.mono fun x (hx : x ∈ O) ↦ hx.1.1).contMDiffOn_frameTransition
      (h₁'.mono fun x (hx : x ∈ O) ↦ hx.1.2) hO)
    have hT₂ := ((h₂'.mono fun x (hx : x ∈ O) ↦ hx.2.2).contMDiffOn_frameTransition
      (h₂.mono fun x (hx : x ∈ O) ↦ hx.2.1) hO)
    exact (hT₂.clm_comp hT₁).congr fun x _ ↦ (ContinuousLinearEquiv.comp_coe _ _).symm
  have hDσ (x : M) (hx : x ∈ O) (v w : StdSpace κ) : stdForm κ (D x v) (D x w) = stdForm κ v w := by
    have hT₁ := (h₁.mono fun x (hx : x ∈ O) ↦ hx.1.1).isSymplectomorphism_frameTransition
      (h₁'.mono fun x (hx : x ∈ O) ↦ hx.1.2) hx
    have hT₂ := (h₂'.mono fun x (hx : x ∈ O) ↦ hx.2.2).isSymplectomorphism_frameTransition
      (h₂.mono fun x (hx : x ∈ O) ↦ hx.2.1) hx
    exact (hT₂.apply _ _).trans (hT₁.apply v w)
  -- Tau Ceti's charts on the symplectic group are stated for the topology of the operator norm
  -- on matrices, which is the product topology (`Matrix.linftyOpTopologicalSpace_eq`), but not
  -- reducibly so.
  let : TopologicalSpace (Matrix (κ ⊕ κ) (κ ⊕ κ) ℝ) := Matrix.linftyOpTopologicalSpace _ _ _
  -- The symplectic matrix of `D x` for `x ∈ O`, and the identity elsewhere.
  classical
  let C (x : M) : symplecticGroup κ ℝ := if hx : x ∈ O then
      ⟨(toEuclideanCLM (𝕜 := ℝ)).symm (D x : StdSpace κ →L[ℝ] StdSpace κ),
        mem_symplecticGroup_iff_forall_stdForm.2 fun v w ↦ by
          rw [← toEuclideanCLM_apply, ← toEuclideanCLM_apply, StarAlgEquiv.apply_symm_apply]
          exact hDσ x hx v w⟩
    else 1
  have hC (x : M) (hx : x ∈ O) :
      toEuclideanCLM (𝕜 := ℝ) (C x : Matrix (κ ⊕ κ) (κ ⊕ κ) ℝ) = D x := by
    simp only [C, hx, dite_true, StarAlgEquiv.apply_symm_apply]
  -- The map `z ↦ C (ψ z)` is smooth on the annulus `A` of the chart.
  set A : Set ℂ := {z | 1 - ε < ‖z‖ ∧ ‖z‖ < 1 + ε}
  have hψO (z : ℂ) (hz : z ∈ A) : ψ z ∈ O := by
    have hb : z ∈ CoordinateDisc.ball := CoordinateDisc.mem_ball_iff.2 (by linarith [hz.2])
    rw [show z = ((⟨z, hb⟩ : CoordinateDisc.ball) : ℂ) from rfl, hψ]
    exact hεO _ hz.1 hz.2
  have hf : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, TauCeti.Lie.SymplecticGroupModel κ ℝ)
      ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z ↦ C (ψ z)) A := by
    have hA : IsOpen A :=
      (isOpen_lt continuous_const continuous_norm).inter
        (isOpen_lt continuous_norm continuous_const)
    intro z hz
    refine ContMDiffAt.contMDiffWithinAt
      ((Matrix.SymplecticGroup.contMDiffAt_iff_toEuclideanCLM (κ := κ)
        (f := fun z ↦ C (ψ z)) (x := z)).2 ?_)
    have hψz : ContMDiffAt 𝓘(ℝ, ℂ) (𝓡 2) ∞ ψ z :=
      (CoordinateDisc.contMDiffOn_ofChart e hr hc hea).contMDiffAt
      (Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.2 (by linarith [hz.2])))
    refine ((hD.contMDiffAt (hO.mem_nhds (hψO z hz))).comp z hψz).congr_of_eventuallyEq ?_
    filter_upwards [hA.mem_nhds hz] with y hy
    exact hC _ (hψO y hy)
  -- On the boundary circle, `D` is the loop `Ψ₂ Ψ₁⁻¹`, of Maslov index `0`.
  have hT₁ (ζ : Circle) (v : StdSpace κ) : frameTransition Φ₁' Φ₁ (φ.boundaryCircle ζ) v =
      toEuclideanCLM (𝕜 := ℝ) ((Ψ₁ ζ : GL (κ ⊕ κ) ℝ) : Matrix (κ ⊕ κ) (κ ⊕ κ) ℝ) v := by
    rw [frameTransition_apply, hΨ₁, ContinuousLinearEquiv.symm_apply_apply, toEuclideanCLM_apply]
  have hT₂ (ζ : Circle) (v : StdSpace κ) : frameTransition Φ₂' Φ₂ (φ.boundaryCircle ζ) v =
      toEuclideanCLM (𝕜 := ℝ) ((Ψ₂ ζ : GL (κ ⊕ κ) ℝ) : Matrix (κ ⊕ κ) (κ ⊕ κ) ℝ) v := by
    rw [frameTransition_apply, hΨ₂, ContinuousLinearEquiv.symm_apply_apply, toEuclideanCLM_apply]
  let γ : C(Circle, symplecticGroup κ ℝ) :=
    (ContinuousMap.mk _ (symplecticGroupContinuousMulEquiv κ ℝ).symm.continuous).comp (Ψ₂ * Ψ₁⁻¹)
  have hγ (ζ : Circle) : γ ζ = C (ψ ζ) := by
    have hb : ψ ζ = φ.boundaryCircle ζ := by rw [CoordinateDisc.boundaryCircle_apply, ← hψ]
    have hγζ : ((γ ζ : symplecticGroup κ ℝ) : Matrix (κ ⊕ κ) (κ ⊕ κ) ℝ) =
        (((Ψ₂ * Ψ₁⁻¹) ζ : GLSymplectic κ ℝ) : GL (κ ⊕ κ) ℝ) :=
      coe_symplecticGroupContinuousMulEquiv_symm κ ℝ _
    have hmul : ((((Ψ₂ * Ψ₁⁻¹) ζ : GLSymplectic κ ℝ) : GL (κ ⊕ κ) ℝ) :
        Matrix (κ ⊕ κ) (κ ⊕ κ) ℝ) * ((Ψ₁ ζ : GL (κ ⊕ κ) ℝ) : Matrix (κ ⊕ κ) (κ ⊕ κ) ℝ) =
        ((Ψ₂ ζ : GL (κ ⊕ κ) ℝ) : Matrix (κ ⊕ κ) (κ ⊕ κ) ℝ) := by
      rw [← Units.val_mul, ← Subgroup.coe_mul, ContinuousMap.mul_apply, ContinuousMap.inv_apply,
        inv_mul_cancel_right]
    apply Subtype.ext
    refine EquivLike.injective (toEuclideanCLM (n := κ ⊕ κ) (𝕜 := ℝ)) ?_
    rw [hb, hC _ (hφO ζ), hγζ]
    ext1 v
    -- Write `v = T₁ w`, so that `D v = T₂ w`.
    obtain ⟨w, rfl⟩ := (frameTransition Φ₁' Φ₁ (φ.boundaryCircle ζ)).surjective v
    have hDw : D (φ.boundaryCircle ζ) (frameTransition Φ₁' Φ₁ (φ.boundaryCircle ζ) w) =
        frameTransition Φ₂' Φ₂ (φ.boundaryCircle ζ) w := by
      simp [D, frameTransition_apply]
    rw [ContinuousLinearEquiv.coe_coe, hDw, hT₂, hT₁, ← hmul, map_mul,
      mul_apply_eq_comp]
  have hγ0 : γ.Nullhomotopic := by
    refine ContinuousMap.Nullhomotopic.comp_right
      (nullhomotopic_of_maslovIndex_toBasedLoop_eq_zero ?_) _
    have h := maslovIndex_toBasedLoop_mul (Ψ₂ * Ψ₁⁻¹) Ψ₁
    rw [inv_mul_cancel_right] at h
    linarith
  -- Extend `C ∘ ψ` from the annulus to a smooth map `g` on the disc of radius `1 + ε`.
  obtain ⟨g, hg, hgf⟩ := ContMDiffOn.exists_contMDiffOn_ball_eq_of_nullhomotopic (n := ⊤)
    (a := 1 - ε) (a' := 1 - ε / 2) (b := 1 + ε) (by linarith) (by linarith) (by linarith)
    (by linarith) hf γ hγ hγ0
  -- Change the frame `Φ₂` over the image `W` of that disc by `g`.
  let P (x : M) : StdSpace κ ≃L[ℝ] StdSpace κ :=
    Matrix.GeneralLinearGroup.ofEuclideanCLE.symm (ofSymplecticGroup κ ℝ (g (φ.coord x)))
  have hP (x : M) : (P x : StdSpace κ →L[ℝ] StdSpace κ) =
      toEuclideanCLM (𝕜 := ℝ) (g (φ.coord x) : Matrix (κ ⊕ κ) (κ ⊕ κ) ℝ) := by
    simp only [P, Matrix.GeneralLinearGroup.ofEuclideanCLE_symm_apply, coe_toEuclideanCLE,
      coe_ofSymplecticGroup]
  set W := φ '' {z | ‖(z : ℂ)‖ < 1 + ε}
  have hW : IsOpen W :=
    φ.isOpenEmbedding.isOpenMap _ (isOpen_lt continuous_subtypeVal.norm continuous_const)
  have hWU : W ⊆ U₁ ∩ U₂ := by
    rintro _ ⟨z, hz, rfl⟩
    by_cases h : ‖(z : ℂ)‖ ≤ 1
    · exact ⟨hDU₁ (φ.apply_mem_disc_iff.2 h), hDU₂ (φ.apply_mem_disc_iff.2 h)⟩
    · have := hεO z (by linarith [not_le.1 h]) hz
      exact ⟨this.1.1, this.2.1⟩
  have hPs : ω₂.IsSymplecticFrameOn (stdForm κ) W fun x ↦ (P x).trans (Φ₂ x) := by
    refine (h₂.mono fun x hx ↦ (hWU hx).2).precomp_of_contMDiffOn ?_ fun x _ ↦ ?_
    · have hcoord := CoordinateDisc.contMDiffOn_coord_ofChart e hr hc he hea
      refine ContMDiffOn.congr ?_ fun x _ ↦ hP x
      refine (Matrix.SymplecticGroup.contMDiff_toEuclideanCLM (κ := κ)).comp_contMDiffOn
        (hg.comp (hcoord.mono ?_) ?_)
      · rintro _ ⟨z, -, rfl⟩
        exact Set.mem_range_self z
      · rintro _ ⟨z, hz, rfl⟩
        rw [Set.mem_preimage, CoordinateDisc.coord_apply]
        exact mem_ball_zero_iff.2 hz
    · refine TauCeti.SymplecticForm.isSymplectomorphism_iff.2 fun v w ↦ ?_
      have := mem_symplecticGroup_iff_forall_stdForm.1 (g (φ.coord x)).property v w
      rwa [← toEuclideanCLM_apply, ← toEuclideanCLM_apply, ← hP] at this
  -- Away from a smaller closed disc, keep the frames `Φ₁'` and `Φ₂'`, and glue.
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
  -- On the overlap, `g = C`, so the new frame has the transition of the first bundle.
  have htrans : ∀ x ∈ W ∩ U', frameTransition Φ₁' Φ₁ x =
      frameTransition Φ₂' (fun x ↦ (P x).trans (Φ₂ x)) x := by
    rintro x ⟨⟨z, hz, rfl⟩, -, hxz⟩
    have hz' : 1 - ε / 2 < ‖(z : ℂ)‖ := not_le.1 fun h ↦ hxz ⟨z, h, rfl⟩
    have hgz : g (φ.coord (φ z)) = C (φ z) := by
      rw [CoordinateDisc.coord_apply, hgf z hz'.le hz, hψ]
    have hPx (y : StdSpace κ) : P (φ z) y = D (φ z) y := by
      rw [← ContinuousLinearEquiv.coe_coe, hP, hgz, hC _ (hεO z (by linarith) hz),
        ContinuousLinearEquiv.coe_coe]
    refine ContinuousLinearEquiv.ext (funext fun v ↦ ?_)
    rw [frameTransition_apply, frameTransition_apply, ContinuousLinearEquiv.eq_symm_apply,
      ContinuousLinearEquiv.trans_apply, hPx]
    simp [D, frameTransition_apply]
  obtain ⟨Ψ, hΨ, hpush, -, -⟩ := exists_pushforward_eq_of_frameTransition_eq
    (h₁.mono fun x hx ↦ (hWU hx).1) (h₁'.mono fun x (hx : x ∈ U') ↦ hx.1.1) hPs
    (h₂'.mono fun x (hx : x ∈ U') ↦ hx.1.2) hW hU' hcover htrans
  exact ⟨Ψ, hΨ, hpush⟩

omit [IsManifold (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) M] [T2Space M] [DecidableEq κ]
  [FiniteDimensional ℝ F₁] in
/-- A symplectic frame over `U` restricts to a continuous frame over a subset `S` of `U`, in the
form of the clutching formula. -/
private theorem ContMDiffTwoForm.IsSymplecticFrameOn.continuous_restrict {U S : Set M}
    {Φ : ∀ x, StdSpace κ ≃L[ℝ] V₁ x} (h : ω₁.IsSymplecticFrameOn (stdForm κ) U Φ) (hS : S ⊆ U) :
    Continuous fun q : S × StdSpace κ ↦ TotalSpace.mk' F₁ (q.1 : M) (Φ q.1 q.2) :=
  h.contMDiffOn.continuousOn.comp_continuous
    ((continuous_subtypeVal.comp continuous_fst).prodMk continuous_snd)
    fun q ↦ ⟨hS q.1.property, Set.mem_univ _⟩

omit [IsManifold (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) M] [T2Space M] [FiniteDimensional ℝ F₁] in
/-- Two symplectic frames over open sets that contain a loop `γ` of `M` differ along `γ` by a
continuous loop of symplectic matrices. -/
private theorem exists_frameTransition_loop {U U' : Set M} (hU : IsOpen U) (hU' : IsOpen U')
    {Φ Φ' : ∀ x, StdSpace κ ≃L[ℝ] V₁ x} (h : ω₁.IsSymplecticFrameOn (stdForm κ) U Φ)
    (h' : ω₁.IsSymplecticFrameOn (stdForm κ) U' Φ') (γ : C(Circle, M))
    (hγ : ∀ ζ, γ ζ ∈ U ∩ U') :
    ∃ Ψ : C(Circle, GLSymplectic κ ℝ), ∀ ζ v,
      Φ' (γ ζ) v = Φ (γ ζ) (toEuclideanLin (Ψ ζ : GL (κ ⊕ κ) ℝ) v) := by
  have hT : Continuous fun ζ ↦ (frameTransition Φ' Φ (γ ζ) : StdSpace κ →L[ℝ] StdSpace κ) :=
    ((h'.mono Set.inter_subset_right).contMDiffOn_frameTransition (h.mono Set.inter_subset_left)
      (hU.inter hU')).continuousOn.comp_continuous γ.continuous hγ
  have hmem (ζ : Circle) :
      GeneralLinearGroup.ofEuclideanCLE (frameTransition Φ' Φ (γ ζ)) ∈ GLSymplectic κ ℝ := by
    rw [mem_GLSymplectic_iff_isSymplectomorphism, GeneralLinearGroup.toEuclideanCLE_ofEuclideanCLE]
    exact (h'.mono Set.inter_subset_right).isSymplectomorphism_frameTransition
      (h.mono Set.inter_subset_left) (hγ ζ)
  refine ⟨⟨fun ζ ↦ ⟨_, hmem ζ⟩, (GeneralLinearGroup.continuous_ofEuclideanCLE hT).subtype_mk _⟩,
    fun ζ v ↦ ?_⟩
  simp only [ContinuousMap.coe_mk]
  rw [← toEuclideanCLM_apply, GeneralLinearGroup.toEuclideanCLM_ofEuclideanCLE,
    ContinuousLinearEquiv.coe_coe, frameTransition_apply, ContinuousLinearEquiv.apply_symm_apply]

omit [DecidableEq κ] in
/-- **Isomorphic bundles from equal first Chern numbers.** Let `ω₁`, `ω₂` be nondegenerate smooth
two-forms on smooth vector bundles `V₁`, `V₂` of the same rank `2 |κ|` over a closed connected
surface `M` with a smooth orientation `o`. If their first Chern numbers `symplecticChernNumber`
agree, then `(V₁, ω₁)` and `(V₂, ω₂)` are isomorphic: some fibrewise linear isomorphism `Ψ`,
smooth on total spaces, carries `ω₁` to `ω₂`. -/
theorem nonempty_iso_of_symplecticChernNumber_eq [CompactSpace M] [ConnectedSpace M]
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
  obtain ⟨Ψ₁, hΨ₁⟩ := exists_frameTransition_loop hU₁ hU₁' h₁ h₁' _ (hbc hD₁ hD₁')
  obtain ⟨Ψ₂, hΨ₂⟩ := exists_frameTransition_loop (V₁ := V₂) hU₂ hU₂' h₂ h₂' _ (hbc hD₂ hD₂')
  refine nonempty_iso_of_maslovIndex_eq (hea ()) (hr ()) (hc ()) (he ()) hU₁ hU₁' hU₂ hU₂' hD₁
    hD₂ hD₁' hD₂' h₁ h₁' h₂ h₂' Ψ₁ Ψ₂ hΨ₁ hΨ₂ ?_
  -- By the clutching formula, the Maslov indices are the Chern numbers.
  have hc₁ := symplecticChernNumber_eq_sum_maslovIndex_clutching hdisj
    (Φ := fun _ x ↦ Φ₁ x) (Φout := fun x ↦ Φ₁' x) (fun _ ↦ h₁.continuous_restrict hD₁)
    (h₁'.continuous_restrict hD₁') G₁ finrank_euclideanSpace_fin
    (fun _ x ↦ h₁.map_bilinFormAt x (hD₁ x.property))
    (fun x ↦ h₁'.map_bilinFormAt x (hD₁' x.property)) (fun _ ↦ Ψ₁) fun _ ↦ hΨ₁
  have hc₂ := symplecticChernNumber_eq_sum_maslovIndex_clutching hdisj
    (Φ := fun _ x ↦ Φ₂ x) (Φout := fun x ↦ Φ₂' x)
    (fun _ ↦ ContMDiffTwoForm.IsSymplecticFrameOn.continuous_restrict (V₁ := V₂) h₂ hD₂)
    (ContMDiffTwoForm.IsSymplecticFrameOn.continuous_restrict (V₁ := V₂) h₂' hD₂') G₂
    finrank_euclideanSpace_fin
    (fun _ x ↦ h₂.map_bilinFormAt x (hD₂ x.property))
    (fun x ↦ h₂'.map_bilinFormAt x (hD₂' x.property)) (fun _ ↦ Ψ₂) fun _ ↦ hΨ₂
  rw [hc₁, hc₂, Fintype.sum_unique, Fintype.sum_unique] at h
  exact h

end Iso

end Bundle

end SymplecticGeometry

end
