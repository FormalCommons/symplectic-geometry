/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.VectorBundle.ChernNumber.UnitSection
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Hermitian.CircleBundle
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import SymplecticGeometry.Analysis.SpecialFunctions.Complex.CircleLog
import SymplecticGeometry.Geometry.Manifold.VectorBundle.Section.Generic
import SymplecticGeometry.Topology.Circle.FreeLoop
import TauCeti.Analysis.SpecialFunctions.Complex.Arg
import TauCeti.Geometry.Manifold.Algebra.LieGroup
import TauCeti.Geometry.Manifold.VectorBundle.Section.FiniteSpan

/-!
# Unit sections of a Hermitian line bundle with transitions `(z / ‖z‖) ^ k`

Let `M` be a closed smooth surface with an orientation `o`, and `V` a smooth Hermitian line bundle
over `M`, with circle bundle `P = TauCeti.OrthonormalFrameBundle.Fiber ℂ F V ℂ` of unitary
frames (`Geometry/Manifold/VectorBundle/Hermitian/CircleBundle.lean`). This file proves that `V`
has unit sections whose transitions on coordinate discs are exactly `(z / ‖z‖) ^ k`
(`SymplecticGeometry.Bundle.exists_coordinateDisc_unitSection_eq_exp_arg_zpow_smul`): there are
finitely many coordinate discs `φ i = CoordinateDisc.ofChart (e i) …`, from smooth charts that
preserve orientation, with pairwise disjoint images, integers `k i`, sections `σ i` of `P` smooth
on the image of `φ i`, and a section `σout` of `P` smooth off the centres `φ i 0`, such that
`σout (φ i z) = σ i (φ i z) • (z / ‖z‖) ^ k i` for `0 < ‖z‖ < 1`. Then `∑ i, k i` is the first
Chern number of `V`, by `SymplecticGeometry.Bundle.chernNumber_eq_sum_of_collar_eq_zpow_smul`.

The construction:

* a smooth section `s` of `V` with finitely many zeros, a linear combination of a finite spanning
  family (Tau Ceti's `TauCeti.exists_fin_spanning_contMDiffSection` and
  `ContMDiffSection.exists_mem_span_isClosed_isDiscrete_zero`); its zero set is closed and
  discrete in a compact space;
* disjoint oriented coordinate discs `φ i` about the zeros, each inside the domain of a smooth
  local unit section `σ i`
  (`SymplecticGeometry.CoordinateDisc.exists_ofChart_pairwise_disjoint`,
  `SymplecticGeometry.Bundle.exists_contMDiffOn_circleFiber`);
* off the zeros, the unit section `ν = s / ‖s‖`
  (`SymplecticGeometry.Bundle.contMDiffOn_normalizedFrame`), which on the punctured `i`-th disc is
  `σ i` acted on by a smooth map `w i` to the circle (Tau Ceti's `ContMDiffOn.division`);
* the normal form of `w i` (`Circle.exists_contMDiffOn_mul_eq_exp_arg_zpow`): with `k i` the
  degree of `w i` on the unit circle, `w i * (z / ‖z‖) ^ (-k i)` has degree `0`, so it is
  `exp (i h)` for a smooth real `h` (`Circle.exists_contDiffOn_exp_eq_of_circleDegree_eq_zero`),
  and multiplying `w i` by `c i = exp (-i χ h)`, for a radial cut-off `χ` equal to `1` on the unit
  disc and to `0` from radius `3 / 2` on, makes it `(z / ‖z‖) ^ k i` on the punctured unit disc
  without changing it near the edge of the disc;
* `σout = ν • ∏ i, c i`, with `c i` read through the inverse of `φ i` and extended by `1`.

## Main results

* `Circle.contMDiffOn_exp_arg`: the direction `z ↦ z / ‖z‖ = exp (i arg z)` is smooth on
  `ℂ \ {0}`.
* `Circle.exists_contMDiffOn_mul_eq_exp_arg_zpow`: a smooth circle-valued map on a punctured
  disc agrees with `(z / ‖z‖) ^ k` near the centre after multiplication by a smooth map that is
  `1` near the edge.
* `SymplecticGeometry.Bundle.exists_coordinateDisc_unitSection_eq_exp_arg_zpow_smul`: unit
  sections over coordinate discs and off their centres with transitions `(z / ‖z‖) ^ k i`, whose
  sum is the first Chern number.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.7
  (the first Chern number of a line bundle over a surface from the transitions of unitary
  trivializations over discs and over their complement).
-/

public section

noncomputable section

open Bundle Complex Function Module MulOpposite Set TauCeti TauCeti.OrthonormalFrameBundle
  TauCeti.PrincipalBundle
open scoped Manifold ContDiff

namespace Circle

attribute [local instance] finrank_real_complex_fact'

/-- The direction `z / ‖z‖ = exp (i arg z)` is a smooth map from `ℂ \ {0}` to the circle. -/
theorem contMDiffOn_exp_arg {n : ℕ∞ω} :
    ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 1) n (fun z : ℂ ↦ exp (arg z)) {0}ᶜ := by
  refine ContMDiffOn.of_coe_sphere (E := ℂ) (contMDiffOn_iff_contDiffOn.2 ?_)
  refine (contDiffOn_div_norm_pow 1).congr fun z hz ↦ ?_
  simp [coe_exp, exp_arg_mul_I (show z ≠ 0 from hz)]

/-- **Normal form of a smooth circle-valued map on a punctured disc.** Let `0 < r₁ < r₂` and
`r₁ < b`, and let `w : ℂ → S¹` be smooth on the punctured disc `0 < ‖z‖ < b`. Then there are an
integer `k` and a map `c : ℂ → S¹`, smooth on the punctured disc and equal to `1` where
`r₂ ≤ ‖z‖`, such that `w z * c z = (z / ‖z‖) ^ k` (written `exp (i arg z) ^ k`) whenever
`0 < ‖z‖ ≤ r₁`. -/
theorem exists_contMDiffOn_mul_eq_exp_arg_zpow {r₁ r₂ b : ℝ} (h₁ : 0 < r₁) (h₁₂ : r₁ < r₂)
    (h₁b : r₁ < b) {w : ℂ → Circle}
    (hw : ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 1) ∞ w {z | 0 < ‖z‖ ∧ ‖z‖ < b}) :
    ∃ (k : ℤ) (c : ℂ → Circle), ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 1) ∞ c {z | 0 < ‖z‖ ∧ ‖z‖ < b} ∧
      (∀ z, r₂ ≤ ‖z‖ → c z = 1) ∧
      ∀ z, 0 < ‖z‖ → ‖z‖ ≤ r₁ → w z * c z = exp (arg z) ^ k := by
  have hmem (ζ : Circle) : ((r₁ : ℂ) * ζ) ∈ {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < b} := by
    simp [abs_of_pos h₁, h₁.ne', h₁b]
  -- the loop of `w` on the circle of radius `r₁`, and its degree `k`
  let f : C(Circle, Circle) := ⟨fun ζ ↦ w (r₁ * ζ), hw.continuousOn.comp_continuous
    (continuous_const.mul continuous_subtypeVal) hmem⟩
  set k := f.circleDegree
  -- `v = w / (z / ‖z‖) ^ k` has degree `0`, so it has a smooth logarithm `h`
  let v : ℂ → Circle := fun z ↦ w z * (exp (arg z) ^ k)⁻¹
  have hv : ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 1) ∞ v {z | 0 < ‖z‖ ∧ ‖z‖ < b} :=
    hw.mul (((TauCeti.contMDiff_zpow k).comp_contMDiffOn
      (contMDiffOn_exp_arg.mono (t := {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < b})
        fun z hz ↦ norm_pos_iff.1 hz.1)).inv)
  let g : C(Circle, Circle) := f * (⟨(· ^ k), continuous_zpow k⟩ : C(Circle, Circle))⁻¹
  have hg (ζ : Circle) : g ζ = v (r₁ * ζ) := by
    simp [g, v, f, arg_ofReal_mul h₁, exp_arg]
  obtain ⟨h, hh, hvh⟩ := exists_contDiffOn_exp_eq_of_circleDegree_eq_zero le_rfl h₁ h₁b hv g hg
    (by simp [g, k])
  -- `c = exp (-i χ h)` for a radial cut-off `χ`, equal to `1` on `‖z‖ ≤ r₁` and `0` on `r₂ ≤ ‖z‖`
  let χ : ContDiffBump (0 : ℂ) := ⟨r₁, r₂, h₁, h₁₂⟩
  refine ⟨k, fun z ↦ exp (-(χ z * h z)), contMDiff_circleExp.comp_contMDiffOn
    ((χ.contDiff.contDiffOn.mul hh).neg).contMDiffOn, fun z hz ↦ ?_, fun z hz hz₁ ↦ ?_⟩
  · simp [χ.zero_of_le_dist (by simpa using hz)]
  · dsimp only
    rw [χ.one_of_mem_closedBall (by simpa using hz₁), one_mul, exp_neg, ← hvh z hz
      (hz₁.trans_lt h₁b)]
    simp [v]

end Circle

namespace SymplecticGeometry

namespace Bundle

section Disc

variable {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (𝓡 2) ∞ M] [T2Space M]

/-- The coordinate disc of a chart `e` of the maximal smooth atlas is the restriction to the ball
of a map `ψ : ℂ → M` that is smooth on the ball of radius `2`, and it has an inverse `B` that is
smooth on the source of `e`. -/
private theorem exists_contMDiffOn_ofChart {o : Manifold.Orientation (𝓡 2) M (Fin 2)}
    {e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))}
    (hatlas : e ∈ IsManifold.maximalAtlas (𝓡 2) ∞ M) {r : ℝ} (hr : 0 < r)
    (hc : Metric.ball 0 r ⊆ e.target)
    (he : ∀ y ∈ e.source,
      o.IsOrientationPreservingAt (Manifold.Orientation.euclideanSpace 2) e y) :
    ∃ (ψ : ℂ → M) (B : M → ℂ), ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 2) ∞ ψ (Metric.ball 0 2) ∧
      ContMDiffOn (𝓡 2) 𝓘(ℝ, ℂ) ∞ B e.source ∧
      ∀ z : CoordinateDisc.ball, CoordinateDisc.ofChart e hr hc he z = ψ z ∧
        B (CoordinateDisc.ofChart e hr hc he z) = z := by
  -- `ψ = e.symm ∘ A` and `B = D ∘ e`, for the linear maps `A z = (r / 2) (re z, im z)` and
  -- `D = A⁻¹`
  let A : ℂ →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
    (r / 2) • (Complex.orthonormalBasisOneI.repr.toContinuousLinearEquiv :
      ℂ →L[ℝ] EuclideanSpace ℝ (Fin 2))
  let D : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℂ :=
    (r / 2)⁻¹ • (Complex.orthonormalBasisOneI.repr.symm.toContinuousLinearEquiv :
      EuclideanSpace ℝ (Fin 2) →L[ℝ] ℂ)
  have hDA (z : ℂ) : D (A z) = z := by
    have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    simp [D, A]
    field_simp
  have hA {z : ℂ} (hz : ‖z‖ < 2) : A z ∈ e.target := by
    simpa [A] using hc (CoordinateDisc.add_smul_orthonormalBasisOneI_repr_mem_ball 0 hr
      ⟨z, CoordinateDisc.mem_ball_iff.2 hz⟩)
  have hψ (z : CoordinateDisc.ball) : CoordinateDisc.ofChart e hr hc he z = e.symm (A z) := by
    simp [A]
  refine ⟨fun z ↦ e.symm (A z), fun x ↦ D (e x),
    (contMDiffOn_symm_of_mem_maximalAtlas hatlas).comp A.contMDiff.contMDiffOn
      fun z hz ↦ hA (by simpa using hz),
    D.contMDiff.comp_contMDiffOn (contMDiffOn_of_mem_maximalAtlas hatlas),
    fun z ↦ ⟨hψ z, ?_⟩⟩
  rw [hψ]
  dsimp only
  rw [e.right_inv (hA (CoordinateDisc.mem_ball_iff.1 z.property)), hDA]

omit [IsManifold (𝓡 2) ∞ M] in
open scoped Classical in
/-- Let `φ` be a coordinate disc, `B` a smooth inverse of `φ` on its image, and `c : ℂ → S¹`
smooth on the punctured ball `0 < ‖z‖ < 2` and equal to `1` from radius `3 / 2` on. Then the
map equal to `c ∘ B` on the image of `φ` and to `1` off it is smooth off the centre `φ 0`. -/
private theorem contMDiffAt_ite_mem_range
    {o : HomologicalOrientation M (EuclideanSpace ℝ (Fin 2)) 2} (φ : CoordinateDisc o)
    {B : M → ℂ} (hB : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℂ) ∞ B (range φ)) (hBφ : ∀ z, B (φ z) = z)
    {c : ℂ → Circle} (hc : ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 1) ∞ c {z | 0 < ‖z‖ ∧ ‖z‖ < 2})
    (hc1 : ∀ z, 3 / 2 ≤ ‖z‖ → c z = 1) {x : M} (hx : x ≠ φ 0) :
    ContMDiffAt (𝓡 2) (𝓡 1) ∞ (fun y ↦ if y ∈ range φ then c (B y) else 1) x := by
  by_cases hxφ : x ∈ range φ
  · -- on the punctured image, the map is `c ∘ B`
    set W := range φ \ {φ 0}
    have hW : IsOpen W := φ.isOpenEmbedding.isOpen_range.sdiff isClosed_singleton
    have hBW : MapsTo B W {z | 0 < ‖z‖ ∧ ‖z‖ < 2} := by
      rintro _ ⟨⟨z, rfl⟩, hz⟩
      rw [mem_ofPred_eq, hBφ]
      refine ⟨norm_pos_iff.2 fun h ↦ hz ?_, CoordinateDisc.mem_ball_iff.1 z.property⟩
      rw [show z = 0 from Subtype.ext h]
      rfl
    exact ((hc.comp (hB.mono sdiff_subset) hBW).congr fun y (hy : y ∈ W) ↦
      ite_eq_left hy.1).contMDiffAt (hW.mem_nhds ⟨hxφ, hx⟩)
  · -- off the image of the closed disc of radius `3 / 2`, the map is `1`
    have hK : IsClosed (φ '' {z | ‖(z : ℂ)‖ ≤ 3 / 2}) :=
      (φ.isCompact_image_closedBall (by norm_num)).isClosed
    refine (contMDiffAt_const (c := (1 : Circle))).congr_of_eventuallyEq ?_
    filter_upwards [hK.isOpen_compl.mem_nhds fun h ↦ hxφ (image_subset_range _ _ h)] with y hy
    by_cases hyφ : y ∈ range φ
    · obtain ⟨z, rfl⟩ := hyφ
      rw [ite_eq_left (mem_range_self z), hBφ]
      exact hc1 z (not_le.1 fun h ↦ hy ⟨z, h, rfl⟩).le
    · exact ite_eq_right hyφ

end Disc

section Surface

attribute [local instance] finrank_real_complex_fact'

variable {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (𝓡 2) ∞ M] [T2Space M] [CompactSpace M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [Fact (finrank ℂ F = 1)]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)]
  [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℂ F V]

local instance instVectorBundleRealStandardTransition : VectorBundle ℝ F V :=
  VectorBundle.restrictScalars ℝ ℂ F V

local instance : FiniteDimensional ℂ F := .of_fact_finrank_eq_succ 0

variable [ContMDiffVectorBundle ∞ F V (𝓡 2)] (g : ContMDiffRiemannianMetric (𝓡 2) ∞ F V)
  (hI : ∀ x (v w : V x), g.inner x (Complex.I • v) (Complex.I • w) = g.inner x v w)

/-- **Unit sections with transitions `(z / ‖z‖) ^ k` on coordinate discs.** Let `M` be a closed
smooth surface with an orientation `o`, and `V` a smooth complex line bundle over `M` with a
smooth Hermitian metric `g`. Then there are:

* a finite type `ι` and coordinate discs `φ i = CoordinateDisc.ofChart (e i) …` for
  `o.toHomologicalOrientation`, from charts `e i` of the maximal smooth atlas that preserve
  orientation on their source, with pairwise disjoint images;
* integers `k i`;
* sections `σ i` of the circle bundle of unitary frames of `V`, smooth on the image of `φ i`;
* a section `σout` of the circle bundle, smooth off the centres `φ i 0`,

such that `σout (φ i z) = σ i (φ i z) • (z / ‖z‖) ^ k i` whenever `0 < ‖z‖ < 1`, where
`z / ‖z‖` is written `Circle.exp (arg z)`, and `∑ i, k i` is the first Chern number of `V`. -/
theorem exists_coordinateDisc_unitSection_eq_exp_arg_zpow_smul
    (o : Manifold.Orientation (𝓡 2) M (Fin 2)) :
    letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
    letI : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
    letI : IsContinuousRiemannianBundle F V :=
      instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric
    haveI : ContMDiffFiberBundle ∞ Circle (Fiber ℂ F V ℂ) (𝓡 2) (𝓡 1) :=
      contMDiffFiberBundle_circleFiber g hI
    ∃ (ι : Type) (_ : Fintype ι) (e : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)))
      (r : ι → ℝ) (hr : ∀ i, 0 < r i) (hc : ∀ i, Metric.ball 0 (r i) ⊆ (e i).target)
      (he : ∀ i, ∀ y ∈ (e i).source,
        o.IsOrientationPreservingAt (Manifold.Orientation.euclideanSpace 2) (e i) y)
      (φ : ι → CoordinateDisc (o.toHomologicalOrientation finrank_euclideanSpace_fin)),
      (∀ i, φ i = CoordinateDisc.ofChart (e i) (hr i) (hc i) (he i)) ∧
      (∀ i, e i ∈ IsManifold.maximalAtlas (𝓡 2) ∞ M) ∧
      (Pairwise fun i j ↦ Disjoint (range (φ i)) (range (φ j))) ∧
      ∃ (k : ι → ℤ) (σ : ι → ∀ x, Fiber ℂ F V ℂ x) (σout : ∀ x, Fiber ℂ F V ℂ x),
        (∀ i, ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 1)) ∞
          (fun x ↦ ManifoldTotalSpace.homeomorph Circle (Fiber ℂ F V ℂ) ⟨x, σ i x⟩)
          (range (φ i))) ∧
        ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 1)) ∞
          (fun x ↦ ManifoldTotalSpace.homeomorph Circle (Fiber ℂ F V ℂ) ⟨x, σout x⟩)
          {x | ∀ i, x ≠ φ i 0} ∧
        (∀ i (z : CoordinateDisc.ball), 0 < ‖(z : ℂ)‖ → ‖(z : ℂ)‖ < 1 →
          σout (φ i z) = op (Circle.exp (arg z) ^ k i) • σ i (φ i z)) ∧
        ∑ i, k i = chernNumber (o.toHomologicalOrientation finrank_euclideanSpace_fin)
          finrank_euclideanSpace_fin F V := by
  classical
  let : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
  let : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
  let : IsContinuousRiemannianBundle F V :=
    instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric
  have : ContMDiffFiberBundle ∞ Circle (Fiber ℂ F V ℂ) (𝓡 2) (𝓡 1) :=
    contMDiffFiberBundle_circleFiber g hI
  have : SecondCountableTopology M :=
    ChartedSpace.secondCountable_of_sigmaCompact (EuclideanSpace ℝ (Fin 2)) M
  have : FiniteDimensional ℝ F := Module.Finite.trans ℂ F
  -- a smooth section `s` with finitely many zeros
  have hF : finrank ℝ F = 2 := by
    rw [← Module.finrank_mul_finrank ℝ ℂ F, Complex.finrank_real_complex,
      Fact.out (p := finrank ℂ F = 1)]
  obtain ⟨n, t, ht⟩ := exists_fin_spanning_contMDiffSection (I := 𝓡 2) (F := F) (V := V)
  obtain ⟨s, -, hsc, hsd⟩ := ContMDiffSection.exists_mem_span_isClosed_isDiscrete_zero
    (by rw [finrank_euclideanSpace_fin, hF]) t ht
  let ι : Type := {x | s x = 0}
  let : Fintype ι := (hsc.isCompact.finite hsd).fintype
  -- smooth unit sections `τ x` near each point, and oriented charts `e i` about the zeros
  choose U hUo hxU τ hτ using fun x : M ↦ exists_contMDiffOn_circleFiber (n := ∞) g hI x
  obtain ⟨e, r, hr, hc, he, hatlas, -, -, -, hφ0, -, -, hrU, hrdisj⟩ :=
    CoordinateDisc.exists_ofChart_pairwise_disjoint o (x := fun i : ι ↦ (i : M))
      Subtype.val_injective (U := fun i ↦ U i) fun i ↦ (hUo i).mem_nhds (hxU i)
  set φ := fun i ↦ CoordinateDisc.ofChart (e i) (hr i) (hc i) (he i)
  choose ψ B hψs hBs hψB using fun i ↦ exists_contMDiffOn_ofChart (hatlas i) (hr i) (hc i) (he i)
  -- the unit section `ν = s / ‖s‖`, smooth off the zeros
  set ν : ∀ x, Fiber ℂ F V ℂ x := fun x ↦ normalizedFrame (F := F) (s x)
  have hν : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 1)) ∞
      (fun x ↦ ManifoldTotalSpace.homeomorph Circle (Fiber ℂ F V ℂ) ⟨x, ν x⟩) {x | s x ≠ 0} :=
    contMDiffOn_normalizedFrame g hI (b := id) hsc.isOpen_compl s.contMDiff.contMDiffOn
      fun x hx ↦ hx
  -- every zero of `s` is the centre of its disc, and `s` has no other zero on the discs
  have hzero {x : M} (hx : s x = 0) : x = φ ⟨x, hx⟩ 0 := (hφ0 ⟨x, hx⟩).symm
  have hne (i : ι) {z : CoordinateDisc.ball} (hz : z ≠ 0) : s (φ i z) ≠ 0 := fun h ↦ by
    have h0 := hzero h
    by_cases hij : (⟨φ i z, h⟩ : ι) = i
    · rw [hij] at h0
      exact hz ((φ i).injective h0)
    · exact (hrdisj hij).ne_of_mem (mem_range_self 0) (mem_range_self z) h0.symm
  -- the quotient `w i` of `ν` by `τ` on the punctured `i`-th disc, read on `ℂ`
  let w (i : ι) (z : ℂ) : Circle := division Circle (τ i (ψ i z)) (ν (ψ i z))
  have hw (i : ι) : ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 1) ∞ (w i) {z | 0 < ‖z‖ ∧ ‖z‖ < 2} := by
    refine (((hτ i).mono inter_subset_left).division (hν.mono inter_subset_right)).comp
      ((hψs i).mono fun z hz ↦ by simpa using hz.2) fun z hz ↦ ?_
    have hzφ := (hψB i ⟨z, CoordinateDisc.mem_ball_iff.2 hz.2⟩).1
    refine ⟨hzφ ▸ hrU i (mem_range_self _), ?_⟩
    rw [mem_ofPred_eq, ← hzφ]
    exact hne i fun h ↦ norm_pos_iff.1 hz.1 (congrArg Subtype.val h)
  -- the degrees `k i`, and the corrections `c i`, equal to `1` near the edge of the disc
  choose k c hcs hc1 hck using fun i ↦
    Circle.exists_contMDiffOn_mul_eq_exp_arg_zpow (r₁ := 1) (r₂ := 3 / 2) one_pos
      (by norm_num) (by norm_num) (hw i)
  -- the outer section `σout = ν • ∏ i, c i`, with `c i` extended by `1` off the `i`-th disc
  let G (i : ι) (x : M) : Circle := if x ∈ range (φ i) then c i (B i x) else 1
  have hGφ (i j : ι) (z : CoordinateDisc.ball) : G j (φ i z) = if j = i then c i z else 1 := by
    split_ifs with hji
    · subst hji
      exact (ite_eq_left (mem_range_self z)).trans (congrArg _ (hψB j z).2)
    · exact ite_eq_right fun h ↦ (hrdisj hji).ne_of_mem h (mem_range_self z) rfl
  let σout : ∀ x, Fiber ℂ F V ℂ x := fun x ↦ op (∏ i, G i x) • ν x
  have hσout : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 1)) ∞
      (fun x ↦ ManifoldTotalSpace.homeomorph Circle (Fiber ℂ F V ℂ) ⟨x, σout x⟩)
      {x | s x ≠ 0} :=
    hν.totalSpaceMk_smul fun x hx ↦ (ContMDiffAt.prod fun i _ ↦
      contMDiffAt_ite_mem_range (φ i)
        ((hBs i).mono (CoordinateDisc.range_ofChart_subset_source _ _ _ _))
        (fun z ↦ (hψB i z).2) (hcs i) (hc1 i) fun h ↦
          hx (by rw [h, hφ0 i]; exact i.property)).contMDiffWithinAt
  -- on the punctured unit disc, `σout = τ i • (z / ‖z‖) ^ k i`
  have hrel (i : ι) (z : CoordinateDisc.ball) (hz : 0 < ‖(z : ℂ)‖) (hz1 : ‖(z : ℂ)‖ < 1) :
      σout (φ i z) = op (Circle.exp (arg z) ^ k i) • τ i (φ i z) := by
    have hprod : ∏ j, G j (φ i z) = c i z := by simp [hGφ]
    have hdiv : division Circle (τ i (φ i z)) (ν (φ i z)) = w i z := by
      simp only [w]
      rw [(hψB i z).1]
    rw [← hck i z hz hz1.le, ← hdiv, ← hprod, op_mul, mul_smul, smul_division]
  have hcont {S : Set M} {σ : ∀ x, Fiber ℂ F V ℂ x} (h : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 1)) ∞
      (fun x ↦ ManifoldTotalSpace.homeomorph Circle (Fiber ℂ F V ℂ) ⟨x, σ x⟩) S) :
      ContinuousOn (fun x ↦ TotalSpace.mk' Circle x (σ x)) S :=
    ((ManifoldTotalSpace.homeomorph Circle (Fiber ℂ F V ℂ)).symm.continuous.comp_continuousOn
      h.continuousOn).congr fun x _ ↦ by simp
  refine ⟨ι, inferInstance, e, r, hr, hc, he, φ, fun i ↦ rfl, hatlas, hrdisj, k,
    fun i ↦ τ i, σout, fun i ↦ (hτ i).mono (hrU i),
    hσout.mono fun x hx h ↦ hx ⟨x, h⟩ (hzero h), hrel, ?_⟩
  refine (chernNumber_eq_sum_of_collar_eq_zpow_smul finrank_euclideanSpace_fin
    (fun i j h ↦ (hrdisj h).mono (φ i).disc_subset_range (φ j).disc_subset_range)
    zero_lt_one (fun i ↦ hcont ((hτ i).mono ((φ i).disc_subset_range.trans (hrU i))))
    (hcont (hσout.mono fun x hx h ↦ hx ?_)) k hrel).symm
  exact mem_iUnion.2 ⟨⟨x, h⟩, 0, by simp, (hzero h).symm⟩

end Surface

end Bundle

end SymplecticGeometry

end
