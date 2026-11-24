/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.VectorBundle.ChernNumber.UnitSection
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Hermitian.CircleBundle
public import SymplecticGeometry.Topology.VectorBundle.Complex.RestrictScalars
public import SymplecticGeometry.LinearAlgebra.Complex.FiniteDimensional
import SymplecticGeometry.Analysis.SpecialFunctions.Complex.CircleLog
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Integration.CoordinateDisc
import SymplecticGeometry.Geometry.Manifold.FiberBundle.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Section.Generic

/-!
# Unit sections of a Hermitian line bundle with transitions `(z / ‖z‖) ^ k`

Let `M` be a closed smooth surface with an orientation `o`, and `V` a smooth Hermitian line bundle
over `M`, with circle bundle `P = TauCeti.OrthonormalFrameBundle.Fiber ℂ F V ℂ` of unitary
frames (`Geometry/Manifold/VectorBundle/Hermitian/CircleBundle.lean`). This file proves that `V`
has unit sections whose transitions on coordinate discs are exactly `(z / ‖z‖) ^ k`
(`SymplecticGeometry.Bundle.exists_coordinateDisc_unitSection_eq_phase_zpow_smul`): there are
finitely many coordinate discs `φ i = CoordinateDisc.ofChart (e i) …`, from smooth charts that
preserve orientation, with pairwise disjoint images, integers `k i`, sections `σ i` of `P` smooth
on the image of `φ i`, and a section `σout` of `P` smooth off the centres `φ i 0`, such that
`σout (φ i z) = σ i (φ i z) • (φ i).phase (φ i z) ^ k i` for `0 < ‖z‖ < 1`, where the angular
coordinate `(φ i).phase (φ i z)` (`CoordinateDisc.phase`) is `z / ‖z‖`. Then `∑ i, k i` is
the first Chern number of `V`, by
`SymplecticGeometry.Bundle.chernNumber_eq_sum_of_collar_eq_zpow_smul`.

The construction:

* a smooth section `s` of `V` with finitely many zeros (Tau Ceti's
  `TauCeti.exists_contMDiffSection_regular_finite_zero_of_finrank_eq`);
* disjoint oriented coordinate discs `φ i` about the zeros, each inside the domain of a smooth
  local unit section `σ i`
  (`SymplecticGeometry.CoordinateDisc.exists_ofChart_pairwise_disjoint`,
  `SymplecticGeometry.Bundle.exists_contMDiffOn_circleFiber`), with smooth extensions to the
  ball of radius `2` and smooth inverses on their images
  (`SymplecticGeometry.CoordinateDisc.contMDiffOn_symm_add_smul_orthonormalBasisOneI_repr`,
  `SymplecticGeometry.CoordinateDisc.contMDiffOn_coord_ofChart`);
* off the zeros, the unit section `ν = s / ‖s‖`
  (`SymplecticGeometry.Bundle.contMDiffOn_normalizedFrame`), which on the punctured `i`-th disc is
  `σ i` acted on by a smooth map `w i` to the circle (Tau Ceti's `ContMDiffOn.division`);
* the normal form of `w i` (`Circle.exists_contMDiffOn_mul_eq_exp_arg_zpow`, in
  `Analysis/SpecialFunctions/Complex/CircleLog.lean`): with `k i` the degree of `w i` on the unit
  circle, a correction `c i`, smooth on the punctured disc and equal to `1` from radius `3 / 2`
  on, makes `w i * c i = (z / ‖z‖) ^ k i` on the punctured unit disc;
* `σout = ν • ∏ i, c i`, with `c i` read through the inverse of `φ i` and extended by `1`.

## Main results

* `SymplecticGeometry.Bundle.exists_coordinateDisc_unitSection_eq_phase_zpow_smul`: unit
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

namespace SymplecticGeometry

namespace Bundle

section Disc

variable {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [T2Space M]

open scoped Classical in
/-- Let `φ` be a coordinate disc whose coordinate `φ.coord` is smooth on its image, and
`c : ℂ → S¹` smooth on the punctured ball `0 < ‖z‖ < 2` and equal to `1` from radius `3 / 2` on.
Then the map equal to `c ∘ φ.coord` on the image of `φ` and to `1` off it is smooth off the
centre `φ 0`. -/
private theorem contMDiffAt_ite_mem_range
    {o : HomologicalOrientation M (EuclideanSpace ℝ (Fin 2)) 2} (φ : CoordinateDisc o)
    (hB : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℂ) ∞ φ.coord (range φ))
    {c : ℂ → Circle} (hc : ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 1) ∞ c {z | 0 < ‖z‖ ∧ ‖z‖ < 2})
    (hc1 : ∀ z, 3 / 2 ≤ ‖z‖ → c z = 1) {x : M} (hx : x ≠ φ 0) :
    ContMDiffAt (𝓡 2) (𝓡 1) ∞ (fun y ↦ if y ∈ range φ then c (φ.coord y) else 1) x := by
  by_cases hxφ : x ∈ range φ
  · -- on the punctured image, the map is `c ∘ φ.coord`
    set W := range φ \ {φ 0}
    have hW : IsOpen W := φ.isOpenEmbedding.isOpen_range.sdiff isClosed_singleton
    have hBW : MapsTo φ.coord W {z | 0 < ‖z‖ ∧ ‖z‖ < 2} := by
      rintro _ ⟨⟨z, rfl⟩, hz⟩
      rw [mem_ofPred_eq, CoordinateDisc.coord_apply]
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
      rw [ite_eq_left (mem_range_self z), CoordinateDisc.coord_apply]
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

open scoped VectorBundle.ComplexToReal Module.ComplexToReal

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

such that `σout (φ i z) = σ i (φ i z) • (φ i).phase (φ i z) ^ k i` whenever `0 < ‖z‖ < 1`, the
angular coordinate `(φ i).phase (φ i z)` being `z / ‖z‖`, and `∑ i, k i` is the first Chern
number of `V`. -/
theorem exists_coordinateDisc_unitSection_eq_phase_zpow_smul
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
          σout (φ i z) = op ((φ i).phase (φ i z) ^ k i) • σ i (φ i z)) ∧
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
  -- a smooth section `s` with finitely many zeros
  have hF : finrank ℝ F = 2 := by
    rw [← Module.finrank_mul_finrank ℝ ℂ F, Complex.finrank_real_complex,
      Fact.out (p := finrank ℂ F = 1)]
  obtain ⟨s, -, hfin⟩ := exists_contMDiffSection_regular_finite_zero_of_finrank_eq
    (n := ∞) (X := EuclideanSpace ℝ (Fin 2)) (F := F) (V := V)
    (by rw [finrank_euclideanSpace_fin, hF])
  have hsc : IsClosed {x | s x = 0} := hfin.isClosed
  let ι : Type := {x | s x = 0}
  let : Fintype ι := hfin.fintype
  -- smooth unit sections `τ x` near each point, and oriented charts `e i` about the zeros
  choose U hUo hxU τ hτ using fun x : M ↦ exists_contMDiffOn_circleFiber (n := ∞) g hI x
  obtain ⟨e, r, hr, hc, he, hatlas, -, -, -, hφ0, -, -, hrU, hrdisj⟩ :=
    CoordinateDisc.exists_ofChart_pairwise_disjoint o (x := fun i : ι ↦ (i : M))
      Subtype.val_injective (U := fun i ↦ U i) fun i ↦ (hUo i).mem_nhds (hxU i)
  set φ := fun i ↦ CoordinateDisc.ofChart (e i) (hr i) (hc i) (he i)
  -- `φ i` extends to `ψ i`, smooth on the ball of radius `2`
  let ψ (i : ι) (z : ℂ) : M := (e i).symm (0 + (r i / 2) • Complex.orthonormalBasisOneI.repr z)
  have hψs (i : ι) : ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 2) ∞ (ψ i) (CoordinateDisc.ball : Set ℂ) :=
    CoordinateDisc.contMDiffOn_symm_add_smul_orthonormalBasisOneI_repr (e i) (hr i) (hc i)
      (hatlas i)
  have hψ (i : ι) (z : CoordinateDisc.ball) : φ i z = ψ i z :=
    CoordinateDisc.ofChart_apply (e i) (hr i) (hc i) (he i) z
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
    have hzφ := hψ i ⟨z, CoordinateDisc.mem_ball_iff.2 hz.2⟩
    refine ⟨hzφ ▸ hrU i (mem_range_self _), ?_⟩
    rw [mem_ofPred_eq, ← hzφ]
    exact hne i fun h ↦ norm_pos_iff.1 hz.1 (congrArg Subtype.val h)
  -- the degrees `k i`, and the corrections `c i`, equal to `1` near the edge of the disc
  choose k c hcs hc1 hck using fun i ↦
    Circle.exists_contMDiffOn_mul_eq_exp_arg_zpow (r₁ := 1) (r₂ := 3 / 2) one_pos
      (by norm_num) (by norm_num) (hw i)
  -- the outer section `σout = ν • ∏ i, c i`, with `c i` extended by `1` off the `i`-th disc
  let G (i : ι) (x : M) : Circle := if x ∈ range (φ i) then c i ((φ i).coord x) else 1
  have hGφ (i j : ι) (z : CoordinateDisc.ball) : G j (φ i z) = if j = i then c i z else 1 := by
    split_ifs with hji
    · subst hji
      exact (ite_eq_left (mem_range_self z)).trans (congrArg _ ((φ j).coord_apply z))
    · exact ite_eq_right fun h ↦ (hrdisj hji).ne_of_mem h (mem_range_self z) rfl
  let σout : ∀ x, Fiber ℂ F V ℂ x := fun x ↦ op (∏ i, G i x) • ν x
  have hσout : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 1)) ∞
      (fun x ↦ ManifoldTotalSpace.homeomorph Circle (Fiber ℂ F V ℂ) ⟨x, σout x⟩)
      {x | s x ≠ 0} :=
    hν.totalSpaceMk_smul fun x hx ↦ (ContMDiffAt.prod fun i _ ↦
      contMDiffAt_ite_mem_range (φ i)
        (CoordinateDisc.contMDiffOn_coord_ofChart (e i) (hr i) (hc i) (he i) (hatlas i))
        (hcs i) (hc1 i) fun h ↦
          hx (by rw [h, hφ0 i]; exact i.property)).contMDiffWithinAt
  -- on the punctured unit disc, `σout = τ i • (z / ‖z‖) ^ k i`
  have hrel (i : ι) (z : CoordinateDisc.ball) (hz : 0 < ‖(z : ℂ)‖) (hz1 : ‖(z : ℂ)‖ < 1) :
      σout (φ i z) = op ((φ i).phase (φ i z) ^ k i) • τ i (φ i z) := by
    have hprod : ∏ j, G j (φ i z) = c i z := by simp [hGφ]
    have hdiv : division Circle (τ i (φ i z)) (ν (φ i z)) = w i z := by
      simp only [w]
      rw [hψ i z]
    rw [CoordinateDisc.phase_apply_self, ← hck i z hz hz1.le, ← hdiv,
      ← hprod, op_mul, mul_smul, smul_division]
  refine ⟨ι, inferInstance, e, r, hr, hc, he, φ, fun i ↦ rfl, hatlas, hrdisj, k,
    fun i ↦ τ i, σout, fun i ↦ (hτ i).mono (hrU i),
    hσout.mono fun x hx h ↦ hx ⟨x, h⟩ (hzero h), hrel, ?_⟩
  refine (chernNumber_eq_sum_of_collar_eq_zpow_smul finrank_euclideanSpace_fin
    (fun i j h ↦ (hrdisj h).mono (φ i).disc_subset_range (φ j).disc_subset_range)
    zero_lt_one (fun i ↦ ManifoldTotalSpace.continuousOn_of_contMDiffOn_homeomorph
      ((hτ i).mono ((φ i).disc_subset_range.trans (hrU i))))
    (ManifoldTotalSpace.continuousOn_of_contMDiffOn_homeomorph
      (hσout.mono fun x hx h ↦ hx ?_)) k fun i z hz hz1 ↦ hrel i z hz hz1).symm
  exact mem_iUnion.2 ⟨⟨x, h⟩, 0, by simp, (hzero h).symm⟩

end Surface

end Bundle

end SymplecticGeometry

end
