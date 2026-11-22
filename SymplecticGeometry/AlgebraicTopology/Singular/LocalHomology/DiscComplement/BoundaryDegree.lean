/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Singular.DisjointCircles
public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.DiscComplement.Basic
public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.HolomorphicZero
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import SymplecticGeometry.Analysis.Complex.RadialProjection
import TauCeti.Topology.Circle.Normalize

/-!
# The boundary degree of one disc's angle on the complement of coordinate discs

Let `φ i`, `i : ι`, be coordinate discs of a compact homologically oriented surface `M` with
pairwise disjoint closed discs, and `X = discComplement φ` the complement of their open discs,
with interior `discComplementInterior φ` oriented by the restriction of `o`. Its boundary is
`ι × S¹` (`SymplecticGeometry.discComplementBoundaryHomeomorph`). The map `∂X → S¹` that reads
the circle of `φ i` in its chart and sends the other circles to `1`
(`TopCat.prodFiberRetraction (TopCat.of ι) (1 : Circle) i`, read on `ι × S¹` through
`TopCat.prodHomeomorphTensorObj`) has boundary degree `-1`; this is
`SymplecticGeometry.boundaryDegree_prodFiberRetraction_comp_discComplementBoundaryHomeomorph_symm`.
The boundary of `X` runs clockwise in each chart.

## Proof

We show that its inverse, `z⁻¹` on circle `i` and `1` on the others, has boundary degree `1`,
with a test map `G : X → ℂ`. Take a width `δ ∈ (0, 1)` of the collar of circle `i`
(`SymplecticGeometry.exists_pairwise_disjoint_image_ball`), a cut-off `λ` that is `1` up to
`1 + δ/2` and `0` from `1 + 3δ/4` on, and `c = (1 + δ/4)⁻¹`. Let `G (φ i w) = λ(|w|) w⁻¹ - c`
and `G = -c` on the rest of `X`. Its only zero is `φ i (1/c)`, near which `G ∘ φ i` is
`w ↦ w⁻¹ - c`, holomorphic with nonzero derivative. A small coordinate disc of the interior
around the zero (`SymplecticGeometry.CoordinateDisc.affineBall`,
`SymplecticGeometry.CoordinateDisc.restrict`) and
`SymplecticGeometry.boundaryDegree_eq_one_of_hasDerivAt` give boundary degree `1` for `G / |G|`.
On `∂X`, `G / |G|` is homotopic to the inverse map above, through the normalizations of
`z⁻¹ - t c` on circle `i`, which do not vanish since `|z⁻¹| = 1 > t c`, and through
`e^{iπt}` on the others.

## Main results

* `SymplecticGeometry.boundaryDegree_prodFiberRetraction_comp_discComplementBoundaryHomeomorph_symm`
  says that the boundary degree of the angle of one disc is `-1`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.7,
  where the first Chern number of a bundle over a surface is computed from trivializations over
  discs and over their complement.
* L. Ahlfors, *Complex Analysis*, 3rd ed., McGraw-Hill, 1979, Chapter 4, §3.3 (the local
  mapping theorem), for the degree `1` of a simple zero.
-/

public section

noncomputable section

open Set Topology Module TauCeti Function

namespace SymplecticGeometry

variable {M : Type} [TopologicalSpace M] [T2Space M] {E : Type} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M] {o : HomologicalOrientation M E 2}
  {ι : Type} (φ : ι → CoordinateDisc o)

namespace DiscComplementBoundaryDegree

/-! ### The test map -/

variable (i : ι) (δ c : ℝ)

/-- The inverse of the chart of `φ i`, on its range. -/
private def chartInv : M → CoordinateDisc.ball :=
  ((φ i).isOpenEmbedding.toOpenPartialHomeomorph _).symm

private lemma chartInv_apply (w : CoordinateDisc.ball) : chartInv φ i (φ i w) = w :=
  (φ i).isOpenEmbedding.toOpenPartialHomeomorph_left_inv _

open scoped Classical in
/-- The test map: `λ(|w|) w⁻¹ - c` at `φ i w`, and `-c` off the range of `φ i`, where the
cut-off `λ s = smoothTransition (4/δ (1 + 3δ/4 - s))` is `1` up to `1 + δ/2` and `0` from
`1 + 3δ/4` on. -/
private def testFun (x : discComplement φ) : ℂ :=
  if (x : M) ∈ range (φ i) then
    (Real.smoothTransition (4 / δ * (1 + 3 * δ / 4 - ‖(chartInv φ i x : ℂ)‖)) : ℂ) *
      (chartInv φ i x : ℂ)⁻¹ - c
  else -c

private lemma testFun_of_eq {x : discComplement φ} {w : CoordinateDisc.ball}
    (hx : (x : M) = φ i w) :
    testFun φ i δ c x =
      (Real.smoothTransition (4 / δ * (1 + 3 * δ / 4 - ‖(w : ℂ)‖)) : ℂ) * (w : ℂ)⁻¹ - c := by
  rw [testFun, ite_eq_left ⟨w, hx.symm⟩, hx, chartInv_apply]

private lemma testFun_of_notMem {x : discComplement φ} (hx : (x : M) ∉ range (φ i)) :
    testFun φ i δ c x = -c := by
  rw [testFun, ite_eq_right hx]

variable {δ} in
private lemma continuous_testFun (hδ : δ ∈ Ioo (0 : ℝ) 1) : Continuous (testFun φ i δ c) := by
  set s : Set (discComplement φ) := Subtype.val ⁻¹' range (φ i)
  have hs : IsOpen s := (φ i).isOpenEmbedding.isOpen_range.preimage continuous_subtypeVal
  have hsymm : ContinuousOn (chartInv φ i) (range (φ i)) :=
    ((φ i).isOpenEmbedding.toOpenPartialHomeomorph _).continuousOn_symm.mono (by
      simp [IsOpenEmbedding.toOpenPartialHomeomorph_target])
  have hinv : ContinuousOn (fun x : discComplement φ ↦ (chartInv φ i x : ℂ)) s :=
    continuous_subtypeVal.comp_continuousOn
      (hsymm.comp continuous_subtypeVal.continuousOn fun x hx ↦ hx)
  have hF : Continuous fun x ↦ testFun φ i δ c x + c := by
    refine ContinuousOn.continuous_of_tsupport_subset (s := s) ?_ hs ?_
    · refine ContinuousOn.congr (f := fun x : discComplement φ ↦
        (Real.smoothTransition (4 / δ * (1 + 3 * δ / 4 - ‖(chartInv φ i x : ℂ)‖)) : ℂ) *
          (chartInv φ i x : ℂ)⁻¹) ?_ fun x hx ↦ ?_
      · refine (Complex.continuous_ofReal.comp_continuousOn
          (Real.smoothTransition.continuous.comp_continuousOn
            ((continuous_const.mul (continuous_const.sub continuous_id)).comp_continuousOn
              hinv.norm))).mul (hinv.inv₀ fun x hx ↦ ?_)
        obtain ⟨w, hw⟩ := hx
        rw [← hw, chartInv_apply]
        exact norm_pos_iff.1 (zero_lt_one.trans_le
          (one_le_norm_of_mem_discComplement φ (hw ▸ x.property)))
      · rw [testFun, ite_eq_left (show (x : M) ∈ range (φ i) from hx), sub_add_cancel]
    · have hK := ((φ i).isCompact_image_closedBall (ρ := 1 + 3 * δ / 4)
        (by linarith [hδ.2])).isClosed
      refine (closure_minimal ?_ (hK.preimage continuous_subtypeVal)).trans
        (preimage_mono (image_subset_range _ _))
      intro x hx
      by_cases hxr : (x : M) ∈ range (φ i)
      · obtain ⟨w, hw⟩ := hxr
        refine ⟨w, show ‖(w : ℂ)‖ ≤ 1 + 3 * δ / 4 from not_lt.1 fun h ↦ hx ?_, hw⟩
        have h0 : 4 / δ * (1 + 3 * δ / 4 - ‖(w : ℂ)‖) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (div_nonneg (by norm_num) hδ.1.le) (by linarith)
        simp only [testFun_of_eq φ i δ c hw.symm, Real.smoothTransition.zero_of_nonpos h0]
        simp
      · exact absurd (by simp only [testFun_of_notMem φ i δ c hxr]; ring) hx
  exact (hF.sub continuous_const).congr fun x ↦ add_sub_cancel_right _ (c : ℂ)

/-! ### The constants -/

variable {δ}

/-- The zero `1 + δ/4` of the test map, in the chart of `φ i`. -/
private def zeroPt (hδ : δ ∈ Ioo (0 : ℝ) 1) : CoordinateDisc.ball :=
  ⟨((1 + δ / 4 : ℝ) : ℂ), CoordinateDisc.mem_ball_iff.2 <| by
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith [hδ.1])]
    linarith [hδ.2]⟩

private lemma norm_zeroPt (hδ : δ ∈ Ioo (0 : ℝ) 1) : ‖((1 + δ / 4 : ℝ) : ℂ)‖ = 1 + δ / 4 := by
  rw [Complex.norm_real, Real.norm_of_nonneg (by linarith [hδ.1])]

private lemma norm_zeroPt_add_le (hδ : δ ∈ Ioo (0 : ℝ) 1) :
    ‖((1 + δ / 4 : ℝ) : ℂ)‖ + 2 * (δ / 16) ≤ 2 := by
  rw [norm_zeroPt hδ]
  linarith [hδ.2]

/-- The small disc `z ↦ 1 + δ/4 + (δ/16) z` around the zero, in the chart of `φ i`. -/
private abbrev smallBall (hδ : δ ∈ Ioo (0 : ℝ) 1) : CoordinateDisc.ball → CoordinateDisc.ball :=
  CoordinateDisc.affineBall _ (by linarith [hδ.1] : (0 : ℝ) < δ / 16) (norm_zeroPt_add_le hδ)

private lemma norm_smallBall (hδ : δ ∈ Ioo (0 : ℝ) 1) (z : CoordinateDisc.ball) :
    1 + δ / 8 < ‖(smallBall hδ z : ℂ)‖ ∧ ‖(smallBall hδ z : ℂ)‖ < 1 + 3 * δ / 8 := by
  have hz := CoordinateDisc.mem_ball_iff.1 z.property
  have hw : (smallBall hδ z : ℂ) = ((1 + δ / 4 : ℝ) : ℂ) + ((δ / 16 : ℝ) : ℂ) * z :=
    CoordinateDisc.coe_affineBall_apply _ _ _ _
  have h := abs_norm_sub_norm_le (smallBall hδ z : ℂ) ((1 + δ / 4 : ℝ) : ℂ)
  rw [hw, add_sub_cancel_left, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (by linarith [hδ.1] : (0 : ℝ) ≤ δ / 16),
    Real.norm_of_nonneg (by linarith [hδ.1] : (0 : ℝ) ≤ 1 + δ / 4)] at h
  rw [hw]
  have h1 : δ / 16 * ‖(z : ℂ)‖ < δ / 8 := by nlinarith [hδ.1]
  constructor <;> linarith [abs_le.1 h]

/-- The small disc around the zero lies in the interior. -/
private lemma smallBall_mem_discComplementInterior [Finite ι] {ε : ι → ℝ}
    (hε : ∀ j, ε j ∈ Ioo (0 : ℝ) 1)
    (hd : Pairwise (Disjoint on fun j ↦ φ j '' {z | ‖(z : ℂ)‖ < 1 + ε j}))
    (z : CoordinateDisc.ball) : φ i (smallBall (hε i) z) ∈ discComplementInterior φ := by
  obtain ⟨h1, h2⟩ := norm_smallBall (hε i) z
  refine (mem_discComplementInterior_iff φ).2 fun j hj ↦ ?_
  obtain rfl | hij := eq_or_ne j i
  · exact ((φ j).apply_mem_disc_iff.1 hj).not_gt (by linarith [(hε j).1])
  · exact (disjoint_image_ball_disc φ (fun k ↦ (hε k).1) hd hij.symm).notMem_of_mem_left
      (mem_image_of_mem _ (show ‖(smallBall (hε i) z : ℂ)‖ < 1 + ε i by linarith [(hε i).1]))
      hj

/-- On the small disc, the test map is `w ↦ w⁻¹ - c`. -/
private lemma testFun_smallBall (hδ : δ ∈ Ioo (0 : ℝ) 1) {x : discComplement φ}
    {z : CoordinateDisc.ball} (hx : (x : M) = φ i (smallBall hδ z)) :
    testFun φ i δ (1 + δ / 4)⁻¹ x = (smallBall hδ z : ℂ)⁻¹ - ((1 + δ / 4)⁻¹ : ℝ) := by
  rw [testFun_of_eq φ i δ _ hx, Real.smoothTransition.one_of_one_le (by
    rw [div_mul_eq_mul_div, le_div_iff₀ hδ.1]; linarith [(norm_smallBall hδ z).2, hδ.1]),
    Complex.ofReal_one, one_mul]

/-- The only zero of the test map is `φ i (1 + δ/4)`. -/
private lemma testFun_eq_zero_iff (hδ : δ ∈ Ioo (0 : ℝ) 1) (x : discComplement φ) :
    testFun φ i δ (1 + δ / 4)⁻¹ x = 0 ↔ (x : M) = φ i (zeroPt hδ) := by
  have hc : (0 : ℝ) < (1 + δ / 4)⁻¹ := inv_pos.2 (by linarith [hδ.1])
  constructor
  · intro hx
    by_cases hxr : (x : M) ∈ range (φ i)
    · obtain ⟨w, hw⟩ := hxr
      rw [testFun_of_eq φ i δ _ hw.symm, sub_eq_zero] at hx
      have hw0 : (w : ℂ) ≠ 0 :=
        norm_pos_iff.1 (zero_lt_one.trans_le
          (one_le_norm_of_mem_discComplement φ (hw ▸ x.property)))
      -- `λ w⁻¹ = c` gives `w = λ / c = λ (1 + δ/4)`, of norm at most `1 + δ/4`, so `λ = 1`.
      set l := Real.smoothTransition (4 / δ * (1 + 3 * δ / 4 - ‖(w : ℂ)‖)) with hl
      have hwl : (w : ℂ) = ((l * (1 + δ / 4) : ℝ) : ℂ) := by
        have h4 : (4 + δ : ℂ) ≠ 0 := by exact_mod_cast (by linarith [hδ.1] : (4 + δ : ℝ) ≠ 0)
        push_cast at hx ⊢
        field_simp at hx
        linear_combination -hx / 4
      have hnorm : ‖(w : ℂ)‖ ≤ 1 + δ / 2 := by
        rw [hwl, Complex.norm_real, Real.norm_of_nonneg (mul_nonneg
          (Real.smoothTransition.nonneg _) (by linarith [hδ.1]))]
        nlinarith [Real.smoothTransition.le_one (4 / δ * (1 + 3 * δ / 4 - ‖(w : ℂ)‖)), hδ.1]
      rw [hl, Real.smoothTransition.one_of_one_le (by
        rw [div_mul_eq_mul_div, le_div_iff₀ hδ.1]; linarith), one_mul] at hwl
      rw [← hw]
      exact congrArg (φ i) (Subtype.ext hwl)
    · rw [testFun_of_notMem φ i δ _ hxr, neg_eq_zero, Complex.ofReal_eq_zero] at hx
      exact absurd hx hc.ne'
  · intro hx
    rw [testFun_of_eq φ i δ _ hx, zeroPt, Real.smoothTransition.one_of_one_le (by
      rw [div_mul_eq_mul_div, le_div_iff₀ hδ.1, norm_zeroPt hδ]; linarith [hδ.1]),
      Complex.ofReal_one, one_mul, Complex.ofReal_inv, sub_self]

/-! ### The test map on the boundary circles -/

section Boundary

variable [TopologicalSpace ι] [DiscreteTopology ι] (hφ : Pairwise (Disjoint on fun i ↦ (φ i).disc))

/-- On the circle of `φ i`, the test map is `z ↦ z⁻¹ - c`. -/
private lemma testFun_boundary_self (hδ : δ ∈ Ioo (0 : ℝ) 1) (c : ℝ) (z : Circle) :
    testFun φ i δ c (discComplementBoundary φ hφ (i, z)) = (z : ℂ)⁻¹ - c := by
  rw [testFun_of_eq φ i δ c (by rw [coe_discComplementBoundary_apply,
    CoordinateDisc.boundaryCircle_apply]), Real.smoothTransition.one_of_one_le (by
      rw [div_mul_eq_mul_div, le_div_iff₀ hδ.1]; simp; linarith [hδ.1]),
    Complex.ofReal_one, one_mul]

/-- On the other circles, the test map is `-c`. -/
private lemma testFun_boundary_of_ne {ε : ι → ℝ} (hε : ∀ j, ε j ∈ Ioo (0 : ℝ) 1)
    (hd : Pairwise (Disjoint on fun j ↦ φ j '' {z | ‖(z : ℂ)‖ < 1 + ε j})) (c : ℝ) {j : ι}
    (hij : j ≠ i) (z : Circle) :
    testFun φ i (ε i) c (discComplementBoundary φ hφ (j, z)) = -c := by
  by_cases hxr : (discComplementBoundary φ hφ (j, z) : M) ∈ range (φ i)
  · obtain ⟨w, hw⟩ := hxr
    have hs : 1 + 3 * ε i / 4 ≤ ‖(w : ℂ)‖ := by
      refine not_lt.1 fun h ↦ (disjoint_image_ball_disc φ (fun k ↦ (hε k).1) hd
        hij.symm).notMem_of_mem_left
        ⟨w, show ‖(w : ℂ)‖ < 1 + ε i by linarith [(hε i).1], hw⟩ ?_
      rw [coe_discComplementBoundary_apply]
      exact (φ j).boundaryCircle_mem_disc z
    rw [testFun_of_eq φ i (ε i) c hw.symm, Real.smoothTransition.zero_of_nonpos
      (mul_nonpos_of_nonneg_of_nonpos (div_nonneg (by norm_num) (hε i).1.le) (by linarith)),
      Complex.ofReal_zero, zero_mul, zero_sub]
  · exact testFun_of_notMem φ i (ε i) c hxr

end Boundary

/-! ### The homotopy on the boundary -/

private lemma inv_sub_ne_zero {c : ℝ} (hc : c ∈ Ioo (0 : ℝ) 1) (t : unitInterval) (z : Circle) :
    (z : ℂ)⁻¹ - (t : ℝ) * c ≠ 0 := by
  intro h
  have h' := congrArg norm (sub_eq_zero.1 h)
  rw [norm_inv, Circle.norm_coe, inv_one, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (unitInterval.nonneg t), Real.norm_of_nonneg hc.1.le] at h'
  linarith [mul_le_of_le_one_left hc.1.le (unitInterval.le_one t), hc.2]

section Homotopy

variable [TopologicalSpace ι] [DiscreteTopology ι] [DecidableEq ι] {c : ℝ} (hc : c ∈ Ioo (0 : ℝ) 1)

/-- The homotopy from `z⁻¹` on circle `i` and `1` on the others to the normalized test map:
`(z⁻¹ - t c) / |z⁻¹ - t c|` on circle `i` and `e^{iπt}` on the others. -/
private def homotopyFun : C(unitInterval × (ι × Circle), Circle) where
  toFun q := if q.2.1 = i then
      Circle.radialProjection ⟨(q.2.2 : ℂ)⁻¹ - (q.1 : ℝ) * c, inv_sub_ne_zero hc q.1 q.2.2⟩
    else Circle.exp (Real.pi * q.1)
  continuous_toFun := by
    have hinv : Continuous fun q : unitInterval × Circle ↦ (q.2 : ℂ)⁻¹ := by
      simp_rw [← Circle.coe_inv]
      fun_prop
    have hA : Continuous fun q : unitInterval × Circle ↦ Circle.radialProjection
        ⟨(q.2 : ℂ)⁻¹ - (q.1 : ℝ) * c, inv_sub_ne_zero hc q.1 q.2⟩ :=
      Circle.radialProjection.continuous.comp (Continuous.subtype_mk (hinv.sub (by fun_prop)) _)
    have hB : Continuous fun q : unitInterval × Circle ↦ Circle.exp (Real.pi * q.1) := by
      fun_prop
    -- The circles of `ι × Circle` are open, so the map is continuous on each of them.
    have h : Continuous fun p : ι × (unitInterval × Circle) ↦
        if p.1 = i then Circle.radialProjection ⟨(p.2.2 : ℂ)⁻¹ - (p.2.1 : ℝ) * c,
          inv_sub_ne_zero hc p.2.1 p.2.2⟩ else Circle.exp (Real.pi * p.2.1) :=
      continuous_prod_of_discrete_left.2 fun j ↦ by
        by_cases hj : j = i
        · simpa [hj] using hA
        · simpa [hj] using hB
    exact h.comp (by fun_prop : Continuous fun q : unitInterval × (ι × Circle) ↦
      (q.2.1, (q.1, q.2.2)))

private lemma homotopyFun_apply (q : unitInterval × (ι × Circle)) :
    homotopyFun i hc q = if q.2.1 = i then
      Circle.radialProjection ⟨(q.2.2 : ℂ)⁻¹ - (q.1 : ℝ) * c, inv_sub_ne_zero hc q.1 q.2.2⟩
    else Circle.exp (Real.pi * q.1) :=
  (rfl)

end Homotopy

/-! ### The degree of the test map -/

section TestMap

variable {ε : ι → ℝ} (hε : ∀ j, ε j ∈ Ioo (0 : ℝ) 1)

/-- The test map, for `δ = ε i` and `c = (1 + δ/4)⁻¹`. -/
private def testMap : C(discComplement φ, ℂ) :=
  ⟨testFun φ i (ε i) (1 + ε i / 4)⁻¹, continuous_testFun φ i _ (hε i)⟩

private lemma testMap_apply (x : discComplement φ) :
    testMap φ i hε x = testFun φ i (ε i) (1 + ε i / 4)⁻¹ x :=
  (rfl)

variable [Finite ι] (hd : Pairwise (Disjoint on fun j ↦ φ j '' {z | ‖(z : ℂ)‖ < 1 + ε j}))

/-- The small coordinate disc of the interior around the zero of the test map. -/
private def smallDisc : CoordinateDisc (o.comap (discComplementInterior φ).isOpenEmbedding') :=
  ((φ i).comp (smallBall (hε i)) (CoordinateDisc.isOpenEmbedding_affineBall _ _ _)
    (CoordinateDisc.comap_affineBall_complexHomologicalOrientation _ _ _)).restrict
    (discComplementInterior φ) (by
      rintro _ ⟨z, rfl⟩
      rw [CoordinateDisc.comp_apply]
      exact smallBall_mem_discComplementInterior φ i hε hd z)

private lemma coe_inclusion_smallDisc_apply (z : CoordinateDisc.ball) :
    ((inclusion (discComplementInterior_subset φ) (smallDisc φ i hε hd z) : discComplement φ) :
      M) = φ i (smallBall (hε i) z) :=
  (CoordinateDisc.coe_restrict_apply _ _ _ z).trans (CoordinateDisc.comp_apply _ _ _ _ z)

/-- The only zero of the test map is the centre of the small disc. -/
private lemma preimage_testMap_zero :
    testMap φ i hε ⁻¹' {0} =
      {inclusion (discComplementInterior_subset φ) (smallDisc φ i hε hd 0)} := by
  have hzero : smallBall (hε i) 0 = zeroPt (hε i) := Subtype.ext (by
    rw [CoordinateDisc.coe_affineBall_apply, CoordinateDisc.coe_zero, mul_zero, add_zero, zeroPt])
  ext x
  rw [mem_preimage, mem_singleton_iff, mem_singleton_iff, testMap_apply,
    testFun_eq_zero_iff φ i (hε i) x, ← hzero, ← coe_inclusion_smallDisc_apply φ i hε hd,
    Subtype.ext_iff]

variable [TopologicalSpace ι] [DiscreteTopology ι] (hφ : Pairwise (Disjoint on fun i ↦ (φ i).disc))

include hd in
/-- The normalization of the test map on the boundary has boundary degree `1`. -/
private lemma boundaryDegree_testMap [CompactSpace M] (hn : finrank ℝ E = 2)
    {u : C(↥(range (inclusion (discComplementInterior_subset φ)))ᶜ, Circle)}
    (hu : ∀ x, (u x : ℂ) = ‖testMap φ i hε x‖⁻¹ • testMap φ i hε x) :
    (o.comap (discComplementInterior φ).isOpenEmbedding').boundaryDegree hn
      (isOpenEmbedding_inclusion_discComplementInterior φ)
      (range_inclusion_discComplementInterior φ hφ) (isCollared_discComplementBoundary φ hφ) u =
      1 := by
  set a : ℂ := ((1 + ε i / 4 : ℝ) : ℂ)
  set r : ℂ := ((ε i / 16 : ℝ) : ℂ)
  have h0 : a + r * ((0 : CoordinateDisc.ball) : ℂ) ≠ 0 := by
    rw [CoordinateDisc.coe_zero, mul_zero, add_zero, Complex.ofReal_ne_zero]
    linarith [(hε i).1]
  have hg := (((hasDerivAt_id' ((0 : CoordinateDisc.ball) : ℂ)).const_mul r).const_add a).inv
    h0 |>.sub_const (((1 + ε i / 4)⁻¹ : ℝ) : ℂ)
  refine boundaryDegree_eq_one_of_hasDerivAt hn _ _ _ (smallDisc φ i hε hd) hg
    (div_ne_zero (by simp [r, (hε i).1.ne']) (pow_ne_zero _ h0))
    (preimage_testMap_zero φ i hε hd) (Filter.Eventually.of_forall fun w ↦ ?_) hu
  rw [testMap_apply, testFun_smallBall φ i (hε i) (coe_inclusion_smallDisc_apply φ i hε hd w),
    CoordinateDisc.coe_affineBall_apply, Pi.inv_apply]

include hd in
/-- The test map on the boundary circles. -/
private lemma testMap_discComplementBoundaryHomeomorph [DecidableEq ι] (p : ι × Circle) :
    testMap φ i hε (discComplementBoundaryHomeomorph φ hφ p) =
      if p.1 = i then (p.2 : ℂ)⁻¹ - ((1 + ε i / 4)⁻¹ : ℝ) else -((1 + ε i / 4)⁻¹ : ℝ) := by
  rw [testMap_apply, coe_discComplementBoundaryHomeomorph_apply]
  obtain ⟨j, z⟩ := p
  by_cases hj : j = i
  · rw [ite_eq_left hj, hj]
    exact testFun_boundary_self φ i hφ (hε i) _ z
  · rw [ite_eq_right hj, testFun_boundary_of_ne φ i hφ hε hd _ hj z]

end TestMap

end DiscComplementBoundaryDegree

open DiscComplementBoundaryDegree in
/-- **The boundary degree of one disc's angle.** Let `φ i` be coordinate discs of a compact
surface `M` with pairwise disjoint closed discs, and `X` the complement of their open discs, with
interior oriented by the restriction of `o`. The map `∂X → S¹` that sends the point
`(φ i).boundaryCircle z` to `z` and the other boundary circles to `1` has boundary degree `-1`:
the boundary of `X` runs clockwise in the chart of each disc. -/
theorem boundaryDegree_prodFiberRetraction_comp_discComplementBoundaryHomeomorph_symm
    [CompactSpace M] [Finite ι] [TopologicalSpace ι] [DiscreteTopology ι]
    (hn : finrank ℝ E = 2) (hφ : Pairwise (Disjoint on fun i ↦ (φ i).disc)) (i : ι) :
    (o.comap (discComplementInterior φ).isOpenEmbedding').boundaryDegree hn
      (isOpenEmbedding_inclusion_discComplementInterior φ)
      (range_inclusion_discComplementInterior φ hφ) (isCollared_discComplementBoundary φ hφ)
      ((TopCat.prodFiberRetraction (TopCat.of ι) (X := TopCat.of Circle) 1 i).hom.comp
        ((discComplementBoundaryHomeomorph φ hφ).symm.trans
          (TopCat.prodHomeomorphTensorObj ι Circle) : C(_, _))) = -1 := by
  classical
  obtain ⟨ε, hε, hd⟩ := exists_pairwise_disjoint_image_ball φ hφ
  have hc : (1 + ε i / 4)⁻¹ ∈ Ioo (0 : ℝ) 1 :=
    ⟨inv_pos.2 (by linarith [(hε i).1]), inv_lt_one_of_one_lt₀ (by linarith [(hε i).1])⟩
  -- The test map does not vanish on the boundary, since its zero lies in the interior.
  have hne (x : ↥(range (inclusion (discComplementInterior_subset φ)))ᶜ) :
      testMap φ i hε x ≠ 0 := fun hx ↦ x.property ⟨smallDisc φ i hε hd 0,
    (mem_singleton_iff.1 (preimage_testMap_zero φ i hε hd ▸ hx :
      (x : discComplement φ) ∈ _)).symm⟩
  let u : C(↥(range (inclusion (discComplementInterior_subset φ)))ᶜ, Circle) :=
    ((testMap φ i hε).restrict _).normalizeToCircle (by simpa using hne)
  have hu (x : ↥(range (inclusion (discComplementInterior_subset φ)))ᶜ) :
      (u x : ℂ) = ‖testMap φ i hε x‖⁻¹ • testMap φ i hε x := by
    simp [u, div_eq_inv_mul]
  -- On the boundary, `u` is homotopic to `z⁻¹` on circle `i` and `1` on the others.
  let K : C(unitInterval × ↥(range (inclusion (discComplementInterior_subset φ)))ᶜ, Circle) :=
    (homotopyFun i hc).comp
      ⟨fun q ↦ (q.1, (discComplementBoundaryHomeomorph φ hφ).symm q.2), by fun_prop⟩
  have hK (t : unitInterval) (p : ι × Circle) :
      K (t, discComplementBoundaryHomeomorph φ hφ p) = homotopyFun i hc (t, p) := by
    simp only [K, ContinuousMap.comp_apply, ContinuousMap.coe_mk, Homeomorph.symm_apply_apply]
  have hr (p : ι × Circle) :
      (TopCat.prodFiberRetraction (TopCat.of ι) (X := TopCat.of Circle) 1 i).hom.comp
        ((discComplementBoundaryHomeomorph φ hφ).symm.trans
          (TopCat.prodHomeomorphTensorObj ι Circle) : C(_, _))
        (discComplementBoundaryHomeomorph φ hφ p) = if p.1 = i then p.2 else 1 := by
    rw [ContinuousMap.comp_apply, ContinuousMap.coe_ofClass, Homeomorph.trans_apply,
      Homeomorph.symm_apply_apply, TopCat.prodFiberRetraction_prodHomeomorphTensorObj]
  let F : ContinuousMap.Homotopy
      ((TopCat.prodFiberRetraction (TopCat.of ι) (X := TopCat.of Circle) 1 i).hom.comp
        ((discComplementBoundaryHomeomorph φ hφ).symm.trans
          (TopCat.prodHomeomorphTensorObj ι Circle) : C(_, _)))⁻¹ u :=
    { toContinuousMap := K
      map_zero_left x := by
        obtain ⟨p, rfl⟩ := (discComplementBoundaryHomeomorph φ hφ).surjective x
        rw [ContinuousMap.toFun_eq_coe, hK, homotopyFun_apply]
        rw [ContinuousMap.inv_apply, hr]
        split_ifs
        · ext
          simp
        · simp
      map_one_left x := by
        obtain ⟨p, rfl⟩ := (discComplementBoundaryHomeomorph φ hφ).surjective x
        rw [ContinuousMap.toFun_eq_coe, hK, homotopyFun_apply]
        ext
        rw [hu, testMap_discComplementBoundaryHomeomorph φ i hε hd hφ]
        split_ifs
        · simp
        · rw [Circle.coe_exp, Set.Icc.coe_one, mul_one, Complex.exp_pi_mul_I, norm_neg,
            Complex.norm_real, Real.norm_of_nonneg hc.1.le, smul_neg, Complex.real_smul,
            ← Complex.ofReal_mul, inv_mul_cancel₀ hc.1.ne', Complex.ofReal_one] }
  have h := (o.comap (discComplementInterior φ).isOpenEmbedding').boundaryDegree_eq_of_homotopy
    hn (isOpenEmbedding_inclusion_discComplementInterior φ)
    (range_inclusion_discComplementInterior φ hφ) (isCollared_discComplementBoundary φ hφ) F
  rw [HomologicalOrientation.boundaryDegree_inv, boundaryDegree_testMap φ i hε hd hφ hn hu] at h
  linarith

end SymplecticGeometry
