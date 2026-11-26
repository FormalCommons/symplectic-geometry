/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Blowup.Weight.Basic
public import SymplecticGeometry.Geometry.Manifold.Projectivization.Hopf
import SymplecticGeometry.Analysis.Complex.Euclidean.Space

/-!
# The Hopf collapse onto the blowup of weight `λ`

Let `ψ` be a symplectic embedding of the closed ball of radius `√(l² + ε²)` into `M`, for
`0 < l` and `0 < ε`, and let `M̃_ψ = WeightBlowup hψ hl hε` be the blowup of weight `l` of
`Blowup/Weight/Basic.lean`. Following McDuff–Salamon, §7.1 (the construction (7.1.14)), the
blowup is obtained from `M ∖ ψ(B°(l))` by collapsing each Hopf circle of the sphere `ψ(∂B(l))` to
a point of the divisor. This file defines the collapse map and proves its first properties.

## Main definitions

* `SymplecticGeometry.WeightBlowup.collapseMap hψ hl hε`: the map from `M ∖ ψ(B°(l))` onto the
  blowup that is `GluedAlong.inl` off `ψ(B(l))` and sends `ψ w`, for `|w| = l`, to the point
  `divisor hψ hl hε` of the line `sphereHopf n (w / l)` through `w`.

## Main results

* `SymplecticGeometry.WeightBlowup.collapseMap_of_notMem` and
  `SymplecticGeometry.WeightBlowup.collapseMap_of_norm_eq`: the two cases of the collapse map.
* `SymplecticGeometry.WeightBlowup.continuous_collapseMap`: the collapse map is continuous. Off
  `ψ(B(l))` it is `inl`. On the image of the open ball of radius `√(l² + ε²)` it is `inr` of
  the map `w ↦ ([w], √(|w|² - l²) / |w| • w)` into the model, which is continuous on `w ≠ 0`, is
  the zero section over `[w]` for `|w| = l`, and for `|w| > l` inverts the radial map
  `F_l ∘ π` that the gluing uses.
* `SymplecticGeometry.WeightBlowup.surjective_collapseMap`: the collapse map is onto, since a point
  of the blowup is either `inl` of a point of `M ∖ ψ(B(l))`, or on the divisor (`range_divisor`),
  or glued to a point of `M ∖ ψ(B(l))`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §7.1.
-/

public section

noncomputable section

open Set Metric Topology TopologicalSpace TauCeti Projectivization
open scoped Manifold ContDiff LinearAlgebra.Projectivization

namespace SymplecticGeometry

namespace WeightBlowup

open BlowupModel

variable {n : ℕ} {M : Type} {ψ : StdSpace (Fin (n + 1)) → M} {l ε : ℝ}

/-- A point `w` of `B(l)` whose image is off `ψ(B°(l))` lies on the sphere `|w| = l`. -/
private theorem norm_eq_of_mem_closedBall_of_notMem {w : StdSpace (Fin (n + 1))}
    (hw : w ∈ closedBall 0 l) (hx : ψ w ∉ ψ '' ball 0 l) : ‖w‖ = l :=
  le_antisymm (mem_closedBall_zero_iff.1 hw) <|
    not_lt.1 fun h ↦ hx ⟨w, mem_ball_zero_iff.2 h, rfl⟩

/-- For `0 < l` and `|w| = l`, the vector `w / l` lies on the unit sphere. -/
private theorem inv_smul_mem_sphere (hl : 0 < l) {w : StdSpace (Fin (n + 1))} (hw : ‖w‖ = l) :
    l⁻¹ • w ∈ sphere (0 : StdSpace (Fin (n + 1))) 1 := by
  rw [mem_sphere_zero_iff_norm, norm_smul, hw, Real.norm_eq_abs, abs_inv, abs_of_pos hl,
    inv_mul_cancel₀ hl.ne']

/-! ### The inverse of the radial map, extended to the sphere -/

/-- The point `([z], √(|z|² - l²) / |z| • z)` of the model blowup, for `z ≠ 0`: for `|z| > l` the
preimage of `z` under the radial map `F_l ∘ π`, and for `|z| = l` the point of the zero section
over `[z]`. -/
private def shellPoint (l : ℝ) (z : puncturedSpace (Fin (n + 1) → ℂ)) : BlowupModel n :=
  ⟨(mk ℂ (z : Fin (n + 1) → ℂ) (mem_puncturedSpace.1 z.property),
    (√(‖complexToRealEuclidean (Fin (n + 1)) z‖ ^ 2 - l ^ 2) /
      ‖complexToRealEuclidean (Fin (n + 1)) z‖) • (z : Fin (n + 1) → ℂ)),
    mem_blowupModel_iff.2 (Submodule.smul_of_tower_mem _ _
      (mem_blowupModel_iff.1 (mk_self_mem_blowupModel _)))⟩

private theorem pr_shellPoint (l : ℝ) (z : puncturedSpace (Fin (n + 1) → ℂ)) :
    (shellPoint l z).pr = mk ℂ (z : Fin (n + 1) → ℂ) (mem_puncturedSpace.1 z.property) := by
  unfold shellPoint; exact pr_mk ..

private theorem blowdown_shellPoint (l : ℝ) (z : puncturedSpace (Fin (n + 1) → ℂ)) :
    (shellPoint l z).blowdown =
      (√(‖complexToRealEuclidean (Fin (n + 1)) z‖ ^ 2 - l ^ 2) /
        ‖complexToRealEuclidean (Fin (n + 1)) z‖) • (z : Fin (n + 1) → ℂ) := by
  unfold shellPoint; exact blowdown_mk ..

private theorem continuous_shellPoint (l : ℝ) : Continuous (shellPoint (n := n) l) := by
  have hmk : (fun z : puncturedSpace (Fin (n + 1) → ℂ) ↦
      mk ℂ (z : Fin (n + 1) → ℂ) (mem_puncturedSpace.1 z.property)) = mkNonzero ℂ n :=
    funext fun z ↦ (mkNonzero_apply z).symm
  have hnorm : Continuous fun z : puncturedSpace (Fin (n + 1) → ℂ) ↦
      ‖complexToRealEuclidean (Fin (n + 1)) z‖ :=
    ((complexToRealEuclidean (Fin (n + 1))).continuous.comp continuous_subtypeVal).norm
  refine Continuous.subtype_mk (Continuous.prodMk ?_ ?_) _
  · rw [hmk]
    exact (contMDiff_mkNonzero ℂ n 0).continuous
  · exact (((Real.continuous_sqrt.comp ((hnorm.pow 2).sub continuous_const)).div hnorm
      fun z ↦ (pow_ne_zero_iff two_ne_zero).1 (norm_sq_complexToRealEuclidean_pos z).ne').smul
        continuous_subtypeVal)

/-- The blowdown of `shellPoint l z` has Euclidean norm `√(|z|² - l²)`. -/
private theorem norm_blowdown_shellPoint (l : ℝ) (z : puncturedSpace (Fin (n + 1) → ℂ)) :
    ‖complexToRealEuclidean (Fin (n + 1)) (shellPoint l z).blowdown‖ =
      √(‖complexToRealEuclidean (Fin (n + 1)) z‖ ^ 2 - l ^ 2) := by
  rw [blowdown_shellPoint, map_smul, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)),
    div_mul_cancel₀ _ ((pow_ne_zero_iff two_ne_zero).1 (norm_sq_complexToRealEuclidean_pos z).ne')]

private theorem shellPoint_of_norm_eq {z : puncturedSpace (Fin (n + 1) → ℂ)}
    (hz : ‖complexToRealEuclidean (Fin (n + 1)) z‖ = l) :
    shellPoint l z = zeroSection (mk ℂ (z : Fin (n + 1) → ℂ) (mem_puncturedSpace.1 z.property)) :=
  BlowupModel.ext ((pr_shellPoint l z).trans (pr_zeroSection _).symm) (by
    rw [blowdown_shellPoint, blowdown_zeroSection, hz, sub_self, Real.sqrt_zero, zero_div,
      zero_smul])

private theorem shellPoint_mem_openNbhd (hε : 0 < ε) {z : puncturedSpace (Fin (n + 1) → ℂ)}
    (hz : ‖complexToRealEuclidean (Fin (n + 1)) z‖ < √(l ^ 2 + ε ^ 2)) :
    shellPoint l z ∈ openNbhd n ε := by
  rw [mem_openNbhd_iff, norm_blowdown_shellPoint, Real.sqrt_lt' hε]
  have := (Real.lt_sqrt (norm_nonneg _)).1 hz
  linarith

private theorem shellPoint_notMem_exceptionalDivisor {z : puncturedSpace (Fin (n + 1) → ℂ)}
    (hl : 0 ≤ l) (hz : l < ‖complexToRealEuclidean (Fin (n + 1)) z‖) :
    shellPoint l z ∉ exceptionalDivisor n := by
  rw [mem_exceptionalDivisor_iff, ← ne_eq,
    ← map_ne_zero_iff _ (complexToRealEuclidean (Fin (n + 1))).injective,
    ← norm_ne_zero_iff, norm_blowdown_shellPoint, Real.sqrt_ne_zero', sub_pos]
  exact pow_lt_pow_left₀ hz hl two_ne_zero

/-- For `|z| > l`, the radial map `F_l` sends the blowdown of `shellPoint l z` back to `z`. -/
private theorem radialMap_shellPoint {z : puncturedSpace (Fin (n + 1) → ℂ)} (hl : 0 ≤ l)
    (hz : l < ‖complexToRealEuclidean (Fin (n + 1)) z‖)
    (b : puncturedSpace (Fin (n + 1) → ℂ))
    (hb : (b : Fin (n + 1) → ℂ) = (shellPoint l z).blowdown) :
    (radialMap (fun s ↦ s + l ^ 2) (fun _ hs ↦ add_pos_of_pos_of_nonneg hs (sq_nonneg l)) b :
      Fin (n + 1) → ℂ) = z := by
  have hd : 0 < ‖complexToRealEuclidean (Fin (n + 1)) z‖ ^ 2 - l ^ 2 :=
    sub_pos.2 (pow_lt_pow_left₀ hz hl two_ne_zero)
  have hn := (pow_ne_zero_iff two_ne_zero).1 (norm_sq_complexToRealEuclidean_pos z).ne'
  have hb' : ∑ i, ‖(b : Fin (n + 1) → ℂ) i‖ ^ 2 =
      ‖complexToRealEuclidean (Fin (n + 1)) z‖ ^ 2 - l ^ 2 := by
    rw [← norm_sq_complexToRealEuclidean, hb, norm_blowdown_shellPoint,
      Real.sq_sqrt hd.le]
  rw [radialMap_apply, hb', hb, blowdown_shellPoint, smul_smul, sub_add_cancel,
    Real.sqrt_div' _ hd.le, Real.sqrt_sq (norm_nonneg _)]
  have hs : √(‖complexToRealEuclidean (Fin (n + 1)) z‖ ^ 2 - l ^ 2) ≠ 0 :=
    (Real.sqrt_pos.2 hd).ne'
  rw [div_mul_div_comm, mul_comm, div_self (mul_ne_zero hs hn), one_smul]

variable [TopologicalSpace M] [ChartedSpace (Fin (n + 1) → ℂ) M]
  [IsManifold 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ M] [T2Space M]
  {σ : SmoothTwoForm 𝓘(ℝ, Fin (n + 1) → ℂ) M}

/-! ### The collapse map -/

open Classical in
/-- **The Hopf collapse map** onto the blowup of weight `l`: on `M ∖ ψ(B°(l))`, it is
`GluedAlong.inl` off `ψ(B(l))`, and sends `ψ w`, for `|w| = l`, to the point of the divisor over
the complex line `sphereHopf n (w / l)` through `w`. -/
def collapseMap (hψ : IsSymplecticBallEmbedding σ (√(l ^ 2 + ε ^ 2)) ψ) (hl : 0 < l)
    (hε : 0 < ε) (x : ((ψ '' ball 0 l)ᶜ : Set M)) : WeightBlowup hψ hl.le hε :=
  if hx : (x : M) ∈ ψ '' closedBall 0 l then
    divisor hψ hl.le hε (sphereHopf n ⟨l⁻¹ • hx.choose, inv_smul_mem_sphere hl <|
      norm_eq_of_mem_closedBall_of_notMem hx.choose_spec.1 (hx.choose_spec.2 ▸ x.property)⟩)
  else GluedAlong.inl _ ⟨x, (mem_outerPiece_iff hψ).2 hx⟩

variable (hψ : IsSymplecticBallEmbedding σ (√(l ^ 2 + ε ^ 2)) ψ) (hl : 0 < l) (hε : 0 < ε)

/-- Off `ψ(B(l))`, the collapse map is `inl`. -/
theorem collapseMap_of_notMem {x : ((ψ '' ball 0 l)ᶜ : Set M)}
    (hx : (x : M) ∉ ψ '' closedBall 0 l) :
    collapseMap hψ hl hε x = GluedAlong.inl _ ⟨x, (mem_outerPiece_iff hψ).2 hx⟩ := by
  rw [collapseMap, dite_eq_right_of_eq_false (eq_false hx)]

/-- On the sphere `ψ(∂B(l))`, the collapse map sends `ψ w` to the point of the divisor over the
line `sphereHopf n (w / l)` through `w`. -/
theorem collapseMap_of_norm_eq {w : StdSpace (Fin (n + 1))} (hw : ‖w‖ = l)
    (hx : ψ w ∈ (ψ '' ball 0 l)ᶜ) :
    collapseMap hψ hl hε ⟨ψ w, hx⟩ =
      divisor hψ hl.le hε (sphereHopf n ⟨l⁻¹ • w, by
        rw [mem_sphere_zero_iff_norm, norm_smul, hw, Real.norm_eq_abs, abs_inv, abs_of_pos hl,
          inv_mul_cancel₀ hl.ne']⟩) := by
  have hmem : ψ w ∈ ψ '' closedBall 0 l := ⟨w, mem_closedBall_zero_iff.2 hw.le, rfl⟩
  have hle : l ≤ √(l ^ 2 + ε ^ 2) := Real.le_sqrt_of_sq_le (by nlinarith)
  have hch : hmem.choose = w :=
    hψ.injOn (closedBall_subset_closedBall hle hmem.choose_spec.1)
      (closedBall_subset_closedBall hle (mem_closedBall_zero_iff.2 hw.le)) hmem.choose_spec.2
  rw [collapseMap, dite_eq_left_of_eq_true (eq_true hmem)]
  have key : ∀ (v : StdSpace (Fin (n + 1))) (_ : v = w) (h₁ : l⁻¹ • v ∈ sphere 0 1)
      (h₂ : l⁻¹ • w ∈ sphere 0 1), divisor hψ hl.le hε (sphereHopf n ⟨l⁻¹ • v, h₁⟩) =
        divisor hψ hl.le hε (sphereHopf n ⟨l⁻¹ • w, h₂⟩) := by
    rintro _ rfl _ _; rfl
  exact key _ hch _ _

/-- On the image of the open ball of radius `√(l² + ε²)`, the collapse map is continuous: there it
is `inr` of `shellPoint l` of the preimage under `ψ`, read in `E`. -/
private theorem continuousOn_collapseMap_image_ball :
    ContinuousOn (collapseMap hψ hl hε) (Subtype.val ⁻¹' (ψ '' ball 0 √(l ^ 2 + ε ^ 2))) := by
  set Φ := hψ.toPartialDiffeomorph
    (complexToRealEuclidean (Fin (n + 1))).toLinearEquiv.finrank_eq.symm
  have hle : l ≤ √(l ^ 2 + ε ^ 2) := Real.le_sqrt_of_sq_le (by nlinarith)
  rw [continuousOn_iff_continuous_domRestrict]
  set W := Subtype.val ⁻¹' (ψ '' ball 0 √(l ^ 2 + ε ^ 2))
  have htarget : ∀ y : W, ((y : ((ψ '' ball 0 l)ᶜ : Set M)) : M) ∈ Φ.target := fun y ↦ by
    rw [hψ.toPartialDiffeomorph_target]
    exact y.property
  have hsymm : ∀ y : W, Φ.symm y ∈ ball 0 √(l ^ 2 + ε ^ 2) ∧ ψ (Φ.symm y) = y := fun y ↦ by
    have h₁ := Φ.map_target (htarget y)
    have h₂ := Φ.right_inv (htarget y)
    rw [hψ.toPartialDiffeomorph_source] at h₁
    rw [hψ.coe_toPartialDiffeomorph] at h₂
    exact ⟨h₁, h₂⟩
  have hge : ∀ y : W, l ≤ ‖Φ.symm y‖ := fun y ↦
    not_lt.1 fun h ↦
      (y : ((ψ '' ball 0 l)ᶜ : Set M)).property ⟨_, mem_ball_zero_iff.2 h, (hsymm y).2⟩
  let z : W → puncturedSpace (Fin (n + 1) → ℂ) := fun y ↦
    ⟨(complexToRealEuclidean (Fin (n + 1))).symm (Φ.symm y), mem_puncturedSpace.2 <| by
      simpa using norm_pos_iff.1 (hl.trans_le (hge y))⟩
  have hnz : ∀ y, ‖complexToRealEuclidean (Fin (n + 1)) (z y)‖ = ‖Φ.symm y‖ := fun y ↦ by
    simp [z]
  have hz : Continuous z := by
    refine Continuous.subtype_mk ((complexToRealEuclidean (Fin (n + 1))).symm.continuous.comp ?_) _
    exact Φ.symm.contMDiffOn.continuousOn.comp_continuous
      (continuous_subtypeVal.comp continuous_subtypeVal) htarget
  have hQ : Continuous fun y ↦ (⟨shellPoint l (z y), mem_modelPiece_iff.2
      (shellPoint_mem_openNbhd hε ((hnz y).trans_lt (mem_ball_zero_iff.1 (hsymm y).1)))⟩ :
        modelPiece n ε) :=
    ((continuous_shellPoint l).comp hz).subtype_mk _
  refine ((GluedAlong.continuous_inr (gluingDiffeomorph hψ hl.le hε).symm).comp hQ).congr
    fun y ↦ ?_
  rw [Function.comp_apply, Set.domRestrict_apply]
  by_cases hy : ((y : ((ψ '' ball 0 l)ᶜ : Set M)) : M) ∈ ψ '' closedBall 0 l
  · obtain ⟨u, hu, hux⟩ := hy
    have hu' : u = Φ.symm y := hψ.injOn (closedBall_subset_closedBall hle hu)
      (ball_subset_closedBall (hsymm y).1) (hux.trans (hsymm y).2.symm)
    have hwl : ‖Φ.symm y‖ = l := le_antisymm (hu' ▸ mem_closedBall_zero_iff.1 hu) (hge y)
    have hmem : ψ (Φ.symm y) ∈ (ψ '' ball 0 l)ᶜ :=
      (hsymm y).2.symm ▸ (y : ((ψ '' ball 0 l)ᶜ : Set M)).property
    have hyw : collapseMap hψ hl hε y = collapseMap hψ hl hε ⟨ψ (Φ.symm y), hmem⟩ :=
      congrArg _ (Subtype.ext (hsymm y).2.symm)
    rw [hyw, collapseMap_of_norm_eq hψ hl hε hwl, divisor_apply]
    congr 2
    rw [shellPoint_of_norm_eq ((hnz y).trans hwl), sphereHopf_apply]
    congr 1
    rw [mk_eq_mk_iff']
    exact ⟨((l : ℝ) : ℂ), by
      rw [Complex.coe_smul, ← map_smul, smul_inv_smul₀ hl.ne']⟩
  · rw [collapseMap_of_notMem hψ hl hε hy]
    have hlt : l < ‖complexToRealEuclidean (Fin (n + 1)) (z y)‖ := by
      rw [hnz]
      refine (hge y).lt_of_ne fun h ↦ hy ⟨_, mem_closedBall_zero_iff.2 h.ge, (hsymm y).2⟩
    refine ((inl_eq_inr_iff hψ hl.le hε).2 ⟨mem_modelOverlap_iff.2
      (shellPoint_notMem_exceptionalDivisor hl.le hlt), Subtype.ext ?_⟩).symm
    rw [coe_gluingDiffeomorph_apply, coe_shellSymplectomorph_apply,
      radialMap_shellPoint hl.le hlt _ (coe_blowdownPuncturedDiffeomorph_apply _)]
    simpa [z] using (hsymm y).2

/-- **The collapse map is continuous.** -/
theorem continuous_collapseMap : Continuous (collapseMap hψ hl hε) := by
  have hlR : l < √(l ^ 2 + ε ^ 2) := (Real.lt_sqrt hl.le).2 (by nlinarith)
  refine continuous_iff_continuousAt.2 fun x ↦ ?_
  by_cases hx : (x : M) ∈ ψ '' closedBall 0 l
  · exact (continuousOn_collapseMap_image_ball hψ hl hε).continuousAt
      (((hψ.isOpen_image_ball
        (complexToRealEuclidean (Fin (n + 1))).toLinearEquiv.finrank_eq.symm).preimage
          continuous_subtypeVal).mem_nhds (image_mono (closedBall_subset_ball hlR) hx))
  · refine ContinuousOn.continuousAt ?_
      (((hψ.isCompact_image_closedBall hlR.le).isClosed.isOpen_compl.preimage
        continuous_subtypeVal).mem_nhds hx)
    rw [continuousOn_iff_continuous_domRestrict]
    refine ((GluedAlong.continuous_inl _).comp
      ((continuous_subtypeVal.comp continuous_subtypeVal).subtype_mk
        fun y ↦ (mem_outerPiece_iff hψ).2 y.property)).congr fun y ↦ ?_
    rw [Function.comp_apply, Set.domRestrict_apply, collapseMap_of_notMem hψ hl hε y.property]
    rfl

/-- **The collapse map is onto**: each point of the blowup is `inl` of a point off `ψ(B(l))`, or
`inr` of a point of the model piece off the divisor, which is glued to such a point, or a point of
the divisor, the image of a point of the sphere `ψ(∂B(l))`. -/
theorem surjective_collapseMap : Function.Surjective (collapseMap hψ hl hε) := by
  have hle : l ≤ √(l ^ 2 + ε ^ 2) := Real.le_sqrt_of_sq_le (by nlinarith)
  have hinl : ∀ x : outerPiece hψ, ∃ y, collapseMap hψ hl hε y = GluedAlong.inl _ x := fun x ↦
    ⟨⟨x, fun h ↦ (mem_outerPiece_iff hψ).1 x.property (image_mono ball_subset_closedBall h)⟩,
      collapseMap_of_notMem hψ hl hε ((mem_outerPiece_iff hψ).1 x.property)⟩
  intro p
  obtain ⟨x, rfl⟩ | ⟨y, rfl⟩ := GluedAlong.exists_inl_or_exists_inr _ p
  · exact hinl x
  by_cases hy : y ∈ modelOverlap n ε
  · obtain ⟨x, hx⟩ := hinl (gluingDiffeomorph hψ hl.le hε ⟨y, hy⟩)
    exact ⟨x, hx.trans (inl_gluingDiffeomorph hψ hl.le hε ⟨y, hy⟩)⟩
  rw [mem_modelOverlap_iff, not_not, exceptionalDivisor_eq_range] at hy
  obtain ⟨ℓ, hℓ⟩ := hy
  obtain ⟨s, rfl⟩ := surjective_sphereHopf n ℓ
  have hw : ‖l • (s : StdSpace (Fin (n + 1)))‖ = l := by
    rw [norm_smul, norm_eq_of_mem_sphere s, Real.norm_eq_abs, abs_of_pos hl, mul_one]
  refine ⟨⟨ψ (l • (s : StdSpace (Fin (n + 1)))), hψ.apply_notMem_image_ball hle hw⟩, ?_⟩
  rw [collapseMap_of_norm_eq hψ hl hε hw, divisor_apply]
  congr 1
  refine Subtype.ext ?_
  rw [← hℓ]
  exact congrArg (fun t ↦ zeroSection (sphereHopf n t)) (Subtype.ext (inv_smul_smul₀ hl.ne' _))

end WeightBlowup

end SymplecticGeometry

end
