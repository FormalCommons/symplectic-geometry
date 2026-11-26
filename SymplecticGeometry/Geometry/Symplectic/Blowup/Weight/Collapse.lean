/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Blowup.Weight.Basic
public import SymplecticGeometry.Analysis.Normed.Module.Ball.Pointwise
import SymplecticGeometry.Geometry.Manifold.Projectivization.Hopf
import SymplecticGeometry.Analysis.Complex.Euclidean.Space
import SymplecticGeometry.Analysis.Real.Sqrt

/-!
# The Hopf collapse onto the blowup of weight `λ`

Let `ψ` be a symplectic embedding of the closed ball of radius `√(l² + ε²)` into `M`, for
`0 < l` and `0 < ε`, and let `M̃_ψ = WeightBlowup hψ hl hε` be the blowup of weight `l` of
`Blowup/Weight/Basic.lean`. Following McDuff–Salamon, §7.1 (the construction (7.1.14)), the
blowup is obtained from `M ∖ ψ(B°(l))` by collapsing each Hopf circle of the sphere `ψ(∂B(l))` to
a point of the divisor. This file defines the collapse map, and shows that it is a quotient map
with these fibres, so that the blowup is homeomorphic to that quotient.

## Main definitions

* `SymplecticGeometry.WeightBlowup.collapseMap hψ hl hε`: the map from `M ∖ ψ(B°(l))` onto the
  blowup that is `GluedAlong.inl` off `ψ(B(l))` and sends `ψ w`, for `|w| = l`, to the point
  `divisor hψ hl hε` of the line `sphereHopf n (w / l)` through `w`.
* `SymplecticGeometry.WeightBlowup.collapseHomeomorph hψ hl hε`: the homeomorphism from the
  quotient of `M ∖ ψ(B°(l))` by the fibres of the collapse map onto the blowup.

## Main results

* `SymplecticGeometry.WeightBlowup.collapseMap_of_notMem` and
  `SymplecticGeometry.WeightBlowup.collapseMap_of_norm_eq`: the two cases of the collapse map.
* `SymplecticGeometry.WeightBlowup.collapseMap_eq_inr_shellPoint`: on the image of the open ball
  of radius `√(l² + ε²)`, the collapse map sends `ψ z`, for `|z| ≥ l`, to `inr` of the point
  `BlowupModel.shellPoint l z = ([z], √(|z|² - l²) / |z| • z)` of the model
  (`Blowup/Model.lean`): for `|z| = l` this is the zero section over `[z]`, and for `|z| > l`
  the preimage of `z` under the radial map `F_l ∘ π` that the gluing uses.
* `SymplecticGeometry.WeightBlowup.continuous_collapseMap`: the collapse map is continuous. Off
  `ψ(B(l))` it is `inl`, and near the sphere it is given by `collapseMap_eq_inr_shellPoint`, as
  `shellPoint l` is continuous on `z ≠ 0`.
* `SymplecticGeometry.WeightBlowup.surjective_collapseMap`: the collapse map is onto, since a point
  of the blowup is `inl` of a point of `M ∖ ψ(B(l))`, or `inr` of a point of the zero section,
  the image of a Hopf circle, or `inr` of a point glued to a point of `M ∖ ψ(B(l))`.
* `SymplecticGeometry.WeightBlowup.collapseMap_eq_collapseMap_iff`: the fibres of the collapse
  map are the points off the sphere `ψ(∂B(l))` and the images under `ψ` of the circles of that
  sphere on which `w ↦ sphereHopf n (w / l)` is constant, the Hopf circles.
* `SymplecticGeometry.WeightBlowup.isClosedMap_collapseMap` and
  `SymplecticGeometry.WeightBlowup.isQuotientMap_collapseMap`: the collapse map is closed, so a
  quotient map. A closed set of `M ∖ ψ(B°(l))` is the union of its part in the compact set
  `ψ(B(√(l² + ε²)))`, whose image is compact, and of its part off `ψ(B°(√(l² + ε²)))`, whose image
  under `inl` is closed, as the image of the model piece does not meet it.

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
    divisor hψ hl.le hε (sphereHopf n ⟨l⁻¹ • hx.choose, inv_smul_mem_sphere_one_of_norm_eq hl <|
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
      divisor hψ hl.le hε (sphereHopf n ⟨l⁻¹ • w, inv_smul_mem_sphere_one_of_norm_eq hl hw⟩) := by
  have hmem : ψ w ∈ ψ '' closedBall 0 l := ⟨w, mem_closedBall_zero_iff.2 hw.le, rfl⟩
  have hle : l ≤ √(l ^ 2 + ε ^ 2) := Real.le_sqrt_sq_add_sq l ε
  have hch : hmem.choose = w :=
    hψ.injOn (closedBall_subset_closedBall hle hmem.choose_spec.1)
      (closedBall_subset_closedBall hle (mem_closedBall_zero_iff.2 hw.le)) hmem.choose_spec.2
  rw [collapseMap, dite_eq_left_of_eq_true (eq_true hmem)]
  have key : ∀ (v : StdSpace (Fin (n + 1))) (_ : v = w) (h₁ : l⁻¹ • v ∈ sphere 0 1)
      (h₂ : l⁻¹ • w ∈ sphere 0 1), divisor hψ hl.le hε (sphereHopf n ⟨l⁻¹ • v, h₁⟩) =
        divisor hψ hl.le hε (sphereHopf n ⟨l⁻¹ • w, h₂⟩) := by
    rintro _ rfl _ _; rfl
  exact key _ hch _ _

/-- **The collapse map near the sphere.** For `z ≠ 0` in `ℂⁿ⁺¹` with `l ≤ |z| < √(l² + ε²)`, the
collapse map sends `ψ z`, with `z` read in `E`, to `inr` of the point `shellPoint l z` of the
model piece. For `|z| = l` both sides are the point of the divisor over `[z]`, and for `|z| > l`
the point `shellPoint l z` is glued to `ψ z`. -/
theorem collapseMap_eq_inr_shellPoint {z : puncturedSpace (Fin (n + 1) → ℂ)}
    (hlz : l ≤ ‖complexToRealEuclidean (Fin (n + 1)) z‖)
    (hz : ‖complexToRealEuclidean (Fin (n + 1)) z‖ < √(l ^ 2 + ε ^ 2))
    (hx : ψ (complexToRealEuclidean (Fin (n + 1)) z) ∈ (ψ '' ball 0 l)ᶜ) :
    collapseMap hψ hl hε ⟨ψ (complexToRealEuclidean (Fin (n + 1)) z), hx⟩ =
      GluedAlong.inr (gluingDiffeomorphSymm hψ hl.le hε).toHomeomorph
        ⟨shellPoint l z, mem_modelPiece_iff.2 (shellPoint_mem_openNbhd hε hz)⟩ := by
  have hle : l ≤ √(l ^ 2 + ε ^ 2) := Real.le_sqrt_sq_add_sq l ε
  rcases hlz.eq_or_lt with hlz | hlz
  · -- On the sphere, both sides are the point of the divisor over the line of `z`.
    rw [collapseMap_of_norm_eq hψ hl hε hlz.symm, divisor_apply]
    congr 2
    rw [shellPoint_of_norm_eq hlz.symm, sphereHopf_apply]
    congr 1
    rw [mk_eq_mk_iff']
    exact ⟨((l⁻¹ : ℝ) : ℂ), by rw [Complex.coe_smul]; simp⟩
  · -- Off the sphere, `ψ z` is off `ψ(B(l))`, and glued to `shellPoint l z`.
    have hx' : ψ (complexToRealEuclidean (Fin (n + 1)) z) ∉ ψ '' closedBall 0 l := by
      rintro ⟨u, hu, hux⟩
      have hu' := hψ.injOn (closedBall_subset_closedBall hle hu)
        (mem_closedBall_zero_iff.2 hz.le) hux
      exact (mem_closedBall_zero_iff.1 hu).not_gt (hu' ▸ hlz)
    rw [collapseMap_of_notMem hψ hl hε hx']
    refine (inl_eq_inr_iff hψ hl.le hε).2 ⟨(mem_modelOverlap_iff (p := ⟨shellPoint l z,
      mem_modelPiece_iff.2 (shellPoint_mem_openNbhd hε hz)⟩)).2
        (shellPoint_notMem_exceptionalDivisor hl.le hlz), Subtype.ext ?_⟩
    rw [coe_gluingDiffeomorph_apply, coe_shellSymplectomorph_apply,
      ← coe_radialBlowdownDiffeomorph_apply, coe_radialBlowdownDiffeomorph_shellPoint hl.le hlz]

/-- On the image of the open ball of radius `√(l² + ε²)`, the collapse map is continuous: there it
is `inr` of `shellPoint l` of the preimage under `ψ`, read in `ℂⁿ⁺¹`
(`collapseMap_eq_inr_shellPoint`). -/
private theorem continuousOn_collapseMap_image_ball :
    ContinuousOn (collapseMap hψ hl hε) (Subtype.val ⁻¹' (ψ '' ball 0 √(l ^ 2 + ε ^ 2))) := by
  -- The inverse `Φ.symm` of `ψ ∘ complexToRealEuclidean` on its image.
  set Φ := complexPartialDiffeomorph hψ
  rw [continuousOn_iff_continuous_domRestrict]
  set W := Subtype.val ⁻¹' (ψ '' ball 0 √(l ^ 2 + ε ^ 2))
  have htarget : ∀ y : W, ((y : ((ψ '' ball 0 l)ᶜ : Set M)) : M) ∈ Φ.target := fun y ↦ by
    rw [complexPartialDiffeomorph_target]
    exact y.property
  have hlt : ∀ y : W, ‖complexToRealEuclidean (Fin (n + 1)) (Φ.symm y)‖ < √(l ^ 2 + ε ^ 2) :=
    fun y ↦ (mem_complexPartialDiffeomorph_source_iff hψ).1 (Φ.map_target (htarget y))
  have hψz : ∀ y : W, ψ (complexToRealEuclidean (Fin (n + 1)) (Φ.symm y)) = y := fun y ↦ by
    simpa [Φ] using Φ.right_inv (htarget y)
  have hge : ∀ y : W, l ≤ ‖complexToRealEuclidean (Fin (n + 1)) (Φ.symm y)‖ := fun y ↦
    not_lt.1 fun h ↦
      (y : ((ψ '' ball 0 l)ᶜ : Set M)).property ⟨_, mem_ball_zero_iff.2 h, hψz y⟩
  -- The preimage `z y` of `y` under `ψ`, read in `ℂⁿ⁺¹`, depends continuously on `y`.
  obtain ⟨z, hz, hzy⟩ : ∃ z : W → puncturedSpace (Fin (n + 1) → ℂ),
      Continuous z ∧ ∀ y, (z y : Fin (n + 1) → ℂ) = Φ.symm y :=
    ⟨fun y ↦ ⟨Φ.symm y, mem_puncturedSpace.2 fun h ↦
        (hl.trans_le (hge y)).ne' (by rw [h, map_zero, norm_zero])⟩,
      (Φ.symm.contMDiffOn.continuousOn.comp_continuous
        (continuous_subtypeVal.comp continuous_subtypeVal) htarget).subtype_mk _, fun _ ↦ rfl⟩
  -- On `W`, the collapse map is `inr ∘ shellPoint l ∘ z`.
  refine ((GluedAlong.continuous_inr (gluingDiffeomorphSymm hψ hl.le hε).toHomeomorph).comp
    (((continuous_shellPoint l).comp hz).subtype_mk fun y ↦ mem_modelPiece_iff.2
      (shellPoint_mem_openNbhd hε ((hzy y).symm ▸ hlt y)))).congr fun y ↦ ?_
  have hx : ψ (complexToRealEuclidean (Fin (n + 1)) (z y)) ∈ (ψ '' ball 0 l)ᶜ := by
    rw [hzy, hψz y]
    exact (y : ((ψ '' ball 0 l)ᶜ : Set M)).property
  have hy : collapseMap hψ hl hε y = collapseMap hψ hl hε ⟨_, hx⟩ :=
    congrArg _ (Subtype.ext ((congrArg (fun w ↦ ψ (complexToRealEuclidean (Fin (n + 1)) w))
      (hzy y)).trans (hψz y)).symm)
  rw [Function.comp_apply, Set.domRestrict_apply, hy, collapseMap_eq_inr_shellPoint hψ hl hε
    ((hzy y).symm ▸ hge y) ((hzy y).symm ▸ hlt y) hx]
  rfl

/-- **The collapse map is continuous.** -/
theorem continuous_collapseMap : Continuous (collapseMap hψ hl hε) := by
  have hlR : l < √(l ^ 2 + ε ^ 2) := Real.lt_sqrt_sq_add_sq l hε.ne'
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
  have hle : l ≤ √(l ^ 2 + ε ^ 2) := Real.le_sqrt_sq_add_sq l ε
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

/-! ### The collapse map is a quotient map, and its fibres -/

/-- A point of `M ∖ ψ(B°(l))` in `ψ(B(l))` is `ψ w` for a `w` with `|w| = l`, and the collapse map
sends it to the point of the divisor over `sphereHopf n (w / l)`. -/
private theorem exists_collapseMap_eq_divisor {x : ((ψ '' ball 0 l)ᶜ : Set M)}
    (hx : (x : M) ∈ ψ '' closedBall 0 l) :
    ∃ (w : StdSpace (Fin (n + 1))) (hw : ‖w‖ = l), ψ w = x ∧ collapseMap hψ hl hε x =
      divisor hψ hl.le hε (sphereHopf n ⟨l⁻¹ • w, inv_smul_mem_sphere_one_of_norm_eq hl hw⟩) := by
  obtain ⟨x, hx'⟩ := x
  obtain ⟨w, hwB, rfl⟩ := hx
  have hw := norm_eq_of_mem_closedBall_of_notMem hwB hx'
  exact ⟨w, hw, rfl, collapseMap_of_norm_eq hψ hl hε hw hx'⟩

/-- **The fibres of the collapse map**: two points of `M ∖ ψ(B°(l))` have the same image exactly
when they are equal, or are `ψ v` and `ψ w` for `v`, `w` on the sphere `|v| = |w| = l` with
`sphereHopf n (v / l) = sphereHopf n (w / l)`, that is, on the same Hopf circle
(`sphereHopf_eq_sphereHopf_iff`). -/
theorem collapseMap_eq_collapseMap_iff {x y : ((ψ '' ball 0 l)ᶜ : Set M)} :
    collapseMap hψ hl hε x = collapseMap hψ hl hε y ↔ x = y ∨
      ∃ (v w : StdSpace (Fin (n + 1))) (hv : ‖v‖ = l) (hw : ‖w‖ = l), ψ v = x ∧ ψ w = y ∧
        sphereHopf n ⟨l⁻¹ • v, inv_smul_mem_sphere_one_of_norm_eq hl hv⟩ =
          sphereHopf n ⟨l⁻¹ • w, inv_smul_mem_sphere_one_of_norm_eq hl hw⟩ := by
  -- A point of the divisor is not `inl` of a point of the outer piece.
  have hne : ∀ (ℓ) (z : outerPiece hψ), divisor hψ hl.le hε ℓ ≠ GluedAlong.inl _ z :=
    fun ℓ z h ↦ (Set.ext_iff.1 (range_divisor hψ hl.le hε) _).1 ⟨ℓ, h⟩
      (inl_mem_complDivisor hψ hl.le hε z)
  constructor
  · intro h
    by_cases hx : (x : M) ∈ ψ '' closedBall 0 l <;> by_cases hy : (y : M) ∈ ψ '' closedBall 0 l
    · obtain ⟨v, hv, hvx, hfx⟩ := exists_collapseMap_eq_divisor hψ hl hε hx
      obtain ⟨w, hw, hwy, hfy⟩ := exists_collapseMap_eq_divisor hψ hl hε hy
      rw [hfx, hfy] at h
      exact Or.inr ⟨v, w, hv, hw, hvx, hwy, (divisor hψ hl.le hε).isEmbedding.injective h⟩
    · obtain ⟨v, hv, -, hfx⟩ := exists_collapseMap_eq_divisor hψ hl hε hx
      rw [hfx, collapseMap_of_notMem hψ hl hε hy] at h
      exact (hne _ _ h).elim
    · obtain ⟨w, hw, -, hfy⟩ := exists_collapseMap_eq_divisor hψ hl hε hy
      rw [hfy, collapseMap_of_notMem hψ hl hε hx] at h
      exact (hne _ _ h.symm).elim
    · rw [collapseMap_of_notMem hψ hl hε hx, collapseMap_of_notMem hψ hl hε hy,
        GluedAlong.inl_inj] at h
      exact Or.inl (Subtype.ext (congrArg (fun z : outerPiece hψ ↦ (z : M)) h))
  · obtain ⟨x, hx⟩ := x
    obtain ⟨y, hy⟩ := y
    rintro (h | ⟨v, w, hv, hw, rfl, rfl, h⟩)
    · rw [h]
    · rw [collapseMap_of_norm_eq hψ hl hε hv, collapseMap_of_norm_eq hψ hl hε hw, h]

/-- **The collapse map is closed**: it sends closed subsets of `M ∖ ψ(B°(l))` to closed subsets of
the blowup. -/
theorem isClosedMap_collapseMap : IsClosedMap (collapseMap hψ hl hε) := by
  set R := √(l ^ 2 + ε ^ 2)
  have hlR : l < R := Real.lt_sqrt_sq_add_sq l hε.ne'
  have hdim := (complexToRealEuclidean (Fin (n + 1))).toLinearEquiv.finrank_eq.symm
  intro C hC
  have hCM : IsClosed (Subtype.val '' C : Set M) :=
    ((hψ.mono hlR.le).isOpen_image_ball hdim).isClosed_compl.isClosedMap_subtypeVal C hC
  -- The part of `C` in `ψ(B(R))`, and the part off `ψ(B°(R))`.
  set K := C ∩ Subtype.val ⁻¹' (ψ '' closedBall 0 R)
  set A := C ∩ Subtype.val ⁻¹' (ψ '' ball 0 R)ᶜ
  have hCKA : C = K ∪ A := by
    rw [← inter_union_distrib_left, ← preimage_union]
    refine (inter_eq_left.2 fun x _ ↦ ?_).symm
    by_cases hx : (x : M) ∈ ψ '' ball 0 R
    · exact Or.inl (image_mono ball_subset_closedBall hx)
    · exact Or.inr hx
  rw [hCKA, image_union]
  refine IsClosed.union ?_ ?_
  · refine (IsCompact.image ?_ (continuous_collapseMap hψ hl hε)).isClosed
    rw [Subtype.isCompact_iff, image_inter_preimage]
    exact (hψ.isCompact_image_closedBall le_rfl).inter_left hCM
  -- On `A`, the collapse map is `inl` of the set `S` of points of the outer piece in `val '' A`.
  set S : Set (outerPiece hψ) := {x | (x : M) ∈ Subtype.val '' C ∧ (x : M) ∉ ψ '' ball 0 R}
  have hS : IsClosed S :=
    (hCM.inter (hψ.isOpen_image_ball hdim).isClosed_compl).preimage continuous_subtypeVal
  have hnot : ∀ {x : M}, x ∉ ψ '' ball 0 R → x ∉ ψ '' closedBall 0 l :=
    fun hx h ↦ hx (image_mono (closedBall_subset_ball hlR) h)
  have hAS : collapseMap hψ hl hε '' A = GluedAlong.inl _ '' S := by
    ext z
    constructor
    · rintro ⟨x, ⟨hxC, hxR⟩, rfl⟩
      exact ⟨⟨x, (mem_outerPiece_iff hψ).2 (hnot hxR)⟩, ⟨⟨x, hxC, rfl⟩, hxR⟩,
        (collapseMap_of_notMem hψ hl hε (hnot hxR)).symm⟩
    · rintro ⟨x', ⟨⟨x, hxC, hxx⟩, hxR⟩, rfl⟩
      have hxR' : (x : M) ∉ ψ '' ball 0 R := fun h ↦ hxR (hxx ▸ h)
      refine ⟨x, ⟨hxC, hxR'⟩, ?_⟩
      rw [collapseMap_of_notMem hψ hl hε (hnot hxR')]
      exact congrArg _ (Subtype.ext hxx)
  rw [hAS]
  exact GluedAlong.isClosed_image_inl _ hS
    (disjoint_left.2 fun x hx hxU ↦ hx.2 ((mem_outerOverlap_iff hψ).1 hxU))

/-- **The collapse map is a quotient map**: it is continuous, onto and closed. -/
theorem isQuotientMap_collapseMap : IsQuotientMap (collapseMap hψ hl hε) :=
  (isClosedMap_collapseMap hψ hl hε).isQuotientMap (continuous_collapseMap hψ hl hε)
    (surjective_collapseMap hψ hl hε)

/-- **The blowup as a quotient**: the homeomorphism from the quotient of `M ∖ ψ(B°(l))` by the
fibres of the collapse map, which are the points off the sphere `ψ(∂B(l))` and the Hopf circles
of that sphere (`collapseMap_eq_collapseMap_iff`), onto the blowup of weight `l`. -/
def collapseHomeomorph :
    Quotient (Setoid.ker (collapseMap hψ hl hε)) ≃ₜ WeightBlowup hψ hl.le hε :=
  (isQuotientMap_collapseMap hψ hl hε).homeomorph (f := ⟨_, continuous_collapseMap hψ hl hε⟩)

/-- `collapseHomeomorph` sends the class of a point to its image under the collapse map. -/
@[simp]
theorem collapseHomeomorph_mk (x : ((ψ '' ball 0 l)ᶜ : Set M)) :
    collapseHomeomorph hψ hl hε (Quotient.mk _ x) = collapseMap hψ hl hε x :=
  (rfl)

end WeightBlowup

end SymplecticGeometry

end
