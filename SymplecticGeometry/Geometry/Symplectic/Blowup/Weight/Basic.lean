/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Gluing.Pair
public import SymplecticGeometry.Geometry.Symplectic.Blowup.Model
public import SymplecticGeometry.Geometry.Symplectic.IsotopyExtension.Ball.Basic

/-!
# The blowup of weight `λ` along a symplectic ball: the glued manifold

Let `M` be a smooth manifold modelled on `E := Fin (n + 1) → ℂ`, let `σ` be a two-form on `M`,
and let `ψ : StdSpace (Fin (n + 1)) → M` be a symplectic embedding of the closed ball of radius
`√(l² + ε²)` (`IsSymplecticBallEmbedding σ (√(l ^ 2 + ε ^ 2)) ψ`), for `0 ≤ l` and `0 ≤ ε`. The
weight `λ` of McDuff–Salamon is called `l` here, as in `Blowup/Model.lean`. Following
McDuff–Salamon, §7.1, the blowup `M̃_ψ` of weight `l` is obtained by removing the closed ball
`ψ(B(l))` from `M` and gluing in the neighbourhood `openNbhd n ε` of the exceptional divisor `Z`
of the model blowup `L = BlowupModel n`: a point `p` of `openNbhd n ε ∖ Z` is identified with
`ψ(F_l(π p))`, where `F_l z = √(1 + l² / |z|²) z` is the radial map and `π` the blowdown, read
on `StdSpace` through `complexToRealEuclidean`. The map `p ↦ F_l(π p)` is
`BlowupModel.shellSymplectomorph`, a diffeomorphism of `openNbhd n ε ∖ Z` onto the open shell
`l < |w| < √(l² + ε²)` of `E`, which `ψ` maps diffeomorphically onto an open subset of
`M ∖ ψ(B(l))`.

## Main definitions

* `SymplecticGeometry.WeightBlowup.outerPiece hψ`: the open subset `M ∖ ψ(B(l))` of `M`, for
  Hausdorff `M`.
* `SymplecticGeometry.WeightBlowup.modelPiece n ε`: the open subset `openNbhd n ε` of the model.
* `SymplecticGeometry.WeightBlowup.shellImage hψ`: the image under `ψ` of the open shell
  `l < |w| < √(l² + ε²)`, an open subset of `M`.
* `SymplecticGeometry.WeightBlowup.gluingDiffeomorph hψ hl hε`: the diffeomorphism
  `p ↦ ψ(F_l(π p))` from `openNbhd n ε ∖ Z`, as an open subset of the model piece, onto
  `shellImage hψ`, as an open subset of the outer piece.
* `SymplecticGeometry.WeightBlowup hψ hl hε`: the blowup of weight `l`, the space
  `SymplecticGeometry.GluedAlong` of `Geometry/Manifold/Gluing/Pair.lean` glued from the two
  pieces along the inverse of `gluingDiffeomorph`. It is a smooth manifold modelled on `E`, and
  second countable when `M` is, by the instances of `GluedAlong`.
* `SymplecticGeometry.WeightBlowup.inl`, `SymplecticGeometry.WeightBlowup.inr`: the open
  embeddings of the two pieces.

## Main results

* `SymplecticGeometry.WeightBlowup.coe_gluingDiffeomorph_apply`: the gluing map is
  `ψ ∘ complexToRealEuclidean ∘ shellSymplectomorph`.
* `SymplecticGeometry.WeightBlowup.inl_eq_inr_iff`: the identification made by the gluing.
* `SymplecticGeometry.WeightBlowup.instT2Space`: the blowup is Hausdorff. A point of `Z` and a
  point `x ∉ ψ(B(l))` that is not glued to the model are separated, for `0 < δ < ε`, by
  `openNbhd n δ` and the complement of the compact set `ψ(B(√(l² + δ²)))`, which does not contain
  `x`, since `x` is not in the image of the open ball of radius `√(l² + ε²)`. This is the
  criterion `GluedAlong.t2Space_iff`.

The gluing follows the other uses of `GluedAlong` in the library, the capped surface of
`Geometry/Manifold/Gluing/CapDiscs/Basic.lean` and the fiber sum of
`Geometry/Symplectic/Sum/Fibre.lean`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §7.1.
-/

public section

noncomputable section

open Set Metric Topology TopologicalSpace TauCeti
open scoped Manifold ContDiff TauCeti.ComplexManifold

namespace SymplecticGeometry

namespace WeightBlowup

open BlowupModel

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Fin (n + 1) → ℂ) M]
  [IsManifold 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ M]
  {σ : SmoothTwoForm 𝓘(ℝ, Fin (n + 1) → ℂ) M} {ψ : StdSpace (Fin (n + 1)) → M} {l ε : ℝ}

/-- `l ≤ √(l² + ε²)`. -/
private theorem le_sqrt_sq_add_sq (l ε : ℝ) : l ≤ √(l ^ 2 + ε ^ 2) :=
  Real.le_sqrt_of_sq_le (le_add_of_nonneg_right (sq_nonneg ε))

/-- `ψ` read on `E` through `complexToRealEuclidean`, as a partial diffeomorphism of `E` into `M`
on the preimage of the open ball of radius `√(l² + ε²)`. -/
private def complexPartialDiffeomorph
    (hψ : IsSymplecticBallEmbedding σ (√(l ^ 2 + ε ^ 2)) ψ) :
    PartialDiffeomorph 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) (Fin (n + 1) → ℂ) M ∞ :=
  (complexToRealEuclidean (Fin (n + 1))).toPartialDiffeomorph.trans
    (hψ.toPartialDiffeomorph (complexToRealEuclidean (Fin (n + 1))).toLinearEquiv.finrank_eq.symm)

private theorem coe_complexPartialDiffeomorph
    (hψ : IsSymplecticBallEmbedding σ (√(l ^ 2 + ε ^ 2)) ψ) :
    ⇑(complexPartialDiffeomorph hψ) = ψ ∘ complexToRealEuclidean (Fin (n + 1)) := by
  simp [complexPartialDiffeomorph]

private theorem mem_complexPartialDiffeomorph_source_iff
    (hψ : IsSymplecticBallEmbedding σ (√(l ^ 2 + ε ^ 2)) ψ) {w : Fin (n + 1) → ℂ} :
    w ∈ (complexPartialDiffeomorph hψ).source ↔
      ‖complexToRealEuclidean (Fin (n + 1)) w‖ < √(l ^ 2 + ε ^ 2) := by
  simp [complexPartialDiffeomorph]

variable [T2Space M]

/-- The first piece of the blowup: the open subset `M ∖ ψ(B(l))` of `M`. -/
def outerPiece (hψ : IsSymplecticBallEmbedding σ (√(l ^ 2 + ε ^ 2)) ψ) : Opens M :=
  ⟨(ψ '' closedBall 0 l)ᶜ,
    (hψ.isCompact_image_closedBall (le_sqrt_sq_add_sq l ε)).isClosed.isOpen_compl⟩

@[simp]
theorem mem_outerPiece_iff (hψ : IsSymplecticBallEmbedding σ (√(l ^ 2 + ε ^ 2)) ψ) {x : M} :
    x ∈ outerPiece hψ ↔ x ∉ ψ '' closedBall 0 l :=
  Iff.rfl

variable (n) in
/-- The second piece of the blowup: the open neighbourhood `openNbhd n ε` of the exceptional
divisor in the model blowup. -/
def modelPiece (ε : ℝ) : Opens (BlowupModel n) :=
  ⟨openNbhd n ε, isOpen_openNbhd ε⟩

@[simp]
theorem mem_modelPiece_iff {p : BlowupModel n} : p ∈ modelPiece n ε ↔ p ∈ openNbhd n ε :=
  Iff.rfl

/-- The image under `ψ` of the open shell `l < |w| < √(l² + ε²)`: the points of the image of the
open ball of radius `√(l² + ε²)` that are not in `ψ(B(l))`. -/
def shellImage (hψ : IsSymplecticBallEmbedding σ (√(l ^ 2 + ε ^ 2)) ψ) : Opens M :=
  ⟨ψ '' ball 0 √(l ^ 2 + ε ^ 2) \ ψ '' closedBall 0 l,
    (hψ.isOpen_image_ball (complexToRealEuclidean (Fin (n + 1))).toLinearEquiv.finrank_eq.symm
      ).sdiff (hψ.isCompact_image_closedBall (le_sqrt_sq_add_sq l ε)).isClosed⟩

@[simp]
theorem mem_shellImage_iff (hψ : IsSymplecticBallEmbedding σ (√(l ^ 2 + ε ^ 2)) ψ) {x : M} :
    x ∈ shellImage hψ ↔ x ∈ ψ '' ball 0 √(l ^ 2 + ε ^ 2) ∧ x ∉ ψ '' closedBall 0 l :=
  Iff.rfl

theorem shellImage_le_outerPiece (hψ : IsSymplecticBallEmbedding σ (√(l ^ 2 + ε ^ 2)) ψ) :
    shellImage hψ ≤ outerPiece hψ :=
  fun _ hx ↦ hx.2

/-- A point `w` of `E` with `|w| < √(l² + ε²)` lies in the open shell exactly when `ψ` maps it,
read on `StdSpace`, into `shellImage hψ`. -/
theorem mem_openShell_iff_mem_shellImage (hψ : IsSymplecticBallEmbedding σ (√(l ^ 2 + ε ^ 2)) ψ)
    {w : Fin (n + 1) → ℂ} (hw : ‖complexToRealEuclidean (Fin (n + 1)) w‖ < √(l ^ 2 + ε ^ 2)) :
    w ∈ openShell n l ε ↔ ψ (complexToRealEuclidean (Fin (n + 1)) w) ∈ shellImage hψ := by
  rw [mem_openShell_iff, mem_shellImage_iff]
  refine ⟨fun h ↦ ⟨⟨_, mem_ball_zero_iff.2 hw, rfl⟩, ?_⟩, fun h ↦ ⟨?_, hw⟩⟩
  · rintro ⟨v, hv, hvw⟩
    have hle := closedBall_subset_closedBall (le_sqrt_sq_add_sq l ε) hv
    rw [hψ.injOn hle (ball_subset_closedBall (mem_ball_zero_iff.2 hw)) hvw,
      mem_closedBall_zero_iff] at hv
    exact h.1.not_ge hv
  · exact not_le.1 fun hle ↦ h.2 ⟨_, mem_closedBall_zero_iff.2 hle, rfl⟩

/-- The map `ψ ∘ complexToRealEuclidean` as a diffeomorphism from the open shell
`l < |w| < √(l² + ε²)` of `E` onto `shellImage hψ`. -/
def shellDiffeomorph (hψ : IsSymplecticBallEmbedding σ (√(l ^ 2 + ε ^ 2)) ψ) :
    openShell n l ε ≃ₘ⟮𝓘(ℝ, Fin (n + 1) → ℂ), 𝓘(ℝ, Fin (n + 1) → ℂ)⟯ shellImage hψ :=
  (Diffeomorph.nestedOpen
      (U := openShell n l ε) (D := ⟨_, (complexPartialDiffeomorph hψ).open_source⟩) fun _ hw ↦
        (mem_complexPartialDiffeomorph_source_iff hψ).2 (mem_openShell_iff.1 hw).2).symm.trans
    (((complexPartialDiffeomorph hψ).toDiffeomorphSourceTarget.subtype fun w ↦ by
        simp only [Opens.mem_comap, ContinuousMap.coe_mk,
          PartialDiffeomorph.toDiffeomorphSourceTarget_apply_coe, coe_complexPartialDiffeomorph,
          Function.comp_apply]
        exact mem_openShell_iff_mem_shellImage hψ
          ((mem_complexPartialDiffeomorph_source_iff hψ).1 w.property)).trans
      (Diffeomorph.nestedOpen fun _ hx ↦ by
        obtain ⟨⟨v, hv, rfl⟩, -⟩ := hx
        have hv' : (complexToRealEuclidean (Fin (n + 1))).symm v ∈
            (complexPartialDiffeomorph hψ).source := by
          rw [mem_complexPartialDiffeomorph_source_iff]
          simpa using hv
        have := (complexPartialDiffeomorph hψ).map_source hv'
        rwa [coe_complexPartialDiffeomorph, Function.comp_apply,
          ContinuousLinearEquiv.apply_symm_apply] at this))

@[simp]
theorem coe_shellDiffeomorph_apply (hψ : IsSymplecticBallEmbedding σ (√(l ^ 2 + ε ^ 2)) ψ)
    (w : openShell n l ε) :
    (shellDiffeomorph hψ w : M) = ψ (complexToRealEuclidean (Fin (n + 1)) w) := by
  simp [shellDiffeomorph, coe_complexPartialDiffeomorph]

variable (n ε) in
theorem sdiff_le_modelPiece :
    (⟨openNbhd n ε \ exceptionalDivisor n, (isOpen_openNbhd ε).sdiff isClosed_exceptionalDivisor⟩ :
      Opens (BlowupModel n)) ≤ modelPiece n ε :=
  fun _ hp ↦ hp.1

variable (n ε) in
/-- The overlap on the side of the model: `openNbhd n ε ∖ Z`, as an open subset of the model
piece. -/
abbrev modelOverlap : Opens (modelPiece n ε) :=
  Opens.comap ⟨Subtype.val, continuous_subtypeVal⟩
    ⟨openNbhd n ε \ exceptionalDivisor n, (isOpen_openNbhd ε).sdiff isClosed_exceptionalDivisor⟩

@[simp]
theorem mem_modelOverlap_iff {p : modelPiece n ε} :
    p ∈ modelOverlap n ε ↔ (p : BlowupModel n) ∉ exceptionalDivisor n := by
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨p.property, h⟩⟩

/-- The overlap on the side of `M`: `shellImage hψ`, as an open subset of the outer piece. -/
abbrev outerOverlap (hψ : IsSymplecticBallEmbedding σ (√(l ^ 2 + ε ^ 2)) ψ) :
    Opens (outerPiece hψ) :=
  Opens.comap ⟨Subtype.val, continuous_subtypeVal⟩ (shellImage hψ)

@[simp]
theorem mem_outerOverlap_iff (hψ : IsSymplecticBallEmbedding σ (√(l ^ 2 + ε ^ 2)) ψ)
    {x : outerPiece hψ} : x ∈ outerOverlap hψ ↔ (x : M) ∈ ψ '' ball 0 √(l ^ 2 + ε ^ 2) := by
  simp only [outerOverlap, Opens.mem_comap, ContinuousMap.coe_mk, mem_shellImage_iff,
    and_iff_left_iff_imp]
  exact fun _ ↦ x.property

/-- **The gluing map** of the blowup of weight `l`: the diffeomorphism `p ↦ ψ(F_l(π p))`, which
is `ψ ∘ complexToRealEuclidean ∘ shellSymplectomorph`, from `openNbhd n ε ∖ Z` in the model
piece onto `shellImage hψ` in the outer piece. -/
def gluingDiffeomorph (hψ : IsSymplecticBallEmbedding σ (√(l ^ 2 + ε ^ 2)) ψ) (hl : 0 ≤ l)
    (hε : 0 ≤ ε) :
    modelOverlap n ε ≃ₘ⟮𝓘(ℝ, Fin (n + 1) → ℂ), 𝓘(ℝ, Fin (n + 1) → ℂ)⟯ outerOverlap hψ :=
  (Diffeomorph.nestedOpen (sdiff_le_modelPiece n ε)).trans
    ((shellSymplectomorph n l ε hl hε).trans
      ((shellDiffeomorph hψ).trans (Diffeomorph.nestedOpen (shellImage_le_outerPiece hψ)).symm))

@[simp]
theorem coe_gluingDiffeomorph_apply (hψ : IsSymplecticBallEmbedding σ (√(l ^ 2 + ε ^ 2)) ψ)
    (hl : 0 ≤ l) (hε : 0 ≤ ε) (p : modelOverlap n ε) :
    ((gluingDiffeomorph hψ hl hε p : outerPiece hψ) : M) =
      ψ (complexToRealEuclidean (Fin (n + 1))
        (shellSymplectomorph n l ε hl hε
          ⟨p.val.val, mem_modelPiece_iff.1 p.val.property,
            mem_modelOverlap_iff.1 p.property⟩)) := by
  simp only [gluingDiffeomorph, Diffeomorph.coe_trans, Function.comp_apply,
    Diffeomorph.nestedOpen_apply, Diffeomorph.nestedOpen_symm_apply, coe_shellDiffeomorph_apply]

/-- **The blowup of weight `l`** of `M` along the symplectic ball embedding `ψ`, following
McDuff–Salamon, §7.1: the outer piece `M ∖ ψ(B(l))` and the model piece `openNbhd n ε` glued
along the inverse of `gluingDiffeomorph`, which identifies `p ∈ openNbhd n ε ∖ Z` with
`ψ(F_l(π p))`. It is a smooth manifold modelled on `Fin (n + 1) → ℂ`. -/
abbrev _root_.SymplecticGeometry.WeightBlowup
    (hψ : IsSymplecticBallEmbedding σ (√(l ^ 2 + ε ^ 2)) ψ) (hl : 0 ≤ l) (hε : 0 ≤ ε) : Type :=
  GluedAlong (gluingDiffeomorph hψ hl hε).symm

variable (hψ : IsSymplecticBallEmbedding σ (√(l ^ 2 + ε ^ 2)) ψ) (hl : 0 ≤ l) (hε : 0 ≤ ε)

example : IsManifold 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ (WeightBlowup hψ hl hε) := inferInstance

example [SecondCountableTopology M] : SecondCountableTopology (WeightBlowup hψ hl hε) :=
  inferInstance

/-- The open embedding of the outer piece `M ∖ ψ(B(l))` into the blowup. -/
def inl : outerPiece hψ → WeightBlowup hψ hl hε :=
  GluedAlong.inl _

/-- The open embedding of the model piece `openNbhd n ε` into the blowup. -/
def inr : modelPiece n ε → WeightBlowup hψ hl hε :=
  GluedAlong.inr _

theorem inl_def : inl hψ hl hε = GluedAlong.inl (gluingDiffeomorph hψ hl hε).symm := (rfl)

theorem inr_def : inr hψ hl hε = GluedAlong.inr (gluingDiffeomorph hψ hl hε).symm := (rfl)

theorem isOpenEmbedding_inl : IsOpenEmbedding (inl hψ hl hε) :=
  GluedAlong.isOpenEmbedding_inl _

theorem isOpenEmbedding_inr : IsOpenEmbedding (inr hψ hl hε) :=
  GluedAlong.isOpenEmbedding_inr _

theorem isLocalDiffeomorph_inl :
    IsLocalDiffeomorph 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ (inl hψ hl hε) :=
  GluedAlong.isLocalDiffeomorph_inl _

theorem isLocalDiffeomorph_inr :
    IsLocalDiffeomorph 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ (inr hψ hl hε) :=
  GluedAlong.isLocalDiffeomorph_inr _

theorem range_inl_union_range_inr : range (inl hψ hl hε) ∪ range (inr hψ hl hε) = univ :=
  GluedAlong.range_inl_union_range_inr _

/-- A point `p` of `openNbhd n ε ∖ Z` is glued to `ψ(F_l(π p))`. -/
@[simp]
theorem inl_gluingDiffeomorph (p : modelOverlap n ε) :
    inl hψ hl hε (gluingDiffeomorph hψ hl hε p) = inr hψ hl hε p := by
  have := GluedAlong.inl_symm_apply (gluingDiffeomorph hψ hl hε).symm p
  rwa [Diffeomorph.symm_symm] at this

/-- A point `x` of the outer piece and a point `y` of the model piece have the same image in the
blowup exactly when `y` is off the divisor and `x` is its image under the gluing map. -/
theorem inl_eq_inr_iff {x : outerPiece hψ} {y : modelPiece n ε} :
    inl hψ hl hε x = inr hψ hl hε y ↔
      ∃ h : y ∈ modelOverlap n ε, (gluingDiffeomorph hψ hl hε ⟨y, h⟩ : outerPiece hψ) = x := by
  refine ⟨fun h ↦ ?_, fun ⟨hy, hx⟩ ↦ hx ▸ inl_gluingDiffeomorph hψ hl hε ⟨y, hy⟩⟩
  obtain ⟨hx, hxy⟩ := (GluedAlong.inl_eq_inr_iff _).1 h
  refine ⟨hxy ▸ ((gluingDiffeomorph hψ hl hε).symm ⟨x, hx⟩).property, ?_⟩
  simp [← hxy]

end WeightBlowup

end SymplecticGeometry

end
