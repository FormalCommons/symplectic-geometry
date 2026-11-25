/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Euclidean.Inversion
public import SymplecticGeometry.Geometry.Manifold.Gluing.Pair
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
public import Mathlib.Analysis.Normed.Module.FiniteDimension

import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions

/-!
# The connected sum by annuli

The connected sum of McDuff–Salamon glues `M₁` and `M₂`, from each of which a small ball has been
removed, along an annulus of the model space `E`, by the map `ξ ↦ ε² Φ ξ / ‖ξ‖²` for a linear
isometry `Φ` of `E`. This map is `Φ` after the inversion `EuclideanGeometry.inversion 0 ε` in the
sphere of radius `ε` about the origin, which sends `‖ξ‖` to `ε² / ‖ξ‖`. So it preserves the open
annulus `ε² < ‖ξ‖ < 1`, whose middle sphere `‖ξ‖ = ε` the inversion fixes, and exchanges its two
ends. This file builds the map, on the model space alone, as a diffeomorphism of that annulus,
and then the connected sum itself.

For the connected sum, `ι₁ : E → M₁` and `ι₂ : E → M₂` are open embeddings that are `C^n` local
diffeomorphisms (on all of `E`, as for Tau Ceti's `TauCeti.ConnectedSum`; only the open unit ball
matters), and `M₁`, `M₂` are Hausdorff. The balls removed have radius `ε²`, the inner radius of
the annulus that the gluing map preserves. Each piece `M_i \ ι_i (closedBall 0 ε²)` is open,
since the image of a compact ball is closed, and contains the image under `ι_i` of the annulus,
along which it is glued. The connected sum is the library's `SymplecticGeometry.GluedAlong` of
the two pieces along `ι₂ ∘ Φ ∘ inversion 0 ε ∘ ι₁⁻¹`; it inherits from `GluedAlong` its atlas,
its structure of `C^n` manifold, and the inclusions `GluedAlong.inl`, `GluedAlong.inr` of the
pieces, which are open embeddings and `C^n` local diffeomorphisms whose ranges cover it.

## Main definitions and results

* `SymplecticGeometry.ConnectedSum.annulus E ε`: the open annulus `{ξ | ε² < ‖ξ‖ < 1}` of `E`,
  with `mem_annulus`.
* `SymplecticGeometry.ConnectedSum.inversion_mem_annulus_iff`: for `ε ≠ 0` the inversion
  `inversion 0 ε` maps the annulus onto itself; it is an involution (Mathlib's
  `EuclideanGeometry.inversion_inversion`) that exchanges the two ends of the annulus
  (`EuclideanGeometry.norm_inversion_zero_lt_iff` and
  `EuclideanGeometry.lt_norm_inversion_zero_iff` with `r = 1` and `r = ε²`).
  `SymplecticGeometry.ConnectedSum.map_mem_annulus_iff`: so does every linear isometry.
* `SymplecticGeometry.ConnectedSum.gluingPartialDiffeomorph Φ ε hε`: the map
  `ξ ↦ Φ (inversion 0 ε ξ)` as a `C^n` partial diffeomorphism of `E` with source and target the
  annulus, and inverse `η ↦ inversion 0 ε (Φ⁻¹ η)`, which is the same map for `Φ⁻¹`
  (`gluingPartialDiffeomorph_symm`).
* `SymplecticGeometry.ConnectedSum.gluingDiffeomorph Φ ε hε`: the diffeomorphism of the annulus
  that it gives, with `coe_gluingDiffeomorph_apply` and `coe_gluingDiffeomorph_symm_apply`; its
  inverse is the gluing diffeomorphism for `Φ⁻¹` (`gluingDiffeomorph_symm`).
* `SymplecticGeometry.ConnectedSum.piece ι ε hι`: the open set `M \ ι (closedBall 0 ε²)`, and
  `SymplecticGeometry.ConnectedSum.overlap`: the image of the annulus in it, as an open subset
  of the piece.
* `SymplecticGeometry.ConnectedSum.annulusDiffeomorph`: `ι` restricted to the annulus, as a
  diffeomorphism onto the overlap, from Mathlib's `IsLocalDiffeomorph.diffeomorphOfBijective`.
* `SymplecticGeometry.ConnectedSum.overlapDiffeomorph`: the gluing map between the overlaps of
  the two pieces, with `overlapDiffeomorph_annulusDiffeomorph`.
* `SymplecticGeometry.ConnectedSum.AnnulusSum`: the connected sum, and
  `SymplecticGeometry.ConnectedSum.AnnulusSum.inl_eq_inr_iff`: a point `x` of the first piece and
  a point `y` of the second are equal in it exactly when `x = ι₁ ξ` and
  `y = ι₂ (Φ (inversion 0 ε ξ))` for some `ξ` of the annulus.

The smoothness of the inversion away from its centre is Tau Ceti's
`EuclideanGeometry.contDiffAt_inversion`, and the diffeomorphism is Tau Ceti's
`PartialDiffeomorph.toDiffeomorphSourceTarget`. The inverse is identified by Tau Ceti's
`LinearIsometryEquiv.map_inversion_zero`: a linear isometry commutes with inversion about `0`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §7.1, Exercise 7.1.4.
-/

public section

noncomputable section

open TopologicalSpace EuclideanGeometry Topology
open scoped Manifold ContDiff

namespace SymplecticGeometry.ConnectedSum

variable (E : Type*) [NormedAddCommGroup E]

/-- The open annulus `{ξ | ε² < ‖ξ‖ < 1}` of `E`, along which the connected sum is glued. -/
def annulus (ε : ℝ) : Opens E :=
  ⟨{ξ | ε ^ 2 < ‖ξ‖ ∧ ‖ξ‖ < 1}, (isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)⟩

variable {E}

@[simp]
theorem mem_annulus {ε : ℝ} {ξ : E} : ξ ∈ annulus E ε ↔ ε ^ 2 < ‖ξ‖ ∧ ‖ξ‖ < 1 :=
  Iff.rfl

/-- The points of the annulus are nonzero. -/
theorem ne_zero_of_mem_annulus {ε : ℝ} {ξ : E} (hξ : ξ ∈ annulus E ε) : ξ ≠ 0 :=
  norm_pos_iff.1 ((sq_nonneg ε).trans_lt hξ.1)

/-- A linear isometry `Φ` of `E` maps the annulus onto itself. -/
theorem map_mem_annulus_iff [NormedSpace ℝ E] (Φ : E ≃ₗᵢ[ℝ] E) {ε : ℝ} {ξ : E} :
    Φ ξ ∈ annulus E ε ↔ ξ ∈ annulus E ε := by
  simp

variable [InnerProductSpace ℝ E]

/-- For `ε ≠ 0`, the inversion in the sphere of radius `ε` about the origin maps the annulus
`ε² < ‖ξ‖ < 1` onto itself. -/
theorem inversion_mem_annulus_iff {ε : ℝ} (hε : ε ≠ 0) {ξ : E} :
    inversion (0 : E) ε ξ ∈ annulus E ε ↔ ξ ∈ annulus E ε := by
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simp only [inversion_self]
  have hε₂ : 0 < ε ^ 2 := by positivity
  rw [mem_annulus, mem_annulus, lt_norm_inversion_zero_iff ε hε₂ hξ,
    norm_inversion_zero_lt_iff ε one_pos hξ, div_self hε₂.ne', div_one, and_comm]

/-- For `ε ≠ 0`, the map `ξ ↦ Φ (inversion 0 ε ξ)`, which is `ε² Φ ξ / ‖ξ‖²`, as a `C^n` partial
diffeomorphism of `E` whose source and target are the annulus `ε² < ‖ξ‖ < 1`. Its inverse is
`η ↦ inversion 0 ε (Φ⁻¹ η)`. -/
def gluingPartialDiffeomorph (Φ : E ≃ₗᵢ[ℝ] E) (ε : ℝ) (hε : ε ≠ 0) {n : ℕ∞ω} :
    PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E n where
  toFun ξ := Φ (inversion 0 ε ξ)
  invFun η := inversion 0 ε (Φ.symm η)
  source := annulus E ε
  target := annulus E ε
  map_source' _ hξ := (map_mem_annulus_iff Φ).2 ((inversion_mem_annulus_iff hε).2 hξ)
  map_target' _ hη := (inversion_mem_annulus_iff hε).2 ((map_mem_annulus_iff Φ.symm).2 hη)
  left_inv' ξ _ := by simp [inversion_inversion (0 : E) hε]
  right_inv' η _ := by simp [inversion_inversion (0 : E) hε]
  open_source := (annulus E ε).isOpen
  open_target := (annulus E ε).isOpen
  contMDiffOn_toFun := contMDiffOn_iff_contDiffOn.2 fun ξ hξ ↦
    (Φ.contDiff.contDiffAt.comp ξ
      (contDiffAt_inversion (ne_zero_of_mem_annulus hξ))).contDiffWithinAt
  contMDiffOn_invFun := contMDiffOn_iff_contDiffOn.2 fun η hη ↦
    ((contDiffAt_inversion (Φ.symm.map_ne_zero_iff.2 (ne_zero_of_mem_annulus hη))).comp η
      Φ.symm.contDiff.contDiffAt).contDiffWithinAt

variable (Φ : E ≃ₗᵢ[ℝ] E) (ε : ℝ) (hε : ε ≠ 0) {n : ℕ∞ω}

@[simp]
theorem gluingPartialDiffeomorph_apply (ξ : E) :
    gluingPartialDiffeomorph Φ ε hε (n := n) ξ = Φ (inversion 0 ε ξ) :=
  (rfl)

@[simp]
theorem gluingPartialDiffeomorph_symm_apply (η : E) :
    (gluingPartialDiffeomorph Φ ε hε (n := n)).toPartialEquiv.symm η = inversion 0 ε (Φ.symm η) :=
  (rfl)

@[simp]
theorem gluingPartialDiffeomorph_source :
    (gluingPartialDiffeomorph Φ ε hε (n := n)).source = annulus E ε :=
  (rfl)

@[simp]
theorem gluingPartialDiffeomorph_target :
    (gluingPartialDiffeomorph Φ ε hε (n := n)).target = annulus E ε :=
  (rfl)

/-- The inverse of the gluing map for `Φ` is the gluing map for `Φ⁻¹`. -/
@[simp]
theorem gluingPartialDiffeomorph_symm :
    (gluingPartialDiffeomorph Φ ε hε (n := n)).symm = gluingPartialDiffeomorph Φ.symm ε hε :=
  PartialDiffeomorph.ext (fun η ↦ by simp [LinearIsometryEquiv.map_inversion_zero])
    (fun ξ ↦ by simp [LinearIsometryEquiv.map_inversion_zero]) rfl

/-- For `ε ≠ 0`, the gluing map `ξ ↦ Φ (inversion 0 ε ξ)` of the connected sum, as a `C^n`
diffeomorphism of the annulus `ε² < ‖ξ‖ < 1` onto itself. -/
def gluingDiffeomorph : annulus E ε ≃ₘ^n⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ annulus E ε :=
  (gluingPartialDiffeomorph Φ ε hε).toDiffeomorphSourceTarget

@[simp]
theorem coe_gluingDiffeomorph_apply (ξ : annulus E ε) :
    (gluingDiffeomorph Φ ε hε (n := n) ξ : E) = Φ (inversion 0 ε ξ) :=
  (gluingPartialDiffeomorph Φ ε hε).toDiffeomorphSourceTarget_apply_coe ξ

theorem coe_gluingDiffeomorph_symm_apply (η : annulus E ε) :
    ((gluingDiffeomorph Φ ε hε (n := n)).symm η : E) = inversion 0 ε (Φ.symm η) :=
  (gluingPartialDiffeomorph Φ ε hε).toDiffeomorphSourceTarget_symm_apply_coe η

/-- The inverse of the gluing diffeomorphism for `Φ` is the gluing diffeomorphism for `Φ⁻¹`. -/
@[simp]
theorem gluingDiffeomorph_symm :
    (gluingDiffeomorph Φ ε hε (n := n)).symm = gluingDiffeomorph Φ.symm ε hε :=
  Diffeomorph.ext fun η ↦ Subtype.ext <| by
    simp [coe_gluingDiffeomorph_symm_apply, LinearIsometryEquiv.map_inversion_zero]

end SymplecticGeometry.ConnectedSum

/-! ### The connected sum glued from two pieces -/

namespace SymplecticGeometry.ConnectedSum

universe u

section Piece

variable {E : Type*} [NormedAddCommGroup E] [ProperSpace E] {M : Type*} [TopologicalSpace M]
  [T2Space M] (ι : E → M) (ε : ℝ)

/-- The piece `M \ ι (closedBall 0 ε²)` of the connected sum: the complement of the image of the
closed ball of radius `ε²` under a continuous map `ι`. It is open, as that image is compact and
`M` is Hausdorff. -/
def piece (hι : Continuous ι) : Opens M :=
  ⟨(ι '' Metric.closedBall 0 (ε ^ 2))ᶜ,
    ((isCompact_closedBall 0 _).image hι).isClosed.isOpen_compl⟩

variable {ι ε} {hι : Continuous ι}

@[simp]
theorem mem_piece_iff {x : M} : x ∈ piece ι ε hι ↔ x ∉ ι '' Metric.closedBall 0 (ε ^ 2) :=
  Iff.rfl

/-- For injective `ι`, the image of a point of the annulus lies in the piece. -/
theorem mem_piece_of_mem_annulus (hι' : Function.Injective ι) {ξ : E} (hξ : ξ ∈ annulus E ε) :
    ι ξ ∈ piece ι ε hι := by
  rintro ⟨η, hη, h⟩
  rw [hι' h, Metric.mem_closedBall, dist_zero_right] at hη
  exact hη.not_gt hξ.1

variable (ι ε hι) in
/-- The part of the piece `piece ι ε` along which it is glued: the image under the open map `ι`
of the annulus `ε² < ‖ξ‖ < 1`, as an open subset of the piece. -/
def overlap (hι' : IsOpenMap ι) : Opens (piece ι ε hι) :=
  ⟨Subtype.val ⁻¹' (ι '' annulus E ε),
    (hι' _ (annulus E ε).isOpen).preimage continuous_subtypeVal⟩

@[simp]
theorem mem_overlap_iff {hι' : IsOpenMap ι} {x : piece ι ε hι} :
    x ∈ overlap ι ε hι hι' ↔ (x : M) ∈ ι '' annulus E ε :=
  Iff.rfl

end Piece

section Diffeomorph

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {n : ℕ∞ω}

section One

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {ι : E → M}
  (hι : IsOpenEmbedding ι) (hdι : IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) n ι) (ε : ℝ)

/-- For an open embedding `ι` that is a `C^n` local diffeomorphism, `ι` restricted to the annulus
`ε² < ‖ξ‖ < 1`, as a `C^n` diffeomorphism onto the overlap `overlap ι ε`. -/
def annulusDiffeomorph :
    annulus E ε ≃ₘ^n⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ overlap ι ε hι.continuous hι.isOpenMap :=
  IsLocalDiffeomorph.diffeomorphOfBijective
    (f := fun ξ ↦ ⟨⟨ι ξ, mem_piece_of_mem_annulus hι.injective ξ.property⟩, ξ, ξ.property, rfl⟩)
    (TauCeti.isLocalDiffeomorph_subtypeVal_comp_iff.1 <|
      TauCeti.isLocalDiffeomorph_subtypeVal_comp_iff.1 <|
        fun ξ ↦ (TauCeti.isLocalDiffeomorph_subtype_val ξ).comp (hg := hdι ξ))
    ⟨fun _ _ h ↦ Subtype.ext <| hι.injective <| congrArg
        (fun x : overlap ι ε hι.continuous hι.isOpenMap ↦ ((x : piece ι ε hι.continuous) : M)) h,
      fun ⟨_, ξ, hξ, h⟩ ↦ ⟨⟨ξ, hξ⟩, Subtype.ext (Subtype.ext h)⟩⟩

variable {hι hdι ε}

@[simp]
theorem coe_annulusDiffeomorph_apply (ξ : annulus E ε) :
    ((annulusDiffeomorph hι hdι ε ξ : piece ι ε hι.continuous) : M) = ι ξ := by
  unfold annulusDiffeomorph
  exact congrArg (fun x : overlap ι ε hι.continuous hι.isOpenMap ↦
    ((x : piece ι ε hι.continuous) : M)) (congrFun (IsLocalDiffeomorph.coe_diffeomorphOfBijective
      _ _) ξ)

theorem apply_coe_annulusDiffeomorph_symm (x : overlap ι ε hι.continuous hι.isOpenMap) :
    ι ((annulusDiffeomorph hι hdι ε).symm x) = ((x : piece ι ε hι.continuous) : M) := by
  conv_rhs => rw [← (annulusDiffeomorph hι hdι ε).apply_symm_apply x]
  rw [coe_annulusDiffeomorph_apply]

end One

variable {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace E M₁] [T2Space M₁]
  [TopologicalSpace M₂] [ChartedSpace E M₂] [T2Space M₂] {ι₁ : E → M₁} {ι₂ : E → M₂}
  (hι₁ : IsOpenEmbedding ι₁) (hdι₁ : IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) n ι₁)
  (hι₂ : IsOpenEmbedding ι₂) (hdι₂ : IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) n ι₂)
  (Φ : E ≃ₗᵢ[ℝ] E) {ε : ℝ} (hε : ε ≠ 0)

/-- The gluing map of the connected sum, `ι₂ ∘ Φ ∘ inversion 0 ε ∘ ι₁⁻¹`, as a `C^n`
diffeomorphism from the overlap of the first piece onto that of the second. -/
def overlapDiffeomorph :
    overlap ι₁ ε hι₁.continuous hι₁.isOpenMap ≃ₘ^n⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯
      overlap ι₂ ε hι₂.continuous hι₂.isOpenMap :=
  (annulusDiffeomorph hι₁ hdι₁ ε).symm.trans
    ((gluingDiffeomorph Φ ε hε).trans (annulusDiffeomorph hι₂ hdι₂ ε))

@[simp]
theorem overlapDiffeomorph_annulusDiffeomorph (ξ : annulus E ε) :
    overlapDiffeomorph hι₁ hdι₁ hι₂ hdι₂ Φ hε (annulusDiffeomorph hι₁ hdι₁ ε ξ) =
      annulusDiffeomorph hι₂ hdι₂ ε (gluingDiffeomorph Φ ε hε (n := n) ξ) := by
  simp [overlapDiffeomorph]

/-- The connected sum of McDuff–Salamon (Exercise 7.1.4): the pieces `M₁ \ ι₁ (closedBall 0 ε²)`
and `M₂ \ ι₂ (closedBall 0 ε²)`, glued by identifying `ι₁ ξ` with `ι₂ (Φ (inversion 0 ε ξ))`,
that is `ι₂ (ε² Φ ξ / ‖ξ‖²)`, for `ξ` in the annulus `ε² < ‖ξ‖ < 1`. Here `ι₁` and `ι₂` are open
embeddings of `E` that are `C^n` local diffeomorphisms, `Φ` is a linear isometry and `ε ≠ 0`
(the book takes `0 < ε < 1`). It is `GluedAlong` of `overlapDiffeomorph`, from which it has its
atlas, its structure of `C^n` manifold, and the inclusions `GluedAlong.inl` and `GluedAlong.inr`
of the two pieces, open embeddings and `C^n` local diffeomorphisms whose ranges cover it. -/
abbrev AnnulusSum : Type u :=
  GluedAlong (overlapDiffeomorph hι₁ hdι₁ hι₂ hdι₂ Φ hε)

/-- A point `x` of the first piece and a point `y` of the second have the same image in the
connected sum exactly when `x = ι₁ ξ` and `y = ι₂ (Φ (inversion 0 ε ξ))` for some `ξ` with
`ε² < ‖ξ‖ < 1`. -/
theorem AnnulusSum.inl_eq_inr_iff {x : piece ι₁ ε hι₁.continuous}
    {y : piece ι₂ ε hι₂.continuous} :
    GluedAlong.inl (overlapDiffeomorph hι₁ hdι₁ hι₂ hdι₂ Φ hε) x =
        GluedAlong.inr (overlapDiffeomorph hι₁ hdι₁ hι₂ hdι₂ Φ hε) y ↔
      ∃ ξ : E, (ε ^ 2 < ‖ξ‖ ∧ ‖ξ‖ < 1) ∧ (x : M₁) = ι₁ ξ ∧
        (y : M₂) = ι₂ (Φ (inversion 0 ε ξ)) := by
  rw [GluedAlong.inl_eq_inr_iff]
  constructor
  · rintro ⟨hx, rfl⟩
    obtain ⟨ξ, hξ⟩ : ∃ ξ, annulusDiffeomorph hι₁ hdι₁ ε ξ = ⟨x, hx⟩ :=
      (annulusDiffeomorph hι₁ hdι₁ ε).surjective _
    refine ⟨ξ, ξ.property, ?_, ?_⟩
    · exact (congrArg (fun z : overlap ι₁ ε hι₁.continuous hι₁.isOpenMap ↦
        ((z : piece ι₁ ε hι₁.continuous) : M₁)) hξ).symm.trans (coe_annulusDiffeomorph_apply ξ)
    · rw [← hξ, overlapDiffeomorph_annulusDiffeomorph, coe_annulusDiffeomorph_apply,
        coe_gluingDiffeomorph_apply]
  · rintro ⟨ξ, hξ, hx, hy⟩
    have hx' : x ∈ overlap ι₁ ε hι₁.continuous hι₁.isOpenMap := ⟨ξ, hξ, hx.symm⟩
    have hξx : annulusDiffeomorph hι₁ hdι₁ ε ⟨ξ, hξ⟩ = ⟨x, hx'⟩ :=
      Subtype.ext <| Subtype.ext <| by rw [coe_annulusDiffeomorph_apply, hx]
    refine ⟨hx', Subtype.ext ?_⟩
    rw [← hξx, overlapDiffeomorph_annulusDiffeomorph, coe_annulusDiffeomorph_apply,
      coe_gluingDiffeomorph_apply, hy]

end Diffeomorph

end SymplecticGeometry.ConnectedSum

end
