/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Topology.Sets.Annulus
public import SymplecticGeometry.Geometry.Manifold.Gluing.Pair
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import TauCeti.Geometry.Manifold.ConnectedSum.Smooth
public import SymplecticGeometry.Geometry.Manifold.ConnectedSum.OrientationPreserving

import TauCeti.Geometry.Manifold.Diffeomorph.Basic
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
import SymplecticGeometry.Geometry.Euclidean.Inversion
public import TauCeti.Geometry.Manifold.Diffeomorph.NormedSpace
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Diffeomorph

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

For `ε ≠ 0` with `ε² < 1` and `M₁`, `M₂` manifolds, this connected sum is `C^n` diffeomorphic to
Tau Ceti's `TauCeti.ConnectedSum e₁ e₂` along the rescaled balls `e₁ v = ι₁ (ε • v)` and
`e₂ v = ι₂ (Φ (ε • v))`, so that later statements can be made about Tau Ceti's construction.
Tau Ceti removes only the centres and glues `e₁ v` to `e₂ (inversion 0 1 v)` for every `v ≠ 0`;
since `ε • inversion 0 1 v = inversion 0 ε (ε • v)`, this glues `ι₁ ξ` to
`ι₂ (Φ (inversion 0 ε ξ))` for every `ξ ≠ 0`, the gluing of the book extended to the whole
punctured ball. The diffeomorphism is the inclusion of each piece into the corresponding punctured
summand. It is injective since two points of the pieces that Tau Ceti glues lie over the annulus,
and surjective since a point `ι₁ ξ` with `0 < ‖ξ‖ ≤ ε²`, which the first piece lacks, is glued to
`ι₂ (Φ (inversion 0 ε ξ))`, of norm at least `1`, in the second piece, and symmetrically. So it
is a bijective local diffeomorphism, and Mathlib's `IsLocalDiffeomorph.diffeomorphOfBijective`
makes it a diffeomorphism, as Tau Ceti's `TauCeti.ConnectedSum.assocDiffeomorph` is built.

For oriented `M₁` and `M₂`, `0 < ε`, balls `ι₁`, `ι₂` that preserve orientation on the unit ball
from an orientation `oE` of `E`, and `Φ` of negative determinant, the rescaled ball
`v ↦ ι₁ (ε • v)` preserves and `v ↦ ι₂ (Φ (ε • v))` reverses orientation at every point, since
`E` is connected and a local diffeomorphism that preserves orientation at one point of a
connected set does so on all of it (Tau Ceti's `IsPreconnected.isOrientationPreservingAt_iff`).
So Tau Ceti's `TauCeti.ConnectedSum.orientation` orients the connected sum along them, and the
connected sum of the book is oriented by carrying it back along the diffeomorphism above, as
`TauCeti.OrientedConnectedSum.orientation` is carried from its connected sum. The inclusions of
the pieces then preserve orientation. Combined with
`TauCeti.OrientedConnectedSum.exists_diffeomorph_connectedSum_isOrientationPreservingAt`, this
shows that, for connected summands, the oriented connected sum of the book does not depend on
`ι₁`, `ι₂`, `Φ` and `ε` up to orientation-preserving diffeomorphism.

## Main definitions and results

The annulus is `SymplecticGeometry.annulus E (ε ^ 2) 1`, which every linear isometry maps onto
itself (`SymplecticGeometry.map_mem_annulus_iff`).

* `SymplecticGeometry.ConnectedSum.inversion_mem_annulus_iff`: for `ε ≠ 0` the inversion
  `inversion 0 ε` maps the annulus onto itself; it is an involution (Mathlib's
  `EuclideanGeometry.inversion_inversion`) that exchanges the two ends of the annulus
  (`EuclideanGeometry.norm_inversion_zero_lt_iff` and
  `EuclideanGeometry.lt_norm_inversion_zero_iff` with `r = 1` and `r = ε²`).
* `SymplecticGeometry.ConnectedSum.gluingPartialDiffeomorph Φ ε hε`: the map
  `ξ ↦ Φ (inversion 0 ε ξ)` as a `C^n` partial diffeomorphism of `E` with source and target the
  annulus, and inverse `η ↦ inversion 0 ε (Φ⁻¹ η)`, which is the same map for `Φ⁻¹`
  (`gluingPartialDiffeomorph_symm`).
* `SymplecticGeometry.ConnectedSum.gluingDiffeomorph Φ ε hε`: the diffeomorphism of the annulus
  that it gives, with `coe_gluingDiffeomorph_apply` and `coe_gluingDiffeomorph_symm_apply`; its
  inverse is the gluing diffeomorphism for `Φ⁻¹` (`gluingDiffeomorph_symm`), and `simp` cancels
  the two with `gluingDiffeomorph_symm_apply_apply`, `gluingDiffeomorph_apply_symm_apply`,
  `gluingDiffeomorph_self_trans_symm` and `gluingDiffeomorph_symm_trans_self`.
* `SymplecticGeometry.ConnectedSum.piece ι ε hι`: the open set `M \ ι (closedBall 0 ε²)`, and
  `SymplecticGeometry.ConnectedSum.overlap`: the image of the annulus in it, as an open subset
  of the piece.
* `SymplecticGeometry.ConnectedSum.annulusDiffeomorph`: `ι` restricted to the annulus, as a
  diffeomorphism onto the overlap, from Mathlib's `IsLocalDiffeomorph.diffeomorphOfBijective`.
* `SymplecticGeometry.ConnectedSum.overlapDiffeomorph`: the gluing map between the overlaps of
  the two pieces, with `overlapDiffeomorph_annulusDiffeomorph` and
  `coe_overlapDiffeomorph_apply`; its inverse is the gluing map for `Φ⁻¹`
  (`overlapDiffeomorph_symm`), and `simp` cancels the two with
  `overlapDiffeomorph_symm_apply_apply`, `overlapDiffeomorph_apply_symm_apply`,
  `overlapDiffeomorph_self_trans_symm` and `overlapDiffeomorph_symm_trans_self`.
* `SymplecticGeometry.ConnectedSum.AnnulusSum`: the connected sum, and
  `SymplecticGeometry.ConnectedSum.AnnulusSum.inl_eq_inr_iff`: a point `x` of the first piece and
  a point `y` of the second are equal in it exactly when `x = ι₁ ξ` and
  `y = ι₂ (Φ (inversion 0 ε ξ))` for some `ξ` of the annulus.
* `SymplecticGeometry.ConnectedSum.AnnulusSum.instT2Space`: the connected sum is Hausdorff, by
  `SymplecticGeometry.GluedAlong.t2Space_of_isClosed_graph`: the graph of the gluing map is
  closed, as the image of the compact closed annulus `ε² ≤ ‖ξ‖ ≤ 1` cut down to the two pieces.
* `SymplecticGeometry.ConnectedSum.rescale ι ε`: the ball `v ↦ ι (ε • v)`, an open embedding and
  a `C^n` local diffeomorphism with `ι` when `ε ≠ 0`, and
  `SymplecticGeometry.ConnectedSum.connectedSum_inl_eq_inr_iff`: the points that Tau Ceti's
  connected sum along `rescale ι₁ ε` and `rescale ι₂ ε` glues, from
  `EuclideanGeometry.inversion_mul_homothety`.
* `SymplecticGeometry.ConnectedSum.apply_inversion_mem_piece`: for `ε ≠ 0` and
  `0 < ‖ξ‖ < 1`, the point `ι (inversion 0 ε ξ)` lies in the piece; with `ε² < 1` this sends each
  removed point `ι ξ`, `0 < ‖ξ‖ ≤ ε²`, into the piece.
* `SymplecticGeometry.ConnectedSum.toConnectedSum`: the map from `AnnulusSum` to Tau Ceti's
  connected sum, with `toConnectedSum_inl` and `toConnectedSum_inr`; it is a local diffeomorphism
  (`isLocalDiffeomorph_toConnectedSum`), injective (`injective_toConnectedSum`) and, for
  `ε² < 1`, surjective (`surjective_toConnectedSum`), so bijective (`bijective_toConnectedSum`).
* `SymplecticGeometry.ConnectedSum.annulusSumDiffeomorph`: the diffeomorphism from `AnnulusSum`
  to Tau Ceti's connected sum, with `annulusSumDiffeomorph_inl` and `annulusSumDiffeomorph_inr`.
* `SymplecticGeometry.ConnectedSum.isOrientationPreservingAt_rescale_of_zero` and
  `SymplecticGeometry.ConnectedSum.isOrientationReversingAt_rescale_of_zero`: for `0 < ε`, the
  rescaled ball of a local diffeomorphism of `E` that preserves (reverses) orientation at `0`
  preserves (reverses) it everywhere.
* `SymplecticGeometry.ConnectedSum.AnnulusSum.orientation`: the orientation of `AnnulusSum`,
  for which `annulusSumDiffeomorph` preserves orientation
  (`isOrientationPreservingAt_annulusSumDiffeomorph`), and so do the inclusions of the pieces
  (`AnnulusSum.isOrientationPreservingAt_inl`, `AnnulusSum.isOrientationPreservingAt_inr`);
  it is the only orientation for which these inclusions preserve orientation
  (`AnnulusSum.eq_orientation_iff`).
* `SymplecticGeometry.ConnectedSum.AnnulusSum.exists_diffeomorph_isOrientationPreservingAt`:
  for connected summands, the oriented connected sums for two choices of `ι₁`, `ι₂`, `Φ`, `ε`
  are diffeomorphic by an orientation-preserving diffeomorphism; each is so diffeomorphic to
  `TauCeti.OrientedConnectedSum`
  (`AnnulusSum.exists_diffeomorph_orientedConnectedSum_isOrientationPreservingAt`).

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

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- For `ε ≠ 0`, the inversion in the sphere of radius `ε` about the origin maps the annulus
`ε² < ‖ξ‖ < 1` onto itself. -/
theorem inversion_mem_annulus_iff {ε : ℝ} (hε : ε ≠ 0) {ξ : E} :
    inversion (0 : E) ε ξ ∈ annulus E (ε ^ 2) 1 ↔ ξ ∈ annulus E (ε ^ 2) 1 := by
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
  source := annulus E (ε ^ 2) 1
  target := annulus E (ε ^ 2) 1
  map_source' _ hξ := (map_mem_annulus_iff Φ).2 ((inversion_mem_annulus_iff hε).2 hξ)
  map_target' _ hη := (inversion_mem_annulus_iff hε).2 ((map_mem_annulus_iff Φ.symm).2 hη)
  left_inv' ξ _ := by simp [inversion_inversion (0 : E) hε]
  right_inv' η _ := by simp [inversion_inversion (0 : E) hε]
  open_source := (annulus E (ε ^ 2) 1).isOpen
  open_target := (annulus E (ε ^ 2) 1).isOpen
  contMDiffOn_toFun := contMDiffOn_iff_contDiffOn.2 fun ξ hξ ↦
    (Φ.contDiff.contDiffAt.comp ξ
      (contDiffAt_inversion (ne_zero_of_mem_annulus (sq_nonneg ε) hξ))).contDiffWithinAt
  contMDiffOn_invFun := contMDiffOn_iff_contDiffOn.2 fun η hη ↦
    ((contDiffAt_inversion
      (Φ.symm.map_ne_zero_iff.2 (ne_zero_of_mem_annulus (sq_nonneg ε) hη))).comp η
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
    (gluingPartialDiffeomorph Φ ε hε (n := n)).source = annulus E (ε ^ 2) 1 :=
  (rfl)

@[simp]
theorem gluingPartialDiffeomorph_target :
    (gluingPartialDiffeomorph Φ ε hε (n := n)).target = annulus E (ε ^ 2) 1 :=
  (rfl)

/-- The inverse of the gluing map for `Φ` is the gluing map for `Φ⁻¹`. -/
@[simp]
theorem gluingPartialDiffeomorph_symm :
    (gluingPartialDiffeomorph Φ ε hε (n := n)).symm = gluingPartialDiffeomorph Φ.symm ε hε :=
  PartialDiffeomorph.ext (fun η ↦ by simp [LinearIsometryEquiv.map_inversion_zero])
    (fun ξ ↦ by simp [LinearIsometryEquiv.map_inversion_zero]) rfl

/-- For `ε ≠ 0`, the gluing map `ξ ↦ Φ (inversion 0 ε ξ)` of the connected sum, as a `C^n`
diffeomorphism of the annulus `ε² < ‖ξ‖ < 1` onto itself. -/
def gluingDiffeomorph : annulus E (ε ^ 2) 1 ≃ₘ^n⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ annulus E (ε ^ 2) 1 :=
  (gluingPartialDiffeomorph Φ ε hε).toDiffeomorphSourceTarget

@[simp]
theorem coe_gluingDiffeomorph_apply (ξ : annulus E (ε ^ 2) 1) :
    (gluingDiffeomorph Φ ε hε (n := n) ξ : E) = Φ (inversion 0 ε ξ) :=
  (gluingPartialDiffeomorph Φ ε hε).toDiffeomorphSourceTarget_apply_coe ξ

theorem coe_gluingDiffeomorph_symm_apply (η : annulus E (ε ^ 2) 1) :
    ((gluingDiffeomorph Φ ε hε (n := n)).symm η : E) = inversion 0 ε (Φ.symm η) :=
  (gluingPartialDiffeomorph Φ ε hε).toDiffeomorphSourceTarget_symm_apply_coe η

/-- The inverse of the gluing diffeomorphism for `Φ` is the gluing diffeomorphism for `Φ⁻¹`. -/
@[simp]
theorem gluingDiffeomorph_symm :
    (gluingDiffeomorph Φ ε hε (n := n)).symm = gluingDiffeomorph Φ.symm ε hε :=
  Diffeomorph.ext fun η ↦ Subtype.ext <| by
    simp [coe_gluingDiffeomorph_symm_apply, LinearIsometryEquiv.map_inversion_zero]

/-- The gluing diffeomorphism for `Φ⁻¹` undoes the one for `Φ`. Since `simp` rewrites the inverse
with `gluingDiffeomorph_symm`, this is the form in which it cancels the two maps. -/
@[simp]
theorem gluingDiffeomorph_symm_apply_apply (ξ : annulus E (ε ^ 2) 1) :
    gluingDiffeomorph Φ.symm ε hε (n := n) (gluingDiffeomorph Φ ε hε (n := n) ξ) = ξ := by
  simpa using (gluingDiffeomorph Φ ε hε (n := n)).symm_apply_apply ξ

/-- The gluing diffeomorphism for `Φ` undoes the one for `Φ⁻¹`. Since `simp` rewrites the inverse
with `gluingDiffeomorph_symm`, this is the form in which it cancels the two maps. -/
@[simp]
theorem gluingDiffeomorph_apply_symm_apply (η : annulus E (ε ^ 2) 1) :
    gluingDiffeomorph Φ ε hε (n := n) (gluingDiffeomorph Φ.symm ε hε (n := n) η) = η := by
  simpa using (gluingDiffeomorph Φ ε hε (n := n)).apply_symm_apply η

/-- Composing the gluing diffeomorphism for `Φ` with the one for `Φ⁻¹` gives the identity of the
annulus. Since `simp` rewrites the inverse with `gluingDiffeomorph_symm`, this is the form in which
it cancels the two maps. -/
@[simp]
theorem gluingDiffeomorph_self_trans_symm :
    (gluingDiffeomorph Φ ε hε (n := n)).trans (gluingDiffeomorph Φ.symm ε hε) =
      Diffeomorph.refl 𝓘(ℝ, E) (annulus E (ε ^ 2) 1) n := by
  simpa using (gluingDiffeomorph Φ ε hε (n := n)).self_trans_symm

/-- Composing the gluing diffeomorphism for `Φ⁻¹` with the one for `Φ` gives the identity of the
annulus. Since `simp` rewrites the inverse with `gluingDiffeomorph_symm`, this is the form in which
it cancels the two maps. -/
@[simp]
theorem gluingDiffeomorph_symm_trans_self :
    (gluingDiffeomorph Φ.symm ε hε (n := n)).trans (gluingDiffeomorph Φ ε hε) =
      Diffeomorph.refl 𝓘(ℝ, E) (annulus E (ε ^ 2) 1) n := by
  simpa using (gluingDiffeomorph Φ ε hε (n := n)).symm_trans_self

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

/-- For injective `ι`, the image `ι ξ` lies in the piece exactly when `ε² < ‖ξ‖`. -/
theorem apply_mem_piece_iff (hι' : Function.Injective ι) {ξ : E} :
    ι ξ ∈ piece ι ε hι ↔ ε ^ 2 < ‖ξ‖ := by
  rw [mem_piece_iff, hι'.mem_set_image, Metric.mem_closedBall, dist_zero_right, not_le]

variable [InnerProductSpace ℝ E] in
/-- For injective `ι` and `ε ≠ 0`, the inversion `inversion 0 ε` sends a point `ξ ≠ 0` inside the
open unit ball to a point whose image under `ι` lies in the piece: its norm `ε² / ‖ξ‖` exceeds
`ε²`. -/
theorem apply_inversion_mem_piece (hι' : Function.Injective ι) (hε : ε ≠ 0) {ξ : E}
    (hξ : ξ ≠ 0) (h : ‖ξ‖ < 1) : ι (inversion 0 ε ξ) ∈ piece ι ε hι := by
  rw [apply_mem_piece_iff hι', lt_norm_inversion_zero_iff ε (by positivity) hξ,
    div_self (by positivity)]
  exact h

/-- For injective `ι`, the image of a point of the annulus lies in the piece. -/
theorem mem_piece_of_mem_annulus (hι' : Function.Injective ι) {ξ : E}
    (hξ : ξ ∈ annulus E (ε ^ 2) 1) : ι ξ ∈ piece ι ε hι := by
  rintro ⟨η, hη, h⟩
  rw [hι' h, Metric.mem_closedBall, dist_zero_right] at hη
  exact hη.not_gt (mem_annulus.1 hξ).1

variable (ε) in
/-- The piece `M \ ι (closedBall 0 ε²)` lies in the complement of `e 0` for every map `e` with
`e 0 = ι 0`: in the summand of Tau Ceti's connected sum along such an `e`. -/
theorem piece_le_puncture {e : E → M} (he : e 0 = ι 0) :
    piece ι ε hι ≤ TauCeti.ConnectedSum.puncture e := by
  intro x hx
  rw [TauCeti.ConnectedSum.mem_puncture, he]
  rintro rfl
  exact hx ⟨0, by simp [sq_nonneg], rfl⟩

variable (ι ε hι) in
/-- The part of the piece `piece ι ε` along which it is glued: the image under the open map `ι`
of the annulus `ε² < ‖ξ‖ < 1`, as an open subset of the piece. -/
def overlap (hι' : IsOpenMap ι) : Opens (piece ι ε hι) :=
  ⟨Subtype.val ⁻¹' (ι '' annulus E (ε ^ 2) 1),
    (hι' _ (annulus E (ε ^ 2) 1).isOpen).preimage continuous_subtypeVal⟩

@[simp]
theorem mem_overlap_iff {hι' : IsOpenMap ι} {x : piece ι ε hι} :
    x ∈ overlap ι ε hι hι' ↔ (x : M) ∈ ι '' annulus E (ε ^ 2) 1 :=
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
    annulus E (ε ^ 2) 1 ≃ₘ^n⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ overlap ι ε hι.continuous hι.isOpenMap :=
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
theorem coe_annulusDiffeomorph_apply (ξ : annulus E (ε ^ 2) 1) :
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
theorem overlapDiffeomorph_annulusDiffeomorph (ξ : annulus E (ε ^ 2) 1) :
    overlapDiffeomorph hι₁ hdι₁ hι₂ hdι₂ Φ hε (annulusDiffeomorph hι₁ hdι₁ ε ξ) =
      annulusDiffeomorph hι₂ hdι₂ ε (gluingDiffeomorph Φ ε hε (n := n) ξ) := by
  simp [overlapDiffeomorph]

@[simp]
theorem coe_overlapDiffeomorph_apply (x : overlap ι₁ ε hι₁.continuous hι₁.isOpenMap) :
    ((overlapDiffeomorph hι₁ hdι₁ hι₂ hdι₂ Φ hε x : piece ι₂ ε hι₂.continuous) : M₂) =
      ι₂ (Φ (inversion 0 ε ((annulusDiffeomorph hι₁ hdι₁ ε).symm x))) := by
  simp [overlapDiffeomorph]

/-- The inverse of the gluing map for `Φ` is the gluing map for `Φ⁻¹`, from the overlap of the
second piece onto that of the first. -/
@[simp]
theorem overlapDiffeomorph_symm :
    (overlapDiffeomorph hι₁ hdι₁ hι₂ hdι₂ Φ hε).symm =
      overlapDiffeomorph hι₂ hdι₂ hι₁ hdι₁ Φ.symm hε :=
  Diffeomorph.ext fun _ ↦ by simp [overlapDiffeomorph]

/-- The gluing map for `Φ⁻¹` undoes the gluing map for `Φ`. Since `simp` rewrites the inverse
with `overlapDiffeomorph_symm`, this is the form in which it cancels the two maps. -/
@[simp]
theorem overlapDiffeomorph_symm_apply_apply (x : overlap ι₁ ε hι₁.continuous hι₁.isOpenMap) :
    overlapDiffeomorph hι₂ hdι₂ hι₁ hdι₁ Φ.symm hε (overlapDiffeomorph hι₁ hdι₁ hι₂ hdι₂ Φ hε x) =
      x := by
  simpa using (overlapDiffeomorph hι₁ hdι₁ hι₂ hdι₂ Φ hε).symm_apply_apply x

/-- The gluing map for `Φ` undoes the gluing map for `Φ⁻¹`. Since `simp` rewrites the inverse
with `overlapDiffeomorph_symm`, this is the form in which it cancels the two maps. -/
@[simp]
theorem overlapDiffeomorph_apply_symm_apply (y : overlap ι₂ ε hι₂.continuous hι₂.isOpenMap) :
    overlapDiffeomorph hι₁ hdι₁ hι₂ hdι₂ Φ hε (overlapDiffeomorph hι₂ hdι₂ hι₁ hdι₁ Φ.symm hε y) =
      y := by
  simpa using (overlapDiffeomorph hι₁ hdι₁ hι₂ hdι₂ Φ hε).apply_symm_apply y

/-- Composing the gluing map for `Φ` with the gluing map for `Φ⁻¹` gives the identity of the
overlap of the first piece. Since `simp` rewrites the inverse with `overlapDiffeomorph_symm`, this
is the form in which it cancels the two maps. -/
@[simp]
theorem overlapDiffeomorph_self_trans_symm :
    (overlapDiffeomorph hι₁ hdι₁ hι₂ hdι₂ Φ hε).trans
        (overlapDiffeomorph hι₂ hdι₂ hι₁ hdι₁ Φ.symm hε) =
      Diffeomorph.refl 𝓘(ℝ, E) (overlap ι₁ ε hι₁.continuous hι₁.isOpenMap) n := by
  simpa using (overlapDiffeomorph hι₁ hdι₁ hι₂ hdι₂ Φ hε).self_trans_symm

/-- Composing the gluing map for `Φ⁻¹` with the gluing map for `Φ` gives the identity of the
overlap of the second piece. Since `simp` rewrites the inverse with `overlapDiffeomorph_symm`,
this is the form in which it cancels the two maps. -/
@[simp]
theorem overlapDiffeomorph_symm_trans_self :
    (overlapDiffeomorph hι₂ hdι₂ hι₁ hdι₁ Φ.symm hε).trans
        (overlapDiffeomorph hι₁ hdι₁ hι₂ hdι₂ Φ hε) =
      Diffeomorph.refl 𝓘(ℝ, E) (overlap ι₂ ε hι₂.continuous hι₂.isOpenMap) n := by
  simpa using (overlapDiffeomorph hι₁ hdι₁ hι₂ hdι₂ Φ hε).symm_trans_self

/-- The connected sum of McDuff–Salamon (Exercise 7.1.4): the pieces `M₁ \ ι₁ (closedBall 0 ε²)`
and `M₂ \ ι₂ (closedBall 0 ε²)`, glued by identifying `ι₁ ξ` with `ι₂ (Φ (inversion 0 ε ξ))`,
that is `ι₂ (ε² Φ ξ / ‖ξ‖²)`, for `ξ` in the annulus `ε² < ‖ξ‖ < 1`. Here `ι₁` and `ι₂` are open
embeddings of `E` that are `C^n` local diffeomorphisms, `Φ` is a linear isometry and `ε ≠ 0`
(the book takes `0 < ε < 1`). It is `GluedAlong` of `overlapDiffeomorph`, from which it has its
atlas, its structure of `C^n` manifold, and the inclusions `GluedAlong.inl` and `GluedAlong.inr`
of the two pieces, open embeddings and `C^n` local diffeomorphisms whose ranges cover it. -/
abbrev AnnulusSum : Type u :=
  GluedAlong (overlapDiffeomorph hι₁ hdι₁ hι₂ hdι₂ Φ hε).toHomeomorph

/-- A point `x` of the first piece and a point `y` of the second have the same image in the
connected sum exactly when `x = ι₁ ξ` and `y = ι₂ (Φ (inversion 0 ε ξ))` for some `ξ` with
`ε² < ‖ξ‖ < 1`. -/
theorem AnnulusSum.inl_eq_inr_iff {x : piece ι₁ ε hι₁.continuous}
    {y : piece ι₂ ε hι₂.continuous} :
    GluedAlong.inl (overlapDiffeomorph hι₁ hdι₁ hι₂ hdι₂ Φ hε).toHomeomorph x =
        GluedAlong.inr (overlapDiffeomorph hι₁ hdι₁ hι₂ hdι₂ Φ hε).toHomeomorph y ↔
      ∃ ξ : E, ξ ∈ annulus E (ε ^ 2) 1 ∧ (x : M₁) = ι₁ ξ ∧
        (y : M₂) = ι₂ (Φ (inversion 0 ε ξ)) := by
  rw [GluedAlong.inl_eq_inr_iff, Diffeomorph.coe_toHomeomorph]
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

/-- The connected sum of the Hausdorff spaces `M₁` and `M₂` is Hausdorff. -/
instance AnnulusSum.instT2Space : T2Space (AnnulusSum hι₁ hdι₁ hι₂ hdι₂ Φ hε) := by
  -- The graph of the gluing map, in the product of the two pieces, is the preimage of the image
  -- of the compact closed annulus `ε² ≤ ‖ξ‖ ≤ 1` under `ξ ↦ (ι₁ ξ, ι₂ (Φ (inversion 0 ε ξ)))`,
  -- since the two ends of that annulus go into the removed balls. So it is closed.
  have hε₂ : 0 < ε ^ 2 := by positivity
  set K : Set E := Metric.closedBall 0 1 \ Metric.ball 0 (ε ^ 2)
  have hK0 : ∀ ξ ∈ K, ξ ≠ 0 := by
    rintro ξ ⟨-, hξ⟩ rfl
    exact hξ (Metric.mem_ball_self hε₂)
  have hg : ContinuousOn (fun ξ ↦ (ι₁ ξ, ι₂ (Φ (inversion 0 ε ξ)))) K :=
    (hι₁.continuous.continuousOn).prodMk fun ξ hξ ↦ (hι₂.continuous.continuousAt.comp
      (Φ.continuous.continuousAt.comp
        (contDiffAt_inversion (n := 0) (hK0 ξ hξ)).continuousAt)).continuousWithinAt
  have hC : IsClosed (Prod.map (Subtype.val : piece ι₁ ε hι₁.continuous → M₁)
      (Subtype.val : piece ι₂ ε hι₂.continuous → M₂) ⁻¹'
        ((fun ξ ↦ (ι₁ ξ, ι₂ (Φ (inversion 0 ε ξ)))) '' K)) :=
    (((isCompact_closedBall 0 1).diff Metric.isOpen_ball).image_of_continuousOn
      hg).isClosed.preimage (continuous_subtypeVal.prodMap continuous_subtypeVal)
  refine GluedAlong.t2Space_of_isClosed_graph _ ?_
  convert hC using 1
  -- The graph, which `AnnulusSum.inl_eq_inr_iff` describes, is that preimage.
  ext ⟨x, y⟩
  have hgraph := AnnulusSum.inl_eq_inr_iff hι₁ hdι₁ hι₂ hdι₂ Φ hε (x := x) (y := y)
  rw [GluedAlong.inl_eq_inr_iff] at hgraph
  simp only [Set.mem_preimage, Prod.map_apply, Set.mem_image, Prod.mk.injEq, Set.mem_ofPred_eq]
  refine ⟨fun ⟨u, hu, hφ⟩ ↦ ?_, fun ⟨ξ, hξ, hx, hy⟩ ↦ ?_⟩
  · subst hu
    obtain ⟨ξ, hξ, hx, hy⟩ := hgraph.1 ⟨u.property, hφ⟩
    refine ⟨ξ, ⟨?_, ?_⟩, hx.symm, hy.symm⟩
    · simpa using (mem_annulus.1 hξ).2.le
    · simpa using (mem_annulus.1 hξ).1.le
  · have h₁ : ε ^ 2 < ‖ξ‖ := by
      by_contra h
      exact x.property ⟨ξ, by simpa using h, hx⟩
    have h₂ : ε ^ 2 < ‖Φ (inversion 0 ε ξ)‖ := by
      by_contra h
      exact y.property ⟨_, by simpa using h, hy⟩
    rw [LinearIsometryEquiv.norm_map, lt_norm_inversion_zero_iff ε hε₂ (hK0 ξ hξ),
      div_self hε₂.ne'] at h₂
    obtain ⟨hx', hy'⟩ := hgraph.2 ⟨ξ, mem_annulus.2 ⟨h₁, h₂⟩, hx.symm, hy.symm⟩
    exact ⟨⟨x, hx'⟩, rfl, hy'⟩

end Diffeomorph

/-! ### The connected sum as Tau Ceti's connected sum -/

section TauCeti

section Rescale

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {M : Type*}

/-- The coordinate ball `ι : E → M` rescaled by `ε`: the map `v ↦ ι (ε • v)`. -/
def rescale (ι : E → M) (ε : ℝ) : E → M := fun v ↦ ι (ε • v)

@[simp]
theorem rescale_apply (ι : E → M) (ε : ℝ) (v : E) : rescale ι ε v = ι (ε • v) :=
  (rfl)

/-- For `ε ≠ 0`, the rescaled ball of an injective map is injective. -/
theorem rescale_injective {ι : E → M} (hι : Function.Injective ι) {ε : ℝ} (hε : ε ≠ 0) :
    Function.Injective (rescale ι ε) :=
  hι.comp (smul_right_injective E hε)

/-- For `ε ≠ 0`, the rescaled ball of an open embedding is an open embedding. -/
theorem isOpenEmbedding_rescale [TopologicalSpace M] {ι : E → M} (hι : IsOpenEmbedding ι) {ε : ℝ}
    (hε : ε ≠ 0) : IsOpenEmbedding (rescale ι ε) :=
  hι.comp (Homeomorph.smulOfNeZero ε hε).isOpenEmbedding

/-- For `ε ≠ 0`, the rescaled ball of a `C^n` local diffeomorphism is a `C^n` local
diffeomorphism. -/
theorem isLocalDiffeomorph_rescale {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω} {ι : E → M}
    (hdι : IsLocalDiffeomorph 𝓘(ℝ, E) I n ι) {ε : ℝ}
    (hε : ε ≠ 0) : IsLocalDiffeomorph 𝓘(ℝ, E) I n (rescale ι ε) := by
  have h : rescale ι ε = ι ∘ Diffeomorph.smulAdd n ε 0 hε := funext fun v ↦ by simp
  exact h ▸ ((Diffeomorph.smulAdd n ε 0 hε).isLocalDiffeomorph_comp_diffeomorph_iff le_rfl).2 hdι

end Rescale

section Gluing

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {M₁ M₂ : Type*}
  [TopologicalSpace M₁] [T1Space M₁] [TopologicalSpace M₂] [T1Space M₂] {ι₁ : E → M₁}
  {ι₂ : E → M₂} {ε : ℝ}

/-- In Tau Ceti's connected sum along the rescaled balls `v ↦ ι₁ (ε • v)` and `v ↦ ι₂ (ε • v)`,
a point `x` of the first summand and a point `y` of the second are glued exactly when
`x = ι₁ ξ` and `y = ι₂ (inversion 0 ε ξ)` for some `ξ ≠ 0`. -/
theorem connectedSum_inl_eq_inr_iff (hι₁ : Function.Injective ι₁) (hε : ε ≠ 0)
    {x : TauCeti.ConnectedSum.puncture (rescale ι₁ ε)}
    {y : TauCeti.ConnectedSum.puncture (rescale ι₂ ε)} :
    TauCeti.ConnectedSum.inl _ _ x = TauCeti.ConnectedSum.inr _ _ y ↔
      ∃ ξ ≠ 0, (x : M₁) = ι₁ ξ ∧ (y : M₂) = ι₂ (inversion 0 ε ξ) := by
  rw [TauCeti.ConnectedSum.inl_eq_inr_iff (rescale_injective hι₁ hε)]
  have key (v : E) : ε • inversion 0 1 v = inversion 0 ε (ε • v) := by
    simpa [AffineMap.homothety_apply] using (inversion_mul_homothety (0 : E) ε 1 v).symm
  constructor
  · rintro ⟨v, hv, hx, hy⟩
    refine ⟨ε • v, smul_ne_zero hε hv, hx.symm, ?_⟩
    rw [← hy, rescale_apply, key]
  · rintro ⟨ξ, hξ, hx, hy⟩
    refine ⟨ε⁻¹ • ξ, smul_ne_zero (inv_ne_zero hε) hξ, ?_, ?_⟩
    · rw [hx, rescale_apply, smul_inv_smul₀ hε]
    · rw [hy, rescale_apply, key, smul_inv_smul₀ hε]

end Gluing

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {n : ℕ∞} {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace E M₁] [T2Space M₁]
  [TopologicalSpace M₂] [ChartedSpace E M₂] [T2Space M₂] {ι₁ : E → M₁} {ι₂ : E → M₂}
  (hι₁ : IsOpenEmbedding ι₁) (hdι₁ : IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) n ι₁)
  (hι₂ : IsOpenEmbedding ι₂) (hdι₂ : IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) n ι₂)
  (Φ : E ≃ₗᵢ[ℝ] E) {ε : ℝ} (hε : ε ≠ 0)

/-- The map from `AnnulusSum` to Tau Ceti's connected sum along `v ↦ ι₁ (ε • v)` and
`v ↦ ι₂ (Φ (ε • v))` that is the inclusion of each piece into the corresponding punctured
summand. -/
def toConnectedSum :
    C(AnnulusSum hι₁ hdι₁ hι₂ hdι₂ Φ hε,
      TauCeti.ConnectedSum (rescale ι₁ ε) (rescale (ι₂ ∘ Φ) ε)) :=
  GluedAlong.desc _
    ⟨fun x ↦ TauCeti.ConnectedSum.inl _ _
      (Opens.inclusion (piece_le_puncture ε (by simp)) x),
      (TauCeti.ConnectedSum.continuous_inl _ _).comp (continuous_inclusion _)⟩
    ⟨fun y ↦ TauCeti.ConnectedSum.inr _ _
      (Opens.inclusion (piece_le_puncture ε (by simp)) y),
      (TauCeti.ConnectedSum.continuous_inr _ _).comp (continuous_inclusion _)⟩
    fun x ↦ by
      obtain ⟨ξ, hξ, hx, hy⟩ := (AnnulusSum.inl_eq_inr_iff hι₁ hdι₁ hι₂ hdι₂ Φ hε).1
        (GluedAlong.inr_apply _ x).symm
      exact ((connectedSum_inl_eq_inr_iff (ι₂ := ι₂ ∘ Φ) hι₁.injective hε).2
        ⟨ξ, ne_zero_of_mem_annulus (sq_nonneg ε) hξ, hx, hy⟩).symm

/-- The map `toConnectedSum` sends a point of the first piece to the same point of the first
punctured summand. -/
@[simp]
theorem toConnectedSum_inl (x : piece ι₁ ε hι₁.continuous) :
    toConnectedSum hι₁ hdι₁ hι₂ hdι₂ Φ hε (GluedAlong.inl _ x) =
      TauCeti.ConnectedSum.inl (rescale ι₁ ε) (rescale (ι₂ ∘ Φ) ε)
        ⟨x, piece_le_puncture ε (by simp) x.property⟩ := by
  simp [toConnectedSum]

/-- The map `toConnectedSum` sends a point of the second piece to the same point of the second
punctured summand. -/
@[simp]
theorem toConnectedSum_inr (y : piece ι₂ ε hι₂.continuous) :
    toConnectedSum hι₁ hdι₁ hι₂ hdι₂ Φ hε (GluedAlong.inr _ y) =
      TauCeti.ConnectedSum.inr (rescale ι₁ ε) (rescale (ι₂ ∘ Φ) ε)
        ⟨y, piece_le_puncture ε (by simp) y.property⟩ := by
  simp [toConnectedSum]

/-- Points of the two pieces that `toConnectedSum` sends to the same point of Tau Ceti's sum are
glued in `AnnulusSum`: Tau Ceti glues `ι₁ ξ` to `ι₂ (Φ (inversion 0 ε ξ))`, and both lie in the
pieces only for `ξ` in the annulus. -/
private theorem inl_eq_inr_of_toConnectedSum_eq {x : piece ι₁ ε hι₁.continuous}
    {y : piece ι₂ ε hι₂.continuous}
    (h : toConnectedSum hι₁ hdι₁ hι₂ hdι₂ Φ hε (GluedAlong.inl _ x) =
      toConnectedSum hι₁ hdι₁ hι₂ hdι₂ Φ hε (GluedAlong.inr _ y)) :
    GluedAlong.inl (overlapDiffeomorph hι₁ hdι₁ hι₂ hdι₂ Φ hε).toHomeomorph x =
      GluedAlong.inr (overlapDiffeomorph hι₁ hdι₁ hι₂ hdι₂ Φ hε).toHomeomorph y := by
  have hε₂ : 0 < ε ^ 2 := by positivity
  rw [toConnectedSum_inl, toConnectedSum_inr,
    connectedSum_inl_eq_inr_iff hι₁.injective hε] at h
  obtain ⟨ξ, hξ, hx, hy⟩ := h
  have h₁ := x.property
  have h₂ := y.property
  rw [hx, apply_mem_piece_iff hι₁.injective] at h₁
  rw [hy, Function.comp_apply, apply_mem_piece_iff hι₂.injective, LinearIsometryEquiv.norm_map,
    lt_norm_inversion_zero_iff ε hε₂ hξ, div_self hε₂.ne'] at h₂
  exact (AnnulusSum.inl_eq_inr_iff hι₁ hdι₁ hι₂ hdι₂ Φ hε).2 ⟨ξ, mem_annulus.2 ⟨h₁, h₂⟩, hx, hy⟩

/-- The map from `AnnulusSum` to Tau Ceti's connected sum is injective. -/
theorem injective_toConnectedSum : Function.Injective (toConnectedSum hι₁ hdι₁ hι₂ hdι₂ Φ hε) := by
  intro z z' h
  rcases GluedAlong.exists_inl_or_exists_inr _ z with ⟨x, rfl⟩ | ⟨y, rfl⟩ <;>
    rcases GluedAlong.exists_inl_or_exists_inr _ z' with ⟨x', rfl⟩ | ⟨y', rfl⟩
  · rw [toConnectedSum_inl, toConnectedSum_inl] at h
    have := TauCeti.ConnectedSum.inl_injective
      (rescale_injective (hι₂.injective.comp Φ.injective) hε) h
    exact congrArg (GluedAlong.inl _) (Subtype.ext (Subtype.mk.inj this))
  · exact inl_eq_inr_of_toConnectedSum_eq hι₁ hdι₁ hι₂ hdι₂ Φ hε h
  · exact (inl_eq_inr_of_toConnectedSum_eq hι₁ hdι₁ hι₂ hdι₂ Φ hε h.symm).symm
  · rw [toConnectedSum_inr, toConnectedSum_inr] at h
    have := TauCeti.ConnectedSum.inr_injective (rescale_injective hι₁.injective hε) h
    exact congrArg (GluedAlong.inr _) (Subtype.ext (Subtype.mk.inj this))

/-- For `ε² < 1`, the map from `AnnulusSum` to Tau Ceti's connected sum is surjective: a point
`ι₁ ξ` with `0 < ‖ξ‖ ≤ ε²`, which Tau Ceti's sum keeps but the first piece removes, is glued to
the point `ι₂ (Φ (inversion 0 ε ξ))` of the second piece, and symmetrically. -/
theorem surjective_toConnectedSum (hε₁ : ε ^ 2 < 1) :
    Function.Surjective (toConnectedSum hι₁ hdι₁ hι₂ hdι₂ Φ hε) := by
  intro p
  obtain ⟨⟨x, hx⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩ :=
    (TauCeti.ConnectedSum.range_inl_union_range_inr (rescale ι₁ ε) (rescale (ι₂ ∘ Φ) ε)).symm ▸
      Set.mem_univ p
  · by_cases hp : x ∈ piece ι₁ ε hι₁.continuous
    · exact ⟨GluedAlong.inl _ ⟨x, hp⟩, toConnectedSum_inl hι₁ hdι₁ hι₂ hdι₂ Φ hε _⟩
    obtain ⟨ξ, hξε, rfl⟩ := not_not.1 hp
    have hξ : ξ ≠ 0 := by
      rintro rfl
      exact (TauCeti.ConnectedSum.mem_puncture.1 hx) (by simp)
    have hy : ι₂ (Φ (inversion 0 ε ξ)) ∈ piece ι₂ ε hι₂.continuous := by
      rw [Φ.map_inversion_zero]
      exact apply_inversion_mem_piece hι₂.injective hε (Φ.map_ne_zero_iff.2 hξ)
        (by simpa using hξε.trans_lt hε₁)
    refine ⟨GluedAlong.inr _ ⟨_, hy⟩, ?_⟩
    rw [toConnectedSum_inr]
    exact ((connectedSum_inl_eq_inr_iff hι₁.injective hε).2 ⟨ξ, hξ, rfl, rfl⟩).symm
  · by_cases hp : y ∈ piece ι₂ ε hι₂.continuous
    · exact ⟨GluedAlong.inr _ ⟨y, hp⟩, toConnectedSum_inr hι₁ hdι₁ hι₂ hdι₂ Φ hε _⟩
    obtain ⟨η, hηε, rfl⟩ := not_not.1 hp
    have hη : η ≠ 0 := by
      rintro rfl
      exact (TauCeti.ConnectedSum.mem_puncture.1 hy) (by simp)
    have hx := apply_inversion_mem_piece (hι := hι₁.continuous) hι₁.injective hε
      (Φ.symm.map_ne_zero_iff.2 hη) (by simpa using hηε.trans_lt hε₁)
    refine ⟨GluedAlong.inl _ ⟨_, hx⟩, ?_⟩
    rw [toConnectedSum_inl]
    exact (connectedSum_inl_eq_inr_iff hι₁.injective hε).2
      ⟨_, by simpa [inversion_eq_center hε] using hη, rfl,
        by simp [inversion_inversion (0 : E) hε]⟩

/-- For `ε ≠ 0` and `ε² < 1`, the map from `AnnulusSum` to Tau Ceti's connected sum is
bijective. -/
theorem bijective_toConnectedSum (hε₁ : ε ^ 2 < 1) :
    Function.Bijective (toConnectedSum hι₁ hdι₁ hι₂ hdι₂ Φ hε) :=
  ⟨injective_toConnectedSum hι₁ hdι₁ hι₂ hdι₂ Φ hε,
    surjective_toConnectedSum hι₁ hdι₁ hι₂ hdι₂ Φ hε hε₁⟩

variable [IsManifold 𝓘(ℝ, E) n M₁] [IsManifold 𝓘(ℝ, E) n M₂]

/-- The map from `AnnulusSum` to Tau Ceti's connected sum is a `C^n` local diffeomorphism: on
each piece it is the inclusion of an open subset followed by the inclusion of a punctured
summand. -/
theorem isLocalDiffeomorph_toConnectedSum :
    letI := TauCeti.ConnectedSum.chartedSpace (H := E) (isOpenEmbedding_rescale hι₁ hε)
      (isOpenEmbedding_rescale (hι₂.comp_linearIsometryEquiv Φ) hε)
    IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) n (toConnectedSum hι₁ hdι₁ hι₂ hdι₂ Φ hε) := by
  let := TauCeti.ConnectedSum.chartedSpace (H := E) (isOpenEmbedding_rescale hι₁ hε)
    (isOpenEmbedding_rescale (hι₂.comp_linearIsometryEquiv Φ) hε)
  have d₁ := TauCeti.ConnectedSum.isLocalDiffeomorph_inl (isOpenEmbedding_rescale hι₁ hε)
    (isOpenEmbedding_rescale (hι₂.comp_linearIsometryEquiv Φ) hε)
    (isLocalDiffeomorph_rescale hdι₁ hε)
    (isLocalDiffeomorph_rescale (hdι₂.comp_linearIsometryEquiv Φ) hε)
  have d₂ := TauCeti.ConnectedSum.isLocalDiffeomorph_inr (isOpenEmbedding_rescale hι₁ hε)
    (isOpenEmbedding_rescale (hι₂.comp_linearIsometryEquiv Φ) hε)
    (isLocalDiffeomorph_rescale hdι₁ hε)
    (isLocalDiffeomorph_rescale (hdι₂.comp_linearIsometryEquiv Φ) hε)
  intro z
  rcases GluedAlong.exists_inl_or_exists_inr _ z with ⟨x, rfl⟩ | ⟨y, rfl⟩
  · refine IsLocalDiffeomorphAt.of_comp_right ?_ (GluedAlong.isLocalDiffeomorph_inl _ x)
    have h : toConnectedSum hι₁ hdι₁ hι₂ hdι₂ Φ hε ∘ GluedAlong.inl _ =
        TauCeti.ConnectedSum.inl _ _ ∘ Opens.inclusion (piece_le_puncture ε (by simp)) :=
      funext fun x ↦ toConnectedSum_inl hι₁ hdι₁ hι₂ hdι₂ Φ hε x
    rw [h]
    exact (TauCeti.isLocalDiffeomorph_inclusion _ x).comp (hg := d₁ _)
  · refine IsLocalDiffeomorphAt.of_comp_right ?_ (GluedAlong.isLocalDiffeomorph_inr _ y)
    have h : toConnectedSum hι₁ hdι₁ hι₂ hdι₂ Φ hε ∘ GluedAlong.inr _ =
        TauCeti.ConnectedSum.inr _ _ ∘ Opens.inclusion (piece_le_puncture ε (by simp)) :=
      funext fun y ↦ toConnectedSum_inr hι₁ hdι₁ hι₂ hdι₂ Φ hε y
    rw [h]
    exact (TauCeti.isLocalDiffeomorph_inclusion _ y).comp (hg := d₂ _)

/-- For `ε ≠ 0` and `ε² < 1`, the connected sum `AnnulusSum` of McDuff–Salamon is `C^n`
diffeomorphic to Tau Ceti's connected sum `TauCeti.ConnectedSum` along the rescaled balls
`v ↦ ι₁ (ε • v)` and `v ↦ ι₂ (Φ (ε • v))`, with Tau Ceti's charts
`TauCeti.ConnectedSum.chartedSpace`. The diffeomorphism is the identity of `M₁` on the first piece
and of `M₂` on the second (`annulusSumDiffeomorph_inl`, `annulusSumDiffeomorph_inr`). -/
def annulusSumDiffeomorph (hε₁ : ε ^ 2 < 1) :
    letI := TauCeti.ConnectedSum.chartedSpace (H := E) (isOpenEmbedding_rescale hι₁ hε)
      (isOpenEmbedding_rescale (hι₂.comp_linearIsometryEquiv Φ) hε)
    AnnulusSum hι₁ hdι₁ hι₂ hdι₂ Φ hε ≃ₘ^n⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯
      TauCeti.ConnectedSum (rescale ι₁ ε) (rescale (ι₂ ∘ Φ) ε) :=
  letI := TauCeti.ConnectedSum.chartedSpace (H := E) (isOpenEmbedding_rescale hι₁ hε)
    (isOpenEmbedding_rescale (hι₂.comp_linearIsometryEquiv Φ) hε)
  (isLocalDiffeomorph_toConnectedSum hι₁ hdι₁ hι₂ hdι₂ Φ hε).diffeomorphOfBijective
    (bijective_toConnectedSum hι₁ hdι₁ hι₂ hdι₂ Φ hε hε₁)

/-- The diffeomorphism `annulusSumDiffeomorph` sends a point `x` of the first piece to the same
point of the first punctured summand of Tau Ceti's connected sum. -/
@[simp]
theorem annulusSumDiffeomorph_inl (hε₁ : ε ^ 2 < 1) (x : piece ι₁ ε hι₁.continuous) :
    letI := TauCeti.ConnectedSum.chartedSpace (H := E) (isOpenEmbedding_rescale hι₁ hε)
      (isOpenEmbedding_rescale (hι₂.comp_linearIsometryEquiv Φ) hε)
    annulusSumDiffeomorph hι₁ hdι₁ hι₂ hdι₂ Φ hε hε₁ (GluedAlong.inl _ x) =
      TauCeti.ConnectedSum.inl (rescale ι₁ ε) (rescale (ι₂ ∘ Φ) ε)
        ⟨x, piece_le_puncture ε (by simp) x.property⟩ := by
  let := TauCeti.ConnectedSum.chartedSpace (H := E) (isOpenEmbedding_rescale hι₁ hε)
    (isOpenEmbedding_rescale (hι₂.comp_linearIsometryEquiv Φ) hε)
  rw [annulusSumDiffeomorph, IsLocalDiffeomorph.coe_diffeomorphOfBijective, toConnectedSum_inl]

/-- The diffeomorphism `annulusSumDiffeomorph` sends a point `y` of the second piece to the same
point of the second punctured summand of Tau Ceti's connected sum. -/
@[simp]
theorem annulusSumDiffeomorph_inr (hε₁ : ε ^ 2 < 1) (y : piece ι₂ ε hι₂.continuous) :
    letI := TauCeti.ConnectedSum.chartedSpace (H := E) (isOpenEmbedding_rescale hι₁ hε)
      (isOpenEmbedding_rescale (hι₂.comp_linearIsometryEquiv Φ) hε)
    annulusSumDiffeomorph hι₁ hdι₁ hι₂ hdι₂ Φ hε hε₁ (GluedAlong.inr _ y) =
      TauCeti.ConnectedSum.inr (rescale ι₁ ε) (rescale (ι₂ ∘ Φ) ε)
        ⟨y, piece_le_puncture ε (by simp) y.property⟩ := by
  let := TauCeti.ConnectedSum.chartedSpace (H := E) (isOpenEmbedding_rescale hι₁ hε)
    (isOpenEmbedding_rescale (hι₂.comp_linearIsometryEquiv Φ) hε)
  rw [annulusSumDiffeomorph, IsLocalDiffeomorph.coe_diffeomorphOfBijective, toConnectedSum_inr]

end TauCeti

/-! ### Orientations -/

section Orientation

open Metric TauCeti.Manifold.Orientation

section Rescale

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι]

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {oE : TauCeti.Manifold.Orientation 𝓘(ℝ, E) E ι}
  {o : TauCeti.Manifold.Orientation I M ι} {f : E → M} {ε : ℝ}

/-- For `0 < ε`, the rescaled ball `v ↦ f (ε • v)` preserves orientation at `v` when `f` does so
at `ε • v`. -/
theorem isOrientationPreservingAt_rescale (hε : 0 < ε) {v : E}
    (hf : IsOrientationPreservingAt oE o f (ε • v)) :
    IsOrientationPreservingAt oE o (rescale f ε) v := by
  let L := (LinearEquiv.smulOfNeZero ℝ E ε hε.ne').toContinuousLinearEquiv
  have hL : 0 < LinearMap.det (L : E →ₗ[ℝ] E) := by
    have : (L : E →ₗ[ℝ] E) = ε • LinearMap.id := by
      ext
      simp [L]
    rw [this, LinearMap.det_smul, LinearMap.det_id, mul_one]
    positivity
  exact hf.comp (isOrientationPreservingAt_of_det_pos oE L hL v)

/-- For `0 < ε`, the rescaled ball `v ↦ f (ε • v)` reverses orientation at `v` when `f` does so
at `ε • v`. -/
theorem isOrientationReversingAt_rescale (hε : 0 < ε) {v : E}
    (hf : IsOrientationReversingAt oE o f (ε • v)) :
    IsOrientationReversingAt oE o (rescale f ε) v := by
  rw [← isOrientationPreservingAt_neg_right] at hf ⊢
  exact isOrientationPreservingAt_rescale hε hf

/-- For `0 < ε`, the rescaled ball `v ↦ f (ε • v)` of a `C¹` local diffeomorphism `f` that
preserves orientation at `0` preserves orientation everywhere, since `E` is connected. -/
theorem isOrientationPreservingAt_rescale_of_zero (hf : IsLocalDiffeomorph 𝓘(ℝ, E) I 1 f)
    (hε : 0 < ε) (h0 : IsOrientationPreservingAt oE o f 0) (v : E) :
    IsOrientationPreservingAt oE o (rescale f ε) v := by
  have hd := isLocalDiffeomorph_rescale hf hε.ne'
  refine (isPreconnected_univ.isOrientationPreservingAt_iff (fun x _ ↦ hd.contMDiff x)
    (fun x _ ↦ (hd x).isInvertible_mfderiv one_ne_zero) oE o (Set.mem_univ 0)
    (Set.mem_univ v)).1 ?_
  exact isOrientationPreservingAt_rescale hε (by simpa using h0)

/-- For `0 < ε`, the rescaled ball `v ↦ f (ε • v)` of a `C¹` local diffeomorphism `f` that
reverses orientation at `0` reverses orientation everywhere, since `E` is connected. -/
theorem isOrientationReversingAt_rescale_of_zero (hf : IsLocalDiffeomorph 𝓘(ℝ, E) I 1 f)
    (hε : 0 < ε) (h0 : IsOrientationReversingAt oE o f 0) (v : E) :
    IsOrientationReversingAt oE o (rescale f ε) v := by
  rw [← isOrientationPreservingAt_neg_right] at h0 ⊢
  exact isOrientationPreservingAt_rescale_of_zero hf hε h0 v

variable {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace E M₁] [IsManifold 𝓘(ℝ, E) ∞ M₁]
  [TopologicalSpace M₂] [ChartedSpace E M₂] [IsManifold 𝓘(ℝ, E) ∞ M₂] {ι₁ : E → M₁} {ι₂ : E → M₂}
  {o₁ : TauCeti.Manifold.Orientation 𝓘(ℝ, E) M₁ ι}
  {o₂ : TauCeti.Manifold.Orientation 𝓘(ℝ, E) M₂ ι}

/-- For `0 < ε`, if the local diffeomorphism `ι₁` preserves orientation on the unit ball, then
the rescaled ball `v ↦ ι₁ (ε • v)` preserves orientation everywhere. -/
theorem isOrientationPreservingAt_rescale_of_mem_ball
    (hdι₁ : IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ ι₁) (hε : 0 < ε)
    (ho₁ : ∀ ξ ∈ ball (0 : E) 1, IsOrientationPreservingAt oE o₁ ι₁ ξ) (v : E) :
    IsOrientationPreservingAt oE o₁ (rescale ι₁ ε) v :=
  isOrientationPreservingAt_rescale_of_zero (hdι₁.of_le (by simp)) hε (ho₁ 0 (by simp)) v

/-- For `0 < ε`, if the local diffeomorphism `ι₂` preserves orientation on the unit ball and the
linear isometry `Φ` has negative determinant, then the rescaled ball `v ↦ ι₂ (Φ (ε • v))`
reverses orientation everywhere. -/
theorem isOrientationReversingAt_rescale_comp_of_mem_ball
    (hdι₂ : IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ ι₂) (Φ : E ≃ₗᵢ[ℝ] E)
    (hΦ : LinearMap.det (Φ.toLinearEquiv : E →ₗ[ℝ] E) < 0) (hε : 0 < ε)
    (ho₂ : ∀ ξ ∈ ball (0 : E) 1, IsOrientationPreservingAt oE o₂ ι₂ ξ) (v : E) :
    IsOrientationReversingAt oE o₂ (rescale (ι₂ ∘ Φ) ε) v :=
  isOrientationReversingAt_rescale_of_zero
    ((hdι₂.comp_linearIsometryEquiv Φ).of_le (by simp)) hε
    (isOrientationReversingAt_comp_of_det_neg (L := Φ.toContinuousLinearEquiv)
      (ho₂ _ (by simp)) hΦ) v

end Rescale

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace E M₁] [IsManifold 𝓘(ℝ, E) ∞ M₁]
  [TopologicalSpace M₂] [ChartedSpace E M₂] [IsManifold 𝓘(ℝ, E) ∞ M₂] {ι₁ : E → M₁} {ι₂ : E → M₂}
  {o₁ : TauCeti.Manifold.Orientation 𝓘(ℝ, E) M₁ ι}
  {o₂ : TauCeti.Manifold.Orientation 𝓘(ℝ, E) M₂ ι}
  {oE : TauCeti.Manifold.Orientation 𝓘(ℝ, E) E ι} {ε : ℝ}

variable [T2Space M₁] [T2Space M₂]
  (hι₁ : IsOpenEmbedding ι₁) (hdι₁ : IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ ι₁)
  (hι₂ : IsOpenEmbedding ι₂) (hdι₂ : IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ ι₂)
  (Φ : E ≃ₗᵢ[ℝ] E) (hΦ : LinearMap.det (Φ.toLinearEquiv : E →ₗ[ℝ] E) < 0) (hε : 0 < ε)
  (hε₁ : ε ^ 2 < 1) (o₁ o₂ oE)
  (ho₁ : ∀ ξ ∈ ball (0 : E) 1, IsOrientationPreservingAt oE o₁ ι₁ ξ)
  (ho₂ : ∀ ξ ∈ ball (0 : E) 1, IsOrientationPreservingAt oE o₂ ι₂ ξ)

/-- The orientation of the connected sum `AnnulusSum` of oriented manifolds, for `0 < ε`,
`ε² < 1`, balls `ι₁` and `ι₂` that preserve orientation on the unit ball from an orientation `oE`
of `E`, and a linear isometry `Φ` of negative determinant: Tau Ceti's
`TauCeti.ConnectedSum.orientation` of the connected sum along `v ↦ ι₁ (ε • v)` and
`v ↦ ι₂ (Φ (ε • v))`, carried back along `annulusSumDiffeomorph`. It agrees with `o₁` on the
first piece (`AnnulusSum.isOrientationPreservingAt_inl`) and with `o₂` on the second
(`AnnulusSum.isOrientationPreservingAt_inr`), and it is the only orientation that does so
(`AnnulusSum.eq_orientation_iff`). -/
def AnnulusSum.orientation :
    TauCeti.Manifold.Orientation 𝓘(ℝ, E) (AnnulusSum hι₁ hdι₁ hι₂ hdι₂ Φ hε.ne') ι :=
  letI := TauCeti.ConnectedSum.chartedSpace (H := E) (isOpenEmbedding_rescale hι₁ hε.ne')
    (isOpenEmbedding_rescale (hι₂.comp_linearIsometryEquiv Φ) hε.ne')
  haveI := TauCeti.ConnectedSum.isManifold (isOpenEmbedding_rescale hι₁ hε.ne')
    (isOpenEmbedding_rescale (hι₂.comp_linearIsometryEquiv Φ) hε.ne')
    (isLocalDiffeomorph_rescale hdι₁ hε.ne')
    (isLocalDiffeomorph_rescale (hdι₂.comp_linearIsometryEquiv Φ) hε.ne')
  (TauCeti.ConnectedSum.orientation (isOpenEmbedding_rescale hι₁ hε.ne')
    (isOpenEmbedding_rescale (hι₂.comp_linearIsometryEquiv Φ) hε.ne')
    (IsLocalDiffeomorph.of_le (isLocalDiffeomorph_rescale hdι₁ hε.ne') ENat.LEInfty.out)
    (IsLocalDiffeomorph.of_le (isLocalDiffeomorph_rescale (hdι₂.comp_linearIsometryEquiv Φ)
      hε.ne') ENat.LEInfty.out) o₁ o₂ oE
    (fun v _ ↦ isOrientationPreservingAt_rescale_of_mem_ball hdι₁ hε ho₁ v)
    (fun v _ ↦ isOrientationReversingAt_rescale_comp_of_mem_ball hdι₂ Φ hΦ hε ho₂ v)).map
    (annulusSumDiffeomorph hι₁ hdι₁ hι₂ hdι₂ Φ hε.ne' hε₁).symm (by simp) o₁.card_eq

theorem AnnulusSum.orientation_def :
    letI := TauCeti.ConnectedSum.chartedSpace (H := E) (isOpenEmbedding_rescale hι₁ hε.ne')
      (isOpenEmbedding_rescale (hι₂.comp_linearIsometryEquiv Φ) hε.ne')
    haveI := TauCeti.ConnectedSum.isManifold (isOpenEmbedding_rescale hι₁ hε.ne')
      (isOpenEmbedding_rescale (hι₂.comp_linearIsometryEquiv Φ) hε.ne')
      (isLocalDiffeomorph_rescale hdι₁ hε.ne')
      (isLocalDiffeomorph_rescale (hdι₂.comp_linearIsometryEquiv Φ) hε.ne')
    AnnulusSum.orientation o₁ o₂ oE hι₁ hdι₁ hι₂ hdι₂ Φ hΦ hε hε₁ ho₁ ho₂ =
      (TauCeti.ConnectedSum.orientation (isOpenEmbedding_rescale hι₁ hε.ne')
        (isOpenEmbedding_rescale (hι₂.comp_linearIsometryEquiv Φ) hε.ne')
        (IsLocalDiffeomorph.of_le (isLocalDiffeomorph_rescale hdι₁ hε.ne') ENat.LEInfty.out)
        (IsLocalDiffeomorph.of_le (isLocalDiffeomorph_rescale
          (hdι₂.comp_linearIsometryEquiv Φ) hε.ne') ENat.LEInfty.out) o₁ o₂ oE
        (fun v _ ↦ isOrientationPreservingAt_rescale_of_mem_ball hdι₁ hε ho₁ v)
        (fun v _ ↦ isOrientationReversingAt_rescale_comp_of_mem_ball hdι₂ Φ hΦ hε ho₂ v)).map
        (annulusSumDiffeomorph hι₁ hdι₁ hι₂ hdι₂ Φ hε.ne' hε₁).symm (by simp) o₁.card_eq :=
  (rfl)

/-- The diffeomorphism `annulusSumDiffeomorph` from `AnnulusSum` to Tau Ceti's connected sum
preserves orientation, from `AnnulusSum.orientation` to `TauCeti.ConnectedSum.orientation`. -/
theorem isOrientationPreservingAt_annulusSumDiffeomorph
    (p : AnnulusSum hι₁ hdι₁ hι₂ hdι₂ Φ hε.ne') :
    letI := TauCeti.ConnectedSum.chartedSpace (H := E) (isOpenEmbedding_rescale hι₁ hε.ne')
      (isOpenEmbedding_rescale (hι₂.comp_linearIsometryEquiv Φ) hε.ne')
    haveI := TauCeti.ConnectedSum.isManifold (isOpenEmbedding_rescale hι₁ hε.ne')
      (isOpenEmbedding_rescale (hι₂.comp_linearIsometryEquiv Φ) hε.ne')
      (isLocalDiffeomorph_rescale hdι₁ hε.ne')
      (isLocalDiffeomorph_rescale (hdι₂.comp_linearIsometryEquiv Φ) hε.ne')
    IsOrientationPreservingAt
      (AnnulusSum.orientation o₁ o₂ oE hι₁ hdι₁ hι₂ hdι₂ Φ hΦ hε hε₁ ho₁ ho₂)
      (TauCeti.ConnectedSum.orientation (isOpenEmbedding_rescale hι₁ hε.ne')
        (isOpenEmbedding_rescale (hι₂.comp_linearIsometryEquiv Φ) hε.ne')
        (IsLocalDiffeomorph.of_le (isLocalDiffeomorph_rescale hdι₁ hε.ne') ENat.LEInfty.out)
        (IsLocalDiffeomorph.of_le (isLocalDiffeomorph_rescale
          (hdι₂.comp_linearIsometryEquiv Φ) hε.ne') ENat.LEInfty.out) o₁ o₂ oE
        (fun v _ ↦ isOrientationPreservingAt_rescale_of_mem_ball hdι₁ hε ho₁ v)
        (fun v _ ↦ isOrientationReversingAt_rescale_comp_of_mem_ball hdι₂ Φ hΦ hε ho₂ v))
      (annulusSumDiffeomorph hι₁ hdι₁ hι₂ hdι₂ Φ hε.ne' hε₁) p := by
  let := TauCeti.ConnectedSum.chartedSpace (H := E) (isOpenEmbedding_rescale hι₁ hε.ne')
    (isOpenEmbedding_rescale (hι₂.comp_linearIsometryEquiv Φ) hε.ne')
  have := TauCeti.ConnectedSum.isManifold (isOpenEmbedding_rescale hι₁ hε.ne')
    (isOpenEmbedding_rescale (hι₂.comp_linearIsometryEquiv Φ) hε.ne')
    (isLocalDiffeomorph_rescale hdι₁ hε.ne')
    (isLocalDiffeomorph_rescale (hdι₂.comp_linearIsometryEquiv Φ) hε.ne')
  rw [AnnulusSum.orientation_def]
  simpa only [Diffeomorph.symm_symm] using isOrientationPreservingAt_map_symm _
    (annulusSumDiffeomorph hι₁ hdι₁ hι₂ hdι₂ Φ hε.ne' hε₁).symm _ o₁.card_eq p

/-- The inclusion of the first piece into `AnnulusSum` preserves orientation, from the
restriction of `o₁` to `AnnulusSum.orientation`. -/
theorem AnnulusSum.isOrientationPreservingAt_inl (x : piece ι₁ ε hι₁.continuous) :
    IsOrientationPreservingAt (o₁.restrict (piece ι₁ ε hι₁.continuous))
      (AnnulusSum.orientation o₁ o₂ oE hι₁ hdι₁ hι₂ hdι₂ Φ hΦ hε hε₁ ho₁ ho₂)
      (GluedAlong.inl (overlapDiffeomorph hι₁ hdι₁ hι₂ hdι₂ Φ hε.ne').toHomeomorph) x := by
  let := TauCeti.ConnectedSum.chartedSpace (H := E) (isOpenEmbedding_rescale hι₁ hε.ne')
    (isOpenEmbedding_rescale (hι₂.comp_linearIsometryEquiv Φ) hε.ne')
  have := TauCeti.ConnectedSum.isManifold (isOpenEmbedding_rescale hι₁ hε.ne')
    (isOpenEmbedding_rescale (hι₂.comp_linearIsometryEquiv Φ) hε.ne')
    (isLocalDiffeomorph_rescale hdι₁ hε.ne')
    (isLocalDiffeomorph_rescale (hdι₂.comp_linearIsometryEquiv Φ) hε.ne')
  set e := annulusSumDiffeomorph hι₁ hdι₁ hι₂ hdι₂ Φ hε.ne' hε₁
  have h : GluedAlong.inl (overlapDiffeomorph hι₁ hdι₁ hι₂ hdι₂ Φ hε.ne').toHomeomorph =
      e.symm ∘ (TauCeti.ConnectedSum.inl _ _ ∘ Opens.inclusion (piece_le_puncture ε (by simp))) :=
    funext fun x ↦ (e.symm_apply_eq.2
      (annulusSumDiffeomorph_inl hι₁ hdι₁ hι₂ hdι₂ Φ hε.ne' hε₁ x).symm).symm
  rw [h, AnnulusSum.orientation_def]
  exact (isOrientationPreservingAt_map _ e.symm _ o₁.card_eq _).comp
    ((TauCeti.ConnectedSum.isOrientationPreservingAt_inl _ _ _ _ _ _
      (isOrientationPreservingAt_restrict o₁ _ _)).comp
      (isOrientationPreservingAt_restrict_inclusion o₁ _ x))

/-- The inclusion of the second piece into `AnnulusSum` preserves orientation, from the
restriction of `o₂` to `AnnulusSum.orientation`. -/
theorem AnnulusSum.isOrientationPreservingAt_inr (y : piece ι₂ ε hι₂.continuous) :
    IsOrientationPreservingAt (o₂.restrict (piece ι₂ ε hι₂.continuous))
      (AnnulusSum.orientation o₁ o₂ oE hι₁ hdι₁ hι₂ hdι₂ Φ hΦ hε hε₁ ho₁ ho₂)
      (GluedAlong.inr (overlapDiffeomorph hι₁ hdι₁ hι₂ hdι₂ Φ hε.ne').toHomeomorph) y := by
  let := TauCeti.ConnectedSum.chartedSpace (H := E) (isOpenEmbedding_rescale hι₁ hε.ne')
    (isOpenEmbedding_rescale (hι₂.comp_linearIsometryEquiv Φ) hε.ne')
  have := TauCeti.ConnectedSum.isManifold (isOpenEmbedding_rescale hι₁ hε.ne')
    (isOpenEmbedding_rescale (hι₂.comp_linearIsometryEquiv Φ) hε.ne')
    (isLocalDiffeomorph_rescale hdι₁ hε.ne')
    (isLocalDiffeomorph_rescale (hdι₂.comp_linearIsometryEquiv Φ) hε.ne')
  set e := annulusSumDiffeomorph hι₁ hdι₁ hι₂ hdι₂ Φ hε.ne' hε₁
  have h : GluedAlong.inr (overlapDiffeomorph hι₁ hdι₁ hι₂ hdι₂ Φ hε.ne').toHomeomorph =
      e.symm ∘ (TauCeti.ConnectedSum.inr _ _ ∘ Opens.inclusion (piece_le_puncture ε (by simp))) :=
    funext fun y ↦ (e.symm_apply_eq.2
      (annulusSumDiffeomorph_inr hι₁ hdι₁ hι₂ hdι₂ Φ hε.ne' hε₁ y).symm).symm
  rw [h, AnnulusSum.orientation_def]
  exact (isOrientationPreservingAt_map _ e.symm _ o₁.card_eq _).comp
    ((TauCeti.ConnectedSum.isOrientationPreservingAt_inr _ _ _ _ _ _
      (isOrientationPreservingAt_restrict o₂ _ _)).comp
      (isOrientationPreservingAt_restrict_inclusion o₂ _ y))

/-- An orientation of the connected sum `AnnulusSum` is `AnnulusSum.orientation` exactly when
the inclusions of the two pieces preserve orientation, from the restrictions of `o₁` and `o₂`. -/
theorem AnnulusSum.eq_orientation_iff
    {o : TauCeti.Manifold.Orientation 𝓘(ℝ, E) (AnnulusSum hι₁ hdι₁ hι₂ hdι₂ Φ hε.ne') ι} :
    o = AnnulusSum.orientation o₁ o₂ oE hι₁ hdι₁ hι₂ hdι₂ Φ hΦ hε hε₁ ho₁ ho₂ ↔
      (∀ x, IsOrientationPreservingAt (o₁.restrict (piece ι₁ ε hι₁.continuous)) o
        (GluedAlong.inl (overlapDiffeomorph hι₁ hdι₁ hι₂ hdι₂ Φ hε.ne').toHomeomorph) x) ∧
      ∀ y, IsOrientationPreservingAt (o₂.restrict (piece ι₂ ε hι₂.continuous)) o
        (GluedAlong.inr (overlapDiffeomorph hι₁ hdι₁ hι₂ hdι₂ Φ hε.ne').toHomeomorph) y := by
  refine ⟨?_, fun ⟨hl, hr⟩ ↦ ?_⟩
  · rintro rfl
    exact ⟨AnnulusSum.isOrientationPreservingAt_inl o₁ o₂ oE hι₁ hdι₁ hι₂ hdι₂ Φ hΦ hε hε₁ ho₁ ho₂,
      AnnulusSum.isOrientationPreservingAt_inr o₁ o₂ oE hι₁ hdι₁ hι₂ hdι₂ Φ hΦ hε hε₁ ho₁ ho₂⟩
  ext p
  rcases GluedAlong.exists_inl_or_exists_inr _ p with ⟨x, rfl⟩ | ⟨y, rfl⟩
  · exact (hl x).orientationAt_eq
      (AnnulusSum.isOrientationPreservingAt_inl o₁ o₂ oE hι₁ hdι₁ hι₂ hdι₂ Φ hΦ hε hε₁ ho₁ ho₂ x)
  · exact (hr y).orientationAt_eq
      (AnnulusSum.isOrientationPreservingAt_inr o₁ o₂ oE hι₁ hdι₁ hι₂ hdι₂ Φ hΦ hε hε₁ ho₁ ho₂ y)

variable [Nontrivial E] [PreconnectedSpace M₁] [PreconnectedSpace M₂]

/-- For connected oriented summands, the connected sum `AnnulusSum` of McDuff–Salamon, with
`AnnulusSum.orientation`, is diffeomorphic to Tau Ceti's oriented connected sum
`TauCeti.OrientedConnectedSum o₁ o₂`, with `TauCeti.OrientedConnectedSum.orientation`, by an
orientation-preserving diffeomorphism. (The summands are nonempty, as `ι₁ 0` and `ι₂ 0` show; the
instances `Nonempty M₁` and `Nonempty M₂` are needed to form Tau Ceti's oriented connected sum.) -/
theorem AnnulusSum.exists_diffeomorph_orientedConnectedSum_isOrientationPreservingAt
    [Nonempty M₁] [Nonempty M₂] :
    ∃ Ψ : AnnulusSum hι₁ hdι₁ hι₂ hdι₂ Φ hε.ne' ≃ₘ^∞⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯
        TauCeti.OrientedConnectedSum o₁ o₂, ∀ p,
      IsOrientationPreservingAt
        (AnnulusSum.orientation o₁ o₂ oE hι₁ hdι₁ hι₂ hdι₂ Φ hΦ hε hε₁ ho₁ ho₂)
        (TauCeti.OrientedConnectedSum.orientation o₁ o₂) Ψ p := by
  let := TauCeti.ConnectedSum.chartedSpace (H := E) (isOpenEmbedding_rescale hι₁ hε.ne')
    (isOpenEmbedding_rescale (hι₂.comp_linearIsometryEquiv Φ) hε.ne')
  have := TauCeti.ConnectedSum.isManifold (isOpenEmbedding_rescale hι₁ hε.ne')
    (isOpenEmbedding_rescale (hι₂.comp_linearIsometryEquiv Φ) hε.ne')
    (isLocalDiffeomorph_rescale hdι₁ hε.ne')
    (isLocalDiffeomorph_rescale (hdι₂.comp_linearIsometryEquiv Φ) hε.ne')
  obtain ⟨Θ, hΘ⟩ :=
    TauCeti.OrientedConnectedSum.exists_diffeomorph_connectedSum_isOrientationPreservingAt o₁ o₂
      (isOpenEmbedding_rescale hι₁ hε.ne')
      (isOpenEmbedding_rescale (hι₂.comp_linearIsometryEquiv Φ) hε.ne')
      (isLocalDiffeomorph_rescale hdι₁ hε.ne')
      (isLocalDiffeomorph_rescale (hdι₂.comp_linearIsometryEquiv Φ) hε.ne') oE
      (isOrientationPreservingAt_rescale_of_mem_ball hdι₁ hε ho₁)
      (isOrientationReversingAt_rescale_comp_of_mem_ball hdι₂ Φ hΦ hε ho₂)
  refine ⟨(annulusSumDiffeomorph hι₁ hdι₁ hι₂ hdι₂ Φ hε.ne' hε₁).trans Θ.symm, fun p ↦ ?_⟩
  rw [Diffeomorph.coe_trans]
  exact ((hΘ _).diffeomorph_symm (by simp)).comp
    (isOrientationPreservingAt_annulusSumDiffeomorph o₁ o₂ oE hι₁ hdι₁ hι₂ hdι₂ Φ hΦ hε hε₁
      ho₁ ho₂ p)

/-- **The connected sum of McDuff–Salamon does not depend on its choices.** Let `M₁` and `M₂` be
connected Hausdorff smooth manifolds modelled on a nontrivial finite-dimensional real inner
product space `E`, with orientations `o₁` and `o₂`. Take open embeddings `ι₁ : E → M₁` and
`ι₂ : E → M₂` that are smooth local diffeomorphisms and preserve orientation on the unit ball
from an orientation `oE` of `E`, a linear isometry `Φ` of `E` of negative determinant, and
`0 < ε` with `ε² < 1`; and take another such choice `ι₁'`, `ι₂'`, `Φ'`, `ε'`, for an orientation
`oE'` of `E`. Then the two connected sums `AnnulusSum`, with their orientations
`AnnulusSum.orientation`, are diffeomorphic by an orientation-preserving diffeomorphism. Each is
also orientation-preservingly diffeomorphic to Tau Ceti's oriented connected sum
(`AnnulusSum.exists_diffeomorph_orientedConnectedSum_isOrientationPreservingAt`).

Milestone: *Disc theorem*. -/
theorem AnnulusSum.exists_diffeomorph_isOrientationPreservingAt {ι₁' : E → M₁} {ι₂' : E → M₂}
    (hι₁' : IsOpenEmbedding ι₁') (hdι₁' : IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ ι₁')
    (hι₂' : IsOpenEmbedding ι₂') (hdι₂' : IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ ι₂')
    (Φ' : E ≃ₗᵢ[ℝ] E) (hΦ' : LinearMap.det (Φ'.toLinearEquiv : E →ₗ[ℝ] E) < 0) {ε' : ℝ}
    (hε' : 0 < ε') (hε₁' : ε' ^ 2 < 1) (oE' : TauCeti.Manifold.Orientation 𝓘(ℝ, E) E ι)
    (ho₁' : ∀ ξ ∈ ball (0 : E) 1, IsOrientationPreservingAt oE' o₁ ι₁' ξ)
    (ho₂' : ∀ ξ ∈ ball (0 : E) 1, IsOrientationPreservingAt oE' o₂ ι₂' ξ) :
    ∃ Ψ : AnnulusSum hι₁ hdι₁ hι₂ hdι₂ Φ hε.ne' ≃ₘ^∞⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯
        AnnulusSum hι₁' hdι₁' hι₂' hdι₂' Φ' hε'.ne', ∀ p,
      IsOrientationPreservingAt
        (AnnulusSum.orientation o₁ o₂ oE hι₁ hdι₁ hι₂ hdι₂ Φ hΦ hε hε₁ ho₁ ho₂)
        (AnnulusSum.orientation o₁ o₂ oE' hι₁' hdι₁' hι₂' hdι₂' Φ' hΦ' hε' hε₁' ho₁' ho₂') Ψ p := by
  have : Nonempty M₁ := ⟨ι₁ 0⟩
  have : Nonempty M₂ := ⟨ι₂ 0⟩
  obtain ⟨Ψ, hΨ⟩ := AnnulusSum.exists_diffeomorph_orientedConnectedSum_isOrientationPreservingAt
    o₁ o₂ oE hι₁ hdι₁ hι₂ hdι₂ Φ hΦ hε hε₁ ho₁ ho₂
  obtain ⟨Ψ', hΨ'⟩ := AnnulusSum.exists_diffeomorph_orientedConnectedSum_isOrientationPreservingAt
    o₁ o₂ oE' hι₁' hdι₁' hι₂' hdι₂' Φ' hΦ' hε' hε₁' ho₁' ho₂'
  refine ⟨Ψ.trans Ψ'.symm, fun p ↦ ?_⟩
  rw [Diffeomorph.coe_trans]
  exact ((hΨ' _).diffeomorph_symm (by simp)).comp (hΨ p)

end Orientation

end SymplecticGeometry.ConnectedSum

end
