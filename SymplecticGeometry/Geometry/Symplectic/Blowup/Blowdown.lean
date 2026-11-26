/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Gluing.Pair
public import SymplecticGeometry.Geometry.Symplectic.Blowup.Model
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset

/-!
# The blowdown of a divisor modelled on the exceptional divisor

Let `M` be a Hausdorff smooth manifold modelled on `E := Fin (n + 1) → ℂ`, let
`f : ℙ ℂ E → M` be a map, and let `Ψ` be a partial diffeomorphism from `M` to the model blowup
`L = BlowupModel n` with target `openNbhd n ε`, whose source contains the image of `f`, and with
`Ψ (f q) = zeroSection q` for all `q`. This is what
`BlowupModel.exists_symplectomorphism_blowupModel` (`Blowup/DivisorNeighborhood.lean`) gives for
a divisor of a symplectic manifold. Following McDuff–Salamon, §7.1, the blowdown of `M` along `f`
with weight `l ≥ 0` is obtained by removing the image `Z` of `f` from `M` and gluing in the open
ball `|w| < √(l² + ε²)` of `E` (for the Euclidean norm `|w|` of `complexToRealEuclidean`): a point
`x` of the source of `Ψ` off `Z` is identified with `F_l(π (Ψ x))`, where `F_l` is the radial map
and `π` the blowdown, that is, with `BlowupModel.shellSymplectomorph` applied to `Ψ x`. This map
is a diffeomorphism of `Ψ.source ∖ Z` onto the open shell `l < |w| < √(l² + ε²)`.

The topology and the smooth structure do not use any form; the form of the blowdown is built from
these pieces in a later step.

## Main definitions

* `SymplecticGeometry.DivisorBlowdown.outerPiece hf`: the open subset `M ∖ Z` of `M`.
* `SymplecticGeometry.DivisorBlowdown.ballPiece n l ε`: the open ball `|w| < √(l² + ε²)` of `E`.
* `SymplecticGeometry.DivisorBlowdown.sourceComplRange hf`: the open subset `Ψ.source ∖ Z` of
  `M`, and `SymplecticGeometry.DivisorBlowdown.sourceComplRangeDiffeomorph hΨ hf`, the
  diffeomorphism `Ψ` from it onto `openNbhd n ε ∖ Z`.
* `SymplecticGeometry.DivisorBlowdown.gluingDiffeomorph hΨ hf hl hε`: the diffeomorphism
  `x ↦ F_l(π (Ψ x))` from `Ψ.source ∖ Z`, as an open subset of the outer piece, onto the open
  shell, as an open subset of the ball piece.
* `SymplecticGeometry.DivisorBlowdown hΨ hf hl hε`: the blowdown, the space
  `SymplecticGeometry.GluedAlong` of `Geometry/Manifold/Gluing/Pair.lean` glued from the two
  pieces along `gluingDiffeomorph`.

## Main results

* `SymplecticGeometry.DivisorBlowdown.apply_mem_exceptionalDivisor_iff`: on the source of `Ψ`,
  `Ψ` sends exactly the points of `Z` into the exceptional divisor.
* `SymplecticGeometry.DivisorBlowdown.isCompact_range`: `Z` is compact.
* `SymplecticGeometry.DivisorBlowdown.coe_gluingDiffeomorph_apply`: the gluing map is
  `shellSymplectomorph ∘ Ψ`.
* `SymplecticGeometry.DivisorBlowdown.instIsManifold`: the blowdown is a smooth manifold
  modelled on `E`.
* `SymplecticGeometry.DivisorBlowdown.inl_eq_inr_iff`: the identification made by the gluing,
  for the embeddings `GluedAlong.inl` and `GluedAlong.inr` of the two pieces.
* `SymplecticGeometry.DivisorBlowdown.instT2Space`: the blowdown is Hausdorff. A point `w` of the
  ball with `|w| ≤ l` and a point `x` of `M ∖ Z` off the source of `Ψ` are separated, for
  `0 < δ < ε`, by the ball `|w| < √(l² + δ²)` and the complement of the compact image of
  `L(δ)` under the inverse of `Ψ`. This is the criterion `GluedAlong.t2Space_iff`.

The construction follows that of `SymplecticGeometry.WeightBlowup` in
`Blowup/Weight/Basic.lean`, with the roles of the model and of the ball exchanged; its proof of
`T2Space` is adapted from `SymplecticGeometry.WeightBlowup.instT2Space`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §7.1.
* [D. McDuff, *Blow ups and symplectic embeddings in dimension 4*][McDuff1991], Lemma 2.1 and
  Corollary 2.2.
-/

public section

noncomputable section

open Set Metric Topology TopologicalSpace TauCeti
open scoped Manifold ContDiff LinearAlgebra.Projectivization

namespace SymplecticGeometry

namespace DivisorBlowdown

open BlowupModel

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Fin (n + 1) → ℂ) M]
  {f : ℙ ℂ (Fin (n + 1) → ℂ) → M}
  {Ψ : PartialDiffeomorph 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) M (BlowupModel n) ∞}
  {l ε : ℝ}

/-- On the source of `Ψ`, a point is sent into the exceptional divisor exactly when it lies in the
image of `f`. -/
theorem apply_mem_exceptionalDivisor_iff (hf : ∀ q, f q ∈ Ψ.source ∧ Ψ (f q) = zeroSection q)
    {x : M} (hx : x ∈ Ψ.source) : Ψ x ∈ exceptionalDivisor n ↔ x ∈ range f := by
  rw [exceptionalDivisor_eq_range]
  refine ⟨fun ⟨q, hq⟩ ↦ ⟨q, Ψ.toOpenPartialHomeomorph.injOn (hf q).1 hx ?_⟩, fun ⟨q, hq⟩ ↦
    ⟨q, hq ▸ (hf q).2.symm⟩⟩
  exact (hf q).2.trans hq

/-- The image of `f` is the image of the exceptional divisor under the inverse of `Ψ`. -/
theorem range_eq_image_exceptionalDivisor
    (hf : ∀ q, f q ∈ Ψ.source ∧ Ψ (f q) = zeroSection q) :
    range f = Ψ.symm '' exceptionalDivisor n := by
  rw [exceptionalDivisor_eq_range, ← range_comp]
  refine congrArg range (funext fun q ↦ ?_)
  rw [Function.comp_apply, ← (hf q).2]
  exact (Ψ.toOpenPartialHomeomorph.left_inv (hf q).1).symm

/-- The image of `f` is compact: it is the image of the compact exceptional divisor under the
inverse of `Ψ`, which is continuous on the target of `Ψ`. -/
theorem isCompact_range (hf : ∀ q, f q ∈ Ψ.source ∧ Ψ (f q) = zeroSection q) :
    IsCompact (range f) := by
  rw [range_eq_image_exceptionalDivisor hf, exceptionalDivisor_eq_range]
  refine (_root_.isCompact_range continuous_zeroSection).image_of_continuousOn
    (Ψ.toOpenPartialHomeomorph.continuousOn_symm.mono ?_)
  rintro _ ⟨q, rfl⟩
  rw [← (hf q).2]
  exact Ψ.toOpenPartialHomeomorph.map_source (hf q).1

variable [T2Space M]

/-- The first piece of the blowdown: the open subset `M ∖ Z` of `M`, for `Z` the image of `f`. -/
def outerPiece (hf : ∀ q, f q ∈ Ψ.source ∧ Ψ (f q) = zeroSection q) : Opens M :=
  ⟨(range f)ᶜ, (isCompact_range hf).isClosed.isOpen_compl⟩

@[simp]
theorem mem_outerPiece_iff (hf : ∀ q, f q ∈ Ψ.source ∧ Ψ (f q) = zeroSection q) {x : M} :
    x ∈ outerPiece hf ↔ x ∉ range f :=
  Iff.rfl

variable (n l ε) in
/-- The second piece of the blowdown: the open ball `|w| < √(l² + ε²)` of `E`, for the Euclidean
norm of `complexToRealEuclidean`. -/
def ballPiece : Opens (Fin (n + 1) → ℂ) :=
  ⟨{w | ‖complexToRealEuclidean (Fin (n + 1)) w‖ < √(l ^ 2 + ε ^ 2)},
    isOpen_lt (complexToRealEuclidean (Fin (n + 1))).continuous.norm continuous_const⟩

@[simp]
theorem mem_ballPiece_iff {w : Fin (n + 1) → ℂ} :
    w ∈ ballPiece n l ε ↔ ‖complexToRealEuclidean (Fin (n + 1)) w‖ < √(l ^ 2 + ε ^ 2) :=
  Iff.rfl

variable (n l ε) in
/-- The open shell `l < |w| < √(l² + ε²)` lies in the ball piece. -/
theorem openShell_le_ballPiece : openShell n l ε ≤ ballPiece n l ε :=
  fun _ hw ↦ (mem_ballPiece_iff).2 (mem_openShell_iff.1 hw).2

/-- The source of `Ψ` minus the image `Z` of `f`, an open subset of `M`. -/
def sourceComplRange (hf : ∀ q, f q ∈ Ψ.source ∧ Ψ (f q) = zeroSection q) : Opens M :=
  ⟨Ψ.source \ range f, Ψ.open_source.sdiff (isCompact_range hf).isClosed⟩

@[simp]
theorem mem_sourceComplRange_iff (hf : ∀ q, f q ∈ Ψ.source ∧ Ψ (f q) = zeroSection q) {x : M} :
    x ∈ sourceComplRange hf ↔ x ∈ Ψ.source ∧ x ∉ range f :=
  Iff.rfl

theorem sourceComplRange_le_outerPiece (hf : ∀ q, f q ∈ Ψ.source ∧ Ψ (f q) = zeroSection q) :
    sourceComplRange hf ≤ outerPiece hf :=
  fun _ hx ↦ hx.2

/-- `Ψ` maps a point of its source off the image of `f` into `openNbhd n ε ∖ Z`. -/
theorem apply_mem_openNbhdComplDivisor (hΨ : Ψ.target = openNbhd n ε)
    (hf : ∀ q, f q ∈ Ψ.source ∧ Ψ (f q) = zeroSection q) {x : M}
    (hx : x ∈ sourceComplRange hf) : Ψ x ∈ openNbhdComplDivisor n ε := by
  rw [mem_sourceComplRange_iff] at hx
  exact mem_openNbhdComplDivisor_iff.2 ⟨hΨ ▸ Ψ.toOpenPartialHomeomorph.map_source hx.1,
    (apply_mem_exceptionalDivisor_iff hf hx.1).not.2 hx.2⟩

/-- **`Ψ` off the divisor**: the restriction of `Ψ` to a diffeomorphism from `Ψ.source ∖ Z` onto
`openNbhd n ε ∖ Z`. -/
def sourceComplRangeDiffeomorph (hΨ : Ψ.target = openNbhd n ε)
    (hf : ∀ q, f q ∈ Ψ.source ∧ Ψ (f q) = zeroSection q) :
    sourceComplRange hf ≃ₘ⟮𝓘(ℝ, Fin (n + 1) → ℂ), 𝓘(ℝ, Fin (n + 1) → ℂ)⟯
      openNbhdComplDivisor n ε :=
  (Diffeomorph.nestedOpen (U := sourceComplRange hf) (D := ⟨Ψ.source, Ψ.open_source⟩)
      fun _ hx ↦ hx.1).symm.trans
    ((Ψ.toDiffeomorphSourceTarget.subtype fun x ↦ by
        simp only [Opens.mem_comap, ContinuousMap.coe_mk,
          PartialDiffeomorph.toDiffeomorphSourceTarget_apply_coe]
        refine ⟨fun hx ↦ apply_mem_openNbhdComplDivisor hΨ hf hx, fun hx ↦ ⟨x.property, ?_⟩⟩
        exact (apply_mem_exceptionalDivisor_iff hf x.property).not.1
          (mem_openNbhdComplDivisor_iff.1 hx).2).trans
      (Diffeomorph.nestedOpen fun _ hp ↦ by
        change _ ∈ Ψ.target
        exact hΨ ▸ (mem_openNbhdComplDivisor_iff.1 hp).1))

@[simp]
theorem coe_sourceComplRangeDiffeomorph_apply (hΨ : Ψ.target = openNbhd n ε)
    (hf : ∀ q, f q ∈ Ψ.source ∧ Ψ (f q) = zeroSection q) (x : sourceComplRange hf) :
    (sourceComplRangeDiffeomorph hΨ hf x : BlowupModel n) = Ψ x := by
  simp [sourceComplRangeDiffeomorph]

/-- The overlap on the side of `M`: `Ψ.source ∖ Z`, as an open subset of the outer piece. -/
def outerOverlap (hf : ∀ q, f q ∈ Ψ.source ∧ Ψ (f q) = zeroSection q) :
    Opens (outerPiece hf) :=
  Opens.comap ⟨Subtype.val, continuous_subtypeVal⟩ (sourceComplRange hf)

/-- A point of the outer piece lies in the overlap exactly when it is in the source of `Ψ`. -/
@[simp]
theorem mem_outerOverlap_iff (hf : ∀ q, f q ∈ Ψ.source ∧ Ψ (f q) = zeroSection q)
    {x : outerPiece hf} : x ∈ outerOverlap hf ↔ (x : M) ∈ Ψ.source := by
  simp only [outerOverlap, Opens.mem_comap, ContinuousMap.coe_mk, mem_sourceComplRange_iff,
    and_iff_left_iff_imp]
  exact fun _ ↦ x.property

/-- A point of the overlap on the side of `M`, as a point of `M`, lies in `Ψ.source ∖ Z`. -/
theorem coe_mem_sourceComplRange (hf : ∀ q, f q ∈ Ψ.source ∧ Ψ (f q) = zeroSection q)
    (x : outerOverlap hf) : ((x : outerPiece hf) : M) ∈ sourceComplRange hf :=
  (mem_sourceComplRange_iff hf).2
    ⟨(mem_outerOverlap_iff hf).1 x.property, (mem_outerPiece_iff hf).1 x.val.property⟩

variable (n l ε) in
/-- The overlap on the side of the ball: the open shell `l < |w| < √(l² + ε²)`, as an open
subset of the ball piece. -/
def ballOverlap : Opens (ballPiece n l ε) :=
  Opens.comap ⟨Subtype.val, continuous_subtypeVal⟩ (openShell n l ε)

/-- A point of the ball piece lies in the overlap exactly when its Euclidean norm exceeds `l`. -/
@[simp]
theorem mem_ballOverlap_iff {w : ballPiece n l ε} :
    w ∈ ballOverlap n l ε ↔ l < ‖complexToRealEuclidean (Fin (n + 1)) (w : Fin (n + 1) → ℂ)‖ := by
  simp only [ballOverlap, Opens.mem_comap, ContinuousMap.coe_mk, mem_openShell_iff,
    and_iff_left_iff_imp]
  exact fun _ ↦ (mem_ballPiece_iff).1 w.property

/-- **The gluing map** of the blowdown: the diffeomorphism `x ↦ F_l(π (Ψ x))`, which is
`shellSymplectomorph ∘ Ψ`, from `Ψ.source ∖ Z` in the outer piece onto the open shell
`l < |w| < √(l² + ε²)` in the ball piece. -/
def gluingDiffeomorph (hΨ : Ψ.target = openNbhd n ε)
    (hf : ∀ q, f q ∈ Ψ.source ∧ Ψ (f q) = zeroSection q) (hl : 0 ≤ l) (hε : 0 < ε) :
    outerOverlap hf ≃ₘ⟮𝓘(ℝ, Fin (n + 1) → ℂ), 𝓘(ℝ, Fin (n + 1) → ℂ)⟯ ballOverlap n l ε :=
  (Diffeomorph.nestedOpen (sourceComplRange_le_outerPiece hf)).trans
    ((sourceComplRangeDiffeomorph hΨ hf).trans
      ((shellSymplectomorph n l ε hl hε.le).trans
        (Diffeomorph.nestedOpen (openShell_le_ballPiece n l ε)).symm))

@[simp]
theorem coe_gluingDiffeomorph_apply (hΨ : Ψ.target = openNbhd n ε)
    (hf : ∀ q, f q ∈ Ψ.source ∧ Ψ (f q) = zeroSection q) (hl : 0 ≤ l) (hε : 0 < ε)
    (x : outerOverlap hf) :
    ((gluingDiffeomorph hΨ hf hl hε x : ballPiece n l ε) : Fin (n + 1) → ℂ) =
      shellSymplectomorph n l ε hl hε.le
        ⟨Ψ x.val.val, apply_mem_openNbhdComplDivisor hΨ hf (coe_mem_sourceComplRange hf x)⟩ := by
  -- The coercion of `gluingDiffeomorph` to a function goes between the types `outerOverlap hf`
  -- and `ballOverlap n l ε`, which the lemmas about `Diffeomorph.trans` and
  -- `Diffeomorph.nestedOpen` match only once both are unfolded, in the type of `x` too.
  revert x
  delta gluingDiffeomorph outerOverlap ballOverlap
  intro x
  simp only [Diffeomorph.coe_trans, Function.comp_apply, Diffeomorph.nestedOpen_apply,
    Diffeomorph.nestedOpen_symm_apply]
  congr 2
  exact Subtype.ext (coe_sourceComplRangeDiffeomorph_apply hΨ hf _)

/-- **The blowdown** of `M` along `f`, with weight `l`, following McDuff–Salamon, §7.1: the outer
piece `M ∖ Z` and the ball piece `|w| < √(l² + ε²)` glued along `gluingDiffeomorph`, which
identifies `x ∈ Ψ.source ∖ Z` with `F_l(π (Ψ x))`. It is a smooth manifold modelled on
`Fin (n + 1) → ℂ`. -/
abbrev _root_.SymplecticGeometry.DivisorBlowdown (hΨ : Ψ.target = openNbhd n ε)
    (hf : ∀ q, f q ∈ Ψ.source ∧ Ψ (f q) = zeroSection q) (hl : 0 ≤ l) (hε : 0 < ε) : Type :=
  GluedAlong (gluingDiffeomorph hΨ hf hl hε).toHomeomorph

variable (hΨ : Ψ.target = openNbhd n ε) (hf : ∀ q, f q ∈ Ψ.source ∧ Ψ (f q) = zeroSection q)
  (hl : 0 ≤ l) (hε : 0 < ε)

/-- The blowdown is a smooth manifold. -/
instance instIsManifold [IsManifold 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ M] :
    IsManifold 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ (DivisorBlowdown hΨ hf hl hε) :=
  inferInstance

/-- A point `x` of `M ∖ Z` and a point `w` of the ball have the same image in the blowdown
exactly when `x` lies in the source of `Ψ` and `w = F_l(π (Ψ x))`. -/
theorem inl_eq_inr_iff {x : outerPiece hf} {w : ballPiece n l ε} :
    GluedAlong.inl (gluingDiffeomorph hΨ hf hl hε).toHomeomorph x =
        GluedAlong.inr (gluingDiffeomorph hΨ hf hl hε).toHomeomorph w ↔
      ∃ h : (x : M) ∈ Ψ.source, (w : Fin (n + 1) → ℂ) =
        shellSymplectomorph n l ε hl hε.le
          ⟨Ψ x, apply_mem_openNbhdComplDivisor hΨ hf
            ((mem_sourceComplRange_iff hf).2 ⟨h, (mem_outerPiece_iff hf).1 x.property⟩)⟩ := by
  rw [GluedAlong.inl_eq_inr_iff]
  refine ⟨fun ⟨h, hw⟩ ↦ ⟨(mem_outerOverlap_iff hf).1 h, ?_⟩,
    fun ⟨h, hw⟩ ↦ ⟨(mem_outerOverlap_iff hf).2 h, Subtype.ext ?_⟩⟩
  · rw [← hw, Diffeomorph.coe_toHomeomorph, coe_gluingDiffeomorph_apply]
  · rw [hw, Diffeomorph.coe_toHomeomorph, coe_gluingDiffeomorph_apply]

/-- **The blowdown is Hausdorff**, for Hausdorff `M`. -/
instance instT2Space : T2Space (DivisorBlowdown hΨ hf hl hε) := by
  -- By `GluedAlong.t2Space_iff`, it suffices to separate a point `x` of `M ∖ Z` off the source
  -- of `Ψ` from a point `w` of the ball with `|w| ≤ l`. For `δ = ε / 2`, the points of
  -- `Ψ.source ∖ Z` glued into the ball `|w| < √(l² + δ²)` lie in the compact image of `L(δ)`
  -- under the inverse of `Ψ`, which misses `x`.
  refine (GluedAlong.t2Space_iff _).2 ⟨inferInstance, inferInstance, fun x hx w hw ↦ ?_⟩
  rw [mem_outerOverlap_iff] at hx
  rw [mem_ballOverlap_iff, not_lt] at hw
  have hδ : 0 < ε / 2 := half_pos hε
  have hK : closedNbhd n (ε / 2) ⊆ Ψ.target :=
    hΨ ▸ fun p hp ↦ (mem_openNbhd_iff).2 ((mem_closedNbhd_iff.1 hp).trans_lt (half_lt_self hε))
  have hKc : IsCompact (Ψ.symm '' closedNbhd n (ε / 2)) :=
    (isCompact_closedNbhd _).image_of_continuousOn
      (Ψ.toOpenPartialHomeomorph.continuousOn_symm.mono hK)
  refine ⟨Subtype.val ⁻¹' (Ψ.symm '' closedNbhd n (ε / 2))ᶜ, ?_,
    Subtype.val ⁻¹' {v | ‖complexToRealEuclidean (Fin (n + 1)) v‖ < √(l ^ 2 + (ε / 2) ^ 2)}, ?_,
    fun z hzA hzB ↦ ?_⟩
  · refine continuous_subtypeVal.continuousAt.preimage_mem_nhds
      (hKc.isClosed.isOpen_compl.mem_nhds ?_)
    rintro ⟨p, hp, hpx⟩
    exact hx (hpx ▸ Ψ.toOpenPartialHomeomorph.map_target (hK hp))
  · refine continuous_subtypeVal.continuousAt.preimage_mem_nhds
      ((isOpen_lt (complexToRealEuclidean (Fin (n + 1))).continuous.norm
        continuous_const).mem_nhds ?_)
    refine hw.trans_lt ?_
    rw [Real.lt_sqrt (by linarith [norm_nonneg (complexToRealEuclidean (Fin (n + 1))
      (w : Fin (n + 1) → ℂ))])]
    nlinarith
  · have hz : Ψ z.val.val ∈ openNbhd n (ε / 2) := by
      have := hzB
      rw [mem_preimage, Diffeomorph.coe_toHomeomorph, coe_gluingDiffeomorph_apply,
        coe_shellSymplectomorph_apply, ← coe_radialBlowdownDiffeomorph_apply] at this
      exact (mem_openNbhd_iff_radialBlowdownDiffeomorph l hδ.le _).2 this
    refine hzA ⟨Ψ z.val.val, openNbhd_subset_closedNbhd _ hz, ?_⟩
    exact Ψ.toOpenPartialHomeomorph.left_inv ((mem_outerOverlap_iff hf).1 z.property)

end DivisorBlowdown

end SymplecticGeometry

end
