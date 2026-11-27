/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Gluing.Pair
public import SymplecticGeometry.Geometry.Symplectic.Blowup.Model
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
public import SymplecticGeometry.Geometry.Symplectic.IsotopyExtension.Ball.Basic
public import SymplecticGeometry.Geometry.Symplectic.Blowup.Weight.Basic
public import SymplecticGeometry.Geometry.Symplectic.Blowup.DivisorNeighborhood
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import SymplecticGeometry.Analysis.Real.Sqrt
import SymplecticGeometry.Geometry.Symplectic.IsotopyExtension.Ball.Comp
import SymplecticGeometry.Geometry.Symplectic.Manifold.SymplecticMap
import TauCeti.Geometry.Manifold.DifferentialForm.Opens.PartialDiffeomorph
import TauCeti.Geometry.Symplectic.Manifold.NeighborhoodGerm
import TauCeti.Geometry.Symplectic.Manifold.Opens

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

The topology and the smooth structure do not use any form. Given a two-form `σ` on `M` such that
`Ψ` pulls `ω̃_l = BlowupModel.blowupForm n l` back to `σ` on its source, the form of the blowdown
is `σ` on `M ∖ Z` and the standard form `ω₀` on the ball. They agree on the overlap, since `Ψ`
carries `σ` to `ω̃_l` and `shellSymplectomorph` carries `ω̃_l` to `ω₀`, so they glue by
`GluedAlong.gluedForm`; the result is symplectic when `σ` is. The inclusion of the ball, read on
`StdSpace`, is a symplectic embedding of every closed ball of radius less than `√(l² + ε²)`, and
the complement of the image of the closed ball of radius `l` is the image of `inl`, so it is
symplectomorphic to `M ∖ Z`.

## Main definitions

* `SymplecticGeometry.DivisorBlowdown.outerPiece hf`: the open subset `M ∖ Z` of `M`.
* `SymplecticGeometry.DivisorBlowdown.ballPiece n l ε`: the open ball `|w| < √(l² + ε²)` of `E`.
* `SymplecticGeometry.DivisorBlowdown.sourceComplRange hf`: the open subset `Ψ.source ∖ Z` of
  `M`, and `SymplecticGeometry.DivisorBlowdown.sourceComplRangeDiffeomorph hΨ hf`, the
  diffeomorphism `Ψ` from it onto `openNbhdComplDivisor n ε`.
* `SymplecticGeometry.DivisorBlowdown.gluingDiffeomorph hΨ hf hl hε`: the diffeomorphism
  `x ↦ F_l(π (Ψ x))` from `Ψ.source ∖ Z`, as an open subset of the outer piece, onto the open
  shell, as an open subset of the ball piece.
* `SymplecticGeometry.DivisorBlowdown hΨ hf hl hε`: the blowdown, the space
  `SymplecticGeometry.GluedAlong` of `Geometry/Manifold/Gluing/Pair.lean` glued from the two
  pieces along `gluingDiffeomorph`.
* `SymplecticGeometry.DivisorBlowdown.blowdownForm hΨ hf hl hε hσ`: the form of the blowdown,
  glued from `σ` and `ω₀`.
* `SymplecticGeometry.DivisorBlowdown.toBallPiece n l hε`: the map from `StdSpace (Fin (n + 1))`
  to the ball piece that inverts `complexToRealEuclidean` on the open ball of radius
  `√(l² + ε²)`.
* `SymplecticGeometry.DivisorBlowdown.blowdownBall hΨ hf hl hε`: the ball embedding
  `StdSpace (Fin (n + 1)) → DivisorBlowdown hΨ hf hl hε`, the inverse of
  `complexToRealEuclidean` followed by `inr` on the open ball of radius `√(l² + ε²)`.
* `SymplecticGeometry.DivisorBlowdown.complBall hΨ hf hl hε`: the complement of the image of
  the closed ball of radius `l` under `blowdownBall`, the range of `inl`, and
  `SymplecticGeometry.DivisorBlowdown.complBallSymplectomorph hΨ hf hl hε`, its diffeomorphism
  onto `M ∖ Z`, the inverse of `inl`.
* `SymplecticGeometry.DivisorBlowdown.weightBlowupBlowdownDiffeomorph hΨ hf hl hε hσ hδ hδε`: for
  `0 < δ < ε`, the diffeomorphism onto `M` of the blowup `WeightBlowup` of weight `l` and
  constant `δ` of the blowdown along `blowdownBall`, glued by `GluedAlong.descDiffeomorph` from
  the inverse of `inl` on `complBall` and the inverse of `Ψ` on `L(δ)`.

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
* `SymplecticGeometry.DivisorBlowdown.isSymplectomorphism_gluingDiffeomorph`: the gluing map
  pulls `ω₀` back to `σ`, by `isSymplectomorphism_sourceComplRangeDiffeomorph` and
  `BlowupModel.isSymplectomorphism_shellSymplectomorph`.
* `SymplecticGeometry.DivisorBlowdown.mpullback_inl_blowdownForm`, `mpullback_inr_blowdownForm`,
  `eq_blowdownForm_iff`: the form of the blowdown is the form that pulls back to `σ` by `inl`
  and to `ω₀` by `inr`.
* `SymplecticGeometry.DivisorBlowdown.isSymplectic_blowdownForm`: for symplectic `σ`, the
  form of the blowdown is symplectic.
* `SymplecticGeometry.DivisorBlowdown.isSymplecticBallEmbedding_blowdownBall`: `blowdownBall`
  is a symplectic embedding of the closed ball of every radius `r < √(l² + ε²)`, and so of
  radius `l` (`isSymplecticBallEmbedding_blowdownBall_weight`). It is `inr ∘ toBallPiece`, and
  `toBallPiece` is one into the ball piece (`isSymplecticBallEmbedding_toBallPiece`), by
  `TauCeti.SymplecticForm.IsSymplectomorphism.isSymplecticBallEmbedding` for the inverse of
  `complexToRealEuclidean` and `IsSymplecticBallEmbedding.subtype_of_eqOn`.
* `SymplecticGeometry.DivisorBlowdown.mem_complBall_iff`,
  `isSymplectomorphism_complBallSymplectomorph`: the complement of the image of the closed ball
  of radius `l` with the form of the blowdown is symplectomorphic to `M ∖ Z` with `σ`.
* `SymplecticGeometry.DivisorBlowdown.weightBlowup_blowdown`: blowing up the blowdown along
  `blowdownBall` with weight `l` gives `(M, σ)` back, by a symplectomorphism that sends the
  divisor to `f`. The constant `δ` of that blowup is below `ε`, as `blowdownBall` embeds
  symplectically only the closed balls of radius less than `√(l² + ε²)`.
* `SymplecticGeometry.DivisorBlowdown.blowdown_weightBlowup`: blowing down the divisor of the
  blowup of weight `l` along `ψ`, with `WeightBlowup.modelChart` as `Ψ`, gives `(M, σ)` back, by a
  symplectomorphism that is `WeightBlowup.complDivisorSymplectomorph` on the outer piece and
  sends `blowdownBall` to `ψ` on the open ball of radius `√(l² + ε²)`. The two pieces are sent
  onto `M ∖ ψ(B(l))` and onto the image under `ψ` of that open ball, which cover `M`, and they
  agree on the overlap, where both are `ψ ∘ shellSymplectomorph`; so the criterion
  `GluedAlong.descDiffeomorph` applies, and `GluedAlong.mpullback_descDiffeomorph` gives the
  statement on forms.
* `SymplecticGeometry.exists_blowdown`: for a symplectic divisor `f` of `(M, σ)` with
  `f^* σ = l² ω_FS`, `l > 0`, and normal bundle isomorphic to that of the zero section of the
  model, the `ε` and `Ψ` of `BlowupModel.exists_symplectomorphism_blowupModel` exist, and the
  blowdown along them has the properties above: its form is symplectic, `blowdownBall` embeds the
  closed ball of radius `l` with complement symplectomorphic to `M ∖ Z`, and
  `weightBlowup_blowdown` and `blowdown_weightBlowup` hold.

The construction follows that of `SymplecticGeometry.WeightBlowup` in
`Blowup/Weight/Basic.lean`, with the roles of the model and of the ball exchanged; its proof of
`T2Space` is adapted from `SymplecticGeometry.WeightBlowup.instT2Space` and its form from
`SymplecticGeometry.WeightBlowup.form`. The diffeomorphism of the complement of the ball is the
inverse of `inl` onto its range, `SymplecticGeometry.GluedAlong.rangeInlDiffeomorph`.

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

/-- The inverse of `Ψ` sends the zero section of the model to `f`. -/
theorem symm_zeroSection (hf : ∀ q, f q ∈ Ψ.source ∧ Ψ (f q) = zeroSection q)
    (q : ℙ ℂ (Fin (n + 1) → ℂ)) : Ψ.symm (zeroSection q) = f q := by
  rw [← (hf q).2, PartialDiffeomorph.symm_toPartialEquiv]
  exact Ψ.left_inv (hf q).1

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

/-- `Ψ` maps a point of its source off the image of `f` into `openNbhdComplDivisor n ε`. -/
theorem apply_mem_openNbhdComplDivisor (hΨ : Ψ.target = openNbhd n ε)
    (hf : ∀ q, f q ∈ Ψ.source ∧ Ψ (f q) = zeroSection q) {x : M}
    (hx : x ∈ sourceComplRange hf) : Ψ x ∈ openNbhdComplDivisor n ε := by
  rw [mem_sourceComplRange_iff] at hx
  exact mem_openNbhdComplDivisor_iff.2 ⟨hΨ ▸ Ψ.toOpenPartialHomeomorph.map_source hx.1,
    (apply_mem_exceptionalDivisor_iff hf hx.1).not.2 hx.2⟩

/-- **`Ψ` off the divisor**: the restriction of `Ψ` to a diffeomorphism from `Ψ.source ∖ Z` onto
`openNbhdComplDivisor n ε`. -/
def sourceComplRangeDiffeomorph (hΨ : Ψ.target = openNbhd n ε)
    (hf : ∀ q, f q ∈ Ψ.source ∧ Ψ (f q) = zeroSection q) :
    sourceComplRange hf ≃ₘ⟮𝓘(ℝ, Fin (n + 1) → ℂ), 𝓘(ℝ, Fin (n + 1) → ℂ)⟯
      openNbhdComplDivisor n ε :=
  Ψ.toDiffeomorphSourceTarget.restrOpens (U := sourceComplRange hf) (fun _ hx ↦ hx.1)
    (fun _ hp ↦ by
      rw [Opens.mem_mk, hΨ]
      exact (mem_openNbhdComplDivisor_iff.1 hp).1)
    fun x ↦ by
      rw [PartialDiffeomorph.toDiffeomorphSourceTarget_apply_coe]
      refine ⟨fun hx ↦ apply_mem_openNbhdComplDivisor hΨ hf hx, fun hx ↦ ⟨x.property, ?_⟩⟩
      exact (apply_mem_exceptionalDivisor_iff hf x.property).not.1
        (mem_openNbhdComplDivisor_iff.1 hx).2

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
  rw [GluedAlong.inl_eq_inr_diffeomorph_iff]
  refine ⟨fun ⟨h, hw⟩ ↦ ⟨(mem_outerOverlap_iff hf).1 h, ?_⟩,
    fun ⟨h, hw⟩ ↦ ⟨(mem_outerOverlap_iff hf).2 h, Subtype.ext ?_⟩⟩
  · rw [← hw, coe_gluingDiffeomorph_apply]
  · rw [hw, coe_gluingDiffeomorph_apply]

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
    hΨ ▸ closedNbhd_subset_openNbhd (half_lt_self hε)
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
      rwa [mem_preimage, Diffeomorph.coe_toHomeomorph, coe_gluingDiffeomorph_apply,
        mem_ofPred_eq, norm_shellSymplectomorph_lt_iff hl hε.le hδ.le] at this
    refine hzA ⟨Ψ z.val.val, openNbhd_subset_closedNbhd _ hz, ?_⟩
    exact Ψ.toOpenPartialHomeomorph.left_inv ((mem_outerOverlap_iff hf).1 z.property)

/-! ### The ball of the blowdown -/

include hε in
/-- The ball piece contains `0`. -/
theorem zero_mem_ballPiece : (0 : Fin (n + 1) → ℂ) ∈ ballPiece n l ε := by
  rw [mem_ballPiece_iff, map_zero, norm_zero]
  exact Real.sqrt_pos.2 (by positivity)

variable (n l) in
/-- The ball piece read on `StdSpace (Fin (n + 1))`: on the open ball of radius `√(l² + ε²)`,
the point of the ball piece that `complexToRealEuclidean` sends to `w`. Off that ball it takes
the value `0`, which plays no role. -/
def toBallPiece : StdSpace (Fin (n + 1)) → ballPiece n l ε := fun w ↦
  if h : ‖w‖ < √(l ^ 2 + ε ^ 2) then
    ⟨(complexToRealEuclidean (Fin (n + 1))).symm w, by simpa using h⟩
  else ⟨0, zero_mem_ballPiece hε⟩

variable (n l) in
theorem toBallPiece_def (w : StdSpace (Fin (n + 1))) :
    toBallPiece n l hε w =
      if h : ‖w‖ < √(l ^ 2 + ε ^ 2) then
        ⟨(complexToRealEuclidean (Fin (n + 1))).symm w, by simpa using h⟩
      else ⟨0, zero_mem_ballPiece hε⟩ :=
  (rfl)

/-- On the open ball of radius `√(l² + ε²)`, `toBallPiece` is the inverse of
`complexToRealEuclidean`. -/
theorem coe_toBallPiece_of_norm_lt {w : StdSpace (Fin (n + 1))} (hw : ‖w‖ < √(l ^ 2 + ε ^ 2)) :
    (toBallPiece n l hε w : Fin (n + 1) → ℂ) = (complexToRealEuclidean (Fin (n + 1))).symm w := by
  simp only [toBallPiece_def, hw, ↓reduceDIte]

/-- `toBallPiece` sends the point of `StdSpace` corresponding to a point `w` of the ball piece
to `w`. -/
@[simp]
theorem toBallPiece_complexToRealEuclidean (w : ballPiece n l ε) :
    toBallPiece n l hε (complexToRealEuclidean (Fin (n + 1)) w) = w :=
  Subtype.ext <| by
    rw [coe_toBallPiece_of_norm_lt hε ((mem_ballPiece_iff).1 w.property)]
    simp

/-- **The ball embedding of the blowdown**: the ball piece read on `StdSpace (Fin (n + 1))` by
`toBallPiece`, followed by `GluedAlong.inr`. -/
def blowdownBall : StdSpace (Fin (n + 1)) → DivisorBlowdown hΨ hf hl hε :=
  GluedAlong.inr (gluingDiffeomorph hΨ hf hl hε).toHomeomorph ∘ toBallPiece n l hε

theorem blowdownBall_def :
    blowdownBall hΨ hf hl hε =
      GluedAlong.inr (gluingDiffeomorph hΨ hf hl hε).toHomeomorph ∘ toBallPiece n l hε :=
  (rfl)

/-- On the open ball of radius `√(l² + ε²)`, `blowdownBall` is `inr` of the point of `E` that
`complexToRealEuclidean` sends to `w`. -/
theorem blowdownBall_of_norm_lt {w : StdSpace (Fin (n + 1))} (hw : ‖w‖ < √(l ^ 2 + ε ^ 2)) :
    blowdownBall hΨ hf hl hε w =
      GluedAlong.inr (gluingDiffeomorph hΨ hf hl hε).toHomeomorph
        ⟨(complexToRealEuclidean (Fin (n + 1))).symm w, by simpa using hw⟩ := by
  rw [blowdownBall_def, Function.comp_apply]
  exact congrArg _ (Subtype.ext (coe_toBallPiece_of_norm_lt hε hw))

/-- `blowdownBall` sends the point of `StdSpace` corresponding to a point `w` of the ball piece
to `inr w`. -/
@[simp]
theorem blowdownBall_complexToRealEuclidean (w : ballPiece n l ε) :
    blowdownBall hΨ hf hl hε (complexToRealEuclidean (Fin (n + 1)) w) =
      GluedAlong.inr (gluingDiffeomorph hΨ hf hl hε).toHomeomorph w := by
  rw [blowdownBall_def, Function.comp_apply, toBallPiece_complexToRealEuclidean]

/-- A point `x` of the overlap `Ψ.source ∖ Z`, seen in the blowdown through `inl`, is the image
under `blowdownBall` of the point of `StdSpace` corresponding to its image under the gluing map. -/
theorem inl_eq_blowdownBall_gluingDiffeomorph (x : outerOverlap hf) :
    GluedAlong.inl (gluingDiffeomorph hΨ hf hl hε).toHomeomorph (x : outerPiece hf) =
      blowdownBall hΨ hf hl hε (complexToRealEuclidean (Fin (n + 1))
        (gluingDiffeomorph hΨ hf hl hε x : ballPiece n l ε)) := by
  rw [blowdownBall_complexToRealEuclidean, ← GluedAlong.inr_apply, Diffeomorph.coe_toHomeomorph]

/-- The image under `blowdownBall` of the closed ball of radius `l` consists of the points `inr w`
with `|w| ≤ l`. -/
theorem mem_image_blowdownBall_closedBall_iff {z : DivisorBlowdown hΨ hf hl hε} :
    z ∈ blowdownBall hΨ hf hl hε '' closedBall 0 l ↔
      ∃ w : ballPiece n l ε, ‖complexToRealEuclidean (Fin (n + 1)) (w : Fin (n + 1) → ℂ)‖ ≤ l ∧
        GluedAlong.inr (gluingDiffeomorph hΨ hf hl hε).toHomeomorph w = z := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    rw [mem_closedBall_zero_iff] at hv
    have hv' := hv.trans_lt (Real.lt_sqrt_sq_add_sq l hε.ne')
    exact ⟨⟨(complexToRealEuclidean (Fin (n + 1))).symm v, by simpa using hv'⟩,
      by simpa using hv, (blowdownBall_of_norm_lt hΨ hf hl hε hv').symm⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨_, mem_closedBall_zero_iff.2 hw, blowdownBall_complexToRealEuclidean hΨ hf hl hε w⟩

section Form

open scoped TauCeti.ComplexManifold

-- As in `Blowup/Weight/Basic.lean`: with the scope `TauCeti.ComplexManifold` open, the search for
-- the `C^1` structure of an open subset of an open subset, which the pull-backs of forms below
-- need, also tries complex structures and times out. Deriving it from the smooth structure first
-- avoids this.
attribute [local instance high] IsManifold.instOfNatWithTopENat_1

variable [IsManifold 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ M] {σ : SmoothTwoForm 𝓘(ℝ, Fin (n + 1) → ℂ) M}
  (hσ : σ.IsSymplecticMapOn (blowupForm n l) Ψ Ψ.source)

/-! ### The form of the blowdown -/

include hσ in
/-- `sourceComplRangeDiffeomorph hΨ hf` pulls the restriction of `ω̃_l` to
`openNbhdComplDivisor n ε` back to the restriction of `σ` to `Ψ.source ∖ Z`, when `Ψ` pulls
`ω̃_l` back to `σ` on its source. -/
theorem isSymplectomorphism_sourceComplRangeDiffeomorph :
    SmoothTwoForm.IsSymplectomorphism
      (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ)
      (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (blowupForm n l))
      (sourceComplRangeDiffeomorph hΨ hf) := by
  rw [sourceComplRangeDiffeomorph]
  exact hσ.isSymplectomorphism_toDiffeomorphSourceTarget.restrOpens _ _ _

include hσ in
/-- **The gluing map is a symplectomorphism**: `gluingDiffeomorph` pulls the restriction of `ω₀`
to the open shell back to the restriction of `σ` to `Ψ.source ∖ Z`, both read on the overlaps in
the ball and the outer piece. -/
theorem isSymplectomorphism_gluingDiffeomorph :
    SmoothTwoForm.IsSymplectomorphism
      (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal
        (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ))
      (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal
        (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (ω₀E n)))
      (gluingDiffeomorph hΨ hf hl hε) := by
  rw [gluingDiffeomorph]
  exact (SmoothTwoForm.isSymplectomorphism_nestedOpen σ _).trans
    ((isSymplectomorphism_sourceComplRangeDiffeomorph hΨ hf hσ).trans
      ((isSymplectomorphism_shellSymplectomorph hl hε.le).trans
        ((SmoothTwoForm.isSymplectomorphism_nestedOpen (ω₀E n) _).symm (by simp)) (by simp))
      (by simp)) (by simp)

include hσ in
/-- The gluing map pulls the restriction of `ω₀` back to that of `σ`: the condition under which
the two forms glue. -/
theorem mpullback_gluingDiffeomorph :
    SmoothForm.mpullback (gluingDiffeomorph hΨ hf hl hε) (gluingDiffeomorph hΨ hf hl hε).contMDiff
        (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal
          (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (ω₀E n))) =
      SmoothForm.mpullback Subtype.val contMDiff_subtypeVal
        (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ) :=
  SmoothTwoForm.isSymplectomorphism_iff_mpullback_eq.1
    (isSymplectomorphism_gluingDiffeomorph hΨ hf hl hε hσ)

/-- **The form of the blowdown**, following McDuff–Salamon, §7.1: the two-form that is `σ` on the
outer piece `M ∖ Z` and the standard form `ω₀` on the ball piece `|w| < √(l² + ε²)`, which agree
on the overlap (`mpullback_gluingDiffeomorph`). -/
def blowdownForm : SmoothTwoForm 𝓘(ℝ, Fin (n + 1) → ℂ) (DivisorBlowdown hΨ hf hl hε) :=
  GluedAlong.gluedForm _ (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ)
    (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (ω₀E n))
    (mpullback_gluingDiffeomorph hΨ hf hl hε hσ)

theorem blowdownForm_def :
    blowdownForm hΨ hf hl hε hσ =
      GluedAlong.gluedForm _ (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ)
        (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (ω₀E n))
        (mpullback_gluingDiffeomorph hΨ hf hl hε hσ) :=
  (rfl)

/-- The form of the blowdown pulls back by `inl` to the restriction of `σ` to `M ∖ Z`. -/
@[simp]
theorem mpullback_inl_blowdownForm :
    SmoothForm.mpullback (GluedAlong.inl (gluingDiffeomorph hΨ hf hl hε).toHomeomorph)
        (GluedAlong.isLocalDiffeomorph_inl _).contMDiff (blowdownForm hΨ hf hl hε hσ) =
      SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ :=
  GluedAlong.mpullback_inl_gluedForm

/-- The form of the blowdown pulls back by `inr` to the restriction of `ω₀` to the ball piece. -/
@[simp]
theorem mpullback_inr_blowdownForm :
    SmoothForm.mpullback (GluedAlong.inr (gluingDiffeomorph hΨ hf hl hε).toHomeomorph)
        (GluedAlong.isLocalDiffeomorph_inr _).contMDiff (blowdownForm hΨ hf hl hε hσ) =
      SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (ω₀E n) :=
  GluedAlong.mpullback_inr_gluedForm

/-- A two-form on the blowdown is `blowdownForm hΨ hf hl hε hσ` exactly when it pulls back by
`inl` to the restriction of `σ` and by `inr` to the restriction of `ω₀`. -/
theorem eq_blowdownForm_iff
    {α : SmoothTwoForm 𝓘(ℝ, Fin (n + 1) → ℂ) (DivisorBlowdown hΨ hf hl hε)} :
    α = blowdownForm hΨ hf hl hε hσ ↔
      SmoothForm.mpullback (GluedAlong.inl (gluingDiffeomorph hΨ hf hl hε).toHomeomorph)
          (GluedAlong.isLocalDiffeomorph_inl _).contMDiff α =
        SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ ∧
      SmoothForm.mpullback (GluedAlong.inr (gluingDiffeomorph hΨ hf hl hε).toHomeomorph)
          (GluedAlong.isLocalDiffeomorph_inr _).contMDiff α =
        SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (ω₀E n) :=
  GluedAlong.eq_gluedForm_iff

/-- **The blowdown is symplectic**: for symplectic `σ`, the form of the blowdown is
symplectic. -/
theorem isSymplectic_blowdownForm (hσs : σ.IsSymplectic) :
    (blowdownForm hΨ hf hl hε hσ).IsSymplectic :=
  GluedAlong.isSymplectic_gluedForm_iff.2
    ⟨hσs.mpullback_subtype_val _,
      (ω₀E_def n ▸ SymplecticForm.isSymplectic_constSmooth _).mpullback_subtype_val _⟩

/-! ### The ball embedding -/

/-- `toBallPiece` is a symplectic embedding of the closed ball of every radius `r < √(l² + ε²)`
into the ball piece with the restriction of `ω₀`. -/
theorem isSymplecticBallEmbedding_toBallPiece {r : ℝ} (hr : r < √(l ^ 2 + ε ^ 2)) :
    IsSymplecticBallEmbedding (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (ω₀E n)) r
      (toBallPiece n l hε) := by
  rw [ω₀E_def]
  exact ((isSymplectomorphism_complexToRealEuclidean (Fin (n + 1))).symm.isSymplecticBallEmbedding
    r).subtype_of_eqOn isOpen_ball
    (closedBall_subset_ball hr) fun w hw ↦ coe_toBallPiece_of_norm_lt hε (mem_ball_zero_iff.1 hw)

/-- **The ball embedding of the blowdown is symplectic**: `blowdownBall` is a symplectic
embedding of the closed ball of every radius `r < √(l² + ε²)`, in particular of radius `l`
(`isSymplecticBallEmbedding_blowdownBall_weight`). -/
theorem isSymplecticBallEmbedding_blowdownBall {r : ℝ} (hr : r < √(l ^ 2 + ε ^ 2)) :
    IsSymplecticBallEmbedding (blowdownForm hΨ hf hl hε hσ) r (blowdownBall hΨ hf hl hε) := by
  rw [blowdownBall_def]
  exact (isSymplecticBallEmbedding_toBallPiece hε hr).comp
    (GluedAlong.isLocalDiffeomorph_inr (gluingDiffeomorph hΨ hf hl hε)).contMDiff
    (GluedAlong.inr_injective _)
    (by rw [← SmoothForm.coe_mpullback _
      (GluedAlong.isLocalDiffeomorph_inr (gluingDiffeomorph hΨ hf hl hε)).contMDiff,
      mpullback_inr_blowdownForm])

/-- `blowdownBall` is a symplectic embedding of the closed ball of radius `l`. -/
theorem isSymplecticBallEmbedding_blowdownBall_weight :
    IsSymplecticBallEmbedding (blowdownForm hΨ hf hl hε hσ) l (blowdownBall hΨ hf hl hε) :=
  isSymplecticBallEmbedding_blowdownBall hΨ hf hl hε hσ
    (Real.lt_sqrt_sq_add_sq l hε.ne')

/-! ### The complement of the ball -/

/-- The complement in the blowdown of the image under `blowdownBall` of the closed ball of radius
`l` (`mem_complBall_iff`): the image of the outer piece under `inl`, an open set. -/
def complBall : Opens (DivisorBlowdown hΨ hf hl hε) :=
  GluedAlong.rangeInl (gluingDiffeomorph hΨ hf hl hε).toHomeomorph

omit [IsManifold 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ M] in
@[simp]
theorem coe_complBall :
    (complBall hΨ hf hl hε : Set (DivisorBlowdown hΨ hf hl hε)) =
      range (GluedAlong.inl (gluingDiffeomorph hΨ hf hl hε).toHomeomorph) :=
  GluedAlong.coe_rangeInl _

omit [IsManifold 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ M] in
/-- Every point `inl x` of the blowdown lies in `complBall`. -/
@[simp]
theorem inl_mem_complBall (x : outerPiece hf) :
    GluedAlong.inl (gluingDiffeomorph hΨ hf hl hε).toHomeomorph x ∈ complBall hΨ hf hl hε :=
  GluedAlong.inl_mem_rangeInl _ x

omit [IsManifold 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ M] in
/-- A point of the blowdown lies in `complBall` exactly when it is not the image under
`blowdownBall` of a point of the closed ball of radius `l`. -/
theorem mem_complBall_iff {z : DivisorBlowdown hΨ hf hl hε} :
    z ∈ complBall hΨ hf hl hε ↔ z ∉ blowdownBall hΨ hf hl hε '' closedBall 0 l := by
  rw [← SetLike.mem_coe, coe_complBall, GluedAlong.range_inl_eq_compl_image_inr, mem_compl_iff,
    mem_image_blowdownBall_closedBall_iff]
  simp only [mem_image, mem_compl_iff, SetLike.mem_coe, mem_ballOverlap_iff, not_lt]

/-- **The complement of the ball**: the diffeomorphism from the complement in the blowdown of the
image of the closed ball of radius `l` under `blowdownBall` onto `M ∖ Z`, the inverse of `inl`.
It pulls `σ` back to the form of the blowdown
(`isSymplectomorphism_complBallSymplectomorph`). -/
def complBallSymplectomorph :
    complBall hΨ hf hl hε ≃ₘ⟮𝓘(ℝ, Fin (n + 1) → ℂ), 𝓘(ℝ, Fin (n + 1) → ℂ)⟯ outerPiece hf :=
  GluedAlong.rangeInlDiffeomorph (GluedAlong.isCompatible_glueData _)

/-- The inverse of `complBallSymplectomorph` is `inl`. -/
@[simp]
theorem coe_complBallSymplectomorph_symm_apply (x : outerPiece hf) :
    ((complBallSymplectomorph hΨ hf hl hε).symm x : DivisorBlowdown hΨ hf hl hε) =
      GluedAlong.inl (gluingDiffeomorph hΨ hf hl hε).toHomeomorph x :=
  GluedAlong.coe_rangeInlDiffeomorph_symm_apply _ x

/-- `inl` undoes `complBallSymplectomorph`. -/
@[simp]
theorem inl_complBallSymplectomorph_apply (z : complBall hΨ hf hl hε) :
    GluedAlong.inl (gluingDiffeomorph hΨ hf hl hε).toHomeomorph
        (complBallSymplectomorph hΨ hf hl hε z) = z :=
  GluedAlong.inl_rangeInlDiffeomorph_apply _ z

/-- `complBallSymplectomorph` sends the point `inl x` to `x`. -/
@[simp]
theorem complBallSymplectomorph_inl (x : outerPiece hf) :
    complBallSymplectomorph hΨ hf hl hε
        ⟨GluedAlong.inl (gluingDiffeomorph hΨ hf hl hε).toHomeomorph x,
          inl_mem_complBall hΨ hf hl hε x⟩ = x :=
  GluedAlong.rangeInlDiffeomorph_mk_inl _ x

/-- **The complement of the ball is symplectomorphic to `M ∖ Z`**: `complBallSymplectomorph`
pulls the restriction of `σ` to `M ∖ Z` back to the restriction of the form of the blowdown to
the complement of the image of the closed ball of radius `l` under `blowdownBall`. -/
theorem isSymplectomorphism_complBallSymplectomorph :
    SmoothTwoForm.IsSymplectomorphism
      (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (blowdownForm hΨ hf hl hε hσ))
      (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ)
      (complBallSymplectomorph hΨ hf hl hε) := by
  rw [← SmoothTwoForm.isSymplectomorphism_symm_iff (by simp),
    SmoothTwoForm.isSymplectomorphism_iff_mpullback_eq, ← mpullback_inl_blowdownForm]
  exact GluedAlong.mpullback_rangeInlDiffeomorph_symm _ _

/-! ### Blowing up the blowdown -/

variable {δ : ℝ}

/-- `blowdownBall` is a symplectic embedding of the closed ball of radius `√(l² + δ²)`, for
`0 ≤ δ < ε`: the ball embedding along which the blowdown is blown up again with weight `l` and
the constant `δ`. -/
theorem isSymplecticBallEmbedding_blowdownBall_sqrt (hδ : 0 ≤ δ) (hδε : δ < ε) :
    IsSymplecticBallEmbedding (blowdownForm hΨ hf hl hε hσ) √(l ^ 2 + δ ^ 2)
      (blowdownBall hΨ hf hl hε) :=
  isSymplecticBallEmbedding_blowdownBall hΨ hf hl hε hσ
    (Real.sqrt_lt_sqrt (by positivity) (by nlinarith))

variable (hδ : 0 < δ) (hδε : δ < ε)

/-- The outer piece of the blowup of the blowdown along `blowdownBall` is `complBall`. -/
theorem mem_outerPiece_weightBlowup_iff {z : DivisorBlowdown hΨ hf hl hε} :
    z ∈ WeightBlowup.outerPiece
        (isSymplecticBallEmbedding_blowdownBall_sqrt hΨ hf hl hε hσ hδ.le hδε) ↔
      z ∈ complBall hΨ hf hl hε := by
  rw [WeightBlowup.mem_outerPiece_iff, mem_complBall_iff]

/-- The outer piece of the blowup of the blowdown along `blowdownBall` is `complBall`. -/
theorem outerPiece_weightBlowup_eq :
    WeightBlowup.outerPiece (isSymplecticBallEmbedding_blowdownBall_sqrt hΨ hf hl hε hσ hδ.le hδε) =
      complBall hΨ hf hl hε :=
  Opens.ext (Set.ext fun _ ↦ mem_outerPiece_weightBlowup_iff hΨ hf hl hε hσ hδ hδε)

/-- The map from the outer piece of the blowup of the blowdown to `M`: the inverse of `inl`, read
in `M ∖ Z ⊆ M`. -/
private def outerMap :
    WeightBlowup.outerPiece (isSymplecticBallEmbedding_blowdownBall_sqrt hΨ hf hl hε hσ hδ.le hδε) →
      M :=
  Subtype.val ∘ complBallSymplectomorph hΨ hf hl hε ∘
    Opens.inclusion (outerPiece_weightBlowup_eq hΨ hf hl hε hσ hδ hδε).le

private theorem outerMap_def :
    outerMap hΨ hf hl hε hσ hδ hδε =
      Subtype.val ∘ complBallSymplectomorph hΨ hf hl hε ∘
        Opens.inclusion (outerPiece_weightBlowup_eq hΨ hf hl hε hσ hδ hδε).le :=
  (rfl)

variable (Ψ) in
/-- The map from the model piece of the blowup of the blowdown to `M`: the inverse of `Ψ`. -/
private def modelMap : openNbhdOpens n δ → M := fun p ↦ Ψ.symm p.val

omit [T2Space M] [IsManifold 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ M] in
private theorem modelMap_apply (p : openNbhdOpens n δ) : modelMap Ψ p = Ψ.symm p.val :=
  (rfl)

omit [T2Space M] [IsManifold 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ M] in
include hΨ hδε in
private theorem coe_mem_target (p : openNbhdOpens n δ) :
    (p : BlowupModel n) ∈ Ψ.target :=
  hΨ ▸ openNbhd_mono hδε.le (mem_openNbhdOpens_iff.1 p.property)

omit [T2Space M] [IsManifold 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ M] in
include hΨ hδε in
private theorem modelMap_mem_source (p : openNbhdOpens n δ) :
    modelMap Ψ p ∈ Ψ.source := by
  rw [modelMap_apply, PartialDiffeomorph.symm_toPartialEquiv]
  exact Ψ.map_target (coe_mem_target hΨ hδε p)

omit [T2Space M] [IsManifold 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ M] in
include hΨ hδε in
private theorem apply_modelMap (p : openNbhdOpens n δ) :
    Ψ (modelMap Ψ p) = p := by
  rw [modelMap_apply, PartialDiffeomorph.symm_toPartialEquiv]
  exact Ψ.right_inv (coe_mem_target hΨ hδε p)

private theorem isLocalDiffeomorph_outerMap :
    IsLocalDiffeomorph 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) ∞
      (outerMap hΨ hf hl hε hσ hδ hδε) := fun z ↦
  ((isLocalDiffeomorph_inclusion _ z).comp
    (hg := (complBallSymplectomorph hΨ hf hl hε).isLocalDiffeomorph _)).comp
    (hg := isLocalDiffeomorph_subtype_val _)

/-- `outerMap` sends a point that is `inl x` in the blowdown to `x`. -/
private theorem outerMap_apply_of_eq
    {z : WeightBlowup.outerPiece
      (isSymplecticBallEmbedding_blowdownBall_sqrt hΨ hf hl hε hσ hδ.le hδε)}
    {x : outerPiece hf} (h : (z : DivisorBlowdown hΨ hf hl hε) =
      GluedAlong.inl (gluingDiffeomorph hΨ hf hl hε).toHomeomorph x) :
    outerMap hΨ hf hl hε hσ hδ hδε z = x := by
  have hz : Opens.inclusion (outerPiece_weightBlowup_eq hΨ hf hl hε hσ hδ hδε).le z =
      ⟨_, inl_mem_complBall hΨ hf hl hε x⟩ :=
    Subtype.ext ((Set.coe_inclusion _ z).trans h)
  rw [outerMap_def, Function.comp_apply, Function.comp_apply, hz, complBallSymplectomorph_inl]

/-- The two maps to `M` agree on the overlap: a point `p` of `L(δ) ∖ Z` and its image under the
gluing map of the blowup are both sent to `Ψ⁻¹ p`. -/
private theorem outerMap_gluingDiffeomorph (p : WeightBlowup.modelOverlap n δ) :
    outerMap hΨ hf hl hε hσ hδ hδε (WeightBlowup.gluingDiffeomorph
      (isSymplecticBallEmbedding_blowdownBall_sqrt hΨ hf hl hε hσ hδ.le hδε) hl hδ p) =
      modelMap Ψ p.val := by
  have hms := modelMap_mem_source hΨ hδε p.val
  have hΨm := apply_modelMap hΨ hδε p.val
  have hm : modelMap Ψ p.val ∈ sourceComplRange hf := by
    refine (mem_sourceComplRange_iff hf).2 ⟨hms, ?_⟩
    rw [← apply_mem_exceptionalDivisor_iff hf hms, hΨm]
    exact WeightBlowup.mem_modelOverlap_iff.1 p.property
  refine outerMap_apply_of_eq hΨ hf hl hε hσ hδ hδε (x := ⟨_, hm.2⟩) ((?_ : _ = _).trans
    (inl_eq_blowdownBall_gluingDiffeomorph hΨ hf hl hε
      ⟨⟨_, hm.2⟩, (mem_outerOverlap_iff hf).2 hms⟩).symm)
  rw [WeightBlowup.coe_gluingDiffeomorph_apply]
  congr 2
  rw [coe_gluingDiffeomorph_apply, coe_shellSymplectomorph_apply, coe_shellSymplectomorph_apply]
  congr 4
  exact hΨm.symm

omit [T2Space M] [IsManifold 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ M] in
include hΨ hδε in
private theorem isLocalDiffeomorph_modelMap :
    IsLocalDiffeomorph 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ (modelMap Ψ (δ := δ)) :=
  fun p ↦ (isLocalDiffeomorph_subtype_val p).comp
    (hg := PartialDiffeomorph.isLocalDiffeomorphAt _ _ _ Ψ.symm (x := p.val) (by
      simpa using coe_mem_target hΨ hδε p))

private theorem injective_outerMap : Function.Injective (outerMap hΨ hf hl hε hσ hδ hδε) :=
  fun _ _ h ↦ Subtype.ext (congrArg Subtype.val
    ((complBallSymplectomorph hΨ hf hl hε).injective (Subtype.ext h)) :)

omit [T2Space M] [IsManifold 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ M] in
include hΨ hδε in
private theorem injective_modelMap : Function.Injective (modelMap Ψ (δ := δ)) := fun p p' h ↦
  Subtype.ext ((apply_modelMap hΨ hδε p).symm.trans (h ▸ apply_modelMap hΨ hδε p'))

/-- The two maps to `M` cover it: `Z` lies in the image of `L(δ)` under the inverse of `Ψ`. -/
private theorem range_outerMap_union_range_modelMap :
    range (outerMap hΨ hf hl hε hσ hδ hδε) ∪ range (modelMap Ψ (δ := δ)) = univ := by
  refine eq_univ_of_forall fun y ↦ ?_
  by_cases hy : y ∈ range f
  · obtain ⟨q, rfl⟩ := hy
    refine Or.inr ⟨⟨zeroSection q, mem_openNbhdOpens_iff.2 (zeroSection_mem_openNbhd hδ q)⟩, ?_⟩
    exact (modelMap_apply _).trans (symm_zeroSection hf q)
  · have hz := (mem_outerPiece_weightBlowup_iff hΨ hf hl hε hσ hδ hδε).2
      (inl_mem_complBall hΨ hf hl hε ⟨y, hy⟩)
    exact Or.inl ⟨⟨_, hz⟩, outerMap_apply_of_eq hΨ hf hl hε hσ hδ hδε (x := ⟨y, hy⟩) rfl⟩

/-- The two maps to `M` meet only on the overlap. -/
private theorem mem_outerOverlap_of_outerMap_eq_modelMap
    (z : WeightBlowup.outerPiece
      (isSymplecticBallEmbedding_blowdownBall_sqrt hΨ hf hl hε hσ hδ.le hδε))
    (p : openNbhdOpens n δ)
    (h : outerMap hΨ hf hl hε hσ hδ hδε z = modelMap Ψ p) :
    z ∈ WeightBlowup.outerOverlap
      (isSymplecticBallEmbedding_blowdownBall_sqrt hΨ hf hl hε hσ hδ.le hδε) := by
  rw [WeightBlowup.mem_outerOverlap_iff]
  have hm : modelMap Ψ p ∈ sourceComplRange hf :=
    (mem_sourceComplRange_iff hf).2 ⟨modelMap_mem_source hΨ hδε p, h ▸ (complBallSymplectomorph
      hΨ hf hl hε
        (Opens.inclusion (outerPiece_weightBlowup_eq hΨ hf hl hε hσ hδ hδε).le z)).property⟩
  have hmδ : Ψ (modelMap Ψ p) ∈ openNbhd n δ := by
    rw [apply_modelMap hΨ hδε p]; exact mem_openNbhdOpens_iff.1 p.property
  set x : outerOverlap hf := ⟨⟨_, hm.2⟩, (mem_outerOverlap_iff hf).2 hm.1⟩
  refine ⟨_, mem_ball_zero_iff.2 ?_,
    (inl_eq_blowdownBall_gluingDiffeomorph hΨ hf hl hε x).symm.trans ?_⟩
  · rw [coe_gluingDiffeomorph_apply, coe_shellSymplectomorph_apply,
      ← coe_radialBlowdownDiffeomorph_apply, ← mem_openNbhd_iff_radialBlowdownDiffeomorph l hδ.le]
    exact hmδ
  refine (congrArg _ (Subtype.ext h.symm)).trans ?_
  exact inl_complBallSymplectomorph_apply hΨ hf hl hε
    (Opens.inclusion (outerPiece_weightBlowup_eq hΨ hf hl hε hσ hδ hδε).le z)

/-- The pull-back of `σ` by `outerMap` is the restriction of the form of the blowdown. -/
private theorem mpullback_outerMap :
    SmoothForm.mpullback (outerMap hΨ hf hl hε hσ hδ hδε)
        (isLocalDiffeomorph_outerMap hΨ hf hl hε hσ hδ hδε).contMDiff σ =
      SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (blowdownForm hΨ hf hl hε hσ) := by
  rw [SmoothForm.mpullback_congr _ (contMDiff_subtypeVal.comp
      ((complBallSymplectomorph hΨ hf hl hε).contMDiff.comp
        (isLocalDiffeomorph_inclusion _).contMDiff))
      (outerMap_def hΨ hf hl hε hσ hδ hδε),
    ← SmoothForm.mpullback_mpullback _ _ ((complBallSymplectomorph hΨ hf hl hε).contMDiff.comp
      (isLocalDiffeomorph_inclusion _).contMDiff) contMDiff_subtypeVal,
    ← SmoothForm.mpullback_mpullback _ _
      (isLocalDiffeomorph_inclusion _).contMDiff
      (complBallSymplectomorph hΨ hf hl hε).contMDiff,
    SmoothTwoForm.isSymplectomorphism_iff_mpullback_eq.1
      (isSymplectomorphism_complBallSymplectomorph hΨ hf hl hε hσ),
    SmoothForm.mpullback_mpullback]
  exact SmoothForm.mpullback_congr _ _
    (funext (Set.coe_inclusion _) : Subtype.val ∘ Opens.inclusion _ = Subtype.val) _

omit [T2Space M] in
include hσ in
/-- The pull-back of `σ` by `modelMap` is the restriction of `ω̃_l`. -/
private theorem mpullback_modelMap :
    SmoothForm.mpullback (modelMap Ψ (δ := δ)) (isLocalDiffeomorph_modelMap hΨ hδε).contMDiff σ =
      SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (blowupForm n l) := by
  have hd : ∀ p : openNbhdOpens n δ, MDifferentiableAt 𝓘(ℝ, Fin (n + 1) → ℂ)
      𝓘(ℝ, Fin (n + 1) → ℂ) Ψ.symm (p : BlowupModel n) := fun p ↦
    (PartialDiffeomorph.isLocalDiffeomorphAt _ _ _ Ψ.symm (x := p.val)
      (by simpa using coe_mem_target hΨ hδε p)).mdifferentiableAt (by simp)
  refine (SmoothTwoForm.isSymplecticMap_iff_mpullback_eq _).1 ?_
  refine SmoothTwoForm.isSymplecticMapOn_univ.1 ((Ψ.isSymplecticMapOn_symm hσ (by simp)).comp
    (((SmoothTwoForm.isSymplecticMap_iff_mpullback_eq contMDiff_subtypeVal).2 rfl).isSymplecticMapOn
      _) (fun p _ ↦ coe_mem_target hΨ hδε p) (fun p _ ↦ hd p)
    (fun p _ ↦ (contMDiff_subtypeVal (n := ∞) p).mdifferentiableAt (by simp)))

/-- **Blowing up the blowdown gives `M` back**: the diffeomorphism from the blowup of weight `l`
and constant `δ` of the blowdown along `blowdownBall`, for `0 < δ < ε`, onto `M`. It is the
identity of `M ∖ Z` on the outer piece, read through `inl` twice
(`weightBlowupBlowdownDiffeomorph_inl_inl`), and the inverse of `Ψ` on the model piece
(`weightBlowupBlowdownDiffeomorph_inr`). -/
def weightBlowupBlowdownDiffeomorph :
    WeightBlowup (isSymplecticBallEmbedding_blowdownBall_sqrt hΨ hf hl hε hσ hδ.le hδε) hl hδ
      ≃ₘ⟮𝓘(ℝ, Fin (n + 1) → ℂ), 𝓘(ℝ, Fin (n + 1) → ℂ)⟯ M :=
  GluedAlong.descDiffeomorph (isLocalDiffeomorph_outerMap hΨ hf hl hε hσ hδ hδε)
    (isLocalDiffeomorph_modelMap hΨ hδε)
    (fun x ↦ by
      have h := outerMap_gluingDiffeomorph hΨ hf hl hε hσ hδ hδε
        (WeightBlowup.gluingDiffeomorphSymm _ hl hδ x)
      rw [WeightBlowup.gluingDiffeomorph_gluingDiffeomorphSymm_apply] at h
      exact h.symm)
    (injective_outerMap hΨ hf hl hε hσ hδ hδε) (injective_modelMap hΨ hδε)
    (range_outerMap_union_range_modelMap hΨ hf hl hε hσ hδ hδε)
    (mem_outerOverlap_of_outerMap_eq_modelMap hΨ hf hl hε hσ hδ hδε)

/-- `weightBlowupBlowdownDiffeomorph` is the inverse of `Ψ` on the model piece `L(δ)`. -/
@[simp]
theorem weightBlowupBlowdownDiffeomorph_inr (p : openNbhdOpens n δ) :
    weightBlowupBlowdownDiffeomorph hΨ hf hl hε hσ hδ hδε
        (GluedAlong.inr (WeightBlowup.gluingDiffeomorphSymm _ hl hδ).toHomeomorph p) =
      Ψ.symm p :=
  GluedAlong.descDiffeomorph_inr _ _ _ _ _ _ _ p

/-- `weightBlowupBlowdownDiffeomorph` is the identity of `M ∖ Z`: it sends the point `inl x` of the
blowdown, seen in the outer piece of its blowup, to `x`. -/
@[simp]
theorem weightBlowupBlowdownDiffeomorph_inl_inl (x : outerPiece hf) :
    weightBlowupBlowdownDiffeomorph hΨ hf hl hε hσ hδ hδε
        (GluedAlong.inl (WeightBlowup.gluingDiffeomorphSymm _ hl hδ).toHomeomorph
          ⟨GluedAlong.inl (gluingDiffeomorph hΨ hf hl hε).toHomeomorph x,
            (mem_outerPiece_weightBlowup_iff hΨ hf hl hε hσ hδ hδε).2
              (inl_mem_complBall hΨ hf hl hε x)⟩) =
      x :=
  (GluedAlong.descDiffeomorph_inl _ _ _ _ _ _ _ _).trans
    (outerMap_apply_of_eq hΨ hf hl hε hσ hδ hδε rfl)

/-- `weightBlowupBlowdownDiffeomorph` sends the divisor of the blowup to `f`. -/
theorem weightBlowupBlowdownDiffeomorph_divisor (q : ℙ ℂ (Fin (n + 1) → ℂ)) :
    weightBlowupBlowdownDiffeomorph hΨ hf hl hε hσ hδ hδε (WeightBlowup.divisor _ hl hδ q) =
      f q := by
  rw [WeightBlowup.divisor_apply, weightBlowupBlowdownDiffeomorph_inr]
  exact symm_zeroSection hf q

/-- **`weightBlowupBlowdownDiffeomorph` is a symplectomorphism**: it pulls `σ` back to the form
`ω̃_ψ` of the blowup of the blowdown. -/
theorem isSymplectomorphism_weightBlowupBlowdownDiffeomorph :
    SmoothTwoForm.IsSymplectomorphism (WeightBlowup.form _ hl hδ) σ
      (weightBlowupBlowdownDiffeomorph hΨ hf hl hε hσ hδ hδε) := by
  rw [SmoothTwoForm.isSymplectomorphism_iff_mpullback_eq, weightBlowupBlowdownDiffeomorph,
    GluedAlong.mpullback_descDiffeomorph, WeightBlowup.form_def]
  simp_rw [mpullback_outerMap, mpullback_modelMap hΨ hσ hδε]

/-- **Blowing up the blowdown gives `M` back**, following McDuff–Salamon, §7.1: for `0 < δ < ε`,
the blowup of weight `l` and constant `δ` of the blowdown along `blowdownBall` is symplectomorphic
to `(M, σ)` by a symplectomorphism that sends its divisor to `f`. -/
theorem weightBlowup_blowdown :
    ∃ Φ : WeightBlowup (isSymplecticBallEmbedding_blowdownBall_sqrt hΨ hf hl hε hσ hδ.le hδε) hl
        hδ ≃ₘ⟮𝓘(ℝ, Fin (n + 1) → ℂ), 𝓘(ℝ, Fin (n + 1) → ℂ)⟯ M,
      SmoothTwoForm.IsSymplectomorphism (WeightBlowup.form _ hl hδ) σ Φ ∧
        ∀ q, Φ (WeightBlowup.divisor _ hl hδ q) = f q :=
  ⟨_, isSymplectomorphism_weightBlowupBlowdownDiffeomorph hΨ hf hl hε hσ hδ hδε,
    weightBlowupBlowdownDiffeomorph_divisor hΨ hf hl hε hσ hδ hδε⟩

end Form

end DivisorBlowdown

/-! ### Blowing down the blowup of weight `l` -/

section WeightBlowup

open BlowupModel
open scoped TauCeti.ComplexManifold

-- As in the section `Form` above.
attribute [local instance high] IsManifold.instOfNatWithTopENat_1

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Fin (n + 1) → ℂ) M]
  [IsManifold 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ M] [T2Space M]
  {σ : SmoothTwoForm 𝓘(ℝ, Fin (n + 1) → ℂ) M} {ψ : StdSpace (Fin (n + 1)) → M} {l ε : ℝ}
  (hψ : IsSymplecticBallEmbedding σ (√(l ^ 2 + ε ^ 2)) ψ) (hl : 0 ≤ l) (hε : 0 < ε)

namespace DivisorBlowdown

/-- A point of the blowup of weight `l` lies in the outer piece of the blowdown of its divisor
exactly when it lies in the complement `complDivisor` of the divisor. -/
theorem mem_outerPiece_divisor_iff (x : WeightBlowup hψ hl hε) :
    x ∈ outerPiece (WeightBlowup.divisor_mem_modelChart_source hψ hl hε) ↔
      x ∈ WeightBlowup.complDivisor hψ hl hε := by
  rw [mem_outerPiece_iff, WeightBlowup.range_divisor, mem_compl_iff, not_not, SetLike.mem_coe]

/-- The outer piece of the blowdown of the divisor, read in `M`: `complDivisorSymplectomorph`. -/
private def outerDiffeomorph :
    outerPiece (WeightBlowup.divisor_mem_modelChart_source hψ hl hε) ≃ₘ⟮𝓘(ℝ, Fin (n + 1) → ℂ),
      𝓘(ℝ, Fin (n + 1) → ℂ)⟯ WeightBlowup.outerPiece hψ :=
  (Diffeomorph.setCongr (SetLike.ext (mem_outerPiece_divisor_iff hψ hl hε))).trans
    (WeightBlowup.complDivisorSymplectomorph hψ hl hε)

private theorem inl_outerDiffeomorph
    (x : outerPiece (WeightBlowup.divisor_mem_modelChart_source hψ hl hε)) :
    GluedAlong.inl (WeightBlowup.gluingDiffeomorphSymm hψ hl hε).toHomeomorph
      (outerDiffeomorph hψ hl hε x) = x := by
  rw [outerDiffeomorph, Diffeomorph.coe_trans, Function.comp_apply,
    WeightBlowup.inl_complDivisorSymplectomorph_apply, Diffeomorph.coe_setCongr_apply]

private theorem isSymplectomorphism_outerDiffeomorph :
    SmoothTwoForm.IsSymplectomorphism
      (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (WeightBlowup.form hψ hl hε))
      (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ) (outerDiffeomorph hψ hl hε) :=
  (SmoothTwoForm.isSymplectomorphism_setCongr _ _).trans
    (WeightBlowup.isSymplectomorphism_complDivisorSymplectomorph hψ hl hε) (by simp)

/-- The ball piece of the blowdown, read in `M`: `ψ ∘ complexToRealEuclidean`. -/
private def ballDiffeomorph :
    ballPiece n l ε ≃ₘ⟮𝓘(ℝ, Fin (n + 1) → ℂ), 𝓘(ℝ, Fin (n + 1) → ℂ)⟯
      (⟨_, hψ.complexPartialDiffeomorph.open_target⟩ : Opens M) :=
  (Diffeomorph.setCongr (SetLike.ext fun _ ↦
      mem_ballPiece_iff.trans hψ.mem_complexPartialDiffeomorph_source_iff.symm)).trans
    hψ.complexPartialDiffeomorph.toDiffeomorphSourceTarget

omit [T2Space M] in
private theorem coe_ballDiffeomorph_apply (w : ballPiece n l ε) :
    (ballDiffeomorph hψ w : M) = ψ (complexToRealEuclidean (Fin (n + 1)) w) := by
  simp only [ballDiffeomorph, Diffeomorph.coe_trans, Function.comp_apply,
    PartialDiffeomorph.toDiffeomorphSourceTarget_apply_coe, hψ.coe_complexPartialDiffeomorph,
    Diffeomorph.coe_setCongr_apply]

omit [T2Space M] in
private theorem isSymplectomorphism_ballDiffeomorph :
    SmoothTwoForm.IsSymplectomorphism
      (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (ω₀E n))
      (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ) (ballDiffeomorph (l := l) hψ) :=
  (SmoothTwoForm.isSymplectomorphism_setCongr _ _).trans
    (ω₀E_def n ▸ hψ.isSymplecticMapOn_complexPartialDiffeomorph
      ).isSymplectomorphism_toDiffeomorphSourceTarget (by simp)

/-- On the overlap, the outer piece and the ball piece, read in `M`, agree through the gluing map
of the blowdown. -/
private theorem ballDiffeomorph_gluingDiffeomorph
    (x : outerOverlap (WeightBlowup.divisor_mem_modelChart_source hψ hl hε)) :
    (ballDiffeomorph hψ (gluingDiffeomorph (WeightBlowup.modelChart_target hψ hl hε)
        (WeightBlowup.divisor_mem_modelChart_source hψ hl hε) hl hε x) : M) =
      (outerDiffeomorph hψ hl hε x : M) := by
  have hx := (mem_outerOverlap_iff _).1 x.property
  rw [WeightBlowup.modelChart_source] at hx
  obtain ⟨p, hp⟩ := hx
  obtain ⟨hp', he⟩ := (WeightBlowup.inl_eq_inr_iff hψ hl hε).1
    ((inl_outerDiffeomorph hψ hl hε x).trans hp.symm)
  rw [coe_ballDiffeomorph_apply, DivisorBlowdown.coe_gluingDiffeomorph_apply, ← he,
    WeightBlowup.coe_gluingDiffeomorph_apply]
  refine congrArg (fun q ↦ ψ (complexToRealEuclidean (Fin (n + 1))
    (shellSymplectomorph n l ε hl hε.le q : Fin (n + 1) → ℂ))) (Subtype.ext ?_)
  exact (congrArg (WeightBlowup.modelChart hψ hl hε) hp.symm).trans
    (WeightBlowup.modelChart_inr hψ hl hε p)

/-- A point of the outer piece whose image in `M` lies in the image of the ball piece is in the
overlap. -/
private theorem mem_outerOverlap_of_eq
    (x : outerPiece (WeightBlowup.divisor_mem_modelChart_source hψ hl hε)) (w : ballPiece n l ε)
    (h : (outerDiffeomorph hψ hl hε x : M) = ballDiffeomorph hψ w) :
    x ∈ outerOverlap (WeightBlowup.divisor_mem_modelChart_source hψ hl hε) := by
  rw [mem_outerOverlap_iff, WeightBlowup.modelChart_source]
  have hmem : outerDiffeomorph hψ hl hε x ∈ WeightBlowup.outerOverlap hψ := by
    rw [WeightBlowup.mem_outerOverlap_iff, h, coe_ballDiffeomorph_apply]
    exact ⟨_, mem_ball_zero_iff.2 (mem_ballPiece_iff.1 w.property), rfl⟩
  exact ⟨_, (GluedAlong.inr_diffeomorph_apply _ ⟨_, hmem⟩).trans (inl_outerDiffeomorph hψ hl hε x)⟩

/-- The images in `M` of the outer piece and of the ball piece cover `M`. -/
private theorem range_outerDiffeomorph_union_range_ballDiffeomorph :
    range (Subtype.val ∘ outerDiffeomorph hψ hl hε) ∪
      range (Subtype.val ∘ ballDiffeomorph (l := l) (ε := ε) hψ) = univ := by
  refine eq_univ_of_forall fun y ↦ ?_
  by_cases hy : y ∈ ψ '' closedBall 0 l
  · obtain ⟨v, hv, rfl⟩ := hy
    have hv' : ‖v‖ < √(l ^ 2 + ε ^ 2) :=
      (mem_closedBall_zero_iff.1 hv).trans_lt (Real.lt_sqrt_sq_add_sq l hε.ne')
    refine Or.inr ⟨⟨(complexToRealEuclidean (Fin (n + 1))).symm v, by simpa using hv'⟩, ?_⟩
    rw [Function.comp_apply, coe_ballDiffeomorph_apply, ContinuousLinearEquiv.apply_symm_apply]
  · refine Or.inl
      ⟨(outerDiffeomorph hψ hl hε).symm ⟨y, (WeightBlowup.mem_outerPiece_iff hψ).2 hy⟩, ?_⟩
    rw [Function.comp_apply, Diffeomorph.apply_symm_apply]

/-- **Blowing down the blowup of weight `l` gives the manifold back**, following McDuff–Salamon,
§7.1. Blow down the divisor `WeightBlowup.divisor` of the blowup of weight `l` of `M` along `ψ`,
with the model chart, the inverse of `inr`, as `Ψ`. The result is symplectomorphic to `(M, σ)`,
by a symplectomorphism that is `complDivisorSymplectomorph` on the outer piece, and so the
identity of `M ∖ ψ(B(l))`, and that carries `blowdownBall` to `ψ` on the open ball of radius
`√(l² + ε²)`. -/
theorem blowdown_weightBlowup :
    ∃ Φ : DivisorBlowdown (WeightBlowup.modelChart_target hψ hl hε)
        (WeightBlowup.divisor_mem_modelChart_source hψ hl hε) hl hε ≃ₘ⟮𝓘(ℝ, Fin (n + 1) → ℂ),
          𝓘(ℝ, Fin (n + 1) → ℂ)⟯ M,
      SmoothTwoForm.IsSymplectomorphism
        (blowdownForm _ _ hl hε (WeightBlowup.isSymplecticMapOn_modelChart hψ hl hε)) σ Φ ∧
      (∀ x, Φ (GluedAlong.inl _ x) =
        WeightBlowup.complDivisorSymplectomorph hψ hl hε
          ⟨x, (mem_outerPiece_divisor_iff hψ hl hε x).1 x.property⟩) ∧
      ∀ w : StdSpace (Fin (n + 1)), ‖w‖ < √(l ^ 2 + ε ^ 2) →
        Φ (blowdownBall _ _ hl hε w) = ψ w := by
  have hg₁ : IsLocalDiffeomorph 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) ∞
      (Subtype.val ∘ outerDiffeomorph hψ hl hε) :=
    (outerDiffeomorph hψ hl hε).isLocalDiffeomorph_subtypeVal_comp
  have hg₂ : IsLocalDiffeomorph 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) ∞
      (Subtype.val ∘ ballDiffeomorph (l := l) (ε := ε) hψ) :=
    (ballDiffeomorph hψ).isLocalDiffeomorph_subtypeVal_comp
  refine ⟨GluedAlong.descDiffeomorph hg₁ hg₂ (ballDiffeomorph_gluingDiffeomorph hψ hl hε)
      (Subtype.val_injective.comp (outerDiffeomorph hψ hl hε).injective)
      (Subtype.val_injective.comp (ballDiffeomorph hψ).injective)
      (range_outerDiffeomorph_union_range_ballDiffeomorph hψ hl hε)
      (fun x w h ↦ mem_outerOverlap_of_eq hψ hl hε x w h), ?_, fun x ↦ ?_, fun w hw ↦ ?_⟩
  · rw [SmoothTwoForm.isSymplectomorphism_iff_mpullback_eq, GluedAlong.mpullback_descDiffeomorph,
      blowdownForm_def]
    congr 1
    · rw [← SmoothForm.mpullback_mpullback _ _ (outerDiffeomorph hψ hl hε).contMDiff
        contMDiff_subtypeVal]
      exact SmoothTwoForm.isSymplectomorphism_iff_mpullback_eq.1
        (isSymplectomorphism_outerDiffeomorph hψ hl hε)
    · rw [← SmoothForm.mpullback_mpullback _ _ (ballDiffeomorph hψ).contMDiff contMDiff_subtypeVal]
      exact SmoothTwoForm.isSymplectomorphism_iff_mpullback_eq.1
        (isSymplectomorphism_ballDiffeomorph hψ)
  · rw [GluedAlong.descDiffeomorph_inl, Function.comp_apply, outerDiffeomorph,
      Diffeomorph.coe_trans, Function.comp_apply]
    exact congrArg (fun z ↦ (WeightBlowup.complDivisorSymplectomorph hψ hl hε z : M))
      (Subtype.ext (Diffeomorph.coe_setCongr_apply _ _))
  · rw [blowdownBall_of_norm_lt _ _ hl hε hw, GluedAlong.descDiffeomorph_inr, Function.comp_apply,
      coe_ballDiffeomorph_apply, ContinuousLinearEquiv.apply_symm_apply]

end DivisorBlowdown

end WeightBlowup

/-! ### The blowdown of a divisor -/

section Milestone

open BlowupModel Module
open _root_.Bundle (TotalSpace)
open scoped TauCeti.ComplexManifold

-- As in the section `Form` above.
attribute [local instance high] IsManifold.instOfNatWithTopENat_1

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Fin (n + 1) → ℂ) M]
  [IsManifold 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ M] [T2Space M] [SecondCountableTopology M]
  {P₀ P₁ : Type*} [NormedAddCommGroup P₀] [NormedSpace ℝ P₀] [FiniteDimensional ℝ P₀]
  [NormedAddCommGroup P₁] [NormedSpace ℝ P₁] [FiniteDimensional ℝ P₁]

/-- **The symplectic blowdown**, following McDuff–Salamon, §7.1, and McDuff, Lemma 2.1 and
Corollary 2.2. Let `(M, σ)` be a symplectic manifold without boundary, `l > 0`, and
`f : ℙ ℂ (Fin (n + 1) → ℂ) → M` a smooth embedding with `f^* σ = l² ω_FS`, whose normal bundle is
isomorphic to that of the zero section of the model blowup `L` by a smooth fibrewise isomorphism
`Φ` that sends each pair of positive normal symplectic pairing for `σ` to one of positive pairing
for `ω̃_l = blowupForm n l`. Then there are `ε > 0` and a partial diffeomorphism `Ψ` from `M`
to the model with target `L(ε) = openNbhd n ε`, whose source contains the image `Z` of `f`,
sending `f q` to `zeroSection q` and symplectic from `σ` to `ω̃_l` on its source
(`BlowupModel.exists_symplectomorphism_blowupModel`), such that the blowdown `DivisorBlowdown`
of `M` along `f`, `Ψ`, `l` and `ε`, with its form `blowdownForm`:
* is symplectic;
* has the symplectic embedding `blowdownBall` of the closed ball of radius `l`, and the
  complement `complBall` of the image of that closed ball is symplectomorphic to `M ∖ Z`;
* blown up along `blowdownBall` with weight `l` and any constant `δ` with `0 < δ < ε`, gives
  `(M, σ)` back, by a symplectomorphism sending the divisor to `f` (`weightBlowup_blowdown`).

Moreover, for every `ε' > 0` and every symplectic embedding `ψ` of the closed ball of radius
`√(l² + ε'²)` in `M`, blowing down the divisor of the blowup of weight `l` of `M` along `ψ`
gives `(M, σ)` back, by a symplectomorphism that is `complDivisorSymplectomorph` on the outer
piece and sends `blowdownBall` to `ψ` on the open ball of radius `√(l² + ε'²)`
(`blowdown_weightBlowup`).

Milestone: *Symplectic blowdown*. -/
theorem exists_blowdown {σ : SmoothTwoForm 𝓘(ℝ, Fin (n + 1) → ℂ) M} (hσ : σ.IsSymplectic)
    {f : SmoothEmbedding 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ (ℙ ℂ (Fin (n + 1) → ℂ)) M}
    {l : ℝ} (hl : 0 < l) (hf : SmoothForm.mpullback f f.contMDiff σ = l ^ 2 • fubiniStudyForm n)
    (hn : (∞ : ℕ∞ω) ≠ 0)
    (hP₀ : finrank ℝ P₀ = finrank ℝ (Fin (n + 1) → ℂ) - finrank ℝ (Fin n → ℂ))
    (hP₁ : finrank ℝ P₁ = finrank ℝ (Fin (n + 1) → ℂ) - finrank ℝ (Fin n → ℂ))
    (Φ : ∀ q, f.isImmersion.NormalSpace q hn ≃L[ℝ]
        (zeroSectionRealEmbedding n).isImmersion.NormalSpace q hn)
    (hΦ : letI := f.normalSpaceFiberBundle hn hP₀
      letI := (zeroSectionRealEmbedding n).normalSpaceFiberBundle hn hP₁
      ContMDiff (𝓘(ℝ, Fin n → ℂ).prod 𝓘(ℝ, P₀)) (𝓘(ℝ, Fin n → ℂ).prod 𝓘(ℝ, P₁)) ∞
        (fun p : TotalSpace P₀ (fun q ↦ f.isImmersion.NormalSpace q hn) ↦
          (⟨p.proj, Φ p.proj p.snd⟩ :
            TotalSpace P₁ (fun q ↦ (zeroSectionRealEmbedding n).isImmersion.NormalSpace q hn))))
    (hΦσ : ∀ q v w,
      0 < f.symplecticNormalForm (hasSymplecticTangentImages_of_mpullback_eq_smul_fubiniStudyForm
        hσ.isNondegenerate f.contMDiff (pow_ne_zero 2 hl.ne') hf) q hn v w →
      0 < (zeroSectionRealEmbedding n).symplecticNormalForm
        (hasSymplecticTangentImages_zeroSectionRealEmbedding hl.ne') q hn (Φ q v) (Φ q w)) :
    (∃ ε, ∃ hε : 0 < ε,
      ∃ Ψ : PartialDiffeomorph 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) M (BlowupModel n) ∞,
      ∃ hΨ : Ψ.target = openNbhd n ε, ∃ hfΨ : ∀ q, f q ∈ Ψ.source ∧ Ψ (f q) = zeroSection q,
      ∃ hσΨ : σ.IsSymplecticMapOn (blowupForm n l) Ψ Ψ.source,
        (DivisorBlowdown.blowdownForm hΨ hfΨ hl.le hε hσΨ).IsSymplectic ∧
        IsSymplecticBallEmbedding (DivisorBlowdown.blowdownForm hΨ hfΨ hl.le hε hσΨ) l
          (DivisorBlowdown.blowdownBall hΨ hfΨ hl.le hε) ∧
        (∀ z, z ∈ DivisorBlowdown.complBall hΨ hfΨ hl.le hε ↔
          z ∉ DivisorBlowdown.blowdownBall hΨ hfΨ hl.le hε '' closedBall 0 l) ∧
        (∃ Θ : DivisorBlowdown.complBall hΨ hfΨ hl.le hε ≃ₘ⟮𝓘(ℝ, Fin (n + 1) → ℂ),
            𝓘(ℝ, Fin (n + 1) → ℂ)⟯ DivisorBlowdown.outerPiece hfΨ,
          SmoothTwoForm.IsSymplectomorphism
            (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal
              (DivisorBlowdown.blowdownForm hΨ hfΨ hl.le hε hσΨ))
            (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ) Θ) ∧
        ∀ δ (hδ : 0 < δ) (hδε : δ < ε),
          ∃ Θ : WeightBlowup (DivisorBlowdown.isSymplecticBallEmbedding_blowdownBall_sqrt hΨ hfΨ
              hl.le hε hσΨ hδ.le hδε) hl.le hδ ≃ₘ⟮𝓘(ℝ, Fin (n + 1) → ℂ),
                𝓘(ℝ, Fin (n + 1) → ℂ)⟯ M,
            SmoothTwoForm.IsSymplectomorphism (WeightBlowup.form _ hl.le hδ) σ Θ ∧
              ∀ q, Θ (WeightBlowup.divisor _ hl.le hδ q) = f q) ∧
    ∀ ε' (hε' : 0 < ε') (ψ : StdSpace (Fin (n + 1)) → M)
      (hψ : IsSymplecticBallEmbedding σ (√(l ^ 2 + ε' ^ 2)) ψ),
      ∃ Θ : DivisorBlowdown (WeightBlowup.modelChart_target hψ hl.le hε')
          (WeightBlowup.divisor_mem_modelChart_source hψ hl.le hε') hl.le hε' ≃ₘ⟮
            𝓘(ℝ, Fin (n + 1) → ℂ), 𝓘(ℝ, Fin (n + 1) → ℂ)⟯ M,
        SmoothTwoForm.IsSymplectomorphism (DivisorBlowdown.blowdownForm _ _ hl.le hε'
          (WeightBlowup.isSymplecticMapOn_modelChart hψ hl.le hε')) σ Θ ∧
        (∀ x, Θ (GluedAlong.inl _ x) =
          WeightBlowup.complDivisorSymplectomorph hψ hl.le hε'
            ⟨x, (DivisorBlowdown.mem_outerPiece_divisor_iff hψ hl.le hε' x).1 x.property⟩) ∧
        ∀ w : StdSpace (Fin (n + 1)), ‖w‖ < √(l ^ 2 + ε' ^ 2) →
          Θ (DivisorBlowdown.blowdownBall _ _ hl.le hε' w) = ψ w := by
  refine ⟨?_, fun ε' hε' ψ hψ ↦ DivisorBlowdown.blowdown_weightBlowup hψ hl.le hε'⟩
  obtain ⟨ε, hε, Ψ, hΨ, hfΨ, hσΨ⟩ :=
    exists_symplectomorphism_blowupModel hσ hl.ne' hf hn hP₀ hP₁ Φ hΦ hΦσ
  exact ⟨ε, hε, Ψ, hΨ, hfΨ, hσΨ, DivisorBlowdown.isSymplectic_blowdownForm hΨ hfΨ hl.le hε hσΨ hσ,
    DivisorBlowdown.isSymplecticBallEmbedding_blowdownBall_weight hΨ hfΨ hl.le hε hσΨ,
    fun _ ↦ DivisorBlowdown.mem_complBall_iff hΨ hfΨ hl.le hε,
    ⟨_, DivisorBlowdown.isSymplectomorphism_complBallSymplectomorph hΨ hfΨ hl.le hε hσΨ⟩,
    fun δ hδ hδε ↦ DivisorBlowdown.weightBlowup_blowdown hΨ hfΨ hl.le hε hσΨ hδ hδε⟩

end Milestone

end SymplecticGeometry

end
