/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Gluing.Pair
public import SymplecticGeometry.Geometry.Symplectic.Blowup.Model
public import SymplecticGeometry.Geometry.Symplectic.IsotopyExtension.Ball.Basic
public import SymplecticGeometry.Geometry.Manifold.Complex.Blowup.Tautological
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective
public import TauCeti.Geometry.Manifold.SmoothEmbedding.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Map
public import TauCeti.Geometry.Symplectic.Lagrangian.Embedding.Symplectic.Basic
import SymplecticGeometry.Geometry.Symplectic.Manifold.SymplecticMap
import TauCeti.Geometry.Manifold.DifferentialForm.Opens.PartialDiffeomorph
import TauCeti.Geometry.Symplectic.Manifold.NeighborhoodGerm
import TauCeti.Geometry.Symplectic.Manifold.Opens
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions

/-!
# The blowup of weight `λ` along a symplectic ball

Let `M` be a Hausdorff smooth manifold modelled on `E := Fin (n + 1) → ℂ`, let `σ` be a two-form
on `M`,
and let `ψ : StdSpace (Fin (n + 1)) → M` be a symplectic embedding of the closed ball of radius
`√(l² + ε²)` (`IsSymplecticBallEmbedding σ (√(l ^ 2 + ε ^ 2)) ψ`), for `0 ≤ l` and `0 < ε`. The
weight `λ` of McDuff–Salamon is called `l` here, as in `Blowup/Model.lean`. Following
McDuff–Salamon, §7.1, the blowup `M̃_ψ` of weight `l` is obtained by removing the closed ball
`ψ(B(l))` from `M` and gluing in the neighbourhood `openNbhd n ε` of the exceptional divisor `Z`
of the model blowup `L = BlowupModel n`: a point `p` of `openNbhd n ε ∖ Z` is identified with
`ψ(F_l(π p))`, where `F_l z = √(1 + l² / |z|²) z` is the radial map and `π` the blowdown, read
on `StdSpace` through `complexToRealEuclidean`. The map `p ↦ F_l(π p)` is
`BlowupModel.shellSymplectomorph`, a diffeomorphism of `openNbhd n ε ∖ Z` onto the open shell
`l < |w| < √(l² + ε²)` of `E`, which `ψ` maps diffeomorphically onto an open subset of
`M ∖ ψ(B(l))`. The topology and the smooth structure use the form `σ` only through the ball
embedding, so for them it need not be closed or nondegenerate.

The form `ω̃_ψ` of the blowup is `σ` on `M ∖ ψ(B(l))` and the form `ω̃_l` of the model
(`BlowupModel.blowupForm n l`) on `openNbhd n ε`. These agree on the overlap: `ψ` pulls `σ` back
to `ω₀` on the open ball, and `shellSymplectomorph` pulls `ω₀` back to `ω̃_l`. So they glue, by
`GluedAlong.gluedForm`, and the result is symplectic when `σ` is and `l ≠ 0`. Off the image of
the divisor `Z`, the blowup is the image of `inl`, and so symplectomorphic to `M ∖ ψ(B(l))`.

## Main definitions

* `SymplecticGeometry.WeightBlowup.outerPiece hψ`: the open subset `M ∖ ψ(B(l))` of `M`.
* `SymplecticGeometry.WeightBlowup.modelPiece n ε`: the open subset `openNbhd n ε` of the model.
* `SymplecticGeometry.WeightBlowup.shellImage hψ`: the image under `ψ` of the open shell
  `l < |w| < √(l² + ε²)`, an open subset of `M`.
* `SymplecticGeometry.WeightBlowup.gluingDiffeomorph hψ hl hε`: the diffeomorphism
  `p ↦ ψ(F_l(π p))` from `openNbhd n ε ∖ Z`, as an open subset of the model piece, onto
  `shellImage hψ`, as an open subset of the outer piece, and
  `SymplecticGeometry.WeightBlowup.gluingDiffeomorphSymm hψ hl hε`, its inverse.
* `SymplecticGeometry.WeightBlowup hψ hl hε`: the blowup of weight `l`, the space
  `SymplecticGeometry.GluedAlong` of `Geometry/Manifold/Gluing/Pair.lean` glued from the two
  pieces along `gluingDiffeomorphSymm`. It is second countable when `M` is, by the
  instance of `GluedAlong`.
* `SymplecticGeometry.WeightBlowup.form hψ hl hε`: the form `ω̃_ψ` of the blowup, glued from `σ`
  and `ω̃_l`.
* `SymplecticGeometry.WeightBlowup.complDivisor hψ hl hε`: the complement of `inr(Z)`, the
  range of `inl`, and `SymplecticGeometry.WeightBlowup.complDivisorSymplectomorph hψ hl hε`,
  its diffeomorphism onto `M ∖ ψ(B(l))`, the inverse of `inl`.
* `SymplecticGeometry.WeightBlowup.divisor hψ hl hε`: the divisor `ℙ ℂ E → M̃_ψ`, the zero
  section of the model followed by `inr`, as a smooth embedding of real manifolds.
* `SymplecticGeometry.WeightBlowup.normalSpaceDivisorEquiv hψ hl hε hn ℓ`: the real-linear
  isomorphism from the normal space of the divisor at `ℓ` onto the line `ℓ`, the fibre of the
  tautological line bundle.

## Main results

* `SymplecticGeometry.WeightBlowup.coe_gluingDiffeomorph_apply`: the gluing map is
  `ψ ∘ complexToRealEuclidean ∘ shellSymplectomorph`.
* `SymplecticGeometry.WeightBlowup.instIsManifold`: the blowup is a smooth manifold modelled on
  `E`, by the manifold structure of `GluedAlong`.
* `SymplecticGeometry.WeightBlowup.inl_gluingDiffeomorph`, `inl_eq_inr_iff`: the identification
  made by the gluing, for the embeddings `GluedAlong.inl` and `GluedAlong.inr` of the two
  pieces, to which the rest of the API of `GluedAlong` applies.
* `SymplecticGeometry.WeightBlowup.instT2Space`: the blowup is Hausdorff. A point of `Z` and a
  point `x ∉ ψ(B(l))` that is not glued to the model are separated, for `0 < δ < ε`, by
  `openNbhd n δ` and the complement of the compact set `ψ(B(√(l² + δ²)))`, which does not contain
  `x`, since `x` is not in the image of the open ball of radius `√(l² + ε²)`. This is the
  criterion `GluedAlong.t2Space_iff`.
* `SymplecticGeometry.WeightBlowup.isSymplectomorphism_gluingDiffeomorph`: the gluing map pulls
  `σ` back to `ω̃_l`, by `isSymplectomorphism_shellSymplectomorph` and
  `isSymplectomorphism_shellDiffeomorph`.
* `SymplecticGeometry.WeightBlowup.mpullback_inl_form`, `mpullback_inr_form`, `eq_form_iff`: the
  form of the blowup is the form that pulls back to `σ` by `inl` and to `ω̃_l` by `inr`.
* `SymplecticGeometry.WeightBlowup.isSymplectic_form`: for symplectic `σ` and `l ≠ 0`, the form
  of the blowup is symplectic.
* `SymplecticGeometry.WeightBlowup.mem_complDivisor_iff`,
  `isSymplectomorphism_complDivisorSymplectomorph`: the complement of `inr(Z)` with `ω̃_ψ` is
  symplectomorphic to `M ∖ ψ(B(l))` with `σ`.
* `SymplecticGeometry.WeightBlowup.range_divisor`: the image of the divisor is the complement of
  `complDivisor`.
* `SymplecticGeometry.WeightBlowup.mpullback_divisor_form`: `ω̃_ψ` pulls back along the divisor
  to `l² ω_FS`, by `BlowupModel.mpullback_zeroSection_blowupForm`; so, for `l ≠ 0`, the divisor
  is a symplectic submanifold
  (`SymplecticGeometry.WeightBlowup.isSymplecticSubmanifoldEmbedding_divisor`).
* `SymplecticGeometry.WeightBlowup.normalSpaceDivisorEquiv_normalClass`,
  `normalSpaceDivisorEquiv_symm_apply`: the isomorphism of normal spaces sends the class of the
  image under `inr` of a tangent vector `w` of the model at `zeroSection ℓ` to the differential
  of the blowdown applied to `w`. It is `BlowupModel.normalSpaceZeroSectionRealEquiv` of
  `Geometry/Manifold/Complex/Blowup/Tautological.lean`, carried through `inr` by Tau Ceti's
  `SmoothEmbedding.normalSpaceEquiv`, since `inr` is a local diffeomorphism.

The gluing follows the other uses of `GluedAlong` in the library, the capped surface of
`Geometry/Manifold/Gluing/CapDiscs/Basic.lean` and the fiber sum of
`Geometry/Symplectic/Sum/Fibre.lean`, whose form is glued by `GluedAlong.gluedForm` in the same
way. The diffeomorphism of the complement of the divisor follows `Blowup.blowdownRealDiffeomorph`
of `Geometry/Manifold/Complex/Blowup/Basic.lean`, through Tau Ceti's
`IsLocalDiffeomorph.diffeomorphOfInjective`. The divisor is built like `Blowup.divisorRealEmbedding`
of the same file, by Tau Ceti's `SmoothEmbedding.codRestrict` and
`SmoothEmbedding.transLocalDiffeomorph`.

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
    (hψ.isCompact_image_closedBall (Real.le_sqrt_of_sq_le (by nlinarith))).isClosed.isOpen_compl⟩

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
      ).sdiff (hψ.isCompact_image_closedBall (Real.le_sqrt_of_sq_le (by nlinarith))).isClosed⟩

@[simp]
theorem mem_shellImage_iff (hψ : IsSymplecticBallEmbedding σ (√(l ^ 2 + ε ^ 2)) ψ) {x : M} :
    x ∈ shellImage hψ ↔ x ∈ ψ '' ball 0 √(l ^ 2 + ε ^ 2) ∧ x ∉ ψ '' closedBall 0 l :=
  Iff.rfl

/-- The image of the shell lies in the outer piece. -/
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
    have hle : v ∈ closedBall 0 √(l ^ 2 + ε ^ 2) :=
      closedBall_subset_closedBall (Real.le_sqrt_of_sq_le (by nlinarith)) hv
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
/-- `openNbhd n ε ∖ Z` lies in the model piece. -/
theorem openNbhdComplDivisor_le_modelPiece :
    openNbhdComplDivisor n ε ≤ modelPiece n ε :=
  fun _ hp ↦ (mem_openNbhdComplDivisor_iff.1 hp).1

variable (n ε) in
/-- The overlap on the side of the model: `openNbhd n ε ∖ Z`, as an open subset of the model
piece. -/
def modelOverlap : Opens (modelPiece n ε) :=
  Opens.comap ⟨Subtype.val, continuous_subtypeVal⟩ (openNbhdComplDivisor n ε)

@[simp]
theorem mem_modelOverlap_iff {p : modelPiece n ε} :
    p ∈ modelOverlap n ε ↔ (p : BlowupModel n) ∉ exceptionalDivisor n := by
  rw [modelOverlap, Opens.mem_comap, ContinuousMap.coe_mk, mem_openNbhdComplDivisor_iff]
  exact and_iff_right (mem_modelPiece_iff.1 p.property)

/-- The overlap on the side of `M`: `shellImage hψ`, as an open subset of the outer piece. -/
def outerOverlap (hψ : IsSymplecticBallEmbedding σ (√(l ^ 2 + ε ^ 2)) ψ) :
    Opens (outerPiece hψ) :=
  Opens.comap ⟨Subtype.val, continuous_subtypeVal⟩ (shellImage hψ)

/-- A point of the outer piece lies in the overlap exactly when it is in the image of the open
ball of radius `√(l² + ε²)`. -/
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
    (hε : 0 < ε) :
    modelOverlap n ε ≃ₘ⟮𝓘(ℝ, Fin (n + 1) → ℂ), 𝓘(ℝ, Fin (n + 1) → ℂ)⟯ outerOverlap hψ :=
  (Diffeomorph.nestedOpen (openNbhdComplDivisor_le_modelPiece n ε)).trans
    ((shellSymplectomorph n l ε hl hε.le).trans
      ((shellDiffeomorph hψ).trans (Diffeomorph.nestedOpen (shellImage_le_outerPiece hψ)).symm))

@[simp]
theorem coe_gluingDiffeomorph_apply (hψ : IsSymplecticBallEmbedding σ (√(l ^ 2 + ε ^ 2)) ψ)
    (hl : 0 ≤ l) (hε : 0 < ε) (p : modelOverlap n ε) :
    ((gluingDiffeomorph hψ hl hε p : outerPiece hψ) : M) =
      ψ (complexToRealEuclidean (Fin (n + 1))
        (shellSymplectomorph n l ε hl hε.le
          ⟨p.val.val, mem_openNbhdComplDivisor_iff.2 ⟨mem_modelPiece_iff.1 p.val.property,
            mem_modelOverlap_iff.1 p.property⟩⟩)) := by
  -- The coercion of `gluingDiffeomorph` to a function goes between the types `modelOverlap n ε`
  -- and `outerOverlap hψ`, which the lemmas about `Diffeomorph.trans` and `Diffeomorph.nestedOpen`
  -- match only once both are unfolded, in the type of `p` too.
  revert p
  delta gluingDiffeomorph modelOverlap outerOverlap
  intro p
  simp only [Diffeomorph.coe_trans, Function.comp_apply, Diffeomorph.nestedOpen_apply,
    Diffeomorph.nestedOpen_symm_apply, coe_shellDiffeomorph_apply]

/-- A point `p` of `openNbhd n ε ∖ Z` with `|π p| < δ` is glued to a point of the image of the open
ball of radius `√(l² + δ²)`. -/
theorem coe_gluingDiffeomorph_mem_image_ball
    (hψ : IsSymplecticBallEmbedding σ (√(l ^ 2 + ε ^ 2)) ψ) (hl : 0 ≤ l) (hε : 0 < ε) {δ : ℝ}
    (hδ : 0 ≤ δ) (p : modelOverlap n ε) (hp : (p.val : BlowupModel n) ∈ openNbhd n δ) :
    ((gluingDiffeomorph hψ hl hε p : outerPiece hψ) : M) ∈ ψ '' ball 0 √(l ^ 2 + δ ^ 2) := by
  rw [coe_gluingDiffeomorph_apply]
  refine ⟨_, ?_, rfl⟩
  rw [mem_ball_zero_iff, coe_shellSymplectomorph_apply,
    ← coe_radialBlowdownDiffeomorph_apply]
  exact (mem_openNbhd_iff_radialBlowdownDiffeomorph l hδ _).1 hp

/-- The inverse of the gluing map, from `shellImage hψ` in the outer piece onto
`openNbhd n ε ∖ Z` in the model piece: the diffeomorphism along which the blowup is glued. -/
def gluingDiffeomorphSymm (hψ : IsSymplecticBallEmbedding σ (√(l ^ 2 + ε ^ 2)) ψ) (hl : 0 ≤ l)
    (hε : 0 < ε) :
    outerOverlap hψ ≃ₘ⟮𝓘(ℝ, Fin (n + 1) → ℂ), 𝓘(ℝ, Fin (n + 1) → ℂ)⟯ modelOverlap n ε :=
  -- Named, so that the blowup is the `GluedAlong` of a term that `simp` keeps: Mathlib's
  -- `Diffeomorph.symm_toHomeomorph` rewrites `(gluingDiffeomorph hψ hl hε).symm.toHomeomorph`,
  -- also inside the types of terms on the blowup.
  (gluingDiffeomorph hψ hl hε).symm

theorem gluingDiffeomorphSymm_def (hψ : IsSymplecticBallEmbedding σ (√(l ^ 2 + ε ^ 2)) ψ)
    (hl : 0 ≤ l) (hε : 0 < ε) :
    gluingDiffeomorphSymm hψ hl hε = (gluingDiffeomorph hψ hl hε).symm :=
  (rfl)

/-- The inverse of `gluingDiffeomorphSymm` is the gluing map `gluingDiffeomorph`. -/
@[simp]
theorem gluingDiffeomorphSymm_symm (hψ : IsSymplecticBallEmbedding σ (√(l ^ 2 + ε ^ 2)) ψ)
    (hl : 0 ≤ l) (hε : 0 < ε) :
    (gluingDiffeomorphSymm hψ hl hε).symm = gluingDiffeomorph hψ hl hε := by
  rw [gluingDiffeomorphSymm_def, Diffeomorph.symm_symm]

@[simp]
theorem gluingDiffeomorph_gluingDiffeomorphSymm_apply
    (hψ : IsSymplecticBallEmbedding σ (√(l ^ 2 + ε ^ 2)) ψ) (hl : 0 ≤ l) (hε : 0 < ε)
    (x : outerOverlap hψ) : gluingDiffeomorph hψ hl hε (gluingDiffeomorphSymm hψ hl hε x) = x := by
  rw [gluingDiffeomorphSymm_def, Diffeomorph.apply_symm_apply]

@[simp]
theorem gluingDiffeomorphSymm_gluingDiffeomorph_apply
    (hψ : IsSymplecticBallEmbedding σ (√(l ^ 2 + ε ^ 2)) ψ) (hl : 0 ≤ l) (hε : 0 < ε)
    (p : modelOverlap n ε) : gluingDiffeomorphSymm hψ hl hε (gluingDiffeomorph hψ hl hε p) = p := by
  rw [gluingDiffeomorphSymm_def, Diffeomorph.symm_apply_apply]

/-- **The blowup of weight `l`** of `M` along the symplectic ball embedding `ψ`, following
McDuff–Salamon, §7.1: the outer piece `M ∖ ψ(B(l))` and the model piece `openNbhd n ε` glued
along `gluingDiffeomorphSymm`, the inverse of `gluingDiffeomorph`, which identifies
`p ∈ openNbhd n ε ∖ Z` with `ψ(F_l(π p))`. It is a smooth manifold modelled on `Fin (n + 1) → ℂ`. -/
abbrev _root_.SymplecticGeometry.WeightBlowup
    (hψ : IsSymplecticBallEmbedding σ (√(l ^ 2 + ε ^ 2)) ψ) (hl : 0 ≤ l) (hε : 0 < ε) : Type :=
  GluedAlong (gluingDiffeomorphSymm hψ hl hε).toHomeomorph

variable (hψ : IsSymplecticBallEmbedding σ (√(l ^ 2 + ε ^ 2)) ψ) (hl : 0 ≤ l) (hε : 0 < ε)

/-- The blowup of weight `l` is a smooth manifold, the model piece carrying the real structure of
the complex manifold `BlowupModel n`. -/
instance instIsManifold : IsManifold 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ (WeightBlowup hψ hl hε) :=
  inferInstance

/-- A point `p` of `openNbhd n ε ∖ Z` is glued to `ψ(F_l(π p))`. -/
@[simp]
theorem inl_gluingDiffeomorph (p : modelOverlap n ε) :
    GluedAlong.inl (gluingDiffeomorphSymm hψ hl hε).toHomeomorph (gluingDiffeomorph hψ hl hε p) =
      GluedAlong.inr (gluingDiffeomorphSymm hψ hl hε).toHomeomorph p := by
  rw [gluingDiffeomorphSymm_def, Diffeomorph.symm_toHomeomorph,
    GluedAlong.inl_toHomeomorph_symm_apply]

/-- A point `x` of the outer piece and a point `y` of the model piece have the same image in the
blowup exactly when `y` is off the divisor and `x` is its image under the gluing map. -/
theorem inl_eq_inr_iff {x : outerPiece hψ} {y : modelPiece n ε} :
    GluedAlong.inl (gluingDiffeomorphSymm hψ hl hε).toHomeomorph x =
        GluedAlong.inr (gluingDiffeomorphSymm hψ hl hε).toHomeomorph y ↔
      ∃ h : y ∈ modelOverlap n ε, (gluingDiffeomorph hψ hl hε ⟨y, h⟩ : outerPiece hψ) = x := by
  refine ⟨fun h ↦ ?_, fun ⟨hy, hx⟩ ↦ hx ▸ inl_gluingDiffeomorph hψ hl hε ⟨y, hy⟩⟩
  obtain ⟨hx, rfl⟩ := (GluedAlong.inl_eq_inr_diffeomorph_iff _).1 h
  exact ⟨(gluingDiffeomorphSymm hψ hl hε ⟨x, hx⟩).property, by simp⟩

/-- **The blowup of weight `l` is Hausdorff**, for Hausdorff `M`. -/
instance instT2Space : T2Space (WeightBlowup hψ hl hε) := by
  -- By `GluedAlong.t2Space_iff`, it suffices to separate a point `y` of the divisor from a point
  -- `x` of `M ∖ ψ(B(l))` that is not glued, that is, not in the image of the open ball of radius
  -- `√(l² + ε²)`. For `δ = ε / 2`, the neighbourhood `openNbhd n δ` of `y` is glued into the
  -- compact set `ψ(B(√(l² + δ²)))`, which misses `x`.
  refine (GluedAlong.t2Space_iff _).2 ⟨inferInstance, inferInstance, fun x hx y hy ↦ ?_⟩
  rw [mem_outerOverlap_iff] at hx
  rw [mem_modelOverlap_iff, not_not] at hy
  have hδ : 0 < ε / 2 := half_pos hε
  have hR : √(l ^ 2 + (ε / 2) ^ 2) < √(l ^ 2 + ε ^ 2) :=
    Real.sqrt_lt_sqrt (by positivity) (by nlinarith)
  refine ⟨Subtype.val ⁻¹' (ψ '' closedBall 0 √(l ^ 2 + (ε / 2) ^ 2))ᶜ, ?_,
    Subtype.val ⁻¹' openNbhd n (ε / 2), ?_, fun z hzA hzB ↦ ?_⟩
  · refine continuous_subtypeVal.continuousAt.preimage_mem_nhds
      ((hψ.isCompact_image_closedBall hR.le).isClosed.isOpen_compl.mem_nhds ?_)
    rintro ⟨v, hv, hvx⟩
    exact hx ⟨v, mem_ball_zero_iff.2 ((mem_closedBall_zero_iff.1 hv).trans_lt hR), hvx⟩
  · exact continuous_subtypeVal.continuousAt.preimage_mem_nhds
      ((isOpen_openNbhd _).mem_nhds (exceptionalDivisor_subset_openNbhd hδ hy))
  · have h := coe_gluingDiffeomorph_mem_image_ball hψ hl hε hδ.le _ hzB
    rw [Diffeomorph.coe_toHomeomorph, gluingDiffeomorph_gluingDiffeomorphSymm_apply] at h
    exact hzA (image_mono ball_subset_closedBall h)

section Form

-- With the scope `TauCeti.ComplexManifold` open, the search for the `C^1` structure of an open
-- subset of an open subset of `M`, which the pull-backs of forms below need, also tries complex
-- structures and times out. Deriving it from the smooth structure first avoids this.
attribute [local instance high] IsManifold.instOfNatWithTopENat_1

/-! ### The form of the blowup -/

omit [T2Space M] in
/-- `ψ ∘ complexToRealEuclidean` is a symplectic map from `ω₀` on `E` to `σ` on its source. -/
private theorem isSymplecticMapOn_complexPartialDiffeomorph
    (hψ : IsSymplecticBallEmbedding σ (√(l ^ 2 + ε ^ 2)) ψ) :
    (ω₀E n).IsSymplecticMapOn σ (complexPartialDiffeomorph hψ)
      (complexPartialDiffeomorph hψ).source := by
  refine PartialDiffeomorph.isSymplecticMapOn_trans (σ := (stdForm (Fin (n + 1))).constSmooth)
    _ _ ?_ ?_ (by simp)
  · have h : (ω₀E n).IsSymplecticMap (stdForm (Fin (n + 1))).constSmooth
        (complexToRealEuclidean (Fin (n + 1))) := by
      rw [SmoothTwoForm.isSymplecticMap_iff_mpullback_eq
        (complexToRealEuclidean (Fin (n + 1))).contDiff.contMDiff, ω₀E_def,
        constSmooth_stdComplexPiSymplecticForm_eq]
    simpa using h
  · rw [hψ.coe_toPartialDiffeomorph, hψ.toPartialDiffeomorph_source]
    exact hψ.isSymplecticMapOn

/-- `shellDiffeomorph hψ` pulls the restriction of `σ` to `shellImage hψ` back to the restriction
of `ω₀` to the open shell. -/
theorem isSymplectomorphism_shellDiffeomorph
    (hψ : IsSymplecticBallEmbedding σ (√(l ^ 2 + ε ^ 2)) ψ) :
    SmoothTwoForm.IsSymplectomorphism
      (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (ω₀E n))
      (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ) (shellDiffeomorph hψ) := by
  have h : SmoothTwoForm.IsSymplectomorphism
      (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (ω₀E n))
      (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ)
      (complexPartialDiffeomorph hψ).toDiffeomorphSourceTarget := by
    rw [SmoothTwoForm.isSymplectomorphism_iff_mpullback_eq]
    exact (SmoothForm.mpullback_toDiffeomorphSourceTarget_eq_iff _).2 fun _ hw ↦
      (isSymplecticMapOn_complexPartialDiffeomorph hψ).mpullback_apply hw
  rw [shellDiffeomorph]
  exact h.subtype_nestedOpen _ _ _

/-- **The gluing map is a symplectomorphism**: `gluingDiffeomorph` pulls the restriction of `σ`
to `shellImage hψ` back to the restriction of `ω̃_l` to `openNbhd n ε ∖ Z`, both read on the
overlaps in the outer and the model piece. -/
theorem isSymplectomorphism_gluingDiffeomorph :
    SmoothTwoForm.IsSymplectomorphism
      (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal
        (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (blowupForm n l)))
      (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal
        (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ))
      (gluingDiffeomorph hψ hl hε) := by
  rw [gluingDiffeomorph]
  exact (SmoothTwoForm.isSymplectomorphism_nestedOpen _ _).trans
    ((isSymplectomorphism_shellSymplectomorph hl hε.le).trans
      ((isSymplectomorphism_shellDiffeomorph hψ).trans
        ((SmoothTwoForm.isSymplectomorphism_nestedOpen σ _).symm (by simp)) (by simp))
      (by simp)) (by simp)

/-- The inverse of the gluing map pulls the restriction of `ω̃_l` back to that of `σ`: the
condition under which the two forms glue. -/
theorem mpullback_gluingDiffeomorphSymm :
    SmoothForm.mpullback (gluingDiffeomorphSymm hψ hl hε)
        (gluingDiffeomorphSymm hψ hl hε).contMDiff
        (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal
          (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (blowupForm n l))) =
      SmoothForm.mpullback Subtype.val contMDiff_subtypeVal
        (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ) := by
  rw [gluingDiffeomorphSymm_def]
  exact SmoothTwoForm.isSymplectomorphism_iff_mpullback_eq.1
    ((isSymplectomorphism_gluingDiffeomorph hψ hl hε).symm (by simp))

/-- **The form `ω̃_ψ` of the blowup of weight `l`**, following McDuff–Salamon, §7.1: the two-form
that is `σ` on the outer piece `M ∖ ψ(B(l))` and the form `ω̃_l = blowupForm n l` of the model on
the model piece `openNbhd n ε`, which agree on the overlap (`mpullback_gluingDiffeomorphSymm`). -/
def form : SmoothTwoForm 𝓘(ℝ, Fin (n + 1) → ℂ) (WeightBlowup hψ hl hε) :=
  GluedAlong.gluedForm _ (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ)
    (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (blowupForm n l))
    (mpullback_gluingDiffeomorphSymm hψ hl hε)

theorem form_def :
    form hψ hl hε =
      GluedAlong.gluedForm _ (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ)
        (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (blowupForm n l))
        (mpullback_gluingDiffeomorphSymm hψ hl hε) :=
  (rfl)

/-- The form of the blowup pulls back by `inl` to the restriction of `σ` to `M ∖ ψ(B(l))`. -/
@[simp]
theorem mpullback_inl_form :
    SmoothForm.mpullback (GluedAlong.inl (gluingDiffeomorphSymm hψ hl hε).toHomeomorph)
        (GluedAlong.isLocalDiffeomorph_inl _).contMDiff (form hψ hl hε) =
      SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ :=
  GluedAlong.mpullback_inl_gluedForm

/-- The form of the blowup pulls back by `inr` to the restriction of `ω̃_l` to `openNbhd n ε`. -/
@[simp]
theorem mpullback_inr_form :
    SmoothForm.mpullback (GluedAlong.inr (gluingDiffeomorphSymm hψ hl hε).toHomeomorph)
        (GluedAlong.isLocalDiffeomorph_inr _).contMDiff (form hψ hl hε) =
      SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (blowupForm n l) :=
  GluedAlong.mpullback_inr_gluedForm

/-- A two-form on the blowup is `form hψ hl hε` exactly when it pulls back by `inl` to the
restriction of `σ` and by `inr` to the restriction of `ω̃_l`. -/
theorem eq_form_iff {α : SmoothTwoForm 𝓘(ℝ, Fin (n + 1) → ℂ) (WeightBlowup hψ hl hε)} :
    α = form hψ hl hε ↔
      SmoothForm.mpullback (GluedAlong.inl (gluingDiffeomorphSymm hψ hl hε).toHomeomorph)
          (GluedAlong.isLocalDiffeomorph_inl _).contMDiff α =
        SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ ∧
      SmoothForm.mpullback (GluedAlong.inr (gluingDiffeomorphSymm hψ hl hε).toHomeomorph)
          (GluedAlong.isLocalDiffeomorph_inr _).contMDiff α =
        SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (blowupForm n l) :=
  GluedAlong.eq_gluedForm_iff

/-- **The blowup of weight `l` is symplectic**: for symplectic `σ` and `l ≠ 0`, the form
`ω̃_ψ` is symplectic. -/
theorem isSymplectic_form (hσ : σ.IsSymplectic) (hl₀ : l ≠ 0) : (form hψ hl hε).IsSymplectic :=
  GluedAlong.isSymplectic_gluedForm_iff.2
    ⟨hσ.mpullback_subtype_val _, (isSymplectic_blowupForm hl₀).mpullback_subtype_val _⟩

/-! ### The complement of the divisor -/

/-- The complement in the blowup of the image `inr(Z)` of the exceptional divisor: the image of
the outer piece under `inl`, an open set. -/
def complDivisor : Opens (WeightBlowup hψ hl hε) :=
  (GluedAlong.isLocalDiffeomorph_inl (gluingDiffeomorphSymm hψ hl hε)).image

@[simp]
theorem coe_complDivisor :
    (complDivisor hψ hl hε : Set (WeightBlowup hψ hl hε)) =
      range (GluedAlong.inl (gluingDiffeomorphSymm hψ hl hε).toHomeomorph) := by
  rw [complDivisor, ← Opens.carrier_eq_coe, IsLocalDiffeomorph.image_coe]

/-- Every point `inl x` of the blowup lies in `complDivisor`. -/
@[simp]
theorem inl_mem_complDivisor (x : outerPiece hψ) :
    GluedAlong.inl (gluingDiffeomorphSymm hψ hl hε).toHomeomorph x ∈ complDivisor hψ hl hε :=
  SetLike.mem_coe.1 ((coe_complDivisor hψ hl hε).symm ▸ mem_range_self x)

/-- A point of the blowup lies in `complDivisor` exactly when it is not the image under `inr` of a
point of the exceptional divisor. -/
theorem mem_complDivisor_iff {z : WeightBlowup hψ hl hε} :
    z ∈ complDivisor hψ hl hε ↔
      z ∉ GluedAlong.inr (gluingDiffeomorphSymm hψ hl hε).toHomeomorph ''
        {y : modelPiece n ε | (y : BlowupModel n) ∈ exceptionalDivisor n} := by
  rw [← SetLike.mem_coe, coe_complDivisor]
  constructor
  · rintro ⟨x, rfl⟩ ⟨y, hy, hxy⟩
    obtain ⟨h, -⟩ := (inl_eq_inr_iff hψ hl hε).1 hxy.symm
    exact mem_modelOverlap_iff.1 h hy
  · intro hz
    rcases GluedAlong.exists_inl_or_exists_inr _ z with ⟨x, hx⟩ | ⟨y, rfl⟩
    · exact ⟨x, hx⟩
    · exact ⟨_, inl_gluingDiffeomorph hψ hl hε ⟨y, mem_modelOverlap_iff.2 fun h ↦ hz ⟨y, h, rfl⟩⟩⟩

/-- **The complement of the divisor**: the diffeomorphism from the complement of `inr(Z)` in the
blowup onto `M ∖ ψ(B(l))`, the inverse of `inl`. It pulls `σ` back to `ω̃_ψ`
(`isSymplectomorphism_complDivisorSymplectomorph`). -/
def complDivisorSymplectomorph :
    complDivisor hψ hl hε ≃ₘ⟮𝓘(ℝ, Fin (n + 1) → ℂ), 𝓘(ℝ, Fin (n + 1) → ℂ)⟯ outerPiece hψ :=
  -- `complDivisor` is by definition the open set `IsLocalDiffeomorph.image` of `inl`.
  ((GluedAlong.isLocalDiffeomorph_inl _).diffeomorphOfInjective (GluedAlong.inl_injective _)).symm

/-- The inverse of `complDivisorSymplectomorph` is `inl`. -/
@[simp]
theorem coe_complDivisorSymplectomorph_symm_apply (x : outerPiece hψ) :
    ((complDivisorSymplectomorph hψ hl hε).symm x : WeightBlowup hψ hl hε) =
      GluedAlong.inl (gluingDiffeomorphSymm hψ hl hε).toHomeomorph x :=
  IsLocalDiffeomorph.coe_diffeomorphOfInjective_apply _ _ x

/-- `inl` undoes `complDivisorSymplectomorph`. -/
@[simp]
theorem inl_complDivisorSymplectomorph_apply (z : complDivisor hψ hl hε) :
    GluedAlong.inl (gluingDiffeomorphSymm hψ hl hε).toHomeomorph
        (complDivisorSymplectomorph hψ hl hε z) = z := by
  rw [← coe_complDivisorSymplectomorph_symm_apply, Diffeomorph.symm_apply_apply]

/-- `complDivisorSymplectomorph` sends the point `inl x` to `x`. -/
@[simp]
theorem complDivisorSymplectomorph_inl (x : outerPiece hψ) :
    complDivisorSymplectomorph hψ hl hε
        ⟨GluedAlong.inl (gluingDiffeomorphSymm hψ hl hε).toHomeomorph x,
          inl_mem_complDivisor hψ hl hε x⟩ = x := by
  apply GluedAlong.inl_injective (gluingDiffeomorphSymm hψ hl hε).toHomeomorph
  exact inl_complDivisorSymplectomorph_apply hψ hl hε _

/-- **The complement of the divisor is symplectomorphic to `M ∖ ψ(B(l))`**:
`complDivisorSymplectomorph` pulls the restriction of `σ` to `M ∖ ψ(B(l))` back to the restriction
of the form `ω̃_ψ` of the blowup to the complement of `inr(Z)`. -/
theorem isSymplectomorphism_complDivisorSymplectomorph :
    SmoothTwoForm.IsSymplectomorphism
      (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (form hψ hl hε))
      (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ)
      (complDivisorSymplectomorph hψ hl hε) := by
  -- The inverse of `complDivisorSymplectomorph` followed by the inclusion is `inl`; the `show`
  -- states this as an equality of functions, the form `SmoothForm.mpullback_congr` takes.
  rw [← SmoothTwoForm.isSymplectomorphism_symm_iff (by simp),
    SmoothTwoForm.isSymplectomorphism_iff_mpullback_eq,
    SmoothForm.mpullback_mpullback, SmoothForm.mpullback_congr _
      (GluedAlong.isLocalDiffeomorph_inl _).contMDiff
      (show Subtype.val ∘ (complDivisorSymplectomorph hψ hl hε).symm = GluedAlong.inl _ from
        funext (coe_complDivisorSymplectomorph_symm_apply hψ hl hε)), mpullback_inl_form]

/-! ### The divisor and its normal bundle -/

section Divisor

open scoped LinearAlgebra.Projectivization

/-- The zero section of the model blowup lies in the model piece `openNbhd n ε`, for `0 < ε`. -/
theorem zeroSection_mem_modelPiece (hε : 0 < ε) (ℓ : ℙ ℂ (Fin (n + 1) → ℂ)) :
    zeroSection ℓ ∈ modelPiece n ε :=
  mem_modelPiece_iff.2 (zeroSection_mem_openNbhd hε ℓ)

/-- The real zero section of the model blowup, as a smooth embedding into the model piece. -/
private def zeroSectionModelPiece (hε : 0 < ε) :
    SmoothEmbedding 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ (ℙ ℂ (Fin (n + 1) → ℂ))
      (modelPiece n ε) :=
  (zeroSectionRealEmbedding n).codRestrict (modelPiece n ε) fun ℓ ↦ by
    rw [coe_zeroSectionRealEmbedding]
    exact zeroSection_mem_modelPiece hε ℓ

private theorem zeroSectionModelPiece_apply (hε : 0 < ε) (ℓ : ℙ ℂ (Fin (n + 1) → ℂ)) :
    zeroSectionModelPiece hε ℓ = ⟨zeroSection ℓ, zeroSection_mem_modelPiece hε ℓ⟩ :=
  Subtype.ext <| by
    rw [zeroSectionModelPiece, SmoothEmbedding.val_codRestrict_apply,
      coe_zeroSectionRealEmbedding]

private theorem val_comp_zeroSectionModelPiece (hε : 0 < ε) :
    Subtype.val ∘ zeroSectionModelPiece (n := n) hε = zeroSectionRealEmbedding n :=
  SmoothEmbedding.val_comp_codRestrict _ _ _

/-- **The divisor of the blowup of weight `l`**: the exceptional divisor `ℙ ℂ E` of the model,
mapped into the blowup by `inr` after the zero section, as a smooth embedding of the underlying
real manifolds. Its image is the complement of `complDivisor` (`range_divisor`). -/
def divisor :
    SmoothEmbedding 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ (ℙ ℂ (Fin (n + 1) → ℂ))
      (WeightBlowup hψ hl hε) :=
  (zeroSectionModelPiece hε).transLocalDiffeomorph
    (GluedAlong.inr (gluingDiffeomorphSymm hψ hl hε).toHomeomorph) (s := univ)
    (fun y _ ↦ GluedAlong.isLocalDiffeomorph_inr _ y)
    (by
      rw [domRestrict_def]
      exact (GluedAlong.isOpenEmbedding_inr _).isEmbedding.comp .subtypeVal)
    (subset_univ _)

/-- The divisor sends a line `ℓ` to the image under `inr` of the point `zeroSection ℓ` of the
model piece. -/
@[simp]
theorem divisor_apply (ℓ : ℙ ℂ (Fin (n + 1) → ℂ)) :
    divisor hψ hl hε ℓ =
      GluedAlong.inr (gluingDiffeomorphSymm hψ hl hε).toHomeomorph
        ⟨zeroSection ℓ, zeroSection_mem_modelPiece hε ℓ⟩ := by
  rw [divisor, SmoothEmbedding.transLocalDiffeomorph_apply, zeroSectionModelPiece_apply]

private theorem coe_divisor :
    ⇑(divisor hψ hl hε) =
      GluedAlong.inr (gluingDiffeomorphSymm hψ hl hε).toHomeomorph ∘ zeroSectionModelPiece hε := by
  rw [divisor, SmoothEmbedding.coe_transLocalDiffeomorph]

/-- The image of the divisor is the complement of `complDivisor`, the image under `inr` of the
exceptional divisor of the model. -/
theorem range_divisor :
    range (divisor hψ hl hε) = (complDivisor hψ hl hε : Set (WeightBlowup hψ hl hε))ᶜ := by
  ext z
  rw [mem_compl_iff, SetLike.mem_coe, mem_complDivisor_iff, not_not]
  constructor
  · rintro ⟨ℓ, rfl⟩
    refine ⟨_, ?_, (divisor_apply hψ hl hε ℓ).symm⟩
    rw [exceptionalDivisor_eq_range]
    exact mem_range_self ℓ
  · rintro ⟨y, hy, rfl⟩
    rw [exceptionalDivisor_eq_range] at hy
    obtain ⟨ℓ, hℓ⟩ := hy
    exact ⟨ℓ, (divisor_apply hψ hl hε ℓ).trans (congrArg _ (Subtype.ext hℓ))⟩

/-- **The divisor carries `l² ω_FS`**: the form `ω̃_ψ` of the blowup pulls back along the divisor
to `l² • fubiniStudyForm n`. -/
@[simp]
theorem mpullback_divisor_form :
    SmoothForm.mpullback (divisor hψ hl hε) (divisor hψ hl hε).contMDiff (form hψ hl hε) =
      l ^ 2 • fubiniStudyForm n := by
  have hr : ContMDiff 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) ∞
      (GluedAlong.inr (gluingDiffeomorphSymm hψ hl hε).toHomeomorph) :=
    (GluedAlong.isLocalDiffeomorph_inr _).contMDiff
  rw [SmoothForm.mpullback_congr _ (hr.comp (zeroSectionModelPiece hε).contMDiff)
      (coe_divisor hψ hl hε),
    ← SmoothForm.mpullback_mpullback _ _ (zeroSectionModelPiece hε).contMDiff hr,
    mpullback_inr_form, SmoothForm.mpullback_mpullback,
    SmoothForm.mpullback_congr _ ((contMDiff_zeroSection ∞).restrictScalars' ℝ)
      ((val_comp_zeroSectionModelPiece hε).trans (coe_zeroSectionRealEmbedding n)),
    mpullback_zeroSection_blowupForm]

/-- **The divisor is a symplectic submanifold**: for `l ≠ 0` and a nondegenerate form `ω̃_ψ`, as
for symplectic `σ` (`isSymplectic_form`), the divisor is a symplectic submanifold embedding. -/
theorem isSymplecticSubmanifoldEmbedding_divisor (hω : (form hψ hl hε).IsNondegenerate)
    (hl₀ : l ≠ 0) : hω.IsSymplecticSubmanifoldEmbedding 𝓘(ℝ, Fin n → ℂ) (divisor hψ hl hε) := by
  rw [hω.isSymplecticSubmanifoldEmbedding_iff_isNondegenerate_mpullback
    (divisor hψ hl hε).isSmoothEmbedding]
  convert (isSymplectic_fubiniStudyForm n).isNondegenerate.smul _ (pow_ne_zero 2 hl₀)
  exact mpullback_divisor_form hψ hl hε

variable (hn : (∞ : ℕ∞ω) ≠ 0)

/-- The normal spaces of the zero section in the model piece and in the model are the same,
through the inclusion of the model piece. -/
private def normalSpaceZeroSectionModelPieceEquiv (ℓ : ℙ ℂ (Fin (n + 1) → ℂ)) :
    (zeroSectionModelPiece (n := n) hε).isImmersion.NormalSpace ℓ hn ≃L[ℝ]
      (zeroSectionRealEmbedding n).isImmersion.NormalSpace ℓ hn :=
  (zeroSectionModelPiece hε).normalSpaceEquiv (zeroSectionRealEmbedding n) hn hn
    (u := _root_.id) (v := Subtype.val)
    ((isLocalDiffeomorph_subtype_val _).isInvertible_mfderiv hn)
    (by rw [mfderiv_id]; exact Function.surjective_id)
    (Filter.EventuallyEq.of_eq (val_comp_zeroSectionModelPiece hε))

/-- The normal spaces of the zero section in the model piece and of the divisor are the same,
through `inr`. -/
private def normalSpaceZeroSectionModelPieceDivisorEquiv (ℓ : ℙ ℂ (Fin (n + 1) → ℂ)) :
    (zeroSectionModelPiece (n := n) hε).isImmersion.NormalSpace ℓ hn ≃L[ℝ]
      (divisor hψ hl hε).isImmersion.NormalSpace ℓ hn :=
  (zeroSectionModelPiece hε).normalSpaceEquiv (divisor hψ hl hε) hn hn
    (u := _root_.id) (v := GluedAlong.inr (gluingDiffeomorphSymm hψ hl hε).toHomeomorph)
    ((GluedAlong.isLocalDiffeomorph_inr _ _).isInvertible_mfderiv hn)
    (by rw [mfderiv_id]; exact Function.surjective_id)
    (Filter.EventuallyEq.of_eq (coe_divisor hψ hl hε).symm)

/-- **The normal bundle of the divisor is the tautological line.** The real-linear isomorphism
from the normal space of the divisor at `ℓ` onto the line `ℓ`: the isomorphism
`normalSpaceZeroSectionRealEquiv` of the model, transported through `inr`. It sends the normal
class of the image under `inr` of a tangent vector `w` of the model at `zeroSection ℓ` to the
differential of `blowdown` applied to `w` (`normalSpaceDivisorEquiv_normalClass`). -/
def normalSpaceDivisorEquiv (ℓ : ℙ ℂ (Fin (n + 1) → ℂ)) :
    (divisor hψ hl hε).isImmersion.NormalSpace ℓ hn ≃L[ℝ]
      Projectivization.Tautological ℂ (Fin (n + 1) → ℂ) ℓ :=
  ((normalSpaceZeroSectionModelPieceDivisorEquiv hψ hl hε hn ℓ).symm.trans
    (normalSpaceZeroSectionModelPieceEquiv hε hn ℓ)).trans
      (normalSpaceZeroSectionRealEquiv n hn ℓ)

/-- `normalSpaceDivisorEquiv` sends the normal class of the image under `inr` of a tangent vector
`w` of the model at `zeroSection ℓ` to the differential of `blowdown` at `zeroSection ℓ` applied
to `w`, a vector of the line `ℓ`. -/
@[simp]
theorem normalSpaceDivisorEquiv_normalClass (ℓ : ℙ ℂ (Fin (n + 1) → ℂ))
    (w : TangentSpace 𝓘(ℝ, Fin (n + 1) → ℂ) (zeroSection ℓ : BlowupModel n)) :
    normalSpaceDivisorEquiv hψ hl hε hn ℓ ((divisor hψ hl hε).isImmersion.normalClass ℓ hn
        (mfderiv 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ)
          (GluedAlong.inr (gluingDiffeomorphSymm hψ hl hε).toHomeomorph)
          ⟨zeroSection ℓ, zeroSection_mem_modelPiece hε ℓ⟩ w)) =
      ⟨mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) blowdown (zeroSection ℓ) w,
        mfderiv_blowdown_zeroSection_mem ℓ w⟩ := by
  -- The tangent vectors at `zeroSectionModelPiece hε ℓ` and at the point
  -- `⟨zeroSection ℓ, _⟩` of the model piece, equal by `zeroSectionModelPiece_apply`, are both
  -- vectors of `Fin (n + 1) → ℂ`: `h₁` states the first step for every point equal to it.
  have h₁ : ∀ p, p = zeroSectionModelPiece hε ℓ → ∀ v : Fin (n + 1) → ℂ,
      (normalSpaceZeroSectionModelPieceDivisorEquiv hψ hl hε hn ℓ).symm
        ((divisor hψ hl hε).isImmersion.normalClass ℓ hn
          (mfderiv 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ)
            (GluedAlong.inr (gluingDiffeomorphSymm hψ hl hε).toHomeomorph) p v)) =
        (zeroSectionModelPiece hε).isImmersion.normalClass ℓ hn v := by
    rintro _ rfl v
    rw [ContinuousLinearEquiv.symm_apply_eq, normalSpaceZeroSectionModelPieceDivisorEquiv]
    exact (SmoothEmbedding.normalSpaceEquiv_normalClass (zeroSectionModelPiece hε)
      (divisor hψ hl hε) hn hn (u := _root_.id)
      (v := GluedAlong.inr (gluingDiffeomorphSymm hψ hl hε).toHomeomorph) _ _ _ v).symm
  have h₂ : ∀ v : Fin (n + 1) → ℂ, normalSpaceZeroSectionModelPieceEquiv hε hn ℓ
      ((zeroSectionModelPiece hε).isImmersion.normalClass ℓ hn v) =
      (zeroSectionRealEmbedding n).isImmersion.normalClass ℓ hn v := by
    intro v
    rw [normalSpaceZeroSectionModelPieceEquiv]
    refine (SmoothEmbedding.normalSpaceEquiv_normalClass _ _ hn hn _ _ _ v).trans ?_
    exact congrArg _ (Manifold.mfderiv_subtype_val_apply _ v)
  rw [normalSpaceDivisorEquiv, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.trans_apply, h₁ _ (zeroSectionModelPiece_apply hε ℓ).symm w, h₂ w]
  exact normalSpaceZeroSectionRealEquiv_normalClass ℓ w

/-- The inverse of `normalSpaceDivisorEquiv` sends the differential of `blowdown` at
`zeroSection ℓ` applied to a tangent vector `w` of the model to the normal class of the image of
`w` under `inr`. -/
theorem normalSpaceDivisorEquiv_symm_apply (ℓ : ℙ ℂ (Fin (n + 1) → ℂ))
    (w : TangentSpace 𝓘(ℝ, Fin (n + 1) → ℂ) (zeroSection ℓ : BlowupModel n)) :
    (normalSpaceDivisorEquiv hψ hl hε hn ℓ).symm
        ⟨mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) blowdown (zeroSection ℓ) w,
          mfderiv_blowdown_zeroSection_mem ℓ w⟩ =
      (divisor hψ hl hε).isImmersion.normalClass ℓ hn
        (mfderiv 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ)
          (GluedAlong.inr (gluingDiffeomorphSymm hψ hl hε).toHomeomorph)
          ⟨zeroSection ℓ, zeroSection_mem_modelPiece hε ℓ⟩ w) := by
  rw [ContinuousLinearEquiv.symm_apply_eq, normalSpaceDivisorEquiv_normalClass]

end Divisor

end Form

end WeightBlowup

end SymplecticGeometry

end
