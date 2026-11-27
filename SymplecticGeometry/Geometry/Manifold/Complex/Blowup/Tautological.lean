/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Complex.Blowup.Lift
public import SymplecticGeometry.Geometry.Manifold.Projectivization.Tautological
public import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.NormalSpace.ComplexStructure
public import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.RestrictScalars
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import TauCeti.Geometry.Manifold.Complex.Orientation
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.Quotient
import SymplecticGeometry.Geometry.Manifold.ContMDiff.RestrictScalars
import SymplecticGeometry.LinearAlgebra.Complex.Finrank
import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.HolomorphicEmbedding
import SymplecticGeometry.Geometry.Manifold.VectorBundle.Pullback
import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.NormalSpace.Topology
import SymplecticGeometry.Geometry.Manifold.VectorBundle.ZeroSection
import TauCeti.Geometry.Manifold.SmoothEmbedding.Diffeomorph
import TauCeti.Geometry.Manifold.MFDeriv.RestrictScalars

/-!
# The model blowup as the total space of the tautological line

For `n : ℕ` and `E := Fin (n + 1) → ℂ`, a point of the model blowup `BlowupModel n` is a pair
`(ℓ, z)` of a line `ℓ ∈ ℙ ℂ E` and a vector `z ∈ ℓ`: it is a vector of the tautological line
over `ℓ`. Through the library's isomorphism `Projectivization.tautologicalTwistCoreEquiv` of the
tautological line with Tau Ceti's `𝒪(-1)`, the line bundle `Projectivization.twistCore (-1)`, the
blowup is the total space of `𝒪(-1)` over `ℙ ℂ E`, as complex manifolds (McDuff–Salamon,
Lemma 7.1.1; Griffiths–Harris, Chapter 1, §4).

## Main definitions and results

* `SymplecticGeometry.BlowupModel.blowupModelTotalSpaceDiffeomorph n`: the biholomorphism from
  the total space of `(Projectivization.twistCore (-1)).Fiber`, modelled on
  `𝓘(ℂ, Fin n → ℂ).prod 𝓘(ℂ, ℂ)`, onto `BlowupModel n`, sending `⟨ℓ, a⟩` to
  `(ℓ, (tautologicalTwistCoreEquiv ℓ).symm a)`
  (`SymplecticGeometry.BlowupModel.blowupModelTotalSpaceDiffeomorph_apply`).
* `SymplecticGeometry.BlowupModel.pr_blowupModelTotalSpaceDiffeomorph`: under it, the projection
  `BlowupModel.pr` is the bundle projection, and
  `SymplecticGeometry.BlowupModel.blowupModelTotalSpaceDiffeomorph_zero`: the zero of the fibre
  at `ℓ` goes to `BlowupModel.zeroSection ℓ`.
* `SymplecticGeometry.BlowupModel.blowdown_blowupModelTotalSpaceDiffeomorph` and
  `SymplecticGeometry.BlowupModel.proj_blowupModelTotalSpaceDiffeomorph_symm`: the blowdown of the
  image of `⟨ℓ, a⟩`, and the base point of the inverse image of a point of the blowup.
* `SymplecticGeometry.BlowupModel.blowupModelTotalSpaceDiffeomorph_symm_apply` and
  `SymplecticGeometry.BlowupModel.blowupModelTotalSpaceDiffeomorph_symm_zeroSection`: the
  inverse, and its value on the exceptional divisor.
* `SymplecticGeometry.BlowupModel.zeroSectionEmbedding n`: the zero section
  `BlowupModel.zeroSection` as Tau Ceti's holomorphic embedding `TauCeti.SmoothEmbedding`
  (`SymplecticGeometry.BlowupModel.coe_zeroSectionEmbedding`), with image the exceptional divisor
  (`SymplecticGeometry.BlowupModel.range_zeroSectionEmbedding`).
* `SymplecticGeometry.BlowupModel.ker_mfderiv_blowdown_zeroSection`: the kernel of the differential
  of `blowdown` at `zeroSection ℓ` is the tangent image of the zero section, and
  `SymplecticGeometry.BlowupModel.range_mfderiv_blowdown_zeroSection`: its image is the line `ℓ`.
* `SymplecticGeometry.BlowupModel.normalSpaceZeroSectionEquiv n ℓ`: the complex-linear isomorphism
  from Tau Ceti's normal space `Manifold.IsImmersion.NormalSpace` of `zeroSectionEmbedding n` at `ℓ`
  onto the fibre `Projectivization.Tautological ℂ E ℓ` of the tautological line, induced by that
  differential (`SymplecticGeometry.BlowupModel.normalSpaceZeroSectionEquiv_normalClass`,
  `SymplecticGeometry.BlowupModel.normalSpaceZeroSectionEquiv_symm_apply`), and
  `SymplecticGeometry.BlowupModel.continuous_normalSpaceZeroSectionEquiv`: it is continuous on
  total spaces, for Tau Ceti's quotient topology on the normal bundle.
* `SymplecticGeometry.BlowupModel.zeroSectionRealEmbedding n`: the zero section as a smooth
  embedding of the underlying real manifolds, the real form
  `TauCeti.SmoothEmbedding.restrictScalars` of `zeroSectionEmbedding n`
  (`SymplecticGeometry.BlowupModel.zeroSectionRealEmbedding_def`). Its tangent ranges are
  invariant under the almost complex structure
  `TauCeti.SmoothAlmostComplexStructure.ofComplexManifold` of the blowup
  (`SymplecticGeometry.BlowupModel.mapsTo_ofComplexManifold_tangentRange_zeroSectionRealEmbedding`).
* `SymplecticGeometry.BlowupModel.normalSpaceZeroSectionRealEquiv n hn ℓ`: the real form of
  `normalSpaceZeroSectionEquiv n ℓ`, a real-linear isomorphism from the real normal space onto
  the line `ℓ`, whose inverse is computed by
  `SymplecticGeometry.BlowupModel.normalSpaceZeroSectionRealEquiv_symm_apply`. It agrees with
  `normalSpaceZeroSectionEquiv n ℓ` on normal classes
  (`SymplecticGeometry.BlowupModel.normalSpaceZeroSectionRealEquiv_normalClass_eq`), is continuous
  on total spaces (`SymplecticGeometry.BlowupModel.continuous_normalSpaceZeroSectionRealEquiv`),
  and carries the complex structure `SmoothEmbedding.contMDiffNormalComplexStructure` that the
  blowup induces on the normal bundle to multiplication by `Complex.I`
  (`SymplecticGeometry.BlowupModel.normalSpaceZeroSectionRealEquiv_contMDiffNormalComplexStructure`
  ).
* The velocity of the fibre at the divisor, for `v ≠ 0`:
`SymplecticGeometry.BlowupModel.normalSpaceZeroSectionRealEquiv_normalClassL_mfderiv_curveLift_smul`
  says that the fibre `curveLift (· • v)` of the tautological line over `ℓ = [v]` crosses the
  divisor at `t = 0` with normal velocity `v`: read through
  `normalSpaceZeroSectionRealEquiv n hn ℓ`, the normal class of its real derivative at `0`
  applied to `c : ℂ` is `c • v`. This is the form of the derivative hypothesis of the
  slice lemma `TauCeti.SmoothEmbedding.singularCohomologyMap_slice_eq_of_hasFDerivAt`; it follows
  from the chain rule `mfderiv_blowdown_mfderiv_curveLift` of `Lift.lean`.

## Implementation notes

The map into the blowup is shown holomorphic through the embedding of the blowup into
`ℙ ℂ E × E` (`BlowupModel.isSmoothEmbedding_blowupModel_val`), whose second component is
holomorphic by `Projectivization.contMDiff_coe_tautologicalTwistCoreEquiv_symm`. For the
inverse, in the frame of the chart `k` of `𝒪(-1)` the image of `(ℓ, z)` has the coordinate `z k`
(`Projectivization.twistCore_localTriv_tautologicalTwistCoreEquiv`), a coordinate of the
holomorphic map `BlowupModel.blowdown`.

The zero section is the image under `blowupModelTotalSpaceDiffeomorph` of the zero section of
`𝒪(-1)`, a holomorphic embedding by `SymplecticGeometry.Bundle.zeroSectionEmbedding`, so it is
one too, by Tau Ceti's `Diffeomorph.isSmoothEmbedding_comp`.

The differential of `blowdown` at `zeroSection ℓ` vanishes on the tangent image of the zero
section, of dimension `n`, since `blowdown` vanishes on the zero section, and its image contains
`ℓ`, through the curves `t ↦ (ℓ, t • z)`; by rank–nullity in dimension `n + 1`, both inclusions
are equalities. Tau Ceti's `Manifold.IsImmersion.normalSpaceEquivOfKer` then gives the isomorphism
of the normal space with `ℓ`. Its continuity on total spaces follows, by
`TauCeti.SmoothEmbedding.continuous_normalSpaceEquivOfKer`, from that of the differentials of
`blowdown` on the pulled-back tangent bundle, since the normal bundle has the quotient topology
from that bundle; these differentials are continuous as `blowdown` is `C^1`. This needs no
bundle structure on the normal bundle, so it holds for every label of the total space.

The real embedding is the holomorphic one with scalars restricted
(`TauCeti.SmoothEmbedding.restrictScalars`), for Tau Ceti's real manifold structure
`TauCeti.ComplexManifold.isManifold_real`. Its tangent ranges are those of the holomorphic
embedding (`TauCeti.SmoothEmbedding.coe_tangentRange_restrictScalars`), and they are invariant
under the complex structure of the blowup, as for the real form of every holomorphic embedding
(`TauCeti.SmoothEmbedding.mapsTo_ofComplexManifold_tangentRange_restrictScalars`). Since
`blowdown` is holomorphic, its real differential is its complex one
(`MDifferentiableAt.mfderiv_modelWithCornersSelf_restrictScalars_apply`); so the real form of
the normal space isomorphism is built from the same differential of `blowdown`, by
`Manifold.IsImmersion.normalSpaceEquivOfKer` over `ℝ`, and it is complex linear because that
differential is. Its continuity on total spaces is checked in the same way as that of the
complex isomorphism.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §7.1,
  Lemma 7.1.1.
* [P. Griffiths, J. Harris, *Principles of Algebraic Geometry*][GriffithsHarris1978],
  Chapter 1, §4.
-/

public section

open Bundle Projectivization Filter
open scoped LinearAlgebra.Projectivization ContDiff Manifold

namespace SymplecticGeometry

namespace BlowupModel

variable {n : ℕ}

private theorem contMDiff_blowupModelTotalSpaceToFun :
    ContMDiff (𝓘(ℂ, Fin n → ℂ).prod 𝓘(ℂ, ℂ)) 𝓘(ℂ, Fin (n + 1) → ℂ) ω
      (fun q : TotalSpace ℂ (twistCore (𝕜 := ℂ) (n := n) (-1)).Fiber =>
        (⟨(q.proj, (tautologicalTwistCoreEquiv q.proj).symm q.snd),
          mem_blowupModel_iff.2 ((tautologicalTwistCoreEquiv q.proj).symm q.snd).property⟩ :
            BlowupModel n)) :=
  ((isSmoothEmbedding_blowupModel_val (n := n) (r := ω) le_top).contMDiff_iff_comp).2 <|
    (contMDiff_proj _).prodMk (contMDiff_coe_tautologicalTwistCoreEquiv_symm ω)

private theorem contMDiff_blowupModelTotalSpaceInvFun :
    ContMDiff 𝓘(ℂ, Fin (n + 1) → ℂ) (𝓘(ℂ, Fin n → ℂ).prod 𝓘(ℂ, ℂ)) ω
      (fun p : BlowupModel n =>
        (⟨p.val.1, tautologicalTwistCoreEquiv p.val.1 ⟨p.val.2, mem_blowupModel_iff.1 p.property⟩⟩ :
          TotalSpace ℂ (twistCore (𝕜 := ℂ) (n := n) (-1)).Fiber)) := by
  intro p₀
  refine contMDiffAt_totalSpace_iff.2
    ⟨(contMDiff_pr ω).contMDiffAt.congr_of_eventuallyEq
      (Eventually.of_forall fun p => (pr_def p).symm), ?_⟩
  -- In the frame of the chart `k` of `𝒪(-1)`, the image of `p` is the coordinate `k` of
  -- `p.blowdown`.
  set k := (twistCore (𝕜 := ℂ) (n := n) (-1)).indexAt p₀.val.1
  exact ((contDiff_apply ℂ (fun _ => ℂ) k).contMDiff.comp (contMDiff_blowdown ω)).contMDiffAt
    |>.congr_of_eventuallyEq (Eventually.of_forall fun p =>
      (twistCore_localTriv_tautologicalTwistCoreEquiv _ _).trans
        (congrFun (blowdown_def _).symm _))

variable (n) in
/-- **The blowup is the total space of the tautological line.** The biholomorphism from the
total space of `𝒪(-1)`, Tau Ceti's `(Projectivization.twistCore (-1)).Fiber` over `ℙ ℂ E`, onto
the model blowup `BlowupModel n`, sending a vector `a` of the fibre over `ℓ` to the point
`(ℓ, z)` of the blowup, with `z` the vector of the line `ℓ` that
`Projectivization.tautologicalTwistCoreEquiv ℓ` sends to `a`. It identifies the projection of
the blowup to `ℙ ℂ E` with the bundle projection (`pr_blowupModelTotalSpaceDiffeomorph`) and the
exceptional divisor with the zero section (`blowupModelTotalSpaceDiffeomorph_zero`).

Of the milestone below, this states that `pr` is the tautological line bundle, with the
exceptional divisor as its zero section; `blowdownDiffeomorph` states that the blowdown is a
biholomorphism off the divisor, and `normalSpaceZeroSectionEquiv` that the normal bundle of the
divisor is the tautological line.

Milestone: *Tautological line bundle and the exceptional divisor*. -/
noncomputable def blowupModelTotalSpaceDiffeomorph :
    TotalSpace ℂ (twistCore (𝕜 := ℂ) (n := n) (-1)).Fiber
      ≃ₘ^ω⟮𝓘(ℂ, Fin n → ℂ).prod 𝓘(ℂ, ℂ), 𝓘(ℂ, Fin (n + 1) → ℂ)⟯ BlowupModel n where
  toFun q := ⟨(q.proj, (tautologicalTwistCoreEquiv q.proj).symm q.snd),
    mem_blowupModel_iff.2 ((tautologicalTwistCoreEquiv q.proj).symm q.snd).property⟩
  invFun p :=
    ⟨p.val.1, tautologicalTwistCoreEquiv p.val.1 ⟨p.val.2, mem_blowupModel_iff.1 p.property⟩⟩
  left_inv q := congrArg (TotalSpace.mk q.proj) ((tautologicalTwistCoreEquiv _).apply_symm_apply _)
  right_inv _ := Subtype.ext <| Prod.ext rfl <|
    congrArg Subtype.val ((tautologicalTwistCoreEquiv _).symm_apply_apply _)
  contMDiff_toFun := contMDiff_blowupModelTotalSpaceToFun
  contMDiff_invFun := contMDiff_blowupModelTotalSpaceInvFun

theorem blowupModelTotalSpaceDiffeomorph_apply
    (q : TotalSpace ℂ (twistCore (𝕜 := ℂ) (n := n) (-1)).Fiber) :
    blowupModelTotalSpaceDiffeomorph n q =
      ⟨(q.proj, (tautologicalTwistCoreEquiv q.proj).symm q.snd),
        mem_blowupModel_iff.2 ((tautologicalTwistCoreEquiv q.proj).symm q.snd).property⟩ :=
  (rfl)

/-- The inverse of `blowupModelTotalSpaceDiffeomorph` sends a point `p` of the blowup into the
fibre of `𝒪(-1)` over `p.pr`. -/
@[simp]
theorem proj_blowupModelTotalSpaceDiffeomorph_symm (p : BlowupModel n) :
    ((blowupModelTotalSpaceDiffeomorph n).symm p).proj = p.pr :=
  (pr_def p).symm

/-- Under `blowupModelTotalSpaceDiffeomorph`, the projection `pr` of the blowup to `ℙ ℂ E` is
the bundle projection of `𝒪(-1)`. -/
@[simp]
theorem pr_blowupModelTotalSpaceDiffeomorph
    (q : TotalSpace ℂ (twistCore (𝕜 := ℂ) (n := n) (-1)).Fiber) :
    (blowupModelTotalSpaceDiffeomorph n q).pr = q.proj :=
  pr_mk _ _ _

/-- The blowdown of the image of a vector `a` of `𝒪(-1)` over `ℓ` under
`blowupModelTotalSpaceDiffeomorph` is the vector of the line `ℓ` that
`tautologicalTwistCoreEquiv ℓ` sends to `a`. -/
@[simp]
theorem blowdown_blowupModelTotalSpaceDiffeomorph
    (q : TotalSpace ℂ (twistCore (𝕜 := ℂ) (n := n) (-1)).Fiber) :
    (blowupModelTotalSpaceDiffeomorph n q).blowdown =
      (tautologicalTwistCoreEquiv q.proj).symm q.snd :=
  blowdown_mk _ _ _

/-- The inverse of `blowupModelTotalSpaceDiffeomorph` sends a point `p` of the blowup to the
vector of `𝒪(-1)` over `p.pr` that `tautologicalTwistCoreEquiv p.pr` assigns to the vector
`p.blowdown` of the line `p.pr`. -/
theorem blowupModelTotalSpaceDiffeomorph_symm_apply (p : BlowupModel n) :
    (blowupModelTotalSpaceDiffeomorph n).symm p =
      ⟨p.pr, tautologicalTwistCoreEquiv p.pr ⟨p.blowdown, p.blowdown_mem_submodule⟩⟩ := by
  refine (blowupModelTotalSpaceDiffeomorph n).injective ?_
  rw [Diffeomorph.coe_toEquiv, Diffeomorph.apply_symm_apply]
  exact ext (by simp) (by simp)

/-- `blowupModelTotalSpaceDiffeomorph` sends the zero of the fibre of `𝒪(-1)` over `ℓ` to the
point `zeroSection ℓ` of the exceptional divisor. -/
@[simp]
theorem blowupModelTotalSpaceDiffeomorph_zero (ℓ : ℙ ℂ (Fin (n + 1) → ℂ)) :
    blowupModelTotalSpaceDiffeomorph n (TotalSpace.mk' ℂ (E := (twistCore (-1)).Fiber) ℓ 0) =
      zeroSection ℓ :=
  ext (by simp) (by simp)

/-- The inverse of `blowupModelTotalSpaceDiffeomorph` sends the point `zeroSection ℓ` of the
exceptional divisor to the zero of the fibre of `𝒪(-1)` over `ℓ`. -/
@[simp]
theorem blowupModelTotalSpaceDiffeomorph_symm_zeroSection (ℓ : ℙ ℂ (Fin (n + 1) → ℂ)) :
    (blowupModelTotalSpaceDiffeomorph n).symm (zeroSection ℓ) =
      TotalSpace.mk' ℂ (E := (twistCore (-1)).Fiber) ℓ 0 := by
  rw [← blowupModelTotalSpaceDiffeomorph_zero, Diffeomorph.symm_apply_apply]

variable (n) in
/-- The zero section `zeroSection` of the model blowup `BlowupModel n`, which sends a line `ℓ` to
the point `(ℓ, 0)`, as a holomorphic embedding of `ℙ ℂ E` into `BlowupModel n`. Its image is the
exceptional divisor (`range_zeroSectionEmbedding`). -/
noncomputable def zeroSectionEmbedding :
    TauCeti.SmoothEmbedding 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) ω (ℙ ℂ (Fin (n + 1) → ℂ))
      (BlowupModel n) :=
  TauCeti.SmoothEmbedding.ofIsSmoothEmbedding zeroSection <| by
    -- Through `blowupModelTotalSpaceDiffeomorph`, `zeroSection` is the zero section of `𝒪(-1)`.
    let e := Bundle.zeroSectionEmbedding 𝓘(ℂ, Fin n → ℂ) ℂ
      (twistCore (𝕜 := ℂ) (n := n) (-1)).Fiber (n := ω) le_top
    have h : (zeroSection : ℙ ℂ (Fin (n + 1) → ℂ) → BlowupModel n) =
        blowupModelTotalSpaceDiffeomorph n ∘ e := by
      rw [Bundle.coe_zeroSectionEmbedding]
      exact funext fun ℓ => (blowupModelTotalSpaceDiffeomorph_zero ℓ).symm
    rw [h]
    exact (blowupModelTotalSpaceDiffeomorph n).isSmoothEmbedding_comp le_top e.isSmoothEmbedding

variable (n) in
/-- The underlying map of `zeroSectionEmbedding n` is `zeroSection`. -/
@[simp]
theorem coe_zeroSectionEmbedding :
    ⇑(zeroSectionEmbedding n) = (zeroSection : ℙ ℂ (Fin (n + 1) → ℂ) → BlowupModel n) :=
  TauCeti.SmoothEmbedding.coe_ofIsSmoothEmbedding _ _

variable (n) in
/-- The image of the zero section embedding `zeroSectionEmbedding n` is the exceptional
divisor. -/
theorem range_zeroSectionEmbedding :
    Set.range (zeroSectionEmbedding n) = exceptionalDivisor n := by
  rw [coe_zeroSectionEmbedding, exceptionalDivisor_eq_range]

/-- The tangent image of the zero section at `ℓ` lies in the kernel of the differential of
`blowdown` at `zeroSection ℓ`, since `blowdown` vanishes on the zero section. -/
theorem mfderiv_blowdown_comp_mfderiv_zeroSection (ℓ : ℙ ℂ (Fin (n + 1) → ℂ)) :
    (mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) blowdown (zeroSection ℓ)).comp
      (mfderiv 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) zeroSection ℓ) = 0 := by
  rw [← mfderiv_comp ℓ ((contMDiff_blowdown 1).mdifferentiableAt one_ne_zero)
    ((contMDiff_zeroSection 1).mdifferentiableAt one_ne_zero)]
  have h : (blowdown ∘ zeroSection : ℙ ℂ (Fin (n + 1) → ℂ) → Fin (n + 1) → ℂ) = fun _ => 0 :=
    funext blowdown_zeroSection
  rw [h, mfderiv_const]
  -- The two zeros are maps between the tangent spaces and between the model spaces.
  rfl

/-- Every vector `z` of the line `ℓ` is a value of the differential of `blowdown` at
`zeroSection ℓ`: it is the image of the velocity at `0` of the curve `t ↦ (ℓ, t • z)`. -/
theorem exists_mfderiv_blowdown_zeroSection_eq (ℓ : ℙ ℂ (Fin (n + 1) → ℂ))
    {z : Fin (n + 1) → ℂ} (hz : z ∈ ℓ.submodule) :
    ∃ v : TangentSpace 𝓘(ℂ, Fin (n + 1) → ℂ) (zeroSection ℓ),
      mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) blowdown (zeroSection ℓ) v = z := by
  let γ : ℂ → BlowupModel n := fun t =>
    ⟨(ℓ, t • z), mem_blowupModel_iff.2 (ℓ.submodule.smul_mem t hz)⟩
  have hγ : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) 1 γ :=
    ((isSmoothEmbedding_blowupModel_val (n := n) (r := 1) le_rfl).contMDiff_iff_comp).2 <|
      contMDiff_const.prodMk (contDiff_id.smul contDiff_const).contMDiff
  have hγ₀ : γ 0 = zeroSection ℓ := ext (by simp [γ]) (by simp [γ])
  have hcomp : (blowdown ∘ γ) = fun t : ℂ => t • z := funext fun t => blowdown_mk _ _ _
  have hz' : HasFDerivAt (fun t : ℂ => t • z) ((ContinuousLinearMap.id ℂ ℂ).smulRight z) 0 :=
    (hasFDerivAt_id (0 : ℂ)).smul_const z
  have hd : mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) (blowdown ∘ γ) 0 (1 : ℂ) = z := by
    rw [hcomp, (hasMFDerivAt_iff_hasFDerivAt.2 hz').mfderiv]
    -- `ContinuousLinearMap.smulRight_apply` does not rewrite here, as the argument `1` lives in
    -- `TangentSpace 𝓘(ℂ, ℂ) 0`.
    exact one_smul ℂ z
  rw [mfderiv_comp (0 : ℂ) ((contMDiff_blowdown 1).mdifferentiableAt one_ne_zero)
    (hγ.mdifferentiableAt one_ne_zero), hγ₀] at hd
  exact ⟨_, hd⟩

/-- The differential of `blowdown` at `zeroSection ℓ` is not zero: its image has positive
dimension. -/
private theorem one_le_finrank_range_mfderiv_blowdown (ℓ : ℙ ℂ (Fin (n + 1) → ℂ)) :
    1 ≤ Module.finrank ℂ (LinearMap.range
      (mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) blowdown
        (zeroSection ℓ)).toLinearMap) := by
  have : Module.Finite ℂ (TangentSpace 𝓘(ℂ, Fin (n + 1) → ℂ) (zeroSection ℓ)) :=
    inferInstanceAs (Module.Finite ℂ (Fin (n + 1) → ℂ))
  obtain ⟨v, hv⟩ := exists_mfderiv_blowdown_zeroSection_eq ℓ (ℓ.submodule_eq ▸
    Submodule.mem_span_singleton_self ℓ.rep)
  exact Module.finrank_pos_iff_exists_ne_zero.2
    ⟨⟨_, v, rfl⟩, fun h => ℓ.rep_ne_zero (hv ▸ congrArg Subtype.val h)⟩

variable (n) in
/-- The tangent image of the zero section at `ℓ` has dimension `n`. -/
theorem finrank_range_mfderiv_zeroSection (ℓ : ℙ ℂ (Fin (n + 1) → ℂ)) :
    Module.finrank ℂ (LinearMap.range
      (mfderiv 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) zeroSection ℓ).toLinearMap) = n := by
  have hi := (zeroSectionEmbedding n).isImmersion.mfderiv_injective WithTop.top_ne_zero ℓ
  rw [coe_zeroSectionEmbedding] at hi
  rw [LinearMap.finrank_range_of_inj hi]
  exact Module.finrank_fin_fun ℂ

/-- The dimensions of the image and of the kernel of the differential of `blowdown` at
`zeroSection ℓ` add up to `n + 1`. -/
theorem finrank_range_add_finrank_ker_mfderiv_blowdown (ℓ : ℙ ℂ (Fin (n + 1) → ℂ)) :
    Module.finrank ℂ (LinearMap.range
        (mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) blowdown
          (zeroSection ℓ)).toLinearMap) +
      Module.finrank ℂ (LinearMap.ker
        (mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) blowdown
          (zeroSection ℓ)).toLinearMap) =
      n + 1 :=
  (LinearMap.finrank_range_add_finrank_ker
    (mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) blowdown
      (zeroSection ℓ)).toLinearMap).trans (Module.finrank_fin_fun ℂ)

/-- The kernel of the differential of `blowdown` at the point `zeroSection ℓ` of the exceptional
divisor is the tangent image of the zero section. -/
theorem ker_mfderiv_blowdown_zeroSection (ℓ : ℙ ℂ (Fin (n + 1) → ℂ)) :
    LinearMap.ker
        (mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) blowdown
          (zeroSection ℓ)).toLinearMap =
      LinearMap.range
        (mfderiv 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) zeroSection ℓ).toLinearMap := by
  have hle : LinearMap.range
        (mfderiv 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) zeroSection ℓ).toLinearMap ≤
      LinearMap.ker
        (mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) blowdown
          (zeroSection ℓ)).toLinearMap := by
    rintro _ ⟨v, rfl⟩
    exact congrArg (· v) (mfderiv_blowdown_comp_mfderiv_zeroSection ℓ)
  have : FiniteDimensional ℂ (TangentSpace 𝓘(ℂ, Fin (n + 1) → ℂ) (zeroSection ℓ)) :=
    inferInstanceAs (FiniteDimensional ℂ (Fin (n + 1) → ℂ))
  have hrk := finrank_range_add_finrank_ker_mfderiv_blowdown ℓ
  have h₁ := one_le_finrank_range_mfderiv_blowdown ℓ
  have h₂ := finrank_range_mfderiv_zeroSection n ℓ
  exact (Submodule.eq_of_le_of_finrank_le hle (by omega)).symm

/-- The image of the differential of `blowdown` at the point `zeroSection ℓ` of the exceptional
divisor is the line `ℓ`. -/
theorem range_mfderiv_blowdown_zeroSection (ℓ : ℙ ℂ (Fin (n + 1) → ℂ)) :
    LinearMap.range
        (mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) blowdown
          (zeroSection ℓ)).toLinearMap =
      ℓ.submodule := by
  have hle : ℓ.submodule ≤ LinearMap.range
      (mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) blowdown
        (zeroSection ℓ)).toLinearMap := fun z hz =>
    (exists_mfderiv_blowdown_zeroSection_eq ℓ hz).imp fun _ h => h
  have : FiniteDimensional ℂ (TangentSpace 𝓘(ℂ, Fin (n + 1) → ℂ) (zeroSection ℓ)) :=
    inferInstanceAs (FiniteDimensional ℂ (Fin (n + 1) → ℂ))
  have hrk := finrank_range_add_finrank_ker_mfderiv_blowdown ℓ
  rw [ker_mfderiv_blowdown_zeroSection, finrank_range_mfderiv_zeroSection n ℓ] at hrk
  have h₁ : Module.finrank ℂ (LinearMap.range
      (mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) blowdown
        (zeroSection ℓ)).toLinearMap) = 1 := by
    omega
  -- The instance is given by hand: instance search does not see the range, a submodule of a
  -- tangent space, as a submodule of `Fin (n + 1) → ℂ`.
  exact (@Submodule.eq_of_le_of_finrank_le _ _ _ _ _ _ _ (LinearMap.finiteDimensional_range _) hle
    (h₁.trans (Projectivization.finrank_submodule ℓ).symm).le).symm

/-- The differential of `blowdown` at the point `zeroSection ℓ` of the exceptional divisor takes
its values in the line `ℓ`. -/
theorem mfderiv_blowdown_zeroSection_mem (ℓ : ℙ ℂ (Fin (n + 1) → ℂ))
    (v : TangentSpace 𝓘(ℂ, Fin (n + 1) → ℂ) (zeroSection ℓ)) :
    mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) blowdown (zeroSection ℓ) v ∈
      ℓ.submodule :=
  range_mfderiv_blowdown_zeroSection ℓ ▸ LinearMap.mem_range_self _ v

/-- The differential of `blowdown` at `zeroSection ℓ`, as a map into the line `ℓ`. -/
private noncomputable def mfderivBlowdownZeroSection (ℓ : ℙ ℂ (Fin (n + 1) → ℂ)) :
    TangentSpace 𝓘(ℂ, Fin (n + 1) → ℂ) (zeroSectionEmbedding n ℓ) →L[ℂ]
      Projectivization.Tautological ℂ (Fin (n + 1) → ℂ) ℓ :=
  (mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) blowdown (zeroSection ℓ)).codRestrict
    ℓ.submodule (mfderiv_blowdown_zeroSection_mem ℓ)

private theorem coe_mfderivBlowdownZeroSection_apply (ℓ : ℙ ℂ (Fin (n + 1) → ℂ))
    (v : TangentSpace 𝓘(ℂ, Fin (n + 1) → ℂ) (zeroSectionEmbedding n ℓ)) :
    (mfderivBlowdownZeroSection ℓ v : Fin (n + 1) → ℂ) =
      mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) blowdown (zeroSection ℓ) v :=
  (rfl)

private theorem mfderivBlowdownZeroSection_eq_zero_iff (ℓ : ℙ ℂ (Fin (n + 1) → ℂ))
    (v : TangentSpace 𝓘(ℂ, Fin (n + 1) → ℂ) (zeroSectionEmbedding n ℓ)) :
    mfderivBlowdownZeroSection ℓ v = 0 ↔
      v ∈ (zeroSectionEmbedding n).isImmersion.tangentRange ℓ WithTop.top_ne_zero := by
  have h := SetLike.ext_iff.1 (ker_mfderiv_blowdown_zeroSection ℓ) v
  rw [← Subtype.coe_inj, coe_mfderivBlowdownZeroSection_apply, ZeroMemClass.coe_zero,
    Manifold.IsImmersion.mem_tangentRange_iff, coe_zeroSectionEmbedding]
  -- `h` is the goal, with membership in the kernel and the image of a linear map unfolded.
  exact h

variable (n) in
/-- The normal space of the zero section `zeroSectionEmbedding n` at `ℓ` is a complex line. -/
theorem finrank_normalSpace_zeroSectionEmbedding (ℓ : ℙ ℂ (Fin (n + 1) → ℂ)) :
    Module.finrank ℂ ((zeroSectionEmbedding n).isImmersion.NormalSpace ℓ WithTop.top_ne_zero) =
        1 := by
  have h₁ : Module.finrank ℂ
      (TangentSpace 𝓘(ℂ, Fin (n + 1) → ℂ) (zeroSectionEmbedding n ℓ)) = n + 1 :=
    Module.finrank_fin_fun ℂ
  have h₂ : Module.finrank ℂ (TangentSpace 𝓘(ℂ, Fin n → ℂ) ℓ) = n := Module.finrank_fin_fun ℂ
  rw [Manifold.IsImmersion.finrank_normalSpace, h₁, h₂]
  omega

variable (n) in
/-- **The normal bundle of the exceptional divisor is the tautological line.** The
complex-linear isomorphism from the normal space at `ℓ` of the zero section
`zeroSectionEmbedding n` of the model blowup, Tau Ceti's `Manifold.IsImmersion.NormalSpace`, onto
the line `ℓ`, the fibre `Projectivization.Tautological ℂ E ℓ` of the tautological line. It sends the
class of a tangent vector `v` at `zeroSection ℓ` to the differential of `blowdown` at
`zeroSection ℓ` applied to `v` (`normalSpaceZeroSectionEquiv_normalClass`).

Of the milestone *Tautological line bundle and the exceptional divisor*, this states that the
normal space of the exceptional divisor at each of its points is the corresponding fibre of the
tautological line. -/
noncomputable def normalSpaceZeroSectionEquiv (ℓ : ℙ ℂ (Fin (n + 1) → ℂ)) :
    (zeroSectionEmbedding n).isImmersion.NormalSpace ℓ WithTop.top_ne_zero ≃L[ℂ]
      Projectivization.Tautological ℂ (Fin (n + 1) → ℂ) ℓ :=
  (zeroSectionEmbedding n).isImmersion.normalSpaceEquivOfKer ℓ WithTop.top_ne_zero
    (mfderivBlowdownZeroSection ℓ) (mfderivBlowdownZeroSection_eq_zero_iff ℓ)
    ((finrank_normalSpace_zeroSectionEmbedding n ℓ).trans
      (Projectivization.finrank_submodule ℓ).symm)

/-- `normalSpaceZeroSectionEquiv n ℓ` sends the normal class of a tangent vector `v` at
`zeroSection ℓ` to the differential of `blowdown` at `zeroSection ℓ` applied to `v`, as a vector
of the line `ℓ`. -/
@[simp]
theorem normalSpaceZeroSectionEquiv_normalClass (ℓ : ℙ ℂ (Fin (n + 1) → ℂ))
    (v : TangentSpace 𝓘(ℂ, Fin (n + 1) → ℂ) (zeroSectionEmbedding n ℓ)) :
    normalSpaceZeroSectionEquiv n ℓ
        ((zeroSectionEmbedding n).isImmersion.normalClass ℓ WithTop.top_ne_zero v) =
      ⟨mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) blowdown (zeroSection ℓ) v,
        mfderiv_blowdown_zeroSection_mem ℓ v⟩ := by
  rw [normalSpaceZeroSectionEquiv, Manifold.IsImmersion.normalSpaceEquivOfKer_normalClass]
  exact Subtype.ext (coe_mfderivBlowdownZeroSection_apply ℓ v)

/-- The inverse of `normalSpaceZeroSectionEquiv n ℓ` sends the differential of `blowdown` at
`zeroSection ℓ` applied to a tangent vector `v` to the normal class of `v`. -/
theorem normalSpaceZeroSectionEquiv_symm_apply (ℓ : ℙ ℂ (Fin (n + 1) → ℂ))
    (v : TangentSpace 𝓘(ℂ, Fin (n + 1) → ℂ) (zeroSectionEmbedding n ℓ)) :
    (normalSpaceZeroSectionEquiv n ℓ).symm
        ⟨mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) blowdown (zeroSection ℓ) v,
          mfderiv_blowdown_zeroSection_mem ℓ v⟩ =
      (zeroSectionEmbedding n).isImmersion.normalClass ℓ WithTop.top_ne_zero v := by
  rw [ContinuousLinearEquiv.symm_apply_eq, normalSpaceZeroSectionEquiv_normalClass]

/-- The isomorphisms `normalSpaceZeroSectionEquiv n ℓ` form a continuous map from the total
space of the normal bundle of the zero section to the total space of the tautological line
`Projectivization.Tautological ℂ E` over `ℙ ℂ E`. The normal bundle has Tau Ceti's topology
`SmoothEmbedding.instTopologicalSpaceNormalBundle`, the quotient topology from the pulled-back
ambient tangent bundle, for which `SmoothEmbedding.normalSpaceFiberBundle` is a fibre bundle
structure. The label `K` of the total space does not change that topology. -/
theorem continuous_normalSpaceZeroSectionEquiv {K : Type*} :
    Continuous fun p : TotalSpace K
        (fun ℓ => (zeroSectionEmbedding n).isImmersion.NormalSpace ℓ WithTop.top_ne_zero) =>
      (⟨p.proj, normalSpaceZeroSectionEquiv n p.proj p.snd⟩ :
        TotalSpace ℂ (Projectivization.Tautological ℂ (Fin (n + 1) → ℂ))) := by
  -- On the pulled-back tangent bundle, the differentials of `blowdown` along the zero section
  -- form a continuous map, as `blowdown` is `C^1`.
  have hgs : Continuous fun p : TotalSpace (Fin (n + 1) → ℂ)
      ((zeroSectionEmbedding n : ℙ ℂ (Fin (n + 1) → ℂ) → BlowupModel n) *ᵖ
        (TangentSpace 𝓘(ℂ, Fin (n + 1) → ℂ))) =>
      TotalSpace.mk' ℂ (E := Projectivization.Tautological ℂ (Fin (n + 1) → ℂ)) p.proj
        (mfderivBlowdownZeroSection p.proj p.snd) := by
    refine continuous_totalSpace_tautological_iff.2 ⟨FiberBundle.continuous_proj _ _, ?_⟩
    refine (Pullback.continuous_mfderiv_apply (zeroSectionEmbedding n) (contMDiff_blowdown 1)
      le_rfl).congr fun p => ?_
    -- The differential of `blowdown` is taken at `zeroSectionEmbedding n p.proj`, and the one in
    -- `mfderivBlowdownZeroSection` at `zeroSection p.proj`, the same point.
    exact (congrArg (fun x => mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) blowdown x p.snd)
      (congrFun (coe_zeroSectionEmbedding n) p.proj)).trans
        (coe_mfderivBlowdownZeroSection_apply p.proj p.snd).symm
  -- On ambient representatives, the isomorphisms are the differentials of `blowdown`.
  unfold normalSpaceZeroSectionEquiv
  exact TauCeti.SmoothEmbedding.continuous_normalSpaceEquivOfKer _ WithTop.top_ne_zero _ _ _ hgs

/-! ### The real form -/

section Real

open scoped TauCeti.ComplexManifold

variable {hn : (∞ : ℕ∞ω) ≠ 0}

variable (n) in
/-- The zero section `zeroSection` of the model blowup `BlowupModel n` as a smooth embedding of
the underlying real manifolds, modelled on `𝓘(ℝ, Fin n → ℂ)` and `𝓘(ℝ, Fin (n + 1) → ℂ)`: the
real form of the holomorphic embedding `zeroSectionEmbedding n`. -/
noncomputable def zeroSectionRealEmbedding :
    TauCeti.SmoothEmbedding 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ (ℙ ℂ (Fin (n + 1) → ℂ))
      (BlowupModel n) :=
  (zeroSectionEmbedding n).restrictScalars ℝ le_top ENat.LEInfty.out

variable (n) in
theorem zeroSectionRealEmbedding_def :
    zeroSectionRealEmbedding n =
      (zeroSectionEmbedding n).restrictScalars ℝ le_top ENat.LEInfty.out :=
  (rfl)

variable (n) in
/-- The underlying map of `zeroSectionRealEmbedding n` is `zeroSection`. -/
@[simp]
theorem coe_zeroSectionRealEmbedding :
    ⇑(zeroSectionRealEmbedding n) = (zeroSection : ℙ ℂ (Fin (n + 1) → ℂ) → BlowupModel n) := by
  rw [zeroSectionRealEmbedding_def, TauCeti.SmoothEmbedding.coe_restrictScalars,
    coe_zeroSectionEmbedding]

/-- The tangent images of the real zero section `zeroSectionRealEmbedding n` are invariant under
the almost complex structure of the complex manifold `BlowupModel n`, which is multiplication by
`Complex.I`. -/
theorem mapsTo_ofComplexManifold_tangentRange_zeroSectionRealEmbedding
    (ℓ : ℙ ℂ (Fin (n + 1) → ℂ)) :
    Set.MapsTo
      (TauCeti.SmoothAlmostComplexStructure.ofComplexManifold (Fin (n + 1) → ℂ) (BlowupModel n)
        (zeroSectionRealEmbedding n ℓ))
      ((zeroSectionRealEmbedding n).isImmersion.tangentRange ℓ hn)
      ((zeroSectionRealEmbedding n).isImmersion.tangentRange ℓ hn) := by
  rw [zeroSectionRealEmbedding_def]
  exact (zeroSectionEmbedding n).mapsTo_ofComplexManifold_tangentRange_restrictScalars le_top
    ENat.LEInfty.out hn ℓ

/-- The differential of `blowdown` at `zeroSection ℓ`, as a real-linear map into the line `ℓ`. -/
private noncomputable def mfderivBlowdownZeroSectionReal (ℓ : ℙ ℂ (Fin (n + 1) → ℂ)) :
    TangentSpace 𝓘(ℝ, Fin (n + 1) → ℂ) (zeroSectionRealEmbedding n ℓ) →L[ℝ]
      Projectivization.Tautological ℂ (Fin (n + 1) → ℂ) ℓ :=
  (mfderivBlowdownZeroSection ℓ).restrictScalars ℝ

private theorem mfderivBlowdownZeroSectionReal_apply (ℓ : ℙ ℂ (Fin (n + 1) → ℂ))
    (v : TangentSpace 𝓘(ℝ, Fin (n + 1) → ℂ) (zeroSectionRealEmbedding n ℓ)) :
    mfderivBlowdownZeroSectionReal ℓ v = mfderivBlowdownZeroSection ℓ v :=
  (rfl)

private theorem mfderivBlowdownZeroSectionReal_eq_zero_iff (ℓ : ℙ ℂ (Fin (n + 1) → ℂ))
    (v : TangentSpace 𝓘(ℝ, Fin (n + 1) → ℂ) (zeroSectionRealEmbedding n ℓ)) :
    mfderivBlowdownZeroSectionReal ℓ v = 0 ↔
      v ∈ (zeroSectionRealEmbedding n).isImmersion.tangentRange ℓ hn := by
  rw [← SetLike.mem_coe, zeroSectionRealEmbedding_def,
    TauCeti.SmoothEmbedding.coe_tangentRange_restrictScalars _ _ _ _ _ WithTop.top_ne_zero]
  exact (congrArg (· = 0) (mfderivBlowdownZeroSectionReal_apply ℓ v)).to_iff.trans
    (mfderivBlowdownZeroSection_eq_zero_iff ℓ v)

variable (n hn) in
/-- The normal space of the real zero section `zeroSectionRealEmbedding n` at `ℓ` is a real
plane. -/
theorem finrank_normalSpace_zeroSectionRealEmbedding (ℓ : ℙ ℂ (Fin (n + 1) → ℂ)) :
    Module.finrank ℝ ((zeroSectionRealEmbedding n).isImmersion.NormalSpace ℓ hn) = 2 := by
  rw [Manifold.IsImmersion.finrank_normalSpace]
  -- The tangent spaces are `Fin (n + 1) → ℂ` and `Fin n → ℂ`.
  exact (Complex.finrank_real_eq_finrank_pi_succ_sub n).symm.trans Complex.finrank_real_complex

variable (n hn) in
/-- **The real normal bundle of the exceptional divisor is the tautological line.** The real
form of `normalSpaceZeroSectionEquiv n ℓ`: the real-linear isomorphism from the normal space at
`ℓ` of the real zero section `zeroSectionRealEmbedding n` onto the line `ℓ`, which sends the
class of a tangent vector `v` at `zeroSection ℓ` to the differential of `blowdown` at
`zeroSection ℓ` applied to `v` (`normalSpaceZeroSectionRealEquiv_normalClass`). It agrees with
`normalSpaceZeroSectionEquiv n ℓ` on classes
(`normalSpaceZeroSectionRealEquiv_normalClass_eq`), and carries the complex structure that the
almost complex structure of the blowup induces on the normal bundle to multiplication by
`Complex.I`
(`normalSpaceZeroSectionRealEquiv_contMDiffNormalComplexStructure`). -/
noncomputable def normalSpaceZeroSectionRealEquiv (ℓ : ℙ ℂ (Fin (n + 1) → ℂ)) :
    (zeroSectionRealEmbedding n).isImmersion.NormalSpace ℓ hn ≃L[ℝ]
      Projectivization.Tautological ℂ (Fin (n + 1) → ℂ) ℓ :=
  (zeroSectionRealEmbedding n).isImmersion.normalSpaceEquivOfKer ℓ hn
      (mfderivBlowdownZeroSectionReal ℓ)
    (mfderivBlowdownZeroSectionReal_eq_zero_iff ℓ)
    ((finrank_normalSpace_zeroSectionRealEmbedding n hn ℓ).trans
      ((Projectivization.finrank_submodule_of_isScalarTower ℓ).trans
        Complex.finrank_real_complex).symm)

/-- `normalSpaceZeroSectionRealEquiv n hn ℓ` sends the normal class of a tangent vector `v` at
`zeroSection ℓ` to the differential of `blowdown` at `zeroSection ℓ` applied to `v`, as a vector
of the line `ℓ`. -/
@[simp]
theorem normalSpaceZeroSectionRealEquiv_normalClass (ℓ : ℙ ℂ (Fin (n + 1) → ℂ))
    (v : TangentSpace 𝓘(ℝ, Fin (n + 1) → ℂ) (zeroSectionRealEmbedding n ℓ)) :
    normalSpaceZeroSectionRealEquiv n hn ℓ
        ((zeroSectionRealEmbedding n).isImmersion.normalClass ℓ hn v) =
      ⟨mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) blowdown (zeroSection ℓ) v,
        mfderiv_blowdown_zeroSection_mem ℓ v⟩ := by
  rw [normalSpaceZeroSectionRealEquiv,
    Manifold.IsImmersion.normalSpaceEquivOfKer_normalClass, mfderivBlowdownZeroSectionReal_apply]
  exact Subtype.ext (coe_mfderivBlowdownZeroSection_apply ℓ v)

/-- `normalSpaceZeroSectionRealEquiv n hn ℓ` and `normalSpaceZeroSectionEquiv n ℓ` agree on the
classes of a tangent vector `v` at `zeroSection ℓ` in the real and in the complex normal space. -/
theorem normalSpaceZeroSectionRealEquiv_normalClass_eq (ℓ : ℙ ℂ (Fin (n + 1) → ℂ))
    (v : TangentSpace 𝓘(ℝ, Fin (n + 1) → ℂ) (zeroSectionRealEmbedding n ℓ)) :
    normalSpaceZeroSectionRealEquiv n hn ℓ ((zeroSectionRealEmbedding n).isImmersion.normalClass ℓ
        hn v) =
      normalSpaceZeroSectionEquiv n ℓ
        ((zeroSectionEmbedding n).isImmersion.normalClass ℓ WithTop.top_ne_zero v) :=
  (normalSpaceZeroSectionRealEquiv_normalClass ℓ v).trans
    (normalSpaceZeroSectionEquiv_normalClass ℓ v).symm

/-- The inverse of `normalSpaceZeroSectionRealEquiv n hn ℓ` sends the differential of `blowdown`
at `zeroSection ℓ` applied to a tangent vector `v` to the normal class of `v` in the real normal
space. -/
theorem normalSpaceZeroSectionRealEquiv_symm_apply (ℓ : ℙ ℂ (Fin (n + 1) → ℂ))
    (v : TangentSpace 𝓘(ℝ, Fin (n + 1) → ℂ) (zeroSectionRealEmbedding n ℓ)) :
    (normalSpaceZeroSectionRealEquiv n hn ℓ).symm
        ⟨mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) blowdown (zeroSection ℓ) v,
          mfderiv_blowdown_zeroSection_mem ℓ v⟩ =
      (zeroSectionRealEmbedding n).isImmersion.normalClass ℓ hn v := by
  rw [ContinuousLinearEquiv.symm_apply_eq, normalSpaceZeroSectionRealEquiv_normalClass]

/-- The fibre of the tautological line over the line `ℓ` spanned by a nonzero `v`, as the lift
`curveLift (· • v)` of the line `t ↦ t • v`, crosses the exceptional divisor at `t = 0` with
velocity `v`: the real derivative of the lift at `0` applied to `c`, sent to the normal space
of the real zero section at `ℓ` and then to the tautological line by
`normalSpaceZeroSectionRealEquiv n hn ℓ`, is `c • v`. -/
theorem normalSpaceZeroSectionRealEquiv_normalClassL_mfderiv_curveLift_smul
    {v : Fin (n + 1) → ℂ} (hv : v ≠ 0) (c : ℂ) :
    normalSpaceZeroSectionRealEquiv n hn (mk ℂ v hv)
        ((zeroSectionRealEmbedding n).isImmersion.normalClassL (mk ℂ v hv) hn
          (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) (curveLift (· • v)) 0 c)) =
      ⟨c • v, by
        rw [submodule_mk]
        exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self v)⟩ := by
  refine (congrArg _ (Manifold.IsImmersion.normalClassL_apply _ _ _ _)).trans
    ((normalSpaceZeroSectionRealEquiv_normalClass _ _).trans (Subtype.ext ?_))
  dsimp only
  -- The chain rule at the point `curveLift (· • v) 0`, which is `zeroSection ℓ`.
  have key : mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) blowdown
      (curveLift (· • v) (0 : ℂ))
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) (curveLift (· • v)) 0 c) =
        (c • v : Fin (n + 1) → ℂ) :=
    (((contMDiff_blowdown 1).mdifferentiable one_ne_zero
    (curveLift (· • v) (0 : ℂ))).mfderiv_modelWithCornersSelf_restrictScalars_apply ℝ
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) (curveLift (· • v)) 0 c)).symm.trans
    ((mfderiv_blowdown_mfderiv_curveLift (by fun_prop)
      ((contMDiff_curveLift_smul_real (r := 1) hv).mdifferentiable one_ne_zero 0) c).trans
      (congrArg (c • ·) (by simp [deriv_smul_const] : deriv (· • v) (0 : ℂ) = v)))
  exact curveLift_smul_zero hv ▸ key

/-- **The complex structure of the normal bundle of the exceptional divisor is multiplication by
`Complex.I` on the tautological line.** Under `normalSpaceZeroSectionRealEquiv n hn ℓ`, the complex
structure that the almost complex structure of the complex manifold `BlowupModel n` induces on
the normal bundle of the real zero section, `SmoothEmbedding.contMDiffNormalComplexStructure`, is
multiplication by `Complex.I` on the line `ℓ`. -/
theorem normalSpaceZeroSectionRealEquiv_contMDiffNormalComplexStructure {P : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (hdim : Module.finrank ℝ P =
      Module.finrank ℝ (Fin (n + 1) → ℂ) - Module.finrank ℝ (Fin n → ℂ))
    (ℓ : ℙ ℂ (Fin (n + 1) → ℂ)) (v : (zeroSectionRealEmbedding n).isImmersion.NormalSpace ℓ hn) :
    letI := (zeroSectionRealEmbedding n).normalSpaceFiberBundle hn hdim
    letI := (zeroSectionRealEmbedding n).normalSpaceVectorBundle hn hdim
    normalSpaceZeroSectionRealEquiv n hn ℓ
        ((zeroSectionRealEmbedding n).contMDiffNormalComplexStructure hdim
          (TauCeti.SmoothAlmostComplexStructure.ofComplexManifold (Fin (n + 1) → ℂ)
            (BlowupModel n))
          mapsTo_ofComplexManifold_tangentRange_zeroSectionRealEmbedding ℓ v) =
      Complex.I • normalSpaceZeroSectionRealEquiv n hn ℓ v := by
  let := (zeroSectionRealEmbedding n).normalSpaceFiberBundle hn hdim
  let := (zeroSectionRealEmbedding n).normalSpaceVectorBundle hn hdim
  obtain ⟨w, rfl⟩ := (zeroSectionRealEmbedding n).isImmersion.normalClass_surjective ℓ hn v
  rw [TauCeti.SmoothEmbedding.contMDiffNormalComplexStructure_apply,
    TauCeti.SmoothEmbedding.normalComplexStructureAt_normalClass
      (mapsTo_ofComplexManifold_tangentRange_zeroSectionRealEmbedding ℓ),
    TauCeti.SmoothAlmostComplexStructure.ofComplexManifold_apply (E := Fin (n + 1) → ℂ)
      (M := BlowupModel n) _ w,
    normalSpaceZeroSectionRealEquiv_normalClass]
  refine (normalSpaceZeroSectionRealEquiv_normalClass ℓ _).trans (Subtype.ext ?_)
  rw [Submodule.coe_smul]
  exact ((mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) blowdown
    (zeroSection ℓ)).map_smul Complex.I w)

variable (hn) in
/-- The isomorphisms `normalSpaceZeroSectionRealEquiv n hn ℓ` form a continuous map from the total
space of the normal bundle of the real zero section to the total space of the tautological line
`Projectivization.Tautological ℂ E` over `ℙ ℂ E`. The normal bundle has Tau Ceti's topology
`SmoothEmbedding.instTopologicalSpaceNormalBundle`, the quotient topology from the pulled-back
ambient tangent bundle, for which `SmoothEmbedding.normalSpaceFiberBundle` is a fibre bundle
structure. The label `K` of the total space does not change that topology. -/
theorem continuous_normalSpaceZeroSectionRealEquiv {K : Type*} :
    Continuous fun p : TotalSpace K
        (fun ℓ => (zeroSectionRealEmbedding n).isImmersion.NormalSpace ℓ hn) =>
      (⟨p.proj, normalSpaceZeroSectionRealEquiv n hn p.proj p.snd⟩ :
        TotalSpace ℂ (Projectivization.Tautological ℂ (Fin (n + 1) → ℂ))) := by
  -- On the pulled-back real tangent bundle, the real differentials of `blowdown` along the zero
  -- section form a continuous map, as `blowdown` is `C^1`.
  have hgs : Continuous fun p : TotalSpace (Fin (n + 1) → ℂ)
      ((zeroSectionRealEmbedding n : ℙ ℂ (Fin (n + 1) → ℂ) → BlowupModel n) *ᵖ
        (TangentSpace 𝓘(ℝ, Fin (n + 1) → ℂ))) =>
      TotalSpace.mk' ℂ (E := Projectivization.Tautological ℂ (Fin (n + 1) → ℂ)) p.proj
        (mfderivBlowdownZeroSectionReal p.proj p.snd) := by
    refine continuous_totalSpace_tautological_iff.2 ⟨FiberBundle.continuous_proj _ _, ?_⟩
    refine (Pullback.continuous_mfderiv_apply (zeroSectionRealEmbedding n)
      ((contMDiff_blowdown 1).restrictScalars' ℝ) le_rfl).congr fun p => ?_
    -- The real differential is taken at `zeroSectionRealEmbedding n p.proj`, and the complex
    -- differential in `mfderivBlowdownZeroSection` at `zeroSection p.proj`, the same point; the
    -- two differentials agree, as `blowdown` is holomorphic.
    refine (congrArg
      (fun x => mfderiv 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) blowdown x p.snd)
      (congrFun (coe_zeroSectionRealEmbedding n) p.proj)).trans ?_
    exact (((contMDiff_blowdown 1).mdifferentiableAt
      one_ne_zero).mfderiv_modelWithCornersSelf_restrictScalars_apply ℝ p.snd).trans
        (coe_mfderivBlowdownZeroSection_apply p.proj p.snd).symm
  -- On ambient representatives, the isomorphisms are the real differentials of `blowdown`.
  unfold normalSpaceZeroSectionRealEquiv
  exact TauCeti.SmoothEmbedding.continuous_normalSpaceEquivOfKer _ hn _ _ _ hgs

end Real

end BlowupModel

end SymplecticGeometry

end
