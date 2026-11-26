/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Complex.Blowup.Model
public import SymplecticGeometry.Geometry.Manifold.Projectivization.Tautological
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.Quotient
import TauCeti.Geometry.Manifold.SmoothEmbedding.LeftInverse

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
  `SymplecticGeometry.BlowupModel.mfderiv_blowdown_zeroSection_mem` with
  `SymplecticGeometry.BlowupModel.exists_mfderiv_blowdown_zeroSection_eq`: its image is the line
  `ℓ`.
* `SymplecticGeometry.BlowupModel.normalSpaceZeroSectionEquiv n ℓ`: the complex-linear isomorphism
  from Tau Ceti's normal space `SmoothEmbedding.NormalSpace` of `zeroSectionEmbedding n` at `ℓ`
  onto the fibre `Projectivization.Tautological ℂ E ℓ` of the tautological line, induced by that
  differential (`SymplecticGeometry.BlowupModel.coe_normalSpaceZeroSectionEquiv_normalClass`),
  and `SymplecticGeometry.BlowupModel.continuous_normalSpaceZeroSectionEquiv`: it is continuous
  on total spaces, for Tau Ceti's bundle structure `SmoothEmbedding.normalSpaceFiberBundle` on the
  normal bundle.

## Implementation notes

The map into the blowup is shown holomorphic through the embedding of the blowup into
`ℙ ℂ E × E` (`BlowupModel.isSmoothEmbedding_blowupModel_val`), whose second component is
holomorphic by `Projectivization.contMDiff_coe_tautologicalTwistCoreEquiv_symm`. For the
inverse, in the frame of the chart `k` of `𝒪(-1)` the image of `(ℓ, z)` has the coordinate `z k`
(`Projectivization.twistCore_localTriv_tautologicalTwistCoreEquiv`), a coordinate of the
holomorphic map `BlowupModel.blowdown`.

The zero section is holomorphic as the image under `blowupModelTotalSpaceDiffeomorph` of the zero
section of `𝒪(-1)`, and an embedding by Tau Ceti's
`ContMDiff.isSmoothEmbedding_of_leftInverse`, since `BlowupModel.pr` is a holomorphic left
inverse of it.

The differential of `blowdown` at `zeroSection ℓ` vanishes on the tangent image of the zero
section, of dimension `n`, since `blowdown` vanishes on the zero section, and its image contains
`ℓ`, through the curves `t ↦ (ℓ, t • z)`; by rank–nullity in dimension `n + 1`, both inclusions
are equalities. Tau Ceti's `SmoothEmbedding.normalSpaceEquivOfKer` then gives the isomorphism of
the normal space with `ℓ`. Its continuity on total spaces reduces, by Tau Ceti's
`SmoothEmbedding.contMDiff_normalBundle_iff`, to that of the tangent map of `blowdown`, as in the
library's `SmoothEmbedding.contMDiffNormalComplexStructure`.

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
    -- Through `blowupModelTotalSpaceDiffeomorph`, `zeroSection` is the zero section of `𝒪(-1)`,
    -- and `pr` is a holomorphic left inverse of it.
    have h : (zeroSection : ℙ ℂ (Fin (n + 1) → ℂ) → BlowupModel n) =
        blowupModelTotalSpaceDiffeomorph n ∘ Bundle.zeroSection ℂ (twistCore (-1)).Fiber :=
      funext fun ℓ => (blowupModelTotalSpaceDiffeomorph_zero ℓ).symm
    refine ContMDiff.isSmoothEmbedding_of_leftInverse ?_ le_top (contMDiff_pr 1) pr_zeroSection
    rw [h]
    exact (blowupModelTotalSpaceDiffeomorph n).contMDiff.comp
      (Bundle.contMDiff_zeroSection ℂ (twistCore (-1)).Fiber)

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

/-- The differential of `blowdown` at the point `zeroSection ℓ` of the exceptional divisor takes
its values in the line `ℓ`. With `exists_mfderiv_blowdown_zeroSection_eq`, its image is `ℓ`. -/
theorem mfderiv_blowdown_zeroSection_mem (ℓ : ℙ ℂ (Fin (n + 1) → ℂ))
    (v : TangentSpace 𝓘(ℂ, Fin (n + 1) → ℂ) (zeroSection ℓ)) :
    mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) blowdown (zeroSection ℓ) v ∈
      ℓ.submodule := by
  have hrk := finrank_range_add_finrank_ker_mfderiv_blowdown ℓ
  rw [ker_mfderiv_blowdown_zeroSection, finrank_range_mfderiv_zeroSection n ℓ] at hrk
  obtain ⟨w, hw⟩ := exists_mfderiv_blowdown_zeroSection_eq ℓ (ℓ.submodule_eq ▸
    Submodule.mem_span_singleton_self ℓ.rep)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_ne_zero' (⟨_, w, rfl⟩ : LinearMap.range
      (mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) blowdown
        (zeroSection ℓ)).toLinearMap)
    fun h => ℓ.rep_ne_zero (hw ▸ congrArg Subtype.val h)).1
      (Nat.add_right_cancel (hrk.trans (Nat.add_comm n 1))) ⟨_, v, rfl⟩
  have hc' : c • (mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) blowdown
      (zeroSection ℓ) w : Fin (n + 1) → ℂ) =
        mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) blowdown (zeroSection ℓ) v :=
    congrArg Subtype.val hc
  rw [hw] at hc'
  convert ℓ.submodule.smul_mem c (ℓ.submodule_eq ▸ Submodule.mem_span_singleton_self ℓ.rep)
    using 0
  exact Iff.of_eq (congrArg (· ∈ ℓ.submodule) hc'.symm)

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
      v ∈ (zeroSectionEmbedding n).tangentRange ℓ WithTop.top_ne_zero := by
  have h := SetLike.ext_iff.1 (ker_mfderiv_blowdown_zeroSection ℓ) v
  rw [← Subtype.coe_inj, coe_mfderivBlowdownZeroSection_apply, ZeroMemClass.coe_zero,
    TauCeti.SmoothEmbedding.mem_tangentRange_iff, coe_zeroSectionEmbedding]
  -- `h` is the goal, with membership in the kernel and the image of a linear map unfolded.
  exact h

variable (n) in
/-- The normal space of the zero section `zeroSectionEmbedding n` at `ℓ` is a complex line. -/
theorem finrank_normalSpace_zeroSectionEmbedding (ℓ : ℙ ℂ (Fin (n + 1) → ℂ)) :
    Module.finrank ℂ ((zeroSectionEmbedding n).NormalSpace ℓ WithTop.top_ne_zero) = 1 := by
  have h₁ : Module.finrank ℂ
      (TangentSpace 𝓘(ℂ, Fin (n + 1) → ℂ) (zeroSectionEmbedding n ℓ)) = n + 1 :=
    Module.finrank_fin_fun ℂ
  have h₂ : Module.finrank ℂ (TangentSpace 𝓘(ℂ, Fin n → ℂ) ℓ) = n := Module.finrank_fin_fun ℂ
  rw [TauCeti.SmoothEmbedding.finrank_normalSpace, h₁, h₂]
  omega

variable (n) in
/-- **The normal bundle of the exceptional divisor is the tautological line.** The
complex-linear isomorphism from the normal space at `ℓ` of the zero section
`zeroSectionEmbedding n` of the model blowup, Tau Ceti's `SmoothEmbedding.NormalSpace`, onto the
line `ℓ`, the fibre `Projectivization.Tautological ℂ E ℓ` of the tautological line. It sends the
class of a tangent vector `v` at `zeroSection ℓ` to the differential of `blowdown` at
`zeroSection ℓ` applied to `v` (`coe_normalSpaceZeroSectionEquiv_normalClass`).

Of the milestone *Tautological line bundle and the exceptional divisor*, this states that the
normal space of the exceptional divisor at each of its points is the corresponding fibre of the
tautological line. -/
noncomputable def normalSpaceZeroSectionEquiv (ℓ : ℙ ℂ (Fin (n + 1) → ℂ)) :
    (zeroSectionEmbedding n).NormalSpace ℓ WithTop.top_ne_zero ≃L[ℂ]
      Projectivization.Tautological ℂ (Fin (n + 1) → ℂ) ℓ :=
  (zeroSectionEmbedding n).normalSpaceEquivOfKer ℓ WithTop.top_ne_zero
    (mfderivBlowdownZeroSection ℓ) (mfderivBlowdownZeroSection_eq_zero_iff ℓ)
    ((finrank_normalSpace_zeroSectionEmbedding n ℓ).trans
      (Projectivization.finrank_submodule ℓ).symm)

/-- `normalSpaceZeroSectionEquiv n ℓ` sends the normal class of a tangent vector `v` at
`zeroSection ℓ` to the differential of `blowdown` at `zeroSection ℓ` applied to `v`. -/
@[simp]
theorem coe_normalSpaceZeroSectionEquiv_normalClass (ℓ : ℙ ℂ (Fin (n + 1) → ℂ))
    (v : TangentSpace 𝓘(ℂ, Fin (n + 1) → ℂ) (zeroSectionEmbedding n ℓ)) :
    (normalSpaceZeroSectionEquiv n ℓ
        ((zeroSectionEmbedding n).normalClass ℓ WithTop.top_ne_zero v) : Fin (n + 1) → ℂ) =
      mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) blowdown (zeroSection ℓ) v := by
  rw [normalSpaceZeroSectionEquiv, TauCeti.SmoothEmbedding.normalSpaceEquivOfKer_normalClass,
    coe_mfderivBlowdownZeroSection_apply]

/-- The isomorphisms `normalSpaceZeroSectionEquiv n ℓ` form a continuous map from the total
space of the normal bundle of the zero section, with Tau Ceti's bundle structure
`SmoothEmbedding.normalSpaceFiberBundle` of model fibre `ℂ`, to the total space of the
tautological line `Projectivization.Tautological ℂ E` over `ℙ ℂ E`. -/
theorem continuous_normalSpaceZeroSectionEquiv :
    letI := (zeroSectionEmbedding n).normalSpaceFiberBundle (P := ℂ) WithTop.top_ne_zero
      (by simp)
    Continuous fun p : TotalSpace ℂ
        (fun ℓ => (zeroSectionEmbedding n).NormalSpace ℓ WithTop.top_ne_zero) =>
      (⟨p.proj, normalSpaceZeroSectionEquiv n p.proj p.snd⟩ :
        TotalSpace ℂ (Projectivization.Tautological ℂ (Fin (n + 1) → ℂ))) := by
  let := (zeroSectionEmbedding n).normalSpaceFiberBundle (P := ℂ) WithTop.top_ne_zero
    (by simp)
  refine continuous_totalSpace_tautological_iff.2 ⟨FiberBundle.continuous_proj _ _, ?_⟩
  -- On an ambient tangent vector `v` at `zeroSection ℓ`, the map is the differential of
  -- `blowdown` applied to `v`, which is continuous on the tangent bundle.
  have h : (fun p : TotalSpace ℂ
        (fun ℓ => (zeroSectionEmbedding n).NormalSpace ℓ WithTop.top_ne_zero) =>
        (normalSpaceZeroSectionEquiv n p.proj p.snd : Fin (n + 1) → ℂ)) ∘
          (zeroSectionEmbedding n).normalQuotientMap (K := ℂ) WithTop.top_ne_zero =
        fun p => (tangentMap 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) blowdown
          (Pullback.lift _ p)).snd :=
    funext fun p => by
      rw [Function.comp_apply, TauCeti.SmoothEmbedding.normalQuotientMap_apply]
      have key : ∀ x y : BlowupModel n, x = y → ∀ v : Fin (n + 1) → ℂ,
          mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) blowdown x v =
            mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) blowdown y v := by
        rintro _ _ rfl _
        rfl
      -- The tangent map of `blowdown` at `⟨x, v⟩` has second component `mfderiv blowdown x v`.
      exact (coe_normalSpaceZeroSectionEquiv_normalClass p.proj p.snd).trans
        (key _ _ (congrFun (coe_zeroSectionEmbedding n) p.proj).symm p.snd)
  have hc : ContMDiff (𝓘(ℂ, Fin n → ℂ).prod 𝓘(ℂ, ℂ)) 𝓘(ℂ, Fin (n + 1) → ℂ) 0
      (fun p : TotalSpace ℂ
        (fun ℓ => (zeroSectionEmbedding n).NormalSpace ℓ WithTop.top_ne_zero) =>
        (normalSpaceZeroSectionEquiv n p.proj p.snd : Fin (n + 1) → ℂ)) := by
    refine ((zeroSectionEmbedding n).contMDiff_normalBundle_iff WithTop.top_ne_zero le_top
      (by simp) _).2 ?_
    rw [h]
    exact contMDiff_zero_iff.2 <| continuous_snd.comp
      ((tangentBundleModelSpaceHomeomorph _).continuous.comp
        (((contMDiff_blowdown 1).continuous_tangentMap le_rfl).comp
          (Pullback.continuous_lift _ _ _)))
  exact contMDiff_zero_iff.1 hc

end BlowupModel

end SymplecticGeometry

end
