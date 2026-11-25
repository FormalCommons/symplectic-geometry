/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Complex.Blowup.Model
public import SymplecticGeometry.Geometry.Manifold.Projectivization.Tautological

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

## Implementation notes

The map into the blowup is shown holomorphic through the embedding of the blowup into
`ℙ ℂ E × E` (`BlowupModel.isSmoothEmbedding_blowupModel_val`): over the affine open `U_i`, the
vector of the line is the coordinate of `a` in the chart `i` of `𝒪(-1)` times the representative
`[1 : affineChart i ℓ]` of `ℓ`. The inverse is shown holomorphic in the charts
`BlowupModel.blowupModelChart i`: in the frame of the chart `k` of `𝒪(-1)`, the image of `(ℓ, z)`
has the coordinate `z k` (`Projectivization.twistCore_localTriv_tautologicalTwistCoreEquiv`), and
in the chart `i` of the blowup `z = w i • update w i 1`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §7.1,
  Lemma 7.1.1.
* [P. Griffiths, J. Harris, *Principles of Algebraic Geometry*][GriffithsHarris1978],
  Chapter 1, §4.
-/

public section

open Bundle Function Projectivization Filter Topology
open scoped LinearAlgebra.Projectivization ContDiff Manifold

namespace SymplecticGeometry

namespace BlowupModel

variable {n : ℕ}

private theorem contMDiff_blowupModelTotalSpaceToFun :
    ContMDiff (𝓘(ℂ, Fin n → ℂ).prod 𝓘(ℂ, ℂ)) 𝓘(ℂ, Fin (n + 1) → ℂ) ω
      (fun q : TotalSpace ℂ (twistCore (𝕜 := ℂ) (n := n) (-1)).Fiber =>
        (⟨(q.proj, (tautologicalTwistCoreEquiv q.proj).symm q.snd),
          mem_blowupModel_iff.2 ((tautologicalTwistCoreEquiv q.proj).symm q.snd).property⟩ :
            BlowupModel n)) := by
  refine ((isSmoothEmbedding_blowupModel_val (n := n) (r := ω) le_top).contMDiff_iff_comp).2 ?_
  refine fun q₀ => (contMDiffAt_proj _).prodMk ?_
  set i := (twistCore (𝕜 := ℂ) (n := n) (-1)).indexAt q₀.proj
  have hi₀ : q₀.proj ∈ affineOpen i := mem_affineOpen_twistCore_indexAt (-1) q₀.proj
  have hU : {q : TotalSpace ℂ (twistCore (𝕜 := ℂ) (n := n) (-1)).Fiber |
      q.proj ∈ affineOpen i} ∈ 𝓝 q₀ :=
    (FiberBundle.continuous_proj _ _).continuousAt.preimage_mem_nhds
      ((isOpen_affineOpen i).mem_nhds hi₀)
  have : MemTrivializationAtlas ((twistCore (𝕜 := ℂ) (n := n) (-1)).localTriv i) := ⟨⟨i, rfl⟩⟩
  have hsrc : q₀ ∈ ((twistCore (𝕜 := ℂ) (n := n) (-1)).localTriv i).source :=
    ((twistCore (-1)).mem_localTriv_source (i := i) q₀).2
      (by simpa [twistCore_baseSet] using hi₀)
  -- The coordinate of `q` in the chart `i` of `𝒪(-1)`.
  have h₁ : ContMDiffAt (𝓘(ℂ, Fin n → ℂ).prod 𝓘(ℂ, ℂ)) 𝓘(ℂ, ℂ) ω
      (fun q => ((twistCore (𝕜 := ℂ) (n := n) (-1)).localTriv i q).2) q₀ :=
    contMDiffAt_snd.comp _ (((twistCore (-1)).localTriv i).contMDiffAt hsrc)
  -- The representative `[1 : affineChart i ℓ]` of the line.
  have h₂ : ContMDiffAt (𝓘(ℂ, Fin n → ℂ).prod 𝓘(ℂ, ℂ)) 𝓘(ℂ, Fin (n + 1) → ℂ) ω
      (fun q : TotalSpace ℂ (twistCore (𝕜 := ℂ) (n := n) (-1)).Fiber =>
        Fin.insertNth (α := fun _ => ℂ) i 1 (affineChart i q.proj)) q₀ := by
    have hL : ContDiff ℂ ω fun z : Fin n → ℂ => Fin.insertNth (α := fun _ => ℂ) i 1 z :=
      contDiff_const.finInsertNth (F := fun _ => ℂ) i contDiff_id
    exact hL.contMDiff.contMDiffAt.comp _ <|
      ((contMDiffOn_affineChart i ω).contMDiffAt ((isOpen_affineOpen i).mem_nhds hi₀)).comp _
        (contMDiffAt_proj _)
  refine (h₁.smul h₂).congr_of_eventuallyEq (eventually_of_mem hU fun q hq => ?_)
  rw [Pi.smul_apply', insertNth_one_affineChart_eq_normalizedRep i hq]
  exact coe_tautologicalTwistCoreEquiv_symm_apply_of_mem hq q.snd

private theorem contMDiff_blowupModelTotalSpaceInvFun :
    ContMDiff 𝓘(ℂ, Fin (n + 1) → ℂ) (𝓘(ℂ, Fin n → ℂ).prod 𝓘(ℂ, ℂ)) ω
      (fun p : BlowupModel n =>
        (⟨p.val.1, tautologicalTwistCoreEquiv p.val.1 ⟨p.val.2, mem_blowupModel_iff.1 p.property⟩⟩ :
          TotalSpace ℂ (twistCore (𝕜 := ℂ) (n := n) (-1)).Fiber)) := by
  refine contMDiff_iff_forall_contMDiff_comp_blowupModelChart_symm.2 fun i w₀ => ?_
  refine contMDiffAt_totalSpace_iff.2
    ⟨((contMDiff_pr ω).comp (contMDiff_blowupModelChart_symm i ω)).contMDiffAt
      |>.congr_of_eventuallyEq (Eventually.of_forall fun w => (pr_def _).symm), ?_⟩
  -- In the frame of the chart `k` of `𝒪(-1)`, the image of `(ℓ, z)` is `z k`.
  set k := (twistCore (𝕜 := ℂ) (n := n) (-1)).indexAt ((blowupModelChart i).symm w₀).val.1
  have hk : ContDiff ℂ ω fun w : Fin (n + 1) → ℂ => w i * update w i 1 k :=
    (contDiff_apply ℂ (fun _ => ℂ) i).mul
      ((contDiff_apply ℂ (fun _ => ℂ) k).comp (ContDiff.update_self i contDiff_const))
  refine hk.contMDiff.contMDiffAt.congr_of_eventuallyEq (Eventually.of_forall fun w => ?_)
  -- `trivializationAt` of `𝒪(-1)` at `ℓ` is its chart `k`.
  refine (twistCore_localTriv_tautologicalTwistCoreEquiv k _).trans <|
    (congrFun (blowdown_def _).symm k).trans (by simp [blowdown_blowupModelChart_symm_apply])

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
biholomorphism off the divisor.

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

/-- `blowupModelTotalSpaceDiffeomorph` sends the zero of the fibre of `𝒪(-1)` over `ℓ` to the
point `zeroSection ℓ` of the exceptional divisor. -/
@[simp]
theorem blowupModelTotalSpaceDiffeomorph_zero (ℓ : ℙ ℂ (Fin (n + 1) → ℂ)) :
    blowupModelTotalSpaceDiffeomorph n (TotalSpace.mk' ℂ (E := (twistCore (-1)).Fiber) ℓ 0) =
      zeroSection ℓ :=
  ext (by simp) (by simp)

end BlowupModel

end SymplecticGeometry

end
