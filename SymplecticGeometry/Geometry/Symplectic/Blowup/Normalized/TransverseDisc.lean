/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Blowup.Normalized.Basic
public import SymplecticGeometry.Geometry.Manifold.Complex.Blowup.ExceptionalClass
public import SymplecticGeometry.Geometry.Manifold.Complex.Blowup.Lift

/-!
# A transverse disc through a point of the exceptional divisor

Let `ψ` be a normalized ball embedding for a normalization `hN` of `(σ, J)` at `p₀`, with radius
`r`, and let `v ≠ 0` span the line `ℓ = [v]`, a point of the exceptional divisor `Z` of the blowup
`Blowup hN.blowupChart`. The *line disc* `hψ.lineDisc v` is the lift `ψ̃` of the lifted line
`t ↦ t • v` of the model, read on `ℝ²` through the identification
`Complex.orthonormalBasisOneI.repr.symm` of `ℝ²` with `ℂ`: it is defined on the open set of the
`w` whose model point lies in `openNbhd n r`, the source of the lift.

This file shows that it is a disc transverse to `Z` at `ℓ`, oriented as `Z`'s normal bundle:
it is smooth on that open set, which contains `0`; it sends `0` to `ℓ` and no other point into
`Z`; and the normal classes of its derivative at `0` are the values of a linear isomorphism
`ℝ² ≃ ν_ℓ` that carries the standard orientation of `ℝ²` to `Blowup.divisorNormalOrientation`.
These are the hypotheses that
`TauCeti.SmoothEmbedding.singularKronecker_realRelDualClass_relClass_of_hasFDerivAt` asks of a
disc, besides the choice of a simplex. Near `0` the lift is the inclusion of
the model piece, so the facts on the normal classes and on the orientation come from
`Blowup.divisorNormalEquiv_normalClassL_of_lift_eventuallyEq_curveLift_smul` and
`Blowup.orientation_map_eq_divisorNormalOrientation_mk`.

## Main definitions

* `SymplecticGeometry.IsNormalizedBallEmbedding.lineDisc hψ v`: the disc, with
  `IsNormalizedBallEmbedding.lineDisc_def`.

## Main results

* `BlowupModel.isOpen_setOf_curveLift_smul_mem_openNbhd` and
  `BlowupModel.zero_mem_setOf_curveLift_smul_mem_openNbhd`: the set where the disc is defined is
  open and contains `0`.
* `IsNormalizedBallEmbedding.contMDiffOn_lineDisc`: the disc is smooth there, and
  `IsNormalizedBallEmbedding.mdifferentiableAt_lineDisc`: differentiable at `0`.
* `IsNormalizedBallEmbedding.lineDisc_zero`: it sends `0` to the point `ℓ` of the divisor, and
  `IsNormalizedBallEmbedding.eq_zero_of_lineDisc_mem_range`: no other point into the divisor.
* `IsNormalizedBallEmbedding.divisorNormalEquiv_normalClassL_of_hasMFDerivAt_lineDisc`: for a
  derivative `A` at `0`, `Blowup.divisorNormalEquiv` sends the normal class of `A w` to `w • v`.
* `IsNormalizedBallEmbedding.exists_orientation_map_eq_divisorNormalOrientation_lineDisc`: these
  normal classes are the values of an isomorphism `ℝ² ≃ ν_ℓ` that carries the standard orientation
  to `divisorNormalOrientation`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §7.1,
  proof of Theorem 7.1.21 (v).
-/

public section

noncomputable section

open Set Topology
open scoped ContDiff Manifold LinearAlgebra.Projectivization TauCeti.ComplexManifold

namespace SymplecticGeometry

open TauCeti

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Fin (n + 1) → ℂ) M]
  [IsManifold 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ M]
  {σ : SmoothTwoForm 𝓘(ℝ, Fin (n + 1) → ℂ) M}
  {J : SmoothAlmostComplexStructure 𝓘(ℝ, Fin (n + 1) → ℂ) M} {p₀ : M} {δ : ℝ}
  {ψ₀ : StdSpace (Fin (n + 1)) → M} {hN : IsNormalizedAt σ J p₀ δ ψ₀}
  {ψ : StdSpace (Fin (n + 1)) → M} {r l ε : ℝ}

namespace BlowupModel

variable {v : Fin (n + 1) → ℂ}

/-- For `v ≠ 0`, the lift of the line `t ↦ t • v`, with `t` read on `ℝ²` through
`Complex.orthonormalBasisOneI.repr.symm`, is smooth. -/
theorem contMDiff_curveLift_smul_orthonormalBasisOneI_repr_symm (hv : v ≠ 0) {k : ℕ∞ω} :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, Fin (n + 1) → ℂ) k
      fun w ↦ curveLift (· • v) (Complex.orthonormalBasisOneI.repr.symm w) :=
  (contMDiff_curveLift_smul_real hv).comp
    Complex.orthonormalBasisOneI.repr.symm.toContinuousLinearEquiv.contDiff.contMDiff

/-- For `v ≠ 0`, the set of `w ∈ ℝ²` whose point on the lift of the line `t ↦ t • v`, with `w`
read in `ℂ` through `Complex.orthonormalBasisOneI.repr.symm`, lies in `openNbhd n r` is open. -/
theorem isOpen_setOf_curveLift_smul_mem_openNbhd (hv : v ≠ 0) (r : ℝ) :
    IsOpen {w : EuclideanSpace ℝ (Fin 2) |
      curveLift (· • v) (Complex.orthonormalBasisOneI.repr.symm w) ∈ openNbhd n r} :=
  (isOpen_openNbhd r).preimage
    (contMDiff_curveLift_smul_orthonormalBasisOneI_repr_symm hv (k := 0)).continuous

/-- For `v ≠ 0` and `0 < r`, the set of `w ∈ ℝ²` whose point on the lift of the line
`t ↦ t • v`, with `w` read in `ℂ` through `Complex.orthonormalBasisOneI.repr.symm`, lies in
`openNbhd n r` contains `0`. -/
theorem zero_mem_setOf_curveLift_smul_mem_openNbhd (hv : v ≠ 0) {r : ℝ} (hr : 0 < r) :
    (0 : EuclideanSpace ℝ (Fin 2)) ∈
      {w | curveLift (· • v) (Complex.orthonormalBasisOneI.repr.symm w) ∈ openNbhd n r} := by
  rw [mem_ofPred_eq, LinearIsometryEquiv.map_zero, curveLift_smul_zero hv]
  exact zeroSection_mem_openNbhd hr _

end BlowupModel

namespace IsNormalizedBallEmbedding

open BlowupModel

variable (hψ : IsNormalizedBallEmbedding hN ψ r l ε)

/-- The order `∞` of smoothness is not zero, as Tau Ceti's normal spaces ask. -/
local notation "hn" => (Iff.mpr WithTop.coe_ne_zero ENat.top_ne_zero : (∞ : ℕ∞ω) ≠ 0)

/-- **The line disc through `v`.** The lift `ψ̃` of the lift `BlowupModel.curveLift (· • v)` of
the line `t ↦ t • v` of the model, with `w ∈ ℝ²` read in `ℂ` through
`Complex.orthonormalBasisOneI.repr.symm`. It is the lift `ballLift` where the model point lies in
`openNbhd n r`, and arbitrary elsewhere. -/
def lineDisc (v : Fin (n + 1) → ℂ) (w : EuclideanSpace ℝ (Fin 2)) : Blowup hN.blowupChart :=
  hψ.ballLiftPartialDiffeomorph (curveLift (· • v) (Complex.orthonormalBasisOneI.repr.symm w))

theorem lineDisc_def (v : Fin (n + 1) → ℂ) (w : EuclideanSpace ℝ (Fin 2)) :
    hψ.lineDisc v w =
      hψ.ballLiftPartialDiffeomorph
        (curveLift (· • v) (Complex.orthonormalBasisOneI.repr.symm w)) :=
  (rfl)

variable {v : Fin (n + 1) → ℂ}

/-- The line disc is smooth where it is defined. -/
theorem contMDiffOn_lineDisc (hv : v ≠ 0) :
    ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ (hψ.lineDisc v)
      {w | curveLift (· • v) (Complex.orthonormalBasisOneI.repr.symm w) ∈ openNbhd n r} :=
  hψ.ballLiftPartialDiffeomorph.contMDiffOn.comp
    (contMDiff_curveLift_smul_orthonormalBasisOneI_repr_symm hv).contMDiffOn
    fun _ hw ↦ by rwa [ballLiftPartialDiffeomorph_source]

/-- The line disc is differentiable at `0`, so it has a derivative there. -/
theorem mdifferentiableAt_lineDisc (hv : v ≠ 0) :
    MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, Fin (n + 1) → ℂ) (hψ.lineDisc v) 0 :=
  ((hψ.contMDiffOn_lineDisc hv).contMDiffAt
    ((isOpen_setOf_curveLift_smul_mem_openNbhd hv r).mem_nhds
    (zero_mem_setOf_curveLift_smul_mem_openNbhd hv
      (hψ.width_pos.trans hψ.width_lt_radius)))).mdifferentiableAt (by simp)

/-- The line disc through `v` sends `0` to the point `[v]` of the exceptional divisor. -/
theorem lineDisc_zero (hv : v ≠ 0) :
    hψ.lineDisc v 0 = Blowup.divisorRealEmbedding hN.blowupChart (Projectivization.mk ℂ v hv) := by
  have h0 := zeroSection_mem_openNbhd hψ.width_pos (Projectivization.mk ℂ v hv)
  rw [lineDisc_def, LinearIsometryEquiv.map_zero, curveLift_smul_zero hv,
    hψ.ballLiftPartialDiffeomorph_apply ⟨_, openNbhd_mono hψ.width_lt_radius.le h0⟩,
    hψ.ballLift_of_mem_openNbhd _ h0, Blowup.coe_divisorRealEmbedding, Blowup.ofDirection_def]

/-- The line disc sends no point other than `0` of the set where it is defined into the
exceptional divisor. -/
theorem eq_zero_of_lineDisc_mem_range (hv : v ≠ 0) {w : EuclideanSpace ℝ (Fin 2)}
    (hw : curveLift (· • v) (Complex.orthonormalBasisOneI.repr.symm w) ∈ openNbhd n r)
    (hZ : hψ.lineDisc v w ∈ range (Blowup.divisorRealEmbedding hN.blowupChart)) : w = 0 := by
  rw [Blowup.range_divisorRealEmbedding] at hZ
  obtain ⟨y, hy0, hy⟩ := (Blowup.mem_exceptionalDivisor_iff _).1 hZ
  have hyε : (y : BlowupModel n) ∈ openNbhd n ε :=
    exceptionalDivisor_subset_openNbhd hψ.width_pos (mem_exceptionalDivisor_iff.2 hy0)
  have hyr : (y : BlowupModel n) ∈ openNbhd n r := openNbhd_mono hψ.width_lt_radius.le hyε
  have hΦy : hψ.ballLiftPartialDiffeomorph y = hψ.lineDisc v w := by
    rw [← hy, hψ.ballLiftPartialDiffeomorph_apply ⟨y, hyr⟩, hψ.ballLift_of_mem_openNbhd _ hyε]
  have heq := hψ.ballLiftPartialDiffeomorph.injOn
    (by rwa [ballLiftPartialDiffeomorph_source]) (by rwa [ballLiftPartialDiffeomorph_source])
    ((lineDisc_def ..).symm.trans hΦy.symm)
  have h := congrArg BlowupModel.blowdown heq
  rw [blowdown_curveLift, hy0, smul_eq_zero] at h
  exact Complex.orthonormalBasisOneI.repr.symm.map_eq_zero_iff.1 (h.resolve_right hv)

/-- **The line disc crosses the divisor with normal velocity `v`.** If `A` is a derivative at `0`
of the line disc through `v`, then `Blowup.divisorNormalEquiv` sends the normal class of `A w` to
`w • v`, with `w ∈ ℝ²` read in `ℂ` through `Complex.orthonormalBasisOneI.repr.symm`. -/
theorem divisorNormalEquiv_normalClassL_of_hasMFDerivAt_lineDisc (hv : v ≠ 0)
    {A : EuclideanSpace ℝ (Fin 2) →L[ℝ] Fin (n + 1) → ℂ}
    (hA : HasMFDerivAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, Fin (n + 1) → ℂ) (hψ.lineDisc v) 0 A)
    (w : EuclideanSpace ℝ (Fin 2)) :
    (Blowup.divisorNormalEquiv hN.blowupChart (Projectivization.mk ℂ v hv)
        ((Blowup.divisorRealEmbedding hN.blowupChart).isImmersion.normalClassL
          (Projectivization.mk ℂ v hv) hn (A w)) : Fin (n + 1) → ℂ) =
      Complex.orthonormalBasisOneI.repr.symm w • v := by
  set e := Complex.orthonormalBasisOneI.repr.symm.toContinuousLinearEquiv with he
  -- The disc read on `ℂ`.
  set g : ℂ → Blowup hN.blowupChart := fun t ↦ hψ.ballLiftPartialDiffeomorph (curveLift (· • v) t)
  have hge : hψ.lineDisc v ∘ e.symm = g := funext fun t ↦ by
    simp [g, e, lineDisc_def]
  have hg : HasMFDerivAt 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) g 0 (A.comp (e.symm : ℂ →L[ℝ] _)) := by
    rw [← hge]
    have hA0 : HasMFDerivAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, Fin (n + 1) → ℂ) (hψ.lineDisc v)
        (e.symm 0) A := by
      rwa [ContinuousLinearEquiv.map_zero]
    exact HasMFDerivAt.comp 0 hA0 e.symm.hasFDerivAt.hasMFDerivAt
  have hg0 : g 0 = Blowup.divisorRealEmbedding hN.blowupChart (Projectivization.mk ℂ v hv) := by
    rw [← hge, Function.comp_apply, ContinuousLinearEquiv.map_zero, hψ.lineDisc_zero hv]
  -- Near `0` the lift is the inclusion of the model piece, which `lift` undoes.
  have hlift : Blowup.lift hN.blowupChart ∘ g =ᶠ[𝓝 0] curveLift (· • v) := by
    have hε : ∀ᶠ t in 𝓝 (0 : ℂ), curveLift (· • v) t ∈ openNbhd n ε :=
      ((contMDiff_curveLift_smul_real hv (r := ∞)).continuous.continuousAt.preimage_mem_nhds
        ((isOpen_openNbhd ε).mem_nhds (by
          rw [curveLift_smul_zero hv]
          exact zeroSection_mem_openNbhd hψ.width_pos _)))
    filter_upwards [hε] with t ht
    simp only [Function.comp_apply, g]
    rw [
      hψ.ballLiftPartialDiffeomorph_apply ⟨_, openNbhd_mono hψ.width_lt_radius.le ht⟩,
      hψ.ballLift_of_mem_openNbhd _ ht, Blowup.lift_inr]
  have h := congrArg Subtype.val
    (Blowup.divisorNormalEquiv_normalClassL_of_lift_eventuallyEq_curveLift_smul
      hN.blowupChart hv hg hg0 hlift (e w))
  rw [show A w = (A.comp (e.symm : ℂ →L[ℝ] EuclideanSpace ℝ (Fin 2))) (e w) by simp]
  rwa [he, LinearIsometryEquiv.coe_toContinuousLinearEquiv] at h

/-- **The line disc is a transverse disc, oriented as the normal bundle.** There is a linear
isomorphism `m : ℝ² ≃ ν_[v]` onto the normal space of the exceptional divisor at `[v]` that carries
the standard orientation of `ℝ²` to `Blowup.divisorNormalOrientation`, and such that the normal
class of `A w` is `m w` for every derivative `A` at `0` of the line disc through `v`. -/
theorem exists_orientation_map_eq_divisorNormalOrientation_lineDisc (hv : v ≠ 0) :
    ∃ m : EuclideanSpace ℝ (Fin 2) ≃L[ℝ]
        (Blowup.divisorRealEmbedding hN.blowupChart).isImmersion.NormalSpace
          (Projectivization.mk ℂ v hv) hn,
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation.map (Fin 2) m.toLinearEquiv =
        Blowup.divisorNormalOrientation hN.blowupChart (Projectivization.mk ℂ v hv) ∧
      ∀ A : EuclideanSpace ℝ (Fin 2) →L[ℝ] Fin (n + 1) → ℂ,
        HasMFDerivAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, Fin (n + 1) → ℂ) (hψ.lineDisc v) 0 A →
        ∀ w, (Blowup.divisorRealEmbedding hN.blowupChart).isImmersion.normalClassL
          (Projectivization.mk ℂ v hv) hn (A w) = m w := by
  -- The line `ℓ = [v]` as the image of `z ↦ z • v`.
  let L : ℂ ≃ₗ[ℂ] Projectivization.Tautological ℂ (Fin (n + 1) → ℂ) (Projectivization.mk ℂ v hv) :=
    (LinearEquiv.toSpanNonzeroSingleton ℂ _ v hv).trans
      (LinearEquiv.ofEq _ _ (Projectivization.submodule_mk v hv).symm)
  let m : EuclideanSpace ℝ (Fin 2) ≃L[ℝ]
      (Blowup.divisorRealEmbedding hN.blowupChart).isImmersion.NormalSpace
        (Projectivization.mk ℂ v hv) hn :=
    (Complex.orthonormalBasisOneI.repr.symm.toContinuousLinearEquiv.trans
      (L.restrictScalars ℝ).toContinuousLinearEquiv).trans
      (Blowup.divisorNormalEquiv hN.blowupChart (Projectivization.mk ℂ v hv)).symm
  have hm : ∀ w, (Blowup.divisorNormalEquiv hN.blowupChart _ (m w) : Fin (n + 1) → ℂ) =
      Complex.orthonormalBasisOneI.repr.symm w • v := fun w ↦ by
    simp only [m, L, ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.apply_symm_apply,
      LinearEquiv.coe_toContinuousLinearEquiv', LinearEquiv.restrictScalars_apply,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv, LinearEquiv.trans_apply,
      LinearEquiv.coe_ofEq_apply, LinearEquiv.toSpanNonzeroSingleton_apply]
  refine ⟨m, Blowup.orientation_map_eq_divisorNormalOrientation_mk _ hv m hm, fun A hA w ↦ ?_⟩
  refine (Blowup.divisorNormalEquiv hN.blowupChart _).injective (Subtype.ext ?_)
  rw [hψ.divisorNormalEquiv_normalClassL_of_hasMFDerivAt_lineDisc hv hA, hm]

end IsNormalizedBallEmbedding

end SymplecticGeometry

end
