/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Complex.Blowup.Model
public import SymplecticGeometry.Analysis.Calculus.FDeriv.Equiv
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Analysis.Analytic.Hadamard

/-!
# Lifts of holomorphic maps fixing the origin to the model blowup

Let `E := Fin (n + 1) → ℂ` and let `ψ : E → E` be holomorphic near `0`, with `ψ 0 = 0` and with
invertible derivative `L` at `0`. Then `ψ` lifts to the model blowup `BlowupModel n`: off the
exceptional divisor the lift sends the point over `z` to the point `([ψ z], ψ z)` over `ψ z`, and
on the divisor it acts on lines by the derivative, `(ℓ, 0) ↦ (L ℓ, 0)`. This is McDuff–Salamon,
Exercise 7.1.2 (ii). The lift is holomorphic near the divisor: in the chart `i` write `z = w i • v`
with `v = update w i 1`; Hadamard's lemma gives `ψ z = G z z` with `G` analytic and `G 0 = L`, so
`ψ z = w i • G z v`, and the line of the lift is spanned by `G z v`, which depends analytically on
`w` and does not vanish near the divisor.

## Main definitions and results

* `SymplecticGeometry.BlowupModel.liftMap ψ L`: the lift of `ψ`, given the derivative `L` of `ψ`
  at `0` as a continuous linear equivalence. At a point whose blowdown `z` has `ψ z = 0` (on the
  divisor, if `ψ 0 = 0`) its value is the point over `0` on the line `L ℓ`, for `ℓ` the line of
  the point.
* `SymplecticGeometry.BlowupModel.blowdown_liftMap`: the lift lies over `ψ`, that is,
  `π ∘ liftMap ψ L = ψ ∘ π` for the blowdown `π`.
* `SymplecticGeometry.BlowupModel.liftMap_zeroSection`: on the divisor the lift is the action of
  `L` on lines (Mathlib's `Projectivization.map`).
* `SymplecticGeometry.BlowupModel.contMDiffAt_liftMap_of_ne_zero` and
  `SymplecticGeometry.BlowupModel.contMDiffAt_liftMap_zeroSection`: the lift is holomorphic at a
  point over a `z` where `ψ` is analytic and `ψ z ≠ 0`, and at every point of the divisor when
  `ψ` is analytic at `0` with derivative `L` there.
* `SymplecticGeometry.BlowupModel.contMDiffOn_liftMap`: so the lift is holomorphic over a set
  `V` on which `ψ` is analytic and vanishes only at `0`, and
  `SymplecticGeometry.BlowupModel.contMDiffOn_liftMap_of_injOn`: over a set `V ∋ 0` on which
  `ψ` is analytic and injective. Without such a condition the lift may fail to be continuous at a
  point over another zero of `ψ`. For `n ≥ 1`, take `ψ z = update z 0 (z 0 * (1 - z 0))`: its
  derivative at `0` is the identity, and it vanishes at `Pi.single 0 1`, where it is a local
  diffeomorphism, so near that point the line `[ψ z]` depends on the direction of approach. For
  `n = 0` the lift is always continuous, since `ℙ ℂ E` is then a point.
* `SymplecticGeometry.BlowupModel.eqOn_liftMap_of_blowdown_comp`: the lift is unique. Over an
  open set on which `ψ` is analytic and vanishes only at `0`, every continuous map lying over `ψ`
  is the lift, since the two agree off the exceptional divisor, which is dense, and the model is
  Hausdorff.
* `SymplecticGeometry.BlowupModel.liftPartialDiffeomorph`: for a partial homeomorphism `ψ` of `E`
  with `ψ 0 = 0`, analytic on its source with analytic inverse on its target, the lift is a
  biholomorphism from the part of the model over the source of `ψ` onto the part over its target,
  with inverse the lift of `ψ.symm`. Its derivative `L` at `0` is invertible, with inverse the
  derivative of `ψ.symm` at `0`, by the chain rule (`OpenPartialHomeomorph.fderivEquiv`).
  The two lifts are inverse to each other (`liftMap_symm_liftMap`, `liftMap_liftMap_symm`): off
  the divisor because `ψ.symm ∘ ψ` is the identity there, on it because the action of `L.symm`
  on lines undoes that of `L` (Tau Ceti's
  `ContinuousLinearEquiv.mapProjectivization_symm_apply_apply`).

## Implementation notes

The factorisation `ψ z = G z z` is Tau Ceti's `AnalyticAt.exists_analyticAt_eventually_sub_eq`
(Hadamard's lemma). Holomorphy of the lift is checked on its composite with the inclusion of the
blowup into `ℙ ℂ E × E` (`Manifold.IsSmoothEmbedding.contMDiffAt_iff_comp` for
`isSmoothEmbedding_blowupModel_val`), whose factor in `ℙ ℂ E` is handled by Tau Ceti's
`Projectivization.contMDiffAt_of_eventually_eq_mk`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §7.1,
  Exercise 7.1.2.
-/

public section

namespace SymplecticGeometry

namespace BlowupModel

open Function Projectivization Filter Topology
open scoped ContDiff Manifold LinearAlgebra.Projectivization

variable {n : ℕ}

section Def

variable (ψ : (Fin (n + 1) → ℂ) → Fin (n + 1) → ℂ) (L : (Fin (n + 1) → ℂ) ≃L[ℂ] Fin (n + 1) → ℂ)

/-- The lift to the model blowup of a map `ψ : E → E`, meant for `ψ` with `ψ 0 = 0` whose
derivative at `0` is the continuous linear equivalence `L`. A point `p` over `z` with `ψ z ≠ 0`
goes to the point over `ψ z` on the line `[ψ z]`; a point with `ψ z = 0`, such as a point of the
exceptional divisor, goes to the point over `0` on the line `L ℓ`, where `ℓ` is the line of `p`. -/
noncomputable def liftMap (p : BlowupModel n) : BlowupModel n :=
  if h : ψ p.blowdown = 0 then zeroSection (map (L : _ →ₗ[ℂ] _) L.injective p.pr)
  else ⟨(mk ℂ (ψ p.blowdown) h, ψ p.blowdown), mk_self_mem_blowupModel h⟩

variable {ψ} {p : BlowupModel n}

theorem liftMap_of_eq_zero (h : ψ p.blowdown = 0) :
    liftMap ψ L p = zeroSection (map (L : _ →ₗ[ℂ] _) L.injective p.pr) :=
  dite_eq_left h

theorem liftMap_of_ne_zero (h : ψ p.blowdown ≠ 0) :
    liftMap ψ L p = ⟨(mk ℂ (ψ p.blowdown) h, ψ p.blowdown), mk_self_mem_blowupModel h⟩ :=
  dite_eq_right h

/-- Where `ψ` does not vanish, the line of the lift is spanned by `ψ z`. -/
theorem pr_liftMap_of_ne_zero (h : ψ p.blowdown ≠ 0) :
    (liftMap ψ L p).pr = mk ℂ (ψ p.blowdown) h := by
  rw [liftMap_of_ne_zero L h, pr_mk]

/-- The lift lies over `ψ`: `π ∘ liftMap ψ L = ψ ∘ π` for the blowdown `π`. -/
@[simp]
theorem blowdown_liftMap (p : BlowupModel n) : (liftMap ψ L p).blowdown = ψ p.blowdown := by
  by_cases h : ψ p.blowdown = 0
  · rw [liftMap_of_eq_zero L h, blowdown_zeroSection, h]
  · rw [liftMap_of_ne_zero L h, blowdown_mk]

/-- On the exceptional divisor, the lift of a map fixing `0` acts on lines by its derivative `L`. -/
@[simp]
theorem liftMap_zeroSection (h0 : ψ 0 = 0) (ℓ : ℙ ℂ (Fin (n + 1) → ℂ)) :
    liftMap ψ L (zeroSection ℓ) = zeroSection (map (L : _ →ₗ[ℂ] _) L.injective ℓ) := by
  rw [liftMap_of_eq_zero L (by rwa [blowdown_zeroSection]), pr_zeroSection]

end Def

section Holomorphic

variable {ψ : (Fin (n + 1) → ℂ) → Fin (n + 1) → ℂ} (L : (Fin (n + 1) → ℂ) ≃L[ℂ] Fin (n + 1) → ℂ)
  {r : ℕ∞ω}

/-- The lift of `ψ` is holomorphic at a point `p` over a point `z` where `ψ` is analytic and does
not vanish: near `p` it is `q ↦ ([ψ z], ψ z)` with `z` the blowdown of `q`. -/
theorem contMDiffAt_liftMap_of_ne_zero {p : BlowupModel n} (hψ : AnalyticAt ℂ ψ p.blowdown)
    (hp : ψ p.blowdown ≠ 0) :
    ContMDiffAt 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) r (liftMap ψ L) p := by
  refine ContMDiffAt.of_le ?_ le_top
  have hF : ContMDiffAt 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) ω (ψ ∘ blowdown) p :=
    hψ.contDiffAt.contMDiffAt.comp p (contMDiff_blowdown ω p)
  refine (contMDiffAt_iff_contMDiffAt_pr_comp_and_blowdown_comp le_top).2
    ⟨contMDiffAt_of_eventually_eq_mk hF <| (hF.continuousAt.eventually_ne hp).mono fun q hq =>
      ⟨hq, pr_liftMap_of_ne_zero L hq⟩, ?_⟩
  exact hF.congr_of_eventuallyEq (Eventually.of_forall fun q => blowdown_liftMap L q)

/-- The lift of `ψ` is holomorphic at each point of the exceptional divisor, when `ψ` is analytic
at `0` with `ψ 0 = 0` and derivative `L` there. -/
theorem contMDiffAt_liftMap_zeroSection (hψ : AnalyticAt ℂ ψ 0) (h0 : ψ 0 = 0)
    (hL : fderiv ℂ ψ 0 = L) (ℓ : ℙ ℂ (Fin (n + 1) → ℂ)) :
    ContMDiffAt 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) r (liftMap ψ L) (zeroSection ℓ) := by
  refine ContMDiffAt.of_le ?_ le_top
  obtain ⟨G, hG, hG0, hGψ⟩ := hψ.exists_analyticAt_eventually_sub_eq
  rw [hL] at hG0
  obtain ⟨i, hi⟩ := exists_mem_affineOpen ℓ
  have hsrc : zeroSection ℓ ∈ (blowupModelChart i).source := by
    rwa [blowupModelChart_source, Set.mem_preimage, pr_zeroSection]
  refine (contMDiffAt_iff_contMDiffAt_comp_blowupModelChart_symm hsrc).2 ?_
  set w₀ := blowupModelChart i (zeroSection ℓ)
  -- In the chart `i`, the blowdown is `z w = w i • v w` with `v w = update w i 1`.
  set v : (Fin (n + 1) → ℂ) → Fin (n + 1) → ℂ := fun w => update w i 1 with hv_def
  set z : (Fin (n + 1) → ℂ) → Fin (n + 1) → ℂ := fun w => w i • v w with hz_def
  have hv : ContDiff ℂ ω v := ContDiff.update_self i contDiff_const
  have hz : ContDiff ℂ ω z := (contDiff_apply ℂ (fun _ => ℂ) i).smul hv
  have hzw : ∀ w, z w = ((blowupModelChart i).symm w).blowdown := fun w =>
    (blowdown_blowupModelChart_symm_apply i w).symm
  have hz₀ : z w₀ = 0 := by
    rw [hzw, (blowupModelChart i).left_inv hsrc, blowdown_zeroSection]
  have hv0 : ∀ w, v w ≠ 0 := fun w => update_ne_zero w i one_ne_zero
  -- The line of the lift is spanned by `F w = G (z w) (v w)`.
  set F : (Fin (n + 1) → ℂ) → Fin (n + 1) → ℂ := fun w => G (z w) (v w) with hF_def
  have hF : ContDiffAt ℂ ω F w₀ :=
    ((show AnalyticAt ℂ G (z w₀) by rwa [hz₀]).contDiffAt.comp w₀ hz.contDiffAt).clm_apply
      hv.contDiffAt
  have hFw₀ : F w₀ ≠ 0 := by
    simp only [hF_def, hz₀, hG0]
    exact L.map_ne_zero_iff.2 (hv0 w₀)
  have hz_tendsto : Tendsto z (𝓝 w₀) (𝓝 0) := hz₀ ▸ hz.continuous.tendsto w₀
  refine (contMDiffAt_iff_contMDiffAt_pr_comp_and_blowdown_comp le_top).2
    ⟨contMDiffAt_of_eventually_eq_mk hF.contMDiffAt ?_, ?_⟩
  · filter_upwards [hF.continuousAt.eventually_ne hFw₀, hz_tendsto.eventually hGψ] with w hFw hGw
    refine ⟨hFw, ?_⟩
    simp only [comp_apply]
    by_cases hwi : w i = 0
    · have hzw0 : ((blowupModelChart i).symm w).blowdown = 0 := by
        rw [← hzw, hz_def]; simp [hwi]
      rw [liftMap_of_eq_zero L (by rw [hzw0, h0]), pr_zeroSection,
        pr_blowupModelChart_symm_apply, map_mk]
      congr 1
      simp [hF_def, show z w = 0 by rw [hzw, hzw0], hG0, hv_def]
    · have hψz : ψ (z w) = w i • F w := by
        simpa [h0, hF_def, hz_def] using hGw
      have hne : ψ ((blowupModelChart i).symm w).blowdown ≠ 0 := by
        rw [← hzw, hψz]; exact smul_ne_zero hwi hFw
      rw [pr_liftMap_of_ne_zero L hne, mk_eq_mk_iff']
      exact ⟨w i, by rw [← hψz, hzw]⟩
  · have : ContMDiffAt 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) ω (ψ ∘ z) w₀ :=
      ((show AnalyticAt ℂ ψ (z w₀) by rwa [hz₀]).contDiffAt.comp w₀ hz.contDiffAt).contMDiffAt
    refine this.congr_of_eventuallyEq (Eventually.of_forall fun w => ?_)
    simp only [comp_apply, blowdown_liftMap, hzw]

/-- The lift of `ψ` is holomorphic over a set `V` on which `ψ` is analytic and vanishes only
at `0`, when `ψ 0 = 0` and `L` is the derivative of `ψ` at `0`. -/
theorem contMDiffOn_liftMap {V : Set (Fin (n + 1) → ℂ)} (hψ : AnalyticOnNhd ℂ ψ V)
    (h0 : ψ 0 = 0) (hL : fderiv ℂ ψ 0 = L) (hne : ∀ z ∈ V, z ≠ 0 → ψ z ≠ 0) :
    ContMDiffOn 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) r (liftMap ψ L) (blowdown ⁻¹' V) := by
  refine fun p hp => ContMDiffAt.contMDiffWithinAt ?_
  by_cases hp0 : p.blowdown = 0
  · rw [eq_zeroSection_pr hp0]
    rw [Set.mem_preimage, hp0] at hp
    exact contMDiffAt_liftMap_zeroSection L (hψ 0 hp) h0 hL p.pr
  · exact contMDiffAt_liftMap_of_ne_zero L (hψ _ hp) (hne _ hp hp0)

/-- The lift of `ψ` is holomorphic over a set `V ∋ 0` on which `ψ` is analytic and injective,
when `ψ 0 = 0` and `L` is the derivative of `ψ` at `0`. -/
theorem contMDiffOn_liftMap_of_injOn {V : Set (Fin (n + 1) → ℂ)} (hV0 : 0 ∈ V)
    (hψ : AnalyticOnNhd ℂ ψ V) (hinj : Set.InjOn ψ V) (h0 : ψ 0 = 0) (hL : fderiv ℂ ψ 0 = L) :
    ContMDiffOn 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) r (liftMap ψ L) (blowdown ⁻¹' V) :=
  contMDiffOn_liftMap L hψ h0 hL fun _ hz hz0 hψz => hz0 (hinj hz hV0 (hψz.trans h0.symm))

end Holomorphic

section Uniqueness

variable {ψ : (Fin (n + 1) → ℂ) → Fin (n + 1) → ℂ} (L : (Fin (n + 1) → ℂ) ≃L[ℂ] Fin (n + 1) → ℂ)

/-- Uniqueness of the lift: over an open set `U` on which `ψ` is analytic and vanishes only at
`0`, where `ψ 0 = 0` and `L` is the derivative of `ψ` at `0`, a map `f` that is continuous over
`U` and lies over `ψ` there agrees with `liftMap ψ L` over `U`. -/
theorem eqOn_liftMap_of_blowdown_comp {U : Set (Fin (n + 1) → ℂ)} (hU : IsOpen U)
    (hψ : AnalyticOnNhd ℂ ψ U) (h0 : ψ 0 = 0) (hL : fderiv ℂ ψ 0 = L)
    (hne : ∀ z ∈ U, z ≠ 0 → ψ z ≠ 0) {f : BlowupModel n → BlowupModel n}
    (hf : ContinuousOn f (blowdown ⁻¹' U))
    (hfψ : ∀ p ∈ blowdown ⁻¹' U, (f p).blowdown = ψ p.blowdown) :
    Set.EqOn f (liftMap ψ L) (blowdown ⁻¹' U) := by
  have hW : IsOpen (blowdown ⁻¹' U : Set (BlowupModel n)) := hU.preimage continuous_blowdown
  refine Set.EqOn.of_subset_closure (s := blowdown ⁻¹' U ∩ (exceptionalDivisor n)ᶜ) ?_ hf
    (contMDiffOn_liftMap (r := 0) L hψ h0 hL hne).continuousOn Set.inter_subset_left
    (dense_exceptionalDivisor_compl.open_subset_closure_inter hW)
  rintro p ⟨hpU, hpZ⟩
  have hψp : ψ p.blowdown ≠ 0 := hne _ hpU fun h => hpZ (mem_exceptionalDivisor_iff.2 h)
  exact eq_of_blowdown_eq (by rwa [hfψ p hpU]) (by rw [hfψ p hpU, blowdown_liftMap])

end Uniqueness

section PartialDiffeomorph

variable (ψ : OpenPartialHomeomorph (Fin (n + 1) → ℂ) (Fin (n + 1) → ℂ))
  (L : (Fin (n + 1) → ℂ) ≃L[ℂ] Fin (n + 1) → ℂ)

/-- The lift of the inverse of a partial homeomorphism `ψ` of `E` fixing `0 ∈ ψ.source` is a left
inverse of the lift of `ψ` over the source of `ψ`. -/
theorem liftMap_symm_liftMap (h0 : 0 ∈ ψ.source) (hψ0 : ψ 0 = 0) {p : BlowupModel n}
    (hp : p.blowdown ∈ ψ.source) : liftMap ψ.symm L.symm (liftMap ψ L p) = p := by
  by_cases hz : p.blowdown = 0
  · have hsymm0 : ψ.symm 0 = 0 := (congrArg ψ.symm hψ0).symm.trans (ψ.left_inv h0)
    rw [eq_zeroSection_pr hz, liftMap_zeroSection L hψ0, liftMap_zeroSection L.symm hsymm0]
    simp only [← ContinuousLinearEquiv.coe_mapProjectivization,
      ContinuousLinearEquiv.mapProjectivization_symm_apply_apply]
  · exact (eq_of_blowdown_eq hz (by rw [blowdown_liftMap, blowdown_liftMap, ψ.left_inv hp])).symm

/-- The lift of a partial homeomorphism `ψ` of `E` fixing `0 ∈ ψ.source` is a left inverse of the
lift of its inverse over the target of `ψ`. -/
theorem liftMap_liftMap_symm (h0 : 0 ∈ ψ.source) (hψ0 : ψ 0 = 0) {p : BlowupModel n}
    (hp : p.blowdown ∈ ψ.target) : liftMap ψ L (liftMap ψ.symm L.symm p) = p := by
  simpa using liftMap_symm_liftMap ψ.symm L.symm (hψ0 ▸ ψ.map_source h0)
    ((congrArg ψ.symm hψ0).symm.trans (ψ.left_inv h0)) hp

variable {ψ}

/-- The lift of a partial biholomorphism `ψ` of `E` with `ψ 0 = 0`, as a biholomorphism from the
part of the model blowup over the source of `ψ` onto the part over its target. It is the lift of
`ψ` by its derivative at `0`, which is invertible with inverse the derivative of `ψ.symm` at `0`
(`OpenPartialHomeomorph.fderivEquiv`), and its inverse is the lift of `ψ.symm`. -/
noncomputable def liftPartialDiffeomorph (h0 : 0 ∈ ψ.source) (hψ0 : ψ 0 = 0)
    (hψ : AnalyticOnNhd ℂ ψ ψ.source) (hψsymm : AnalyticOnNhd ℂ ψ.symm ψ.target) :
    PartialDiffeomorph 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) (BlowupModel n)
      (BlowupModel n) ω :=
  let L := ψ.fderivEquiv h0 (hψ 0 h0).differentiableAt
    (hψsymm _ (ψ.map_source h0)).differentiableAt
  { toFun := liftMap ψ L
    invFun := liftMap ψ.symm L.symm
    source := blowdown ⁻¹' ψ.source
    target := blowdown ⁻¹' ψ.target
    map_source' p hp := by
      rw [Set.mem_preimage, blowdown_liftMap]
      exact ψ.map_source hp
    map_target' p hp := by
      rw [Set.mem_preimage, blowdown_liftMap]
      exact ψ.map_target hp
    left_inv' _ hp := liftMap_symm_liftMap ψ L h0 hψ0 hp
    right_inv' _ hp := liftMap_liftMap_symm ψ L h0 hψ0 hp
    open_source := ψ.open_source.preimage continuous_blowdown
    open_target := ψ.open_target.preimage continuous_blowdown
    contMDiffOn_toFun := contMDiffOn_liftMap_of_injOn L h0 hψ ψ.injOn hψ0
      (ψ.toContinuousLinearMap_fderivEquiv _ _ _).symm
    contMDiffOn_invFun := by
      have hL' : fderiv ℂ ψ.symm 0 = L.symm := by
        rw [ψ.toContinuousLinearMap_fderivEquiv_symm, hψ0]
      exact contMDiffOn_liftMap_of_injOn L.symm (hψ0 ▸ ψ.map_source h0) hψsymm ψ.symm.injOn
        ((congrArg ψ.symm hψ0).symm.trans (ψ.left_inv h0)) hL' }

variable (h0 : 0 ∈ ψ.source) (hψ0 : ψ 0 = 0) (hψ : AnalyticOnNhd ℂ ψ ψ.source)
  (hψsymm : AnalyticOnNhd ℂ ψ.symm ψ.target)

@[simp]
theorem liftPartialDiffeomorph_apply (p : BlowupModel n) :
    liftPartialDiffeomorph h0 hψ0 hψ hψsymm p =
      liftMap ψ (ψ.fderivEquiv h0 (hψ 0 h0).differentiableAt
        (hψsymm _ (ψ.map_source h0)).differentiableAt) p :=
  (rfl)

@[simp]
theorem liftPartialDiffeomorph_symm_apply (p : BlowupModel n) :
    (liftPartialDiffeomorph h0 hψ0 hψ hψsymm).toPartialEquiv.symm p =
      liftMap ψ.symm (ψ.fderivEquiv h0 (hψ 0 h0).differentiableAt
        (hψsymm _ (ψ.map_source h0)).differentiableAt).symm p :=
  (rfl)

@[simp]
theorem liftPartialDiffeomorph_source :
    (liftPartialDiffeomorph h0 hψ0 hψ hψsymm).source = blowdown ⁻¹' ψ.source :=
  (rfl)

@[simp]
theorem liftPartialDiffeomorph_target :
    (liftPartialDiffeomorph h0 hψ0 hψ hψsymm).target = blowdown ⁻¹' ψ.target :=
  (rfl)

end PartialDiffeomorph

end BlowupModel

end SymplecticGeometry

end
