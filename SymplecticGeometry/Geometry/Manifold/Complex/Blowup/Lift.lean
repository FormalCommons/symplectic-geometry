/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Complex.Blowup.Model
public import SymplecticGeometry.Analysis.Calculus.FDeriv.Equiv
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Analysis.Analytic.Order
public import TauCeti.Topology.Codiscrete
public import TauCeti.Analysis.Analytic.Hadamard
import SymplecticGeometry.Analysis.Analytic.Order
import TauCeti.Analysis.Calculus.IteratedDeriv.Leibniz
import TauCeti.Analysis.Calculus.FDeriv.RestrictScalars
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
import SymplecticGeometry.Geometry.Manifold.ContMDiff.RestrictScalars

/-!
# Lifts of holomorphic maps fixing the origin and of curves through it to the model blowup

Let `E := Fin (n + 1) → ℂ` and let `ψ : E → E` be holomorphic near `0`, with `ψ 0 = 0` and with
invertible derivative `L` at `0`. Then `ψ` lifts to the model blowup `BlowupModel n`: off the
exceptional divisor the lift sends the point over `z` to the point `([ψ z], ψ z)` over `ψ z`, and
on the divisor it acts on lines by the derivative, `(ℓ, 0) ↦ (L ℓ, 0)`. This is McDuff–Salamon,
Exercise 7.1.2 (ii). The lift is holomorphic near the divisor: in the chart `i` write `z = w i • v`
with `v = update w i 1`; Hadamard's lemma gives `ψ z = G z z` with `G` analytic and `G 0 = L`, so
`ψ z = w i • G z v`, and the line of the lift is spanned by `G z v`, which depends analytically on
`w` and does not vanish near the divisor.

A curve `u : ℂ → E` through `0` lifts as well (Exercise 7.1.2 (iii)). If `u` is analytic at `t₀`
with a zero of finite order `k` there, then `u t = (t - t₀) ^ k • g t` near `t₀` with `g` analytic
and `g t₀ ≠ 0`, so `t ↦ ([g t], u t)` is a holomorphic curve in the blowup over `u`. At `t₀` its
line is that of `g t₀`, which is also the line of `iteratedDeriv k u t₀ = k! • g t₀`. The lift is
defined by this last description, without choosing `g`.

## Main definitions and results

* `SymplecticGeometry.BlowupModel.liftMap ψ L`: the lift of `ψ`, given the derivative `L` of `ψ`
  at `0` as a continuous linear equivalence. At a point whose blowdown `z` has `ψ z = 0` (on the
  divisor, if `ψ 0 = 0`) its value is the point over `0` on the line `L ℓ`, for `ℓ` the line of
  the point.
* `SymplecticGeometry.BlowupModel.blowdown_liftMap`: the lift lies over `ψ`, that is,
  `π ∘ liftMap ψ L = ψ ∘ π` for the blowdown `π`.
* `SymplecticGeometry.BlowupModel.liftMap_zeroSection`: on the divisor the lift is the action of
  `L` on lines (Tau Ceti's `ContinuousLinearEquiv.mapProjectivization`).
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
* `SymplecticGeometry.BlowupModel.curveLift u`: the lift of a curve `u : ℂ → E`, equal to
  `([u t], u t)` where `u t ≠ 0` and, at a zero, to the point of the divisor on the line of the
  first nonvanishing derivative of `u` there (`curveLift_apply_self`).
* `SymplecticGeometry.BlowupModel.blowdown_curveLift`: the lift lies over `u`.
* `SymplecticGeometry.BlowupModel.eventually_pr_curveLift_eq_mk`: near a zero `t₀` where
  `u t = (t - t₀) ^ k • g t`, the line of the lift is `[g t]`.
* `SymplecticGeometry.BlowupModel.contMDiffAt_curveLift`: the lift is holomorphic at a point where
  `u` is analytic of finite order, and `contMDiffOn_curveLift` on a set of such points, with
  `continuousOn_curveLift`.
* `SymplecticGeometry.BlowupModel.mfderiv_curveLift_of_ne_zero`: at a point `t` where `u` is
  complex differentiable with `u t ≠ 0`, the real derivative of the lift along `c` is that of the
  inverse of the blowdown off the divisor (`blowdownDiffeomorph`) at `u t` along
  `c • u'(t)`, since near `t` the lift is `u` followed by that inverse.
* `SymplecticGeometry.BlowupModel.mfderiv_blowdown_mfderiv_curveLift_eq_mfderiv`: wherever the
  lift is real differentiable, the differential of the blowdown sends its derivative along `c` to
  the derivative of `u` along `c`, which is `c • u'(t)` where `u` is complex differentiable
  (`mfderiv_blowdown_mfderiv_curveLift`).
* `SymplecticGeometry.BlowupModel.curveLift_smul_zero`, `pr_curveLift_smul` and
  `contMDiff_curveLift_smul`: for `v ≠ 0`, the lift of the line `t ↦ t • v` is a holomorphic curve
  that stays on the line `ℓ` spanned by `v`, the fibre over `ℓ` of the tautological line, and
  passes through the divisor at `zeroSection ℓ` for `t = 0`.
* `SymplecticGeometry.BlowupModel.curveLift_eq_of_blowdown_comp`: the lift of a curve is unique.
  On an open set where `u` is analytic of finite order at every point, a continuous map lying
  over `u` is its lift, since the zeros of `u` there are isolated and the blowdown is injective
  off them; `eqOn_curveLift_of_blowdown_comp` for a map defined on all of `ℂ`.

## Implementation notes

The factorisation `ψ z = G z z` is Tau Ceti's `AnalyticAt.exists_analyticAt_eventually_sub_eq`
(Hadamard's lemma). Holomorphy of the lift is checked on its composite with the inclusion of the
blowup into `ℙ ℂ E × E` (`Manifold.IsSmoothEmbedding.contMDiffAt_iff_comp` for
`isSmoothEmbedding_blowupModel_val`), whose factor in `ℙ ℂ E` is handled by Tau Ceti's
`Projectivization.contMDiffAt_of_eventually_eq_mk`.

The value `iteratedDeriv k u t₀ = k! • g t₀` is Tau Ceti's
`TauCeti.iteratedDeriv_pow_sub_smul_self` (Leibniz's rule).

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §7.1,
  Exercise 7.1.2.
-/

public section

namespace SymplecticGeometry

namespace BlowupModel

open Function Projectivization Filter Topology
open scoped ContDiff Manifold LinearAlgebra.Projectivization Nat

variable {n : ℕ}

section Def

variable (ψ : (Fin (n + 1) → ℂ) → Fin (n + 1) → ℂ) (L : (Fin (n + 1) → ℂ) ≃L[ℂ] Fin (n + 1) → ℂ)

/-- The lift to the model blowup of a map `ψ : E → E`, meant for `ψ` with `ψ 0 = 0` whose
derivative at `0` is the continuous linear equivalence `L`. A point `p` over `z` with `ψ z ≠ 0`
goes to the point over `ψ z` on the line `[ψ z]`; a point with `ψ z = 0`, such as a point of the
exceptional divisor, goes to the point over `0` on the line `L ℓ`, where `ℓ` is the line of `p`. -/
noncomputable def liftMap (p : BlowupModel n) : BlowupModel n :=
  if h : ψ p.blowdown = 0 then zeroSection (L.mapProjectivization p.pr)
  else ofNeZero h

variable {ψ} {p : BlowupModel n}

theorem liftMap_of_eq_zero (h : ψ p.blowdown = 0) :
    liftMap ψ L p = zeroSection (L.mapProjectivization p.pr) :=
  dite_eq_left h

theorem liftMap_of_ne_zero (h : ψ p.blowdown ≠ 0) : liftMap ψ L p = ofNeZero h :=
  dite_eq_right h

/-- Where `ψ` does not vanish, the line of the lift is spanned by `ψ z`. -/
theorem pr_liftMap_of_ne_zero (h : ψ p.blowdown ≠ 0) :
    (liftMap ψ L p).pr = mk ℂ (ψ p.blowdown) h := by
  rw [liftMap_of_ne_zero L h, pr_ofNeZero]

/-- The lift lies over `ψ`: `π ∘ liftMap ψ L = ψ ∘ π` for the blowdown `π`. -/
@[simp]
theorem blowdown_liftMap (p : BlowupModel n) : (liftMap ψ L p).blowdown = ψ p.blowdown := by
  by_cases h : ψ p.blowdown = 0
  · rw [liftMap_of_eq_zero L h, blowdown_zeroSection, h]
  · rw [liftMap_of_ne_zero L h, blowdown_ofNeZero]

/-- On the exceptional divisor, the lift of a map fixing `0` acts on lines by its derivative `L`. -/
@[simp]
theorem liftMap_zeroSection (h0 : ψ 0 = 0) (ℓ : ℙ ℂ (Fin (n + 1) → ℂ)) :
    liftMap ψ L (zeroSection ℓ) = zeroSection (L.mapProjectivization ℓ) := by
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
        pr_blowupModelChart_symm_apply, ContinuousLinearEquiv.mapProjectivization_mk]
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
    rw [ContinuousLinearEquiv.mapProjectivization_symm_apply_apply]
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

section Curve

/-! ### Lifts of curves -/

variable (u : ℂ → Fin (n + 1) → ℂ)

/-- The lift to the model blowup of a curve `u : ℂ → E`. At `t` with `u t ≠ 0` it is the point
`([u t], u t)`; at a zero `t` of `u` it is the point over `0` on the line spanned by the first
nonvanishing derivative of `u` at `t`, that is, by `iteratedDeriv k u t` for `k` the order of the
zero (`analyticOrderNatAt`). Where that derivative vanishes, which happens only when `u` is not
analytic at `t` or vanishes near `t`, the line is an arbitrary one. -/
noncomputable def curveLift (t : ℂ) : BlowupModel n :=
  if h : u t = 0 then
    if h' : iteratedDeriv (analyticOrderNatAt u t) u t = 0 then zeroSection (Classical.arbitrary _)
    else zeroSection (mk ℂ _ h')
  else ofNeZero h

variable {u} {t t₀ : ℂ}

theorem curveLift_of_ne_zero (h : u t ≠ 0) : curveLift u t = ofNeZero h :=
  dite_eq_right h

theorem curveLift_of_eq_zero (h : u t = 0)
    (h' : iteratedDeriv (analyticOrderNatAt u t) u t ≠ 0) :
    curveLift u t = zeroSection (mk ℂ _ h') := by
  rw [curveLift, dite_eq_left h, dite_eq_right h']

/-- Where `u` does not vanish, the line of its lift is spanned by `u t`. -/
theorem pr_curveLift_of_ne_zero (h : u t ≠ 0) : (curveLift u t).pr = mk ℂ (u t) h := by
  rw [curveLift_of_ne_zero h, pr_ofNeZero]

/-- The lift of `u` lies over `u`. -/
@[simp]
theorem blowdown_curveLift (u : ℂ → Fin (n + 1) → ℂ) (t : ℂ) :
    (curveLift u t).blowdown = u t := by
  by_cases h : u t = 0
  · rw [curveLift, dite_eq_left h, h]
    split_ifs <;> exact blowdown_zeroSection _
  · rw [curveLift_of_ne_zero h, blowdown_ofNeZero]

/-- The lift of `u` meets the exceptional divisor exactly over the zeros of `u`. -/
theorem curveLift_mem_exceptionalDivisor_iff :
    curveLift u t ∈ exceptionalDivisor n ↔ u t = 0 := by
  rw [mem_exceptionalDivisor_iff, blowdown_curveLift]

/-- At a zero `t₀` of order `k` of an analytic curve `u`, the lift is the point of the exceptional
divisor on the line of the first nonvanishing derivative `iteratedDeriv k u t₀`, which is nonzero
by Mathlib's `analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero`. -/
theorem curveLift_apply_self {k : ℕ} (hu : AnalyticAt ℂ u t₀) (h0 : u t₀ = 0)
    (hk : analyticOrderAt u t₀ = k) :
    curveLift u t₀ = zeroSection (mk ℂ (iteratedDeriv k u t₀)
      ((analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero hu).1 hk).2) := by
  obtain rfl : analyticOrderNatAt u t₀ = k := by simp [analyticOrderNatAt, hk]
  exact curveLift_of_eq_zero h0 _

/-- If `u t = (t - t₀) ^ k • g t` near `t₀`, with `g` analytic at `t₀` and `g t₀ ≠ 0`, then near
`t₀` the line of the lift of `u` is spanned by `g t`: near `t₀` the lift is `t ↦ ([g t], u t)`. -/
theorem eventually_pr_curveLift_eq_mk {k : ℕ} {g : ℂ → Fin (n + 1) → ℂ}
    (hg : AnalyticAt ℂ g t₀) (hg0 : g t₀ ≠ 0) (hug : ∀ᶠ t in 𝓝 t₀, u t = (t - t₀) ^ k • g t) :
    ∀ᶠ t in 𝓝 t₀, ∃ h : g t ≠ 0, (curveLift u t).pr = mk ℂ (g t) h := by
  have hself : ∃ h : g t₀ ≠ 0, (curveLift u t₀).pr = mk ℂ (g t₀) h := by
    refine ⟨hg0, ?_⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · have hut : u t₀ = g t₀ := by simpa using hug.self_of_nhds
      have hu0 : u t₀ ≠ 0 := hut ▸ hg0
      rw [pr_curveLift_of_ne_zero hu0, mk_eq_mk_iff' ℂ _ _ hu0 hg0]
      exact ⟨1, by simp [hut]⟩
    · have hu0 : u t₀ = 0 := by simpa [zero_pow hk.ne'] using hug.self_of_nhds
      have hua : AnalyticAt ℂ u t₀ :=
        (((analyticAt_id.sub analyticAt_const).pow k).smul hg).congr (hug.mono fun _ h => h.symm)
      rw [curveLift_apply_self hua hu0 (hua.analyticOrderAt_eq_natCast.2 ⟨g, hg, hg0, hug⟩),
        pr_zeroSection, mk_eq_mk_iff' ℂ _ _ _ hg0]
      refine ⟨(k ! : ℂ), ?_⟩
      rw [EventuallyEq.iteratedDeriv_eq (g := fun t => (t - t₀) ^ k • g t) k hug,
        TauCeti.iteratedDeriv_pow_sub_smul_self hg.contDiffAt, Nat.cast_smul_eq_nsmul]
  have hoff : ∀ᶠ t in 𝓝[≠] t₀, ∃ h : g t ≠ 0, (curveLift u t).pr = mk ℂ (g t) h := by
    filter_upwards [nhdsWithin_le_nhds (hg.continuousAt.eventually_ne hg0),
      nhdsWithin_le_nhds hug, self_mem_nhdsWithin] with t hgt hut ht
    have hu0 : u t ≠ 0 := hut ▸ smul_ne_zero (pow_ne_zero _ (sub_ne_zero.2 ht)) hgt
    refine ⟨hgt, ?_⟩
    rw [pr_curveLift_of_ne_zero hu0, mk_eq_mk_iff' ℂ _ _ hu0 hgt]
    exact ⟨(t - t₀) ^ k, hut.symm⟩
  exact (eventually_nhdsWithin_iff.1 hoff).mono fun t h => by
    by_cases ht : t = t₀
    · exact ht ▸ hself
    · exact h ht

/-- The lift of `u` is holomorphic at a point `t₀` where `u` is analytic and has finite order,
that is, does not vanish identically near `t₀`. -/
theorem contMDiffAt_curveLift {r : ℕ∞ω} (hu : AnalyticAt ℂ u t₀)
    (hfin : analyticOrderAt u t₀ ≠ ⊤) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) r (curveLift u) t₀ := by
  refine ContMDiffAt.of_le ?_ le_top
  obtain ⟨g, hg, hg0, hug⟩ := hu.analyticOrderAt_ne_top.1 hfin
  refine (contMDiffAt_iff_contMDiffAt_pr_comp_and_blowdown_comp le_top).2
    ⟨contMDiffAt_of_eventually_eq_mk hg.contDiffAt.contMDiffAt
      (eventually_pr_curveLift_eq_mk hg hg0 hug), ?_⟩
  simpa only [blowdown_curveLift] using hu.contDiffAt.contMDiffAt

/-- The lift of `u` is holomorphic on a set `U` on which `u` is analytic and has finite order at
every point. -/
theorem contMDiffOn_curveLift {r : ℕ∞ω} {U : Set ℂ} (hu : AnalyticOnNhd ℂ u U)
    (hfin : ∀ t ∈ U, analyticOrderAt u t ≠ ⊤) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) r (curveLift u) U := fun t ht =>
  (contMDiffAt_curveLift (hu t ht) (hfin t ht)).contMDiffWithinAt

/-- The lift of `u` is continuous on a set `U` on which `u` is analytic and has finite order at
every point. -/
theorem continuousOn_curveLift {U : Set ℂ} (hu : AnalyticOnNhd ℂ u U)
    (hfin : ∀ t ∈ U, analyticOrderAt u t ≠ ⊤) : ContinuousOn (curveLift u) U :=
  (contMDiffOn_curveLift (r := 0) hu hfin).continuousOn

/-- Uniqueness of the lift of a curve: on an open set `U` on which `u` is analytic and has finite
order at every point, a map `ũ : ℂ → BlowupModel n` that is continuous on `U` and lies over `u`
there agrees with the lift of `u` on `U`. -/
theorem eqOn_curveLift_of_blowdown_comp {U : Set ℂ} (hU : IsOpen U) (hu : AnalyticOnNhd ℂ u U)
    (hfin : ∀ t ∈ U, analyticOrderAt u t ≠ ⊤) {ũ : ℂ → BlowupModel n} (hũ : ContinuousOn ũ U)
    (hũu : ∀ t ∈ U, (ũ t).blowdown = u t) : Set.EqOn ũ (curveLift u) U :=
  hU.eqOn_of_eventuallyEq_codiscreteWithin hũ (continuousOn_curveLift hu hfin) <| by
    filter_upwards [hu.codiscreteWithin_setOfPred_analyticOrderAt_eq_zero_or_top,
      self_mem_codiscreteWithin U] with t ht htU
    have : u t ≠ 0 := (hu t htU).analyticOrderAt_eq_zero.1 (ht.resolve_right (hfin t htU))
    exact eq_of_blowdown_eq (by rwa [hũu t htU]) (by rw [hũu t htU, blowdown_curveLift])

/-- Uniqueness of the lift of a curve: on an open set `U` on which `u` is analytic and has finite
order at every point, a continuous map `ũ : U → BlowupModel n` lying over `u` is the lift of
`u`. -/
theorem curveLift_eq_of_blowdown_comp {U : Set ℂ} (hU : IsOpen U) (hu : AnalyticOnNhd ℂ u U)
    (hfin : ∀ t ∈ U, analyticOrderAt u t ≠ ⊤) {ũ : U → BlowupModel n} (hũ : Continuous ũ)
    (hũu : ∀ t, (ũ t).blowdown = u t) (t : U) : ũ t = curveLift u t := by
  classical
  let v : ℂ → BlowupModel n := fun s => if hs : s ∈ U then ũ ⟨s, hs⟩ else curveLift u s
  have hv : U.domRestrict v = ũ := funext fun s => by simp [v]
  have h := eqOn_curveLift_of_blowdown_comp hU hu hfin (ũ := v)
    (continuousOn_iff_continuous_domRestrict.2 (hv.symm ▸ hũ)) (fun s hs => by simp [v, hs, hũu])
    t.property
  simpa [v] using h

open TauCeti TauCeti.Manifold TopologicalSpace in
/-- The real derivative of the lift of a curve off the zeros of the curve. At `t` with `u` complex
differentiable at `t` and `u t ≠ 0`, the derivative of `curveLift u` along `c` is the derivative
of the inverse of the blowdown off the exceptional divisor, read in the model, at `u t` along
`c • u'(t)`. -/
theorem mfderiv_curveLift_of_ne_zero (hu : DifferentiableAt ℂ u t) (h0 : u t ≠ 0) (c : ℂ) :
    mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) (curveLift u) t c =
      mfderiv 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ)
        (Subtype.val ∘ (blowdownDiffeomorph n).symm) ⟨u t, mem_puncturedSpace.2 h0⟩
        (c • deriv u t) := by
  -- Near `t`, the curve `u` as a curve `ũ` in `E ∖ 0`.
  set ũ : ℂ → puncturedSpace (Fin (n + 1) → ℂ) := fun s ↦
    if h : u s = 0 then ⟨u t, mem_puncturedSpace.2 h0⟩ else ⟨u s, mem_puncturedSpace.2 h⟩
  have hne : ∀ᶠ s in 𝓝 t, u s ≠ 0 := hu.continuousAt.eventually_ne h0
  have hev : Subtype.val ∘ ũ =ᶠ[𝓝 t] u := by
    filter_upwards [hne] with s hs
    simp [ũ, hs]
  have hũt : ũ t = ⟨u t, mem_puncturedSpace.2 h0⟩ := Subtype.ext hev.self_of_nhds
  have hũd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) ũ t :=
    mdifferentiableAt_subtype_val_comp_iff.1
      ((hu.restrictScalars ℝ).mdifferentiableAt.congr_of_eventuallyEq hev)
  -- Near `t`, the lift is `ũ` followed by the inverse of the blowdown off the divisor.
  set Ψ : puncturedSpace (Fin (n + 1) → ℂ) → BlowupModel n :=
    Subtype.val ∘ (blowdownDiffeomorph n).symm
  have hΨ : ContMDiff 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) ω Ψ :=
    (contMDiff_subtypeVal.comp (blowdownDiffeomorph n).symm.contMDiff).restrictScalars' ℝ
  have hlift : curveLift u =ᶠ[𝓝 t] Ψ ∘ ũ := by
    filter_upwards [hne] with s hs
    simp [Ψ, ũ, hs, curveLift_of_ne_zero hs]
  have h₁ := (((hΨ.mdifferentiableAt (by simp)).hasMFDerivAt.comp t
    hũd.hasMFDerivAt).congr_of_eventuallyEq_abuse hlift).mfderiv
  have h₂ : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) ũ t c = c • deriv u t :=
    ((mfderiv_subtype_val_comp_apply c).symm.trans
      (mvfderiv_apply_eq_mfderiv_apply (Subtype.val ∘ ũ) t c).symm).trans
      ((DFunLike.congr_fun hev.mvfderiv_eq c).trans ((mvfderiv_eq_fderiv_apply u t c).trans
        (hu.fderiv_restrictScalars_eq_smul_deriv ℝ c)))
  rw [← hũt]
  -- The tangent spaces at `curveLift u t` and at `Ψ (ũ t)` are both `E`.
  exact (DFunLike.congr_fun h₁ c).trans ((ContinuousLinearMap.comp_apply
    (mfderiv 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) Ψ (ũ t))
    (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) ũ t) c).trans (congrArg _ h₂))

/-- The chain rule for `blowdown ∘ curveLift u = u`: at `t` where the lift is real
differentiable, the real differential of `blowdown` at `curveLift u t` sends the derivative of the
lift along `c` to the derivative of `u` along `c`. -/
theorem mfderiv_blowdown_mfderiv_curveLift_eq_mfderiv
    (hlift : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) (curveLift u) t) (c : ℂ) :
    mfderiv 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) blowdown (curveLift u t)
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) (curveLift u) t c) =
      mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) u t c := by
  have hb : MDifferentiableAt 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) blowdown
      (curveLift u t) :=
    ((contMDiff_blowdown (n := n) 1).restrictScalars' ℝ).mdifferentiableAt one_ne_zero
  have hfun : blowdown ∘ curveLift u = u := funext (blowdown_curveLift u)
  exact (mfderiv_comp_apply t hb hlift c).symm.trans
    (congrArg (fun g ↦ mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) g t c) hfun)

open TauCeti in
/-- The chain rule for `blowdown ∘ curveLift u = u`: at `t` where `u` is complex differentiable
and its lift is real differentiable, the real differential of `blowdown` at `curveLift u t` sends
the derivative of the lift along `c` to `c • u'(t)`. -/
theorem mfderiv_blowdown_mfderiv_curveLift (hu : DifferentiableAt ℂ u t)
    (hlift : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) (curveLift u) t) (c : ℂ) :
    mfderiv 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) blowdown (curveLift u t)
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) (curveLift u) t c) =
      (c • deriv u t : Fin (n + 1) → ℂ) :=
  -- The tangent spaces of `ℂ` and of `E` are `ℂ` and `E`.
  (mfderiv_blowdown_mfderiv_curveLift_eq_mfderiv hlift c).trans
    ((mvfderiv_apply_eq_mfderiv_apply u t c).symm.trans
      ((mvfderiv_eq_fderiv_apply u t c).trans (hu.fderiv_restrictScalars_eq_smul_deriv ℝ c)))

/-! ### The lift of a line through the origin -/

variable {v : Fin (n + 1) → ℂ}

/-- The lift of the line `t ↦ t • v` sends `0` to the point `zeroSection ℓ` of the exceptional
divisor over the line `ℓ` spanned by `v`. -/
theorem curveLift_smul_zero (hv : v ≠ 0) :
    curveLift (· • v) (0 : ℂ) = zeroSection (mk ℂ v hv) := by
  classical
  rw [curveLift_apply_self (by fun_prop) (zero_smul ℂ v) (k := 1)
    (by simpa using analyticOrderAt_id_smul_const hv)]
  congr 1
  rw [mk_eq_mk_iff' ℂ _ _ _ hv]
  exact ⟨1, by simp [iteratedDeriv_one, deriv_smul_const]⟩

/-- The lift of the line `t ↦ t • v` lies, at every `t`, on the line `ℓ` spanned by `v`. -/
@[simp]
theorem pr_curveLift_smul (hv : v ≠ 0) (t : ℂ) :
    (curveLift (· • v) t).pr = mk ℂ v hv := by
  rcases eq_or_ne t 0 with rfl | ht
  · rw [curveLift_smul_zero hv, pr_zeroSection]
  · rw [pr_curveLift_of_ne_zero (smul_ne_zero ht hv), mk_eq_mk_iff' ℂ _ _ _ hv]
    exact ⟨t, rfl⟩

/-- The lift of the line `t ↦ t • v` through a nonzero `v` is holomorphic. -/
theorem contMDiff_curveLift_smul (hv : v ≠ 0) {r : ℕ∞ω} :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) r (curveLift (· • v)) := fun t ↦
  contMDiffAt_curveLift (by fun_prop)
    ((AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero t fun _ ↦ by fun_prop).not.2
      fun h ↦ hv (by simpa using congrFun h 1))

/-- The lift of the line `t ↦ t • v` through a nonzero `v` is smooth over `ℝ`. -/
theorem contMDiff_curveLift_smul_real (hv : v ≠ 0) {r : ℕ∞ω} :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) r (curveLift (· • v)) :=
  ContMDiff.restrictScalars' ℝ (contMDiff_curveLift_smul hv)

end Curve

end BlowupModel

end SymplecticGeometry

end
