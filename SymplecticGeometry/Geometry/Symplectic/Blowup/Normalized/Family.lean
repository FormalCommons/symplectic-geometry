/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Blowup.Normalized.Basic
public import SymplecticGeometry.Geometry.Symplectic.IsotopyExtension.Ball.Basic
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.UnitInterval
import TauCeti.Geometry.Manifold.ContMDiff.Subtype

/-!
# Families of normalized ball embeddings and their lifts

Fix a normalization `hN : IsNormalizedAt σ J p₀ δ ψ₀`, and let `ψ : unitInterval × StdSpace → M`
be a smooth family of symplectic ball embeddings of radius `r` (`IsSymplecticBallFamily σ r ψ`)
whose slices `ψ (t, ·)` are normalized ball embeddings of weight `l t` and width `ε t`, with `ε`
continuous. This file shows that the lifts `ψ̃_t` of the slices to the blowup
`Blowup hN.blowupChart` form a smooth family: the map `(t, y) ↦ ψ̃_t y` is jointly smooth on
`unitInterval × openNbhd n r`, and `(t, y) ↦ (t, ψ̃_t y)` is a local diffeomorphism of
`unitInterval × openNbhd n r` into `unitInterval × Blowup hN.blowupChart`.

These are the inputs, on the side of the lifts, to the smoothness in `t` of the forms
`ω̃_{ψ_t, l t, ε t}` (McDuff–Salamon, Theorem 7.1.21 (iii)).

## Main results

* `SymplecticGeometry.IsNormalizedBallEmbedding.contMDiff_ballLift_family`: the lifts of the
  slices are jointly smooth in the time and the point.
* `SymplecticGeometry.IsNormalizedBallEmbedding.isLocalDiffeomorph_prodMk_ballLift_family`: the
  map `(t, y) ↦ (t, ψ̃_t y)` is a local diffeomorphism.

## Implementation notes

Near a point `(t₀, y₀)` with `y₀` on the exceptional divisor, `y₀` lies in `openNbhd n (ε t₀)`,
and by continuity of `ε` so does `y` in `openNbhd n (ε t)` for `(t, y)` near `(t₀, y₀)`; there
every lift is the inclusion of the model piece, so the family is locally the lift `ψ̃_{t₀}`,
independent of `t`. Off the divisor every lift is `inl ∘ ψ (t, ·) ∘ π`, jointly smooth by the
joint smoothness of `ψ`. Continuity of `ε` is all that is asked of the widths, and nothing is
asked of the weights. The second result is
`ContMDiff.isLocalDiffeomorph_prodMk_unitInterval`, each slice being a local diffeomorphism by
`IsNormalizedBallEmbedding.isLocalDiffeomorph_ballLift`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §7.1,
  Theorem 7.1.21.
-/

public section

noncomputable section

open Set Topology
open scoped ContDiff Manifold TauCeti.ComplexManifold

namespace SymplecticGeometry

open TauCeti BlowupModel

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Fin (n + 1) → ℂ) M]
  [IsManifold 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ M]
  {σ : SmoothTwoForm 𝓘(ℝ, Fin (n + 1) → ℂ) M}
  {J : SmoothAlmostComplexStructure 𝓘(ℝ, Fin (n + 1) → ℂ) M} {p₀ : M} {δ : ℝ}
  {ψ₀ : StdSpace (Fin (n + 1)) → M} {hN : IsNormalizedAt σ J p₀ δ ψ₀}
  {ψ : unitInterval × StdSpace (Fin (n + 1)) → M} {r : ℝ} {l ε : unitInterval → ℝ}

namespace IsNormalizedBallEmbedding

/-- Near a point of the exceptional divisor, the lifts of the slices of a family of normalized
ball embeddings with continuous widths do not depend on the time: they are all the inclusion of
the model piece. -/
private theorem ballLift_family_eventuallyEq_of_blowdown_eq_zero
    (hψ : ∀ t, IsNormalizedBallEmbedding hN (fun z ↦ ψ (t, z)) r (l t) (ε t))
    (hε : Continuous ε) {p : unitInterval × openNbhdOpens n r}
    (hp : (p.2 : BlowupModel n).blowdown = 0) :
    (fun q : unitInterval × openNbhdOpens n r ↦
        (hψ q.1).ballLift ⟨q.2, mem_openNbhdOpens_iff.1 q.2.property⟩) =ᶠ[𝓝 p]
      fun q ↦ (hψ p.1).ballLift ⟨q.2, mem_openNbhdOpens_iff.1 q.2.property⟩ := by
  have hc : Continuous fun q : unitInterval × openNbhdOpens n r ↦
      ‖complexToRealEuclidean (Fin (n + 1)) (q.2 : BlowupModel n).blowdown‖ :=
    ((complexToRealEuclidean (Fin (n + 1))).continuous.comp (continuous_blowdown.comp
      (continuous_subtypeVal.comp continuous_snd))).norm
  have hp₁ : ∀ t, (p.2 : BlowupModel n) ∈ openNbhd n (ε t) := fun t ↦
    exceptionalDivisor_subset_openNbhd (hψ t).width_pos (mem_exceptionalDivisor_iff.2 hp)
  have hW : IsOpen {q : unitInterval × openNbhdOpens n r |
      (q.2 : BlowupModel n) ∈ openNbhd n (ε q.1) ∧ (q.2 : BlowupModel n) ∈ openNbhd n (ε p.1)} := by
    simp only [mem_openNbhd_iff]
    exact (isOpen_lt hc (hε.comp continuous_fst)).inter (isOpen_lt hc continuous_const)
  filter_upwards [hW.mem_nhds ⟨hp₁ p.1, hp₁ p.1⟩] with q hq
  rw [(hψ q.1).ballLift_of_mem_openNbhd _ hq.1, (hψ p.1).ballLift_of_mem_openNbhd _ hq.2]

/-- Off the exceptional divisor, the lifts of the slices of a family of normalized ball
embeddings are jointly smooth, as `inl ∘ ψ (t, ·) ∘ π`. -/
private theorem contMDiffAt_ballLift_family_of_blowdown_ne_zero
    (hψ : ∀ t, IsNormalizedBallEmbedding hN (fun z ↦ ψ (t, z)) r (l t) (ε t))
    (hψf : IsSymplecticBallFamily σ r ψ) {p : unitInterval × openNbhdOpens n r}
    (hp : (p.2 : BlowupModel n).blowdown ≠ 0) :
    ContMDiffAt ((𝓡∂ 1).prod 𝓘(ℝ, Fin (n + 1) → ℂ)) 𝓘(ℝ, Fin (n + 1) → ℂ) ∞
      (fun q : unitInterval × openNbhdOpens n r ↦
        (hψ q.1).ballLift ⟨q.2, mem_openNbhdOpens_iff.1 q.2.property⟩) p := by
  classical
  set e := complexToRealEuclidean (Fin (n + 1))
  obtain ⟨U, hU, hrU, hψU⟩ := hψf.exists_contMDiffOn
  let V : Set (unitInterval × openNbhdOpens n r) := {q | (q.2 : BlowupModel n).blowdown ≠ 0}
  have hV : IsOpen V := isOpen_ne_fun (continuous_blowdown.comp
    (continuous_subtypeVal.comp continuous_snd)) continuous_const
  let g : unitInterval × openNbhdOpens n r → Blowup.puncturedOpens hN.blowupChart := fun q ↦
    if h : q ∈ V then
      ⟨ψ (q.1, e (q.2 : BlowupModel n).blowdown),
        (hψ q.1).apply_blowdown_mem_puncturedOpens (mem_openNbhdOpens_iff.1 q.2.property) h⟩
    else
      ⟨ψ (p.1, e (p.2 : BlowupModel n).blowdown),
        (hψ p.1).apply_blowdown_mem_puncturedOpens (mem_openNbhdOpens_iff.1 p.2.property) hp⟩
  -- The point map `(t, y) ↦ (t, π y)`, read on `StdSpace`, is smooth with values in `univ ×ˢ U`.
  have hk : ContMDiff ((𝓡∂ 1).prod 𝓘(ℝ, Fin (n + 1) → ℂ))
      ((𝓡∂ 1).prod 𝓘(ℝ, StdSpace (Fin (n + 1)))) ∞
      (fun q : unitInterval × openNbhdOpens n r ↦ (q.1, e (q.2 : BlowupModel n).blowdown)) :=
    contMDiff_fst.prodMk (e.contDiff.contMDiff.comp
      ((((BlowupModel.contMDiff_blowdown ∞).restrictScalars' ℝ).comp
        contMDiff_subtypeVal).comp contMDiff_snd))
  have hkU : (p.1, e (p.2 : BlowupModel n).blowdown) ∈ univ ×ˢ U :=
    ⟨mem_univ _, hrU (Metric.mem_closedBall.2 (by
      simpa using (mem_openNbhd_iff.1 (mem_openNbhdOpens_iff.1 p.2.property)).le))⟩
  have hg : ContMDiffAt ((𝓡∂ 1).prod 𝓘(ℝ, Fin (n + 1) → ℂ)) 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ g p := by
    rw [← ContMDiffAt.subtypeVal_comp_iff]
    refine (((hψU.contMDiffAt ((isOpen_univ.prod hU).mem_nhds hkU)).comp p
      hk.contMDiffAt)).congr_of_eventuallyEq ?_
    filter_upwards [hV.mem_nhds hp] with q hq
    simp only [g, dite_eq_left hq, Function.comp_apply]
  refine ((Blowup.isLocalDiffeomorph_inl_real _ (g p)).contMDiffAt.comp p hg).congr_of_eventuallyEq
    ?_
  filter_upwards [hV.mem_nhds hp] with q hq
  rw [(hψ q.1).ballLift_of_blowdown_ne_zero _ hq, Function.comp_apply]
  simp only [g, e, dite_eq_left hq]

/-- **The lifts of a family of normalized ball embeddings are jointly smooth.** Let
`ψ : unitInterval × StdSpace → M` be a smooth family of symplectic ball embeddings of radius `r`
whose slices `ψ (t, ·)` are normalized ball embeddings of weight `l t` and width `ε t`, for a
continuous `ε`. Then the map `(t, y) ↦ ψ̃_t y`, from `unitInterval × openNbhd n r` to the blowup,
is smooth. -/
theorem contMDiff_ballLift_family
    (hψ : ∀ t, IsNormalizedBallEmbedding hN (fun z ↦ ψ (t, z)) r (l t) (ε t))
    (hψf : IsSymplecticBallFamily σ r ψ) (hε : Continuous ε) :
    ContMDiff ((𝓡∂ 1).prod 𝓘(ℝ, Fin (n + 1) → ℂ)) 𝓘(ℝ, Fin (n + 1) → ℂ) ∞
      (fun p : unitInterval × openNbhdOpens n r ↦
        (hψ p.1).ballLift ⟨p.2, mem_openNbhdOpens_iff.1 p.2.property⟩) := by
  intro p
  by_cases hp : (p.2 : BlowupModel n).blowdown = 0
  · refine ContMDiffAt.congr_of_eventuallyEq ?_
      (ballLift_family_eventuallyEq_of_blowdown_eq_zero hψ hε hp)
    exact ((hψ p.1).contMDiff_ballLift.comp contMDiff_snd).contMDiffAt
  · exact contMDiffAt_ballLift_family_of_blowdown_ne_zero hψ hψf hp

/-- **The lifts of a family of normalized ball embeddings give a local diffeomorphism.** For a
family as in `contMDiff_ballLift_family`, the map `(t, y) ↦ (t, ψ̃_t y)` is a local diffeomorphism
of `unitInterval × openNbhd n r` into `unitInterval × Blowup hN.blowupChart`, at every point,
also over the ends of the interval. -/
theorem isLocalDiffeomorph_prodMk_ballLift_family
    (hψ : ∀ t, IsNormalizedBallEmbedding hN (fun z ↦ ψ (t, z)) r (l t) (ε t))
    (hψf : IsSymplecticBallFamily σ r ψ) (hε : Continuous ε) :
    IsLocalDiffeomorph ((𝓡∂ 1).prod 𝓘(ℝ, Fin (n + 1) → ℂ)) ((𝓡∂ 1).prod 𝓘(ℝ, Fin (n + 1) → ℂ)) ∞
      (fun p : unitInterval × openNbhdOpens n r ↦
        (p.1, (hψ p.1).ballLift ⟨p.2, mem_openNbhdOpens_iff.1 p.2.property⟩)) :=
  (contMDiff_ballLift_family hψ hψf hε).isLocalDiffeomorph_prodMk_unitInterval fun t ↦
    (hψ t).isLocalDiffeomorph_ballLift

end IsNormalizedBallEmbedding

end SymplecticGeometry

end
