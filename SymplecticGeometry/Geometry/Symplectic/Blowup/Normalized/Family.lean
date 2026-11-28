/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Blowup.Normalized.Basic
public import SymplecticGeometry.Geometry.Symplectic.IsotopyExtension.Ball.Basic
public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Basic
import SymplecticGeometry.Geometry.Manifold.ContMDiff.Opens
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.UnitInterval
import SymplecticGeometry.Geometry.Symplectic.Moser.Stability
import SymplecticGeometry.Geometry.Manifold.MFDeriv.Opens

/-!
# Families of normalized ball embeddings, their lifts and their forms

Fix a normalization `hN : IsNormalizedAt σ J p₀ δ ψ₀`, and let `ψ : unitInterval × StdSpace → M`
be a smooth family of symplectic ball embeddings of radius `r` (`IsSymplecticBallFamily σ r ψ`)
whose slices `ψ (t, ·)` are normalized ball embeddings of weight `l t` and width `ε t`, with `ε`
continuous. This file shows that the lifts `ψ̃_t` of the slices to the blowup
`Blowup hN.blowupChart` form a smooth family: the map `(t, y) ↦ ψ̃_t y` is jointly smooth on
`unitInterval × openNbhd n r`, and `(t, y) ↦ (t, ψ̃_t y)` is a local diffeomorphism of
`unitInterval × openNbhd n r` into `unitInterval × Blowup hN.blowupChart`.

From these, the forms `ω̃_{ψ_t, l t, ε t}` of the blowup are a smooth family in `t` when `l`
and `ε` are smooth (McDuff–Salamon, Theorem 7.1.21 (iii)). Shrinking the weight and the width of
a single normalized ball embedding `ψ` until `B(l + ε)` lies where `ψ = ψ₀` is pseudoholomorphic
then joins `ω̃_{ψ,l,ε}`, through symplectic forms, to a form compatible with the almost complex
blowup of `J` (Theorem 7.1.21 (vi)).

Finally, for two profiles `h₀ h₁` of the same weight and collar, the forms `ω̃_{ψ,l,ε}` of `h₀`
and `h₁` are related by a diffeotopy of the blowup supported in the lifted ball (Theorem 7.1.21
(vii)), by Moser's argument along the segment of profiles.

## Main results

* `SymplecticGeometry.IsNormalizedBallEmbedding.contMDiff_ballLift_family`: the lifts of the
  slices are jointly smooth in the time and the point.
* `SymplecticGeometry.IsNormalizedBallEmbedding.isLocalDiffeomorph_prodMk_ballLift_family`: the
  map `(t, y) ↦ (t, ψ̃_t y)` is a local diffeomorphism.
* `SymplecticGeometry.IsNormalizedBallEmbedding.isSmoothFamily_of_eq_on_ballLift`: a family of
  two-forms on the blowup is smooth if the lifts pull it back to a smooth family of forms of the
  model, and off the images of `closedNbhd n (c t)`, for a continuous `c < r`, it is the
  pull-back of `σ` by the blowdown.
* `SymplecticGeometry.IsNormalizedBallEmbedding.isSmoothFamily_normalizedBlowupForm`: for smooth
  `l` and `ε`, the forms `ω̃_{ψ_t, l t, ε t}` are a smooth family.
* `SymplecticGeometry.IsNormalizedBallEmbedding.exists_family_normalizedBlowupForm`: moving the
  weight and the width of one normalized ball embedding linearly, along a smooth `ρ` with values
  in `[0, 1]`, gives a smooth family of symplectic forms of the blowup.
* `SymplecticGeometry.IsNormalizedBallEmbedding.exists_path_compatible`: `ω̃_{ψ,l,ε}` is joined,
  through a smooth path of symplectic two-forms of the blowup, to a form compatible with the
  almost complex blowup of `J`.
* `SymplecticGeometry.IsNormalizedBallEmbedding.exists_diffeotopy_normalizedBlowupForm_of_profile`:
  the forms of two profiles are related by a diffeotopy fixed off the image of
  `closedNbhd n (l + ε)`.

## Implementation notes

Near a point `(t₀, y₀)` with `y₀` on the exceptional divisor, `y₀` lies in `openNbhd n (ε t₀)`,
and by continuity of `ε` so does `y` in `openNbhd n (ε t)` for `(t, y)` near `(t₀, y₀)`; there
every lift is the inclusion of the model piece, so the family is locally the lift `ψ̃_{t₀}`,
independent of `t`. Off the divisor every lift is `inl ∘ ψ (t, ·) ∘ π`, jointly smooth by the
joint smoothness of `ψ`. Continuity of `ε` is all that is asked of the widths, and nothing is
asked of the weights. The second result is
`ContMDiff.isLocalDiffeomorph_prodMk_unitInterval`, each slice being a local diffeomorphism by
`IsNormalizedBallEmbedding.isLocalDiffeomorph_ballLift`.

For the gluing step, at a point `(t₀, ψ̃_{t₀} y₀)` of the image of a lift, smoothness comes from
the model through the local diffeomorphism `(t, y) ↦ (t, ψ̃_t y)`
(`IsSmoothFamily.contMDiffAt_of_mpullback_family`). At any other point `(t₀, x₀)`, the points
`(t, ψ̃_t y)` with `y ∈ closedNbhd n (c t)` form a compact set, the image of a compact subset of
`unitInterval × openNbhd n r`, hence a closed one since the blowup is Hausdorff when `M` is; off
it the family is the constant family `blowdown^* σ`. The theorem for `ω̃_{ψ_t, l t, ε t}` is the
gluing step with `P t = profileForm n (l t) (ε t)`, smooth by
`BlowupModel.isSmoothFamily_profileForm`, and `c = l + ε`.

For two profiles, the segment `(1 - s) • h₀ + s • h₁` consists of profiles, and its forms are the
segment between the two forms (`normalizedBlowupForm_one_sub_smul_add_smul`), each symplectic
(`isSymplectic_normalizedBlowupForm`). Their difference has a primitive vanishing off the compact
image of `closedNbhd n (l + ε)` (`exists_mextDeriv_eq_normalizedBlowupForm_sub`), so
`TauCeti.SmoothTwoForm.exists_diffeotopy_mpullback_eq_of_mextDeriv_eq_sub` gives the diffeotopy.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §7.1,
  Theorem 7.1.21 (iii), (vi) and (vii).
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
  have hc : Continuous fun q : unitInterval × openNbhdOpens n r ↦ (q.2 : BlowupModel n) :=
    continuous_subtypeVal.comp continuous_snd
  have hp₁ : ∀ t, (p.2 : BlowupModel n) ∈ openNbhd n (ε t) := fun t ↦
    exceptionalDivisor_subset_openNbhd (hψ t).width_pos (mem_exceptionalDivisor_iff.2 hp)
  have hW : IsOpen {q : unitInterval × openNbhdOpens n r |
      (q.2 : BlowupModel n) ∈ openNbhd n (ε q.1) ∧ (q.2 : BlowupModel n) ∈ openNbhd n (ε p.1)} :=
    (isOpen_setOfPred_mem_openNbhd hc (hε.comp continuous_fst)).inter
      (isOpen_setOfPred_mem_openNbhd hc continuous_const)
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
  set e := complexToRealEuclidean (Fin (n + 1))
  obtain ⟨U, hU, hrU, hψU⟩ := hψf.exists_contMDiffOn
  let V : Set (unitInterval × openNbhdOpens n r) := {q | (q.2 : BlowupModel n).blowdown ≠ 0}
  have hV : IsOpen V := isOpen_ne_fun (continuous_blowdown.comp
    (continuous_subtypeVal.comp continuous_snd)) continuous_const
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
  -- Near `p`, the map `(t, y) ↦ ψ (t, π y)` lifts to the punctured open set of the gluing.
  obtain ⟨g, hg, hgψ⟩ := ContMDiffAt.exists_subtypeVal_comp_eventuallyEq
    ((hψU.contMDiffAt ((isOpen_univ.prod hU).mem_nhds hkU)).comp p hk.contMDiffAt)
    (W := Blowup.puncturedOpens hN.blowupChart)
    ((hψ p.1).apply_blowdown_mem_puncturedOpens (mem_openNbhdOpens_iff.1 p.2.property) hp)
  refine ((Blowup.isLocalDiffeomorph_inl_real _ (g p)).contMDiffAt.comp p hg).congr_of_eventuallyEq
    ?_
  filter_upwards [hV.mem_nhds hp, hgψ] with q hq hgq
  rw [(hψ q.1).ballLift_of_blowdown_ne_zero _ hq, Function.comp_apply]
  exact congrArg _ (Subtype.ext (by simpa using hgq.symm))

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

/-! ### Smooth families of forms on the blowup -/

/-- On the image of the lifts, a family of forms that the lifts pull back to a smooth family of
forms of the model is smooth: its slice section is smooth at each point `(t₀, ψ̃_{t₀} y₀)`. -/
private theorem contMDiffAt_of_eq_on_ballLift
    (hψ : ∀ t, IsNormalizedBallEmbedding hN (fun z ↦ ψ (t, z)) r (l t) (ε t))
    (hψf : IsSymplecticBallFamily σ r ψ) (hε : Continuous ε)
    {P : unitInterval → SmoothTwoForm 𝓘(ℝ, Fin (n + 1) → ℂ) (BlowupModel n)}
    (hP : IsSmoothFamily (𝓡∂ 1) P)
    {β : unitInterval → SmoothTwoForm 𝓘(ℝ, Fin (n + 1) → ℂ) (Blowup hN.blowupChart)}
    (hβP : ∀ t, ∀ y ∈ openNbhd n r, TauCeti.mpullback 𝓘(ℝ, Fin (n + 1) → ℂ)
      𝓘(ℝ, Fin (n + 1) → ℂ) (hψ t).ballLiftPartialDiffeomorph (β t).val y = (P t).val y)
    (p : unitInterval × openNbhdOpens n r) :
    ContMDiffAt ((𝓡∂ 1).prod 𝓘(ℝ, Fin (n + 1) → ℂ))
      (𝓘(ℝ, Fin (n + 1) → ℂ).prod 𝓘(ℝ, (Fin (n + 1) → ℂ) [⋀^Fin 2]→L[ℝ] ℝ)) ∞
      (SymplecticGeometry.sliceSection fun t ↦ (β t).val)
      (p.1, (hψ p.1).ballLift ⟨p.2, mem_openNbhdOpens_iff.1 p.2.property⟩) := by
  refine IsSmoothFamily.contMDiffAt_of_mpullback_family (contMDiff_ballLift_family hψ hψf hε)
    (isLocalDiffeomorph_prodMk_ballLift_family hψ hψf hε p) ?_
  -- The lifts pull the `β t` back to the restrictions of the `P t` to `openNbhd n r`.
  convert hP.mpullback (Subtype.val : openNbhdOpens n r → BlowupModel n) contMDiff_subtypeVal
    using 2 with t
  refine Subtype.ext (funext fun y ↦ ?_)
  have hy := mem_openNbhdOpens_iff.1 y.property
  have hfun :
      (fun x : openNbhdOpens n r ↦ (hψ t).ballLift ⟨x, mem_openNbhdOpens_iff.1 x.property⟩) =
      (hψ t).ballLiftPartialDiffeomorph ∘ Subtype.val :=
    funext fun x ↦ ((hψ t).ballLiftPartialDiffeomorph_apply _).symm
  have hΦ := (hψ t).ballLiftPartialDiffeomorph.mdifferentiableAt (by simp)
    (show (y : BlowupModel n) ∈ (hψ t).ballLiftPartialDiffeomorph.source by simpa using hy)
  simp only [SmoothForm.coe_mpullback]
  rw [hfun, mpullback_comp_at mdifferentiableAt_subtypeVal hΦ,
    mpullback_subtype_val_apply, mpullback_subtype_val_apply, hβP t y hy]

/-- **Gluing a smooth family of forms on the blowup.** Let `M` be Hausdorff, and `ψ` a smooth
family of symplectic ball embeddings of radius `r` whose slices are normalized ball embeddings
of weight `l t` and width `ε t`, with `ε` continuous, and `P` a smooth family of two-forms on
the model blowup. Let `c` be continuous with `c t < r`. A family `β` of two-forms on the blowup
is smooth if, for every `t`, the lift `ψ̃_t` pulls `β t` back to `P t` on `openNbhd n r`, and
`β t` is the pull-back of `σ` by the blowdown off the image under `ψ̃_t` of `closedNbhd n (c t)`. -/
theorem isSmoothFamily_of_eq_on_ballLift [T2Space M]
    (hψ : ∀ t, IsNormalizedBallEmbedding hN (fun z ↦ ψ (t, z)) r (l t) (ε t))
    (hψf : IsSymplecticBallFamily σ r ψ) (hε : Continuous ε)
    {P : unitInterval → SmoothTwoForm 𝓘(ℝ, Fin (n + 1) → ℂ) (BlowupModel n)}
    (hP : IsSmoothFamily (𝓡∂ 1) P) {c : unitInterval → ℝ} (hc : Continuous c)
    (hcr : ∀ t, c t < r)
    {β : unitInterval → SmoothTwoForm 𝓘(ℝ, Fin (n + 1) → ℂ) (Blowup hN.blowupChart)}
    (hβP : ∀ t, ∀ y ∈ openNbhd n r, TauCeti.mpullback 𝓘(ℝ, Fin (n + 1) → ℂ)
      𝓘(ℝ, Fin (n + 1) → ℂ) (hψ t).ballLiftPartialDiffeomorph (β t).val y = (P t).val y)
    (hβσ : ∀ t, ∀ x ∉ (hψ t).ballLiftPartialDiffeomorph '' closedNbhd n (c t),
      (β t).val x = (SmoothForm.mpullback (Blowup.blowdown hN.blowupChart)
        (Blowup.contMDiff_blowdown_real _) σ).val x) :
    IsSmoothFamily (𝓡∂ 1) β := by
  rw [isSmoothFamily_iff_contMDiff]
  rintro ⟨t₀, x₀⟩
  by_cases hx₀ : x₀ ∈ range (hψ t₀).ballLift
  · obtain ⟨y₀, rfl⟩ := hx₀
    exact contMDiffAt_of_eq_on_ballLift hψ hψf hε hP hβP
      (t₀, ⟨y₀, mem_openNbhdOpens_iff.2 y₀.property⟩)
  -- Off the image of the lift at `t₀`, the family is the constant family `blowdown^* σ` near
  -- `(t₀, x₀)`, since the points `(t, ψ̃_t y)` with `y ∈ closedNbhd n (c t)` form a compact set.
  have hmem {t : unitInterval} {y : BlowupModel n} (hy : y ∈ closedNbhd n (c t)) :
      y ∈ openNbhd n r :=
    closedNbhd_subset_openNbhd (hcr t) hy
  let S : Set (unitInterval × openNbhdOpens n r) :=
    {q | (q.2 : BlowupModel n) ∈ closedNbhd n (c q.1)}
  have hS : IsCompact S := by
    rw [(IsEmbedding.id.prodMap IsEmbedding.subtypeVal).isCompact_iff]
    have himage : Prod.map id Subtype.val '' S =
        {q : unitInterval × BlowupModel n | q.2 ∈ closedNbhd n (c q.1)} := by
      refine Subset.antisymm ?_ fun q hq ↦ ?_
      · rintro _ ⟨q, hq, rfl⟩
        exact hq
      · exact ⟨(q.1, ⟨q.2, mem_openNbhdOpens_iff.2 (hmem hq)⟩), hq, rfl⟩
    rw [himage]
    exact isCompact_setOfPred_mem_closedNbhd hc
  have hK : IsClosed ((fun q ↦ (q.1, (hψ q.1).ballLift
      ⟨q.2, mem_openNbhdOpens_iff.1 q.2.property⟩)) '' S) :=
    (hS.image (continuous_fst.prodMk
      (contMDiff_ballLift_family hψ hψf hε).continuous)).isClosed
  have hnot : (t₀, x₀) ∉ (fun q ↦ (q.1, (hψ q.1).ballLift
      ⟨q.2, mem_openNbhdOpens_iff.1 q.2.property⟩)) '' S := by
    rintro ⟨q, -, hq⟩
    obtain ⟨rfl, rfl⟩ := Prod.ext_iff.1 hq
    exact hx₀ ⟨_, rfl⟩
  refine ((isSmoothFamily_iff_contMDiff.1 (isSmoothFamily_const (J := 𝓡∂ 1) (N := unitInterval)
    (SmoothForm.mpullback (Blowup.blowdown hN.blowupChart)
      (Blowup.contMDiff_blowdown_real _) σ))) (t₀, x₀)).congr_of_eventuallyEq ?_
  filter_upwards [hK.isOpen_compl.mem_nhds hnot] with q hq
  obtain ⟨t, x⟩ := q
  rw [SymplecticGeometry.sliceSection_apply, SymplecticGeometry.sliceSection_apply, hβσ t x ?_]
  rintro ⟨y, hy, rfl⟩
  exact hq ⟨(t, ⟨y, mem_openNbhdOpens_iff.2 (hmem hy)⟩), hy,
    Prod.ext rfl ((hψ t).ballLiftPartialDiffeomorph_apply ⟨y, hmem hy⟩).symm⟩

/-- **The forms `ω̃_{ψ_t, l t, ε t}` form a smooth family** (McDuff–Salamon, Theorem 7.1.21
(iii)). Let `M` be Hausdorff, and `ψ` a smooth family of symplectic ball embeddings of radius `r`
whose slices `ψ (t, ·)` are normalized ball embeddings of weight `l t` and width `ε t`, for
smooth `l` and `ε`. Then the forms `t ↦ ω̃_{ψ_t, l t, ε t}` of the blowup, for the profiles
`blowupProfile (l t) (ε t)`, are a smooth family. -/
theorem isSmoothFamily_normalizedBlowupForm [T2Space M]
    (hψ : ∀ t, IsNormalizedBallEmbedding hN (fun z ↦ ψ (t, z)) r (l t) (ε t))
    (hψf : IsSymplecticBallFamily σ r ψ) (hl : ContMDiff (𝓡∂ 1) 𝓘(ℝ) ∞ l)
    (hε : ContMDiff (𝓡∂ 1) 𝓘(ℝ) ∞ ε) :
    IsSmoothFamily (𝓡∂ 1) fun t ↦ (hψ t).normalizedBlowupForm :=
  isSmoothFamily_of_eq_on_ballLift hψ hψf hε.continuous
    (isSmoothFamily_profileForm (n := n) hl hε (fun t ↦ (hψ t).weight_pos) fun t ↦ (hψ t).width_pos)
    (hl.continuous.add hε.continuous) (fun t ↦ (hψ t).weight_add_width_lt)
    (fun t ↦ (hψ t).normalizedBlowupForm_eq_on_ballLift
      (isBlowupProfile_blowupProfile (hψ t).weight_pos (hψ t).width_pos))
    fun t ↦ (hψ t).normalizedBlowupForm_eq_on_compl

/-- Along a smooth `ρ` with values in `[0, 1]`, the forms of a normalized ball embedding whose
weight and width at time `t` are `(1 - ρ t) * l + ρ t * l'` and `(1 - ρ t) * ε + ρ t * ε'` are
symplectic and smooth in time; they are its own form where `ρ = 0`, and the form of weight `l'`
and width `ε'` where `ρ = 1`. -/
theorem exists_family_normalizedBlowupForm [T2Space M] {ψ : StdSpace (Fin (n + 1)) → M}
    {r l ε : ℝ} (hψ : IsNormalizedBallEmbedding hN ψ r l ε) (hσ : σ.IsSymplectic) {l' ε' : ℝ}
    (hl' : 0 < l') (hε' : 0 < ε') (hε'ε : ε' ≤ ε) (hr : l' + ε' < r) {ρ : unitInterval → ℝ}
    (hρ : ContMDiff (𝓡∂ 1) 𝓘(ℝ) ∞ ρ) (hρ₀ : ∀ t, 0 ≤ ρ t) (hρ₁ : ∀ t, ρ t ≤ 1) :
    ∃ τ : unitInterval → SmoothTwoForm 𝓘(ℝ, Fin (n + 1) → ℂ) (Blowup hN.blowupChart),
      IsSmoothFamily (𝓡∂ 1) τ ∧ (∀ t, (τ t).IsSymplectic) ∧
      (∀ t, ρ t = 0 → τ t = hψ.normalizedBlowupForm) ∧
      ∀ t, ρ t = 1 → τ t = (hψ.of_width_le hl' hε' hε'ε hr).normalizedBlowupForm := by
  have hψt (t : unitInterval) : IsNormalizedBallEmbedding hN (fun z ↦ ψ ((t, z) : unitInterval ×
      StdSpace (Fin (n + 1))).2) r ((1 - ρ t) * l + ρ t * l') ((1 - ρ t) * ε + ρ t * ε') :=
    hψ.of_one_sub_mul_add_mul hl' hε' hε'ε hr (hρ₀ t) (hρ₁ t)
  have hsmooth (a b : ℝ) : ContMDiff (𝓡∂ 1) 𝓘(ℝ) ∞ fun t ↦ (1 - ρ t) * a + ρ t * b :=
    ((contMDiff_const.sub hρ).mul contMDiff_const).add (hρ.mul contMDiff_const)
  -- The form depends only on the weight and the width.
  have hcongr {l₁ ε₁ l₂ ε₂ : ℝ} (h₁ : IsNormalizedBallEmbedding hN ψ r l₁ ε₁)
      (h₂ : IsNormalizedBallEmbedding hN ψ r l₂ ε₂) (hl : l₁ = l₂) (hε : ε₁ = ε₂) :
      h₁.normalizedBlowupForm = h₂.normalizedBlowupForm := by
    subst hl hε
    rfl
  refine ⟨fun t ↦ (hψt t).normalizedBlowupForm,
    isSmoothFamily_normalizedBlowupForm hψt
      (isSymplecticBallFamily_const hψ.isSymplecticBallEmbedding) (hsmooth l l') (hsmooth ε ε'),
    fun t ↦ (hψt t).isSymplectic_normalizedBlowupForm
      (isBlowupProfile_blowupProfile (hψt t).weight_pos (hψt t).width_pos) hσ,
    fun t ht ↦ hcongr _ _ (by simp [ht]) (by simp [ht]),
    fun t ht ↦ hcongr _ _ (by simp [ht]) (by simp [ht])⟩

/-! ### A path to a compatible form -/

/-- **A path of forms of the blowup to a compatible one** (McDuff–Salamon, Theorem 7.1.21 (vi)).
Let `M` be Hausdorff, `σ` symplectic, and `ψ` a normalized ball embedding of radius `r`, weight
`l` and width `ε`. Then there are symplectic two-forms `τ t` of the blowup, smooth in
`t ∈ unitInterval`, with `τ 0 = ω̃_{ψ,l,ε}` (for the profile `blowupProfile l ε`) and `τ 1`
compatible with the almost complex blowup `J̃` of `J`. The cohomology
class of `τ t` may change with `t`. -/
theorem exists_path_compatible [T2Space M] {ψ : StdSpace (Fin (n + 1)) → M} {r l ε : ℝ}
    (hψ : IsNormalizedBallEmbedding hN ψ r l ε) (hσ : σ.IsSymplectic) :
    ∃ τ : unitInterval → SmoothTwoForm 𝓘(ℝ, Fin (n + 1) → ℂ) (Blowup hN.blowupChart),
      IsSmoothFamily (𝓡∂ 1) τ ∧ (∀ t, (τ t).IsSymplectic) ∧ τ 0 = hψ.normalizedBlowupForm ∧
      (τ 1).Compatible
        (Blowup.almostComplexStructure hN.blowupChart J hN.blowupChart_isHolomorphic) := by
  -- Move the weight from `l` to `ε / 3` and the width from `ε` to `ε / 3`, linearly in time.
  have hε : 0 < ε / 3 := by linarith [hψ.width_pos]
  have hr : ε / 3 + ε / 3 < r := by linarith [hψ.weight_pos, hψ.weight_add_width_lt]
  have hεε : ε / 3 ≤ ε := by linarith
  obtain ⟨τ, hτ, hτs, hτ₀, hτ₁⟩ := hψ.exists_family_normalizedBlowupForm hσ hε hε hεε hr
    contMDiff_subtypeVal_Icc unitInterval.nonneg unitInterval.le_one
  refine ⟨τ, hτ, hτs, hτ₀ 0 Set.Icc.coe_zero, ?_⟩
  -- At the end, `B(ε / 3 + ε / 3)` lies in the open ball `B°(ε)`, where `ψ = ψ₀` is
  -- pseudoholomorphic.
  rw [hτ₁ 1 Set.Icc.coe_one]
  refine (hψ.of_width_le hε hε hεε hr).compatible_normalizedBlowupForm
    (isBlowupProfile_blowupProfile hε hε) fun z hz ↦ hψ.isPseudoholomorphicAt ?_
  rw [mem_closedBall_zero_iff] at hz
  rw [mem_ball_zero_iff]
  linarith

/-! ### Two profiles give isotopic forms -/

/-- **The forms of two profiles are isotopic** (McDuff–Salamon, Theorem 7.1.21 (vii)). Let `M` be
Hausdorff, `σ` symplectic, and `ψ` a normalized ball embedding of radius `r`, weight `l` and width
`ε`. For two profiles `h₀ h₁` of the blowup of weight `l` with collar `ε`, there is a diffeotopy
`Φ` of the blowup that fixes, at all times, every point off the image under the lift `ψ̃` of the
compact set `L(l + ε) = closedNbhd n (l + ε)`, and whose final map pulls `ω̃_{ψ,l,ε}` for `h₁`
back to `ω̃_{ψ,l,ε}` for `h₀`. -/
theorem exists_diffeotopy_normalizedBlowupForm_of_profile [T2Space M]
    {ψ : StdSpace (Fin (n + 1)) → M} {r l ε : ℝ} (hψ : IsNormalizedBallEmbedding hN ψ r l ε)
    (hσ : σ.IsSymplectic) {h₀ h₁ : ℝ → ℝ} (hh₀ : IsBlowupProfile l ε h₀)
    (hh₁ : IsBlowupProfile l ε h₁) :
    ∃ Φ : Diffeotopy 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ (Blowup hN.blowupChart),
      (∀ t, ∀ x ∉ hψ.ballLiftPartialDiffeomorph '' closedNbhd n (l + ε), Φ (t, x) = x) ∧
      SmoothForm.mpullback Φ.final Φ.final.contMDiff (hψ.normalizedBlowupForm h₁) =
        hψ.normalizedBlowupForm h₀ := by
  obtain ⟨β, hβ, hβK⟩ := hψ.exists_mextDeriv_eq_normalizedBlowupForm_sub hh₀ hh₁
  refine SmoothTwoForm.exists_diffeotopy_mpullback_eq_of_mextDeriv_eq_sub (fun s hs ↦ ?_) hβ
    (hψ.isCompact_ballLiftPartialDiffeomorph_image_closedNbhd hψ.weight_add_width_lt) hβK
  -- The segment between the two forms is the form of the segment between the two profiles.
  have hseg : hψ.normalizedBlowupForm h₀ + s • (hψ.normalizedBlowupForm h₁ -
      hψ.normalizedBlowupForm h₀) = hψ.normalizedBlowupForm ((1 - s) • h₀ + s • h₁) := by
    rw [hψ.normalizedBlowupForm_one_sub_smul_add_smul hh₀ hh₁ hs.1 hs.2]
    module
  rw [hseg]
  exact hψ.isSymplectic_normalizedBlowupForm (hh₀.one_sub_smul_add_smul hh₁ hs.1 hs.2) hσ

end IsNormalizedBallEmbedding

end SymplecticGeometry

end
