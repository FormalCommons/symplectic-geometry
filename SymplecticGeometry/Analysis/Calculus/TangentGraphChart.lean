/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import SymplecticGeometry.Topology.OpenPartialHomeomorph.Compact
import TauCeti.Analysis.Calculus.FDeriv.Equiv
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Calculus.InverseFunctionTheorem
import TauCeti.Analysis.Calculus.IteratedFDeriv.Prod
import TauCeti.Analysis.InnerProductSpace.RangeProjection
import TauCeti.Analysis.Normed.Module.ContinuousInverse

/-!
# Graph coordinates over tangent spaces, uniformly in the base point

Let `g : E → F` be a `C^∞` map from an open subset `U` of a finite-dimensional real normed space
into a real inner product space, whose derivative is injective at a point `w₀ ∈ U`, and for
`w' ∈ U` let `Q w'` be the orthogonal projection of `F` onto the range of `fderiv ℝ g w'`. Near a
point `w'`, the map `w ↦ Q w' (g w - g w')` presents the image of `g` as a graph over its tangent
space at `w'`. This file shows that these graph coordinates can be chosen uniformly for `w'`
near `w₀`: after a fixed linear map `S : F →L[ℝ] E`, they are inverted on one ball around `w₀`,
their images contain one ball around `0`, and the derivatives of every order of `g` composed
with their inverses are bounded independently of `w'`.

## Main results

* `ContDiffOn.exists_uniform_inverse_starProjection`: the uniform graph coordinates above.

## Implementation notes

The inverse function theorem is applied once, to the map `(w', w) ↦ (w', S (Q w' (g w - g w')))`
of `E × E`, where `Q` depends smoothly on `w'` (`ContDiffAt.starProjection_range`) and `S` is a
fixed left inverse of `fderiv ℝ g w₀`, after shrinking `U` to the open set where the derivative
of `g` is injective. Tau Ceti's `DifferentiableAt.hasFDerivAt_fst_prodMk_of_slices` gives the
derivative of this map at `(w₀, w₀)` as a shear, hence an isomorphism. Its inverse gives the
inverses for all `w'` at once, and the bounds come from compactness of a closed ball. For a
single `w'` this is the argument of Tau Ceti's
`ContDiffOn.exists_openPartialHomeomorph_starProjection`, which builds the same graph chart: the
projection fixes the tangent space, so its differential is an isomorphism onto it.

## References

* [A. Weil, *Sur les théorèmes de de Rham*][Weil1952], §1, pp. 120–122
-/

public section

open Set Function Metric
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] {g : E → F} {U : Set E}

/-- **Graph coordinates over tangent spaces, with a parameter.** Let `g : E → F` be `C^∞` with
injective derivatives on an open set `U ∋ w₀`, and write `Q w'` for the orthogonal projection
onto the range of `fderiv ℝ g w'`. For some `S : F →L[ℝ] E`, the map
`(w', w) ↦ (w', S (Q w' (g w - g w')))` agrees with an open partial homeomorphism `Θ` whose
source contains `(w₀, w₀)` and lies in `U ×ˢ U`, whose inverse is smooth on its target, and on
whose source the derivative of the second component in `w` is injective. -/
private theorem exists_openPartialHomeomorph_prod_starProjection (hU : IsOpen U)
    (hg : ContDiffOn ℝ ∞ g U) (hinj : ∀ w ∈ U, Injective (fderiv ℝ g w)) {w₀ : E}
    (hw₀ : w₀ ∈ U) :
    ∃ S : F →L[ℝ] E, ∃ Θ : OpenPartialHomeomorph (E × E) (E × E),
      (∀ p, Θ p = (p.1, S ((fderiv ℝ g p.1).range.starProjection (g p.2 - g p.1)))) ∧
      (w₀, w₀) ∈ Θ.source ∧ Θ.source ⊆ U ×ˢ U ∧ ContDiffOn ℝ ∞ Θ.symm Θ.target ∧
      ∀ q ∈ Θ.source,
        Injective (S ∘L (fderiv ℝ g q.1).range.starProjection ∘L fderiv ℝ g q.2) := by
  set Q : E → F →L[ℝ] F := fun w ↦ (fderiv ℝ g w).range.starProjection
  have hQ : ContDiffOn ℝ ∞ Q U := fun w hw ↦
    (ContDiffAt.starProjection_range ((hg.contDiffAt (hU.mem_nhds hw)).fderiv_right le_rfl)
      (hinj w hw)).contDiffWithinAt
  have hgd : ∀ w ∈ U, HasFDerivAt g (fderiv ℝ g w) w := fun w hw ↦
    ((hg.contDiffAt (hU.mem_nhds hw)).differentiableAt (by simp)).hasFDerivAt
  obtain ⟨S, hSD⟩ :=
    ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional_domain (hinj w₀ hw₀)
  -- The map `G (w', w) = (w', Ψ (w', w))` and its derivatives.
  set Ψ : E × E → E := fun p ↦ S (Q p.1 (g p.2 - g p.1))
  set G : E × E → E × E := fun p ↦ (p.1, Ψ p)
  have hG : ContDiffOn ℝ ∞ G (U ×ˢ U) := by
    refine contDiffOn_fst.prodMk (S.contDiff.comp_contDiffOn ?_)
    exact (hQ.comp contDiffOn_fst fun p (hp : p ∈ U ×ˢ U) ↦ hp.1).clm_apply
      ((hg.comp contDiffOn_snd fun p (hp : p ∈ U ×ˢ U) ↦ hp.2).sub
        (hg.comp contDiffOn_fst fun p (hp : p ∈ U ×ˢ U) ↦ hp.1))
  have hGd : ∀ p ∈ U ×ˢ U, HasFDerivAt G (fderiv ℝ G p) p := fun p hp ↦
    ((hG.contDiffAt ((hU.prod hU).mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt
  -- In the second variable, `G` has derivative `inr ∘ S ∘ Q w' ∘ fderiv ℝ g w`.
  have hslice : ∀ p ∈ U ×ˢ U, fderiv ℝ G p ∘L ContinuousLinearMap.inr ℝ E E =
      ContinuousLinearMap.inr ℝ E E ∘L (S ∘L Q p.1 ∘L fderiv ℝ g p.2) := by
    intro p hp
    have hGp : HasFDerivAt G (fderiv ℝ G p) (p.1, p.2) := hGd p hp
    have h₁ := hGp.comp p.2 (hasFDerivAt_prodMk_right p.1 p.2)
    have h₂ : HasFDerivAt (fun w ↦ G (p.1, w))
        (ContinuousLinearMap.inr ℝ E E ∘L (S ∘L Q p.1 ∘L fderiv ℝ g p.2)) p.2 := by
      have := (hasFDerivAt_const p.1 p.2).prodMk
        (((S ∘L Q p.1).hasFDerivAt).comp p.2 ((hgd p.2 hp.2).sub_const (g p.1)))
      convert this using 1
      all_goals ext a <;> simp [G, Ψ]
    exact h₁.unique h₂
  -- At `(w₀, w₀)`, the slice of `Ψ` in `w` has derivative the identity, since `Q w₀` fixes the
  -- range of `fderiv ℝ g w₀` and `S` is a left inverse of it; so `fderiv ℝ G (w₀, w₀)` is a shear.
  have hΨd : DifferentiableAt ℝ Ψ (w₀, w₀) :=
    ((hG.contDiffAt ((hU.prod hU).mem_nhds ⟨hw₀, hw₀⟩)).differentiableAt (by simp)).snd
  have hx : HasFDerivAt (fun w ↦ Ψ (w, w₀)) _ w₀ :=
    hΨd.hasFDerivAt.comp (f := fun w ↦ (w, w₀)) w₀ (hasFDerivAt_prodMk_left w₀ w₀)
  have hy : HasFDerivAt (fun w ↦ Ψ (w₀, w)) (ContinuousLinearMap.id ℝ E) w₀ := by
    have := ((S ∘L Q w₀).hasFDerivAt).comp w₀ ((hgd w₀ hw₀).sub_const (g w₀))
    convert this using 1
    · ext a
      simp [Ψ, Q]
    · ext a
      simp [Q, ContinuousLinearMap.starProjection_range_apply, hSD a]
  obtain ⟨Θ, hΘ, hp₀Θ, hΘU, hΘsymm⟩ := TauCeti.ContDiffOn.exists_openPartialHomeomorph hG
    (hU.prod hU) (a := (w₀, w₀)) ⟨hw₀, hw₀⟩ (by simp)
    (hΨd.hasFDerivAt_fst_prodMk_of_slices hx hy).fderiv.symm
  refine ⟨S, Θ, fun p ↦ congrFun hΘ p, hp₀Θ, hΘU, hΘsymm, fun q hq a b hab ↦ ?_⟩
  -- On the source of `Θ` the derivative of `G` is invertible, and so is its slice.
  have hq' := hΘU hq
  have hΘd : DifferentiableAt ℝ Θ q := hΘ ▸ (hGd q hq').differentiableAt
  have hΘsd : DifferentiableAt ℝ Θ.symm (Θ q) :=
    (hΘsymm.contDiffAt (Θ.open_target.mem_nhds (Θ.map_source hq))).differentiableAt (by simp)
  obtain ⟨Li, hLi⟩ := Θ.isInvertible_fderiv hq hΘd hΘsd
  rw [hΘ] at hLi
  have h₁ := congrArg (fun L ↦ L a) (hslice q hq')
  have h₂ := congrArg (fun L ↦ L b) (hslice q hq')
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply] at h₁ h₂
  have h : (Li : E × E →L[ℝ] E × E) (0, a) = (Li : E × E →L[ℝ] E × E) (0, b) := by
    rw [hLi, h₁, h₂]
    exact congrArg (Prod.mk 0) hab
  simpa using Li.injective h

/-- **Uniform graph coordinates over tangent spaces.** Let `g : E → F` be `C^∞` on an open set
`U ∋ w₀`, with injective derivative at `w₀`, and write `Q w'` for the orthogonal projection of `F`
onto the range of `fderiv ℝ g w'`. There are `S : F →L[ℝ] E`, radii `0 < η ≤ ε` with
`ball w₀ ε ⊆ U`, maps `h w' : E → E` and bounds `C : ℕ → ℝ` such that, for every
`w' ∈ ball w₀ η`, the map `Ψ w' : w ↦ S (Q w' (g w - g w'))` satisfies:

* on `ball w₀ ε`, the derivative `S ∘ Q w' ∘ fderiv ℝ g w` of `Ψ w'` is injective, `h w'` is a
  left inverse of `Ψ w'` there, and the iterated derivative of order `j` of `g ∘ h w'` at
  `Ψ w' w` has norm at most `C j`, for every `j`;
* its image of `ball w₀ ε` contains `ball 0 η`. -/
theorem ContDiffOn.exists_uniform_inverse_starProjection (hg : ContDiffOn ℝ ∞ g U)
    (hU : IsOpen U) {w₀ : E} (hw₀ : w₀ ∈ U) (hinj : Injective (fderiv ℝ g w₀)) :
    ∃ S : F →L[ℝ] E, ∃ ε > 0, ∃ η > 0, ∃ C : ℕ → ℝ, ∃ h : E → E → E, η ≤ ε ∧ ball w₀ ε ⊆ U ∧
      ∀ w' ∈ ball w₀ η,
        (∀ w ∈ ball w₀ ε,
          Injective (S ∘L (fderiv ℝ g w').range.starProjection ∘L fderiv ℝ g w) ∧
          h w' (S ((fderiv ℝ g w').range.starProjection (g w - g w'))) = w ∧
          ∀ j, ‖iteratedFDeriv ℝ j (g ∘ h w')
            (S ((fderiv ℝ g w').range.starProjection (g w - g w')))‖ ≤ C j) ∧
        ∀ v ∈ ball (0 : E) η, ∃ w ∈ ball w₀ ε,
          S ((fderiv ℝ g w').range.starProjection (g w - g w')) = v := by
  -- Injectivity of the derivative is an open condition, so it holds on an open `U' ∋ w₀`.
  set U' := U ∩ fderiv ℝ g ⁻¹' {L | Injective L}
  have hU' : IsOpen U' := (hg.continuousOn_fderiv_of_isOpen hU (by simp)).isOpen_inter_preimage
    hU ContinuousLinearMap.isOpen_injective
  obtain ⟨S, Θ, hΘG, hp₀Θ, hΘU', hΘsymm, hinjS⟩ :=
    exists_openPartialHomeomorph_prod_starProjection hU' (hg.mono inter_subset_left)
      (fun _ hw ↦ hw.2) (w₀ := w₀) ⟨hw₀, hinj⟩
  have hΘU : Θ.source ⊆ U ×ˢ U :=
    hΘU'.trans (prod_mono inter_subset_left inter_subset_left)
  set Q : E → F →L[ℝ] F := fun w ↦ (fderiv ℝ g w).range.starProjection
  set p₀ : E × E := (w₀, w₀)
  -- A closed ball around `(w₀, w₀)` in the source of `Θ`.
  obtain ⟨ε, hε, hεΘ⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (Θ.open_source.mem_nhds hp₀Θ)
  have hball : ∀ w' ∈ ball w₀ ε, ∀ w ∈ ball w₀ ε, (w', w) ∈ ball p₀ ε := fun w' hw' w hw ↦
    ball_prod_same w₀ w₀ ε ▸ ⟨hw', hw⟩
  have hsrc : ∀ w' ∈ ball w₀ ε, ∀ w ∈ ball w₀ ε, (w', w) ∈ Θ.source := fun w' hw' w hw ↦
    hεΘ (ball_subset_closedBall (hball w' hw' w hw))
  have hεU : ball w₀ ε ⊆ U := fun w hw ↦ (hΘU (hsrc w hw w hw)).2
  -- `k = g ∘ snd ∘ Θ⁻¹` is smooth on the target, with bounded derivatives on a compact set.
  set k : E × E → F := fun q ↦ g (Θ.symm q).2
  have hk : ContDiffOn ℝ ∞ k Θ.target :=
    hg.comp (contDiff_snd.comp_contDiffOn hΘsymm) fun q hq ↦ (hΘU (Θ.map_target hq)).2
  have hKt : Θ '' closedBall p₀ ε ⊆ Θ.target :=
    image_subset_iff.2 fun q hq ↦ Θ.map_source (hεΘ hq)
  have hKc : IsCompact (Θ '' closedBall p₀ ε) :=
    Θ.isCompact_image_of_subset_source (isCompact_closedBall p₀ ε) hεΘ
  have hbd : ∀ j : ℕ, ∃ C, ∀ q ∈ Θ '' closedBall p₀ ε, ‖iteratedFDeriv ℝ j k q‖ ≤ C :=
    fun j ↦ hKc.exists_bound_of_continuousOn fun q hq ↦
      ((hk.contDiffAt (Θ.open_target.mem_nhds (hKt hq))).continuousAt_iteratedFDeriv
        (by exact_mod_cast le_top)).continuousWithinAt
  choose Cf hCf using hbd
  -- The image of the open ball contains a product of balls around `Θ (w₀, w₀) = (w₀, 0)`.
  have hopen : IsOpen (Θ '' ball p₀ ε) :=
    Θ.isOpen_image_of_subset_source isOpen_ball (ball_subset_closedBall.trans hεΘ)
  have hΘp₀ : Θ p₀ = (w₀, 0) := by simp [hΘG, p₀]
  obtain ⟨η, hη, hηsub⟩ := Metric.isOpen_iff.1 hopen _ ⟨p₀, mem_ball_self hε, hΘp₀⟩
  refine ⟨S, ε, hε, min η ε, lt_min hη hε, Cf,
    fun w' v ↦ (Θ.symm (w', v)).2, min_le_right _ _, hεU, fun w' hw' ↦ ⟨fun w hw ↦ ?_, ?_⟩⟩
  · have hw'ε : w' ∈ ball w₀ ε := ball_subset_ball (min_le_right _ _) hw'
    have hq := hsrc w' hw'ε w hw
    have hΘq : Θ (w', w) = (w', S (Q w' (g w - g w'))) := hΘG _
    refine ⟨hinjS (w', w) hq, ?_, fun j ↦ ?_⟩
    · simpa [hΘq] using congrArg Prod.snd (Θ.left_inv hq)
    · have hmem : (w', S (Q w' (g w - g w'))) ∈ Θ '' closedBall p₀ ε :=
        ⟨(w', w), ball_subset_closedBall (hball w' hw'ε w hw), hΘq⟩
      have hkat : ContDiffAt ℝ ∞ k (w', S (Q w' (g w - g w'))) :=
        hk.contDiffAt (Θ.open_target.mem_nhds (hKt hmem))
      exact (hkat.norm_iteratedFDeriv_prod_right_le j (by exact_mod_cast le_top)).trans
        (hCf j _ hmem)
  · intro v hv
    have hmem : (w', v) ∈ ball (w₀, (0 : E)) η := by
      rw [← ball_prod_same]
      exact ⟨ball_subset_ball (min_le_left _ _) hw', ball_subset_ball (min_le_left _ _) hv⟩
    obtain ⟨q, hq, hqv⟩ := hηsub hmem
    rw [hΘG] at hqv
    obtain ⟨hq₁, hq₂⟩ := Prod.mk.inj hqv
    rw [← ball_prod_same] at hq
    exact ⟨q.2, hq.2, hq₁ ▸ hq₂⟩


end
