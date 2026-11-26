/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Diffeomorphism.Diffeotopy.Translate
import SymplecticGeometry.Analysis.Calculus.HolonomicApproximation.Basic
import SymplecticGeometry.Analysis.Calculus.HolonomicApproximation.ZigZag
import SymplecticGeometry.Analysis.Normed.Group.Pi

/-!
# Holonomic approximation over a segment

In the coordinates of `SymplecticGeometry.Analysis.Calculus.HolonomicApproximation.Basic`, on
`D = (Fin 1 → ℝ) × (Fin k → ℝ)` with sup norms and `0 < k`, this file proves holonomic
approximation over the core segment `closedBall 0 1 ×ˢ {0}`, relative to a neighbourhood of its
two end points: the case `m = 1` of [EliashbergMishachev2002], Chapter 3.

Given a smooth formal section `(f, G)` holonomic near the end points, and `ε, δ > 0`, there are a
`δ`-small diffeotopy `h` of `D`, supported in a compact subset of the `δ`-neighbourhood of the
segment and fixed near its end points, and a smooth `f'`, equal to `f` near the end points, that
is `ε`-close to `f` in `C¹` with respect to `G` on an open set containing the image of the
segment under `h 1`.

The proof assembles two earlier results. `SymplecticGeometry.exists_holonomic_approximation_zigzag`,
in the case `m = 1` with no directions besides the core one, gives `f'` near a zig-zag curve
`u ↦ (u, r g₀ (u) e₀)` with `r < δ / 2`, where `g₀ u = g (u 0)` for a profile `g : ℝ → ℝ`, and
`SymplecticGeometry.exists_wiggling_diffeotopy`, applied to the profile `g₀` and the transverse
direction `e₀` over the closed `δ / 2`-neighbourhood of the segment, gives a diffeotopy that moves
the segment onto that curve. Since `g₀` vanishes near `± 1`, the diffeotopy fixes a neighbourhood
of the end points.

## Main results

* `SymplecticGeometry.exists_holonomic_approximation_segment`: holonomic approximation over the
  segment, relative to its end points.

## References

* [Y. Eliashberg and N. Mishachev, *Introduction to the h-Principle*][EliashbergMishachev2002]
-/

public section

open Set Metric
open scoped Manifold ContDiff Topology

namespace SymplecticGeometry

/-- **Holonomic approximation over a segment.** On `D = (Fin 1 → ℝ) × (Fin k → ℝ)` with sup
norms and `0 < k`, let `(f, G)` be a smooth formal section that is holonomic (`D f = G`) on an
open set `U` containing the end points `(± 1, 0)` of the core segment `closedBall 0 1 ×ˢ {0}`,
and let `ε, δ > 0`. There are a diffeotopy `h` of `D`, a smooth map `f'` and an open set `V`
such that:
* `h` is the identity off a compact subset of the `δ`-neighbourhood of the segment, moves every
  point by less than `δ`, and is the identity at all times near the end points;
* `V` contains the image of the segment under `h 1`, and on `V` the map `f'` is `ε`-close to `f`
  and its derivative `ε`-close to `G`;
* `f'` equals `f` near the end points. -/
theorem exists_holonomic_approximation_segment {k : ℕ} (hk : 0 < k)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : (Fin 1 → ℝ) × (Fin k → ℝ) → F}
    {G : (Fin 1 → ℝ) × (Fin k → ℝ) → (Fin 1 → ℝ) × (Fin k → ℝ) →L[ℝ] F}
    (hf : ContDiff ℝ ∞ f) (hG : Continuous G) {U : Set ((Fin 1 → ℝ) × (Fin k → ℝ))}
    (hU : IsOpen U) (hUf : ∀ x ∈ U, fderiv ℝ f x = G x)
    (hU' : sphere 0 1 ×ˢ {0} ⊆ U) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ (h : TauCeti.Diffeotopy 𝓘(ℝ, (Fin 1 → ℝ) × (Fin k → ℝ)) ∞ ((Fin 1 → ℝ) × (Fin k → ℝ)))
      (f' : (Fin 1 → ℝ) × (Fin k → ℝ) → F) (V : Set ((Fin 1 → ℝ) × (Fin k → ℝ))),
      (∃ C, IsCompact C ∧ C ⊆ thickening δ (closedBall 0 1 ×ˢ {0}) ∧
        ∀ t, ∀ x ∉ C, h (t, x) = x) ∧
      (∀ t x, dist (h (t, x)) x < δ) ∧
      (∃ W ∈ 𝓝ˢ (sphere 0 1 ×ˢ {0}), ∀ t, ∀ x ∈ W, h (t, x) = x) ∧
      IsOpen V ∧ (fun x ↦ h (1, x)) '' (closedBall 0 1 ×ˢ {0}) ⊆ V ∧
      ContDiff ℝ ∞ f' ∧ (∀ x ∈ V, ‖f' x - f x‖ < ε ∧ ‖fderiv ℝ f' x - G x‖ < ε) ∧
      ∃ U' ∈ 𝓝ˢ (sphere 0 1 ×ˢ {0}), EqOn f' f U' := by
  set j : Fin k := ⟨0, hk⟩
  have hδ2 : 0 < δ / 2 := by positivity
  -- For `m = 1`, the faces `|u 0| = 1` of the core segment are its end points, and the maps
  -- `u ↦ G (update u 0 s, 0)` are constant.
  have hnorm : ∀ u : Fin 1 → ℝ, ‖u‖ = |u 0| := fun u ↦ by
    rw [Pi.norm_eq_norm_default, Fin.default_eq_zero, Real.norm_eq_abs]
  have hface : {u ∈ closedBall (0 : Fin 1 → ℝ) 1 | |u 0| = 1} = sphere 0 1 := by
    ext u
    simp only [mem_ofPred_eq, mem_closedBall_zero_iff, mem_sphere_zero_iff_norm, hnorm]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨h.le, h⟩⟩
  obtain ⟨r, g, f', V, hr, hrδ, hg, hg1, ⟨b, hb, hbg⟩, hV, hXV, hf', hf'V, hU''⟩ :=
    exists_holonomic_approximation_zigzag 0 j (J' := ∅) hf hG
      (fun s ↦ by simp only [Function.update_eq_const_of_subsingleton]; exact contDiff_const)
      (by simpa only [Function.update_eq_const_of_subsingleton, fderiv_const_apply] using
        continuous_const)
      (fun u _ v hv ↦ by
        obtain rfl : v = 0 := funext fun i ↦ hv i (Finset.notMem_empty i)
        rw [Prod.mk_zero_zero, map_zero, map_zero])
      hU hUf (hface ▸ hU') (half_pos hε) hδ2
  rw [hface] at hU''
  set g₀ : (Fin 1 → ℝ) → ℝ := fun u ↦ g (u 0)
  have hg₀ : ContDiff ℝ ∞ g₀ := hg.comp (by fun_prop)
  have hg₀1 : ∀ u, |g₀ u| ≤ 1 := fun u ↦ hg1 _
  obtain ⟨W₀, hW₀, hW₀g⟩ : ∃ W₀ ∈ 𝓝ˢ (sphere (0 : Fin 1 → ℝ) 1), ∀ u ∈ W₀, g₀ u = 0 :=
    ⟨{u | 1 - b < |u 0|}, (isOpen_lt continuous_const (by fun_prop)).mem_nhdsSet.2 fun u hu ↦ by
      rw [mem_sphere_zero_iff_norm, hnorm] at hu
      simp only [mem_ofPred_eq, hu]; linarith, fun u hu ↦ hbg _ hu⟩
  -- The diffeotopy pushes the closed `δ / 2`-neighbourhood `K` of the segment along `eⱼ`.
  set S : Set ((Fin 1 → ℝ) × (Fin k → ℝ)) := closedBall 0 1 ×ˢ {0}
  set K := cthickening (δ / 2) S
  have hK : IsCompact K := ((isCompact_closedBall _ _).prod isCompact_singleton).cthickening
  obtain ⟨h, ⟨C, hC, hCK, hCh⟩, hsmall, hKh, -, -⟩ :=
    exists_wiggling_diffeotopy hK j hr.le hrδ hg₀ hg₀1
  refine ⟨h, f', V, ⟨C, hC, ?_, hCh⟩, fun t x ↦ (hsmall t x).trans (half_lt_self hδ), ?_, hV, ?_,
    hf', fun x hx ↦ ⟨(hf'V x hx).1.trans (half_lt_self hε), ?_⟩, hU''⟩
  · calc C ⊆ thickening (δ / 2) K := hCK
      _ ⊆ thickening (δ / 2 + δ / 2) S := thickening_cthickening_subset _ hδ2.le _
      _ = thickening δ S := by rw [add_halves]
  · -- Near the end points the profile vanishes, so the diffeotopy is the identity there.
    obtain ⟨O, hO, hsO, hOW⟩ := mem_nhdsSet_iff_exists.1 hW₀
    refine ⟨thickening (δ / 2) S ∩ Prod.fst ⁻¹' O,
      (isOpen_thickening.inter (hO.preimage continuous_fst)).mem_nhdsSet.2 fun x hx ↦
        ⟨self_subset_thickening hδ2 _ ⟨sphere_subset_closedBall hx.1, hx.2⟩, hsO hx.1⟩,
      fun t x hx ↦ ?_⟩
    rw [hKh t x (thickening_subset_cthickening _ _ hx.1), hW₀g _ (hOW hx.2)]
    simp
  · rintro _ ⟨⟨u, v⟩, ⟨hu, hv⟩, rfl⟩
    rw [mem_singleton_iff] at hv
    subst hv
    rw [hKh 1 _ (self_subset_cthickening _ ⟨hu, rfl⟩)]
    simpa using hXV u hu
  · -- In dimension one, every vector is in the direction `0`.
    refine (ContinuousLinearMap.opNorm_le_bound _ (half_pos hε).le fun w ↦
      (hf'V x hx).2 w fun i hi ↦ absurd (by simp [Subsingleton.elim i 0]) hi).trans_lt
      (half_lt_self hε)

end SymplecticGeometry

end
