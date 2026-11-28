/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
public import TauCeti.Geometry.Manifold.Morse.Generic.Relative
import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Evaluation

/-!
# Morse perturbations fixed on a sublevel set

Let `f` be a smooth function on a Hausdorff boundaryless manifold with a finite-dimensional model,
and `c` a real number such that the superlevel set `f⁻¹[c, ∞)` is compact and every critical value
of `f` exceeds `c`. Then every weak Whitney neighbourhood of `f` contains a Morse function `g`
which agrees with `f` on the sublevel set `f⁻¹(-∞, c]` and has the same sublevel set at `c`,
differs from `f` by a compactly supported function, has `c` as a regular value, has compact
superlevel set `g⁻¹[c, ∞)`, lies below one of its regular values above `c`, and has all its
critical points where `f > c`
(`ContMDiffMap.exists_isMorse_eqOn_preimage_Iic`).

## Implementation notes

Since `c` is a regular value of `f`, there is a collar `f⁻¹[c, a]` free of critical points
(Tau Ceti's `TauCeti.exists_mem_Ioc_forall_notMem_criticalPoints`). Tau Ceti's
`ContMDiffMap.exists_isMorseOn_hasCompactSupport_sub_compl`, applied with the compact set
`f⁻¹[c, ∞)` and the closed set `f⁻¹(-∞, a]`, gives `g` equal to `f` near `f⁻¹(-∞, a]`. The
neighbourhood is shrunk so that `g > c` on the compact set `f⁻¹[a, ∞)`; it stays a neighbourhood by
the joint continuity of evaluation (`ContMDiffMap.continuous_eval_manifoldWeakWhitney`). Then
`g⁻¹[c, ∞) ⊆ f⁻¹[c, ∞)`, and `g` has no critical point at the level `c` nor where `f ≤ a`.

## References

* M. Hirsch, *Differential Topology*, Graduate Texts in Mathematics 33, Springer, 1976,
  Chapter 2, §1, for the weak topology, and Chapter 6, §1, for Morse approximation.
-/

public section

open Set Filter Topology TauCeti
open scoped Manifold ContDiff TauCeti.ManifoldWeakWhitney

namespace ContMDiffMap

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M]

/-- **Morse perturbation fixed on a sublevel set.** Let `f` be a smooth function on a Hausdorff
boundaryless manifold with a finite-dimensional model, and `c` a real number such that `f⁻¹[c, ∞)`
is compact and `c < f x` at every critical point `x` of `f`. Then every neighbourhood of `f` in the
weak Whitney topology contains a Morse function `g` which agrees with `f` on `f⁻¹(-∞, c]` and has
the same sublevel set `g⁻¹(-∞, c] = f⁻¹(-∞, c]`, such that `g - f` has compact support, `c < f x`
at every critical point `x` of `g`, `c` is a regular value of `g`, `g⁻¹[c, ∞)` is compact, and
`g < b` everywhere for some regular value `b > c` of `g`. -/
theorem exists_isMorse_eqOn_preimage_Iic (f : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯) {c : ℝ}
    (hc : IsCompact (f ⁻¹' Ici c)) (hcrit : ∀ x ∈ criticalPoints I f, c < f x)
    {𝒰 : Set C^∞⟮I, M; 𝓘(ℝ), ℝ⟯} (h𝒰 : 𝒰 ∈ 𝓝 f) :
    ∃ g ∈ 𝒰, IsMorse I g ∧ EqOn g f (f ⁻¹' Iic c) ∧ g ⁻¹' Iic c = f ⁻¹' Iic c ∧
      HasCompactSupport (fun y ↦ g y - f y) ∧
      (∀ x ∈ criticalPoints I g, c < f x) ∧ IsRegularValue I 𝓘(ℝ) g c ∧
      IsCompact (g ⁻¹' Ici c) ∧ ∃ b, c < b ∧ IsRegularValue I 𝓘(ℝ) g b ∧ ∀ x, g x < b := by
  -- Above `c` there is a collar `f⁻¹[c, a]` free of critical points.
  have hcreg : IsRegularValue I 𝓘(ℝ) f c := isRegularValue_iff_notMem_image_criticalPoints.2
    fun ⟨x, hx, hxc⟩ ↦ (hcrit x hx).ne' hxc
  obtain ⟨a, ⟨hca, -⟩, ha⟩ := exists_mem_Ioc_forall_notMem_criticalPoints
    (f.contMDiff.of_le (by simp)) (lt_add_one c) (hc.of_isClosed_subset
      (isClosed_Icc.preimage (map_continuous f)) (preimage_mono Icc_subset_Ici_self)) hcreg
  have hnc (x : M) (hx : x ∈ criticalPoints I f) : a < f x :=
    lt_of_not_ge fun h ↦ ha x hx ⟨(hcrit x hx).le, h⟩
  have hC : IsClosed (f ⁻¹' Iic a) := isClosed_Iic.preimage (map_continuous f)
  have hKa : IsCompact (f ⁻¹' Ici a) := hc.of_isClosed_subset
    (isClosed_Ici.preimage (map_continuous f)) (preimage_mono (Ici_subset_Ici.2 hca.le))
  -- Keep `g > c` on the compact set `f⁻¹[a, ∞)`, where `f ≥ a > c`.
  have h𝒱 : ∀ᶠ g : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯ in 𝓝 f, ∀ x ∈ f ⁻¹' Ici a, c < g x :=
    hKa.eventually_forall_of_forall_eventually fun x hx ↦
      (continuous_eval_manifoldWeakWhitney.continuousAt (x := (f, x))).eventually
        (lt_mem_nhds (hca.trans_le hx))
  have hfKC : IsMorseOn I f (f ⁻¹' Ici c ∩ f ⁻¹' Iic a) := isMorseOn_iff_criticalPoints.2
    ⟨f.contMDiff.contMDiffOn, fun x hx hxc ↦ absurd hx.2 (hnc x hxc).not_ge⟩
  obtain ⟨g, ⟨hg𝒰, hg𝒱⟩, hgK, hgc, hgs⟩ :=
    f.exists_isMorseOn_hasCompactSupport_sub_compl hc hC hfKC (inter_mem h𝒰 h𝒱)
  -- `g` agrees with `f` near each point of `f⁻¹(-∞, a]`, so has no critical point there.
  have hgf (x : M) (hx : f x ≤ a) : (g : M → ℝ) =ᶠ[𝓝 x] f := by
    filter_upwards [notMem_tsupport_iff_eventuallyEq.1 fun h ↦ hgs h hx] with y hy
    simpa [sub_eq_zero] using hy
  have hgC (x : M) (hx : f x ≤ a) : x ∉ criticalPoints I g := fun hxg ↦
    (hnc x (((hgf x hx).mem_criticalPoints_iff (I := I)).1 hxg)).not_ge hx
  have hK (x : M) (hx : x ∈ criticalPoints I g) : c < f x :=
    hca.trans (lt_of_not_ge fun h ↦ hgC x h hx)
  have hsub : g ⁻¹' Ici c ⊆ f ⁻¹' Ici c := fun x hx ↦ by
    rcases le_or_gt (f x) a with h | h
    · rw [mem_preimage, ← (hgf x h).eq_of_nhds]
      exact hx
    · exact (hca.trans h).le
  -- Where `f > c`, also `g > c`: either `g = f` near the point, or `f ≥ a` there.
  have hIic : g ⁻¹' Iic c = f ⁻¹' Iic c := Set.ext fun x ↦ by
    rcases le_or_gt (f x) a with h | h
    · rw [mem_preimage, mem_preimage, (hgf x h).eq_of_nhds]
    · simp only [mem_preimage, mem_Iic]
      exact iff_of_false (hg𝒱 x h.le).not_ge (hca.trans h).not_ge
  have hgcomp : IsCompact (g ⁻¹' Ici c) :=
    hc.of_isClosed_subset (isClosed_Ici.preimage (map_continuous g)) hsub
  obtain ⟨B, hB⟩ := hgcomp.bddAbove_image (map_continuous g).continuousOn
  have hlt (x : M) : g x < max c B + 1 := by
    rcases le_or_gt c (g x) with h | h
    · linarith [le_max_right c B, hB (mem_image_of_mem g (show x ∈ g ⁻¹' Ici c from h))]
    · linarith [le_max_left c B]
  refine ⟨g, hg𝒰, isMorseOn_univ.1 <| isMorseOn_iff_criticalPoints.2
    ⟨g.contMDiff.contMDiffOn, fun x _ hx ↦
      (isMorseOn_iff_criticalPoints.1 hgK).2 x (hK x hx).le hx⟩,
    fun x hx ↦ (hgf x (le_trans hx hca.le)).eq_of_nhds, hIic, hgc, hK,
    isRegularValue_iff_notMem_image_criticalPoints.2 fun ⟨x, hx, hxc⟩ ↦ ?_, hgcomp,
    max c B + 1, by linarith [le_max_left c B],
    isRegularValue_iff.2 fun x hx ↦ absurd hx (hlt x).ne, hlt⟩
  rcases le_or_gt (f x) a with h | h
  · exact hgC x h hx
  · exact (hg𝒱 x h.le).ne' hxc

end ContMDiffMap

end
