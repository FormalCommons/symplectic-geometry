/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Complex.JConvex.Surround.ConvexShape.Basic

import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The hypersurface surrounding the model disc

For `δ > 0` and a shape `χ : ℝ → ℝ`, `SymplecticGeometry.surroundHypersurface k m δ χ` is the
subset `Σ` of `ℂᵏ × ℂᵐ` that Cieliebak and Eliashberg build in their Theorem 4.1: in the shape
coordinates `s`, `t` of `SymplecticGeometry.shape`, it is the piece `t = δ², √s ≤ χ δ` of the
cylinder around the model disc, together with the graph `√s = χ (√t)` over `t > δ²`. For the
`δ` and `χ` of `SymplecticGeometry.exists_convexShape_surround` (their Proposition 4.21), this
file proves the three properties of their Theorem 4.1 in terms of the shape:

* (ii) `SymplecticGeometry.surroundHypersurface_inter_sq_le_snd`: where `χ r = √(1 + a r²)` for
  `r ≥ γ`, the part of `Σ` in `{γ² ≤ t}` is the part there of the level `a t - s = -1` of the
  standard function.
* (iii) `SymplecticGeometry.surroundHypersurface_inter_fst_le_one`: if `χ` is an `i`-convex shape
  beyond `δ`, continuous from `δ` on, with `χ δ > 1`, the part of `Σ` in `{s ≤ 1}` is the part
  there of the cylinder `t = δ²`, since such a `χ` is strictly increasing on `[δ, ∞)`
  (`SymplecticGeometry.strictMonoOn_Ici_of_isConvexShapeAt`).
* (i) `SymplecticGeometry.exists_levelSet_of_mem_surroundHypersurface`: away from the corner
  `s = χ δ², t = δ²`, near each of its points `Σ` is a level of a function `F`, `C²` with a
  nonzero differential there, whose Levi form is positive on the nonzero complex tangent
  vectors of the level. On the curved part `F` is `shapeGraph χ ∘ shape`, and the positivity is
  `SymplecticGeometry.IsConvexShapeAt.re_leviForm_pos`; on the cylinder `F` is `t`, whose Levi
  form is positive definite (`SymplecticGeometry.fderiv_shape_snd_ne_zero`,
  `SymplecticGeometry.re_leviForm_shape_snd_pos`).

Nothing here is claimed at the corner. For the `χ` of
`SymplecticGeometry.exists_convexShape_surround`, whose slope tends to `+∞` as `r` decreases to
`δ`, the two pieces meet there with the same tangent; for a `χ` of finite slope at `δ` they meet
at an angle. In either case `Σ` is not `C²` at the corner, and the smooth hypersurface that
replaces it there is built later, with the model handle.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  §4.1, Theorem 4.1, and §4.5, Proposition 4.21.
-/

public section

noncomputable section

namespace SymplecticGeometry

open Real Set Filter Topology TauCeti

variable {k m : ℕ}

/-- The **surrounding hypersurface** `Σ` for `δ` and a shape `χ`: in the shape coordinates
`(s, t)`, the union of the part `√s ≤ χ δ` of the cylinder `t = δ²` and of the graph
`√s = χ (√t)` over `t > δ²`. -/
def surroundHypersurface (k m : ℕ) (δ : ℝ) (χ : ℝ → ℝ) :
    Set (EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) :=
  {p | (shape p).2 = δ ^ 2 ∧ √(shape p).1 ≤ χ δ} ∪
    {p | δ ^ 2 < (shape p).2 ∧ √(shape p).1 = χ (√(shape p).2)}

theorem surroundHypersurface_def (δ : ℝ) (χ : ℝ → ℝ) :
    surroundHypersurface k m δ χ =
      {p | (shape p).2 = δ ^ 2 ∧ √(shape p).1 ≤ χ δ} ∪
        {p | δ ^ 2 < (shape p).2 ∧ √(shape p).1 = χ (√(shape p).2)} :=
  (rfl)

theorem mem_surroundHypersurface_iff {δ : ℝ} {χ : ℝ → ℝ}
    {p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)} :
    p ∈ surroundHypersurface k m δ χ ↔
      (shape p).2 = δ ^ 2 ∧ √(shape p).1 ≤ χ δ ∨
        δ ^ 2 < (shape p).2 ∧ √(shape p).1 = χ (√(shape p).2) := by
  rw [surroundHypersurface_def, mem_union, mem_ofPred_eq, mem_ofPred_eq]

/-- **Theorem 4.1 (ii)** of Cieliebak–Eliashberg, in terms of the shape. If `0 ≤ δ < γ`,
`0 ≤ a` and `χ r = √(1 + a r²)` for `r ≥ γ`, then on `{γ² ≤ t}` the hypersurface `Σ` is the level
`a t - s = -1`. -/
theorem surroundHypersurface_inter_sq_le_snd {a γ δ : ℝ} {χ : ℝ → ℝ} (hδ : 0 ≤ δ) (hδγ : δ < γ)
    (ha : 0 ≤ a) (hχ : ∀ r, γ ≤ r → χ r = √(1 + a * r ^ 2)) :
    surroundHypersurface k m δ χ ∩ {p | γ ^ 2 ≤ (shape p).2} =
      {p | a * (shape p).2 - (shape p).1 = -1} ∩ {p | γ ^ 2 ≤ (shape p).2} := by
  ext p
  simp only [mem_inter_iff, mem_surroundHypersurface_iff, mem_ofPred_eq]
  refine and_congr_left fun ht ↦ ?_
  have hs := shape_fst_nonneg p
  have ht₀ := shape_snd_nonneg p
  have hδt : δ ^ 2 < (shape p).2 := by nlinarith
  have hχt : χ √(shape p).2 = √(1 + a * (shape p).2) := by
    rw [hχ _ ((le_sqrt (hδ.trans hδγ.le) ht₀).2 ht), sq_sqrt ht₀]
  rw [hχt, sqrt_inj hs (by positivity)]
  constructor
  · rintro (h | h)
    · exact absurd h.1 hδt.ne'
    · linarith [h.2]
  · exact fun h ↦ Or.inr ⟨hδt, by linarith⟩

/-- **Theorem 4.1 (iii)** of Cieliebak–Eliashberg, in terms of the shape. If `χ` is continuous on
`[δ, ∞)`, an `i`-convex shape at every `r > δ`, and `1 < χ δ`, then on `{s ≤ 1}` the hypersurface
`Σ` is the cylinder `t = δ²`. -/
theorem surroundHypersurface_inter_fst_le_one {δ : ℝ} {χ : ℝ → ℝ} (hc : ContinuousOn χ (Ici δ))
    (hχ : ∀ r, δ < r → IsConvexShapeAt χ r) (h₁ : 1 < χ δ) :
    surroundHypersurface k m δ χ ∩ {p | (shape p).1 ≤ 1} =
      {p | (shape p).2 = δ ^ 2 ∧ (shape p).1 ≤ 1} := by
  ext p
  simp only [mem_inter_iff, mem_surroundHypersurface_iff, mem_ofPred_eq]
  constructor
  · rintro ⟨h | ⟨ht, hs⟩, h₁'⟩
    · exact ⟨h.1, h₁'⟩
    · have hδt : δ < √(shape p).2 := lt_sqrt_of_sq_lt ht
      have := strictMonoOn_Ici_of_isConvexShapeAt hc hχ (mem_Ici.2 le_rfl)
        (mem_Ici.2 hδt.le) hδt
      linarith [sqrt_le_one.2 h₁']
  · rintro ⟨ht, hs⟩
    exact ⟨Or.inl ⟨ht, (sqrt_le_one.2 hs).trans h₁.le⟩, hs⟩

/-- **Theorem 4.1 (i)** of Cieliebak–Eliashberg, in terms of the shape, away from the corner. Let
`0 < δ` and let `χ` be `C²` on `(δ, ∞)`, continuous on `[δ, ∞)` and an `i`-convex shape at every
`r > δ`. Near each point `p` of `Σ` with `shape p ≠ (χ δ ², δ ²)` there is a function `F`, `C²`
at `p` with `dF_p ≠ 0`, of which `Σ` is a level there, and whose Levi form at `p` is positive on
every nonzero `v` with `dF_p v = 0` and `dF_p (i v) = 0`. -/
theorem exists_levelSet_of_mem_surroundHypersurface {δ : ℝ} {χ : ℝ → ℝ} (hδ : 0 < δ)
    (hs : ContDiffOn ℝ 2 χ (Ioi δ)) (hc : ContinuousOn χ (Ici δ))
    (hχ : ∀ r, δ < r → IsConvexShapeAt χ r)
    {p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)}
    (hp : p ∈ surroundHypersurface k m δ χ) (hpc : shape p ≠ (χ δ ^ 2, δ ^ 2)) :
    ∃ F : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m) → ℝ, ∃ c : ℝ, ∃ U ∈ 𝓝 p,
      ContDiffAt ℝ 2 F p ∧ U ∩ surroundHypersurface k m δ χ = U ∩ F ⁻¹' {c} ∧
      fderiv ℝ F p ≠ 0 ∧ ∀ v, v ≠ 0 → fderiv ℝ F p v = 0 →
        fderiv ℝ F p (Complex.I • v) = 0 → 0 < (leviForm F p v v).re := by
  have hsh : Continuous (shape : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m) → ℝ × ℝ) :=
    contDiff_shape.continuous (n := 0)
  have hδ' {q : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)} (hq : δ ^ 2 < (shape q).2) :
      δ < √(shape q).2 :=
    (lt_sqrt hδ.le).2 hq
  rcases mem_surroundHypersurface_iff.1 hp with ⟨ht, hsχ⟩ | ⟨ht, hsχ⟩
  · -- On the cylinder, `Σ` is the level `t = δ²` near `p`.
    have hsχ' : √(shape p).1 < χ δ := by
      refine hsχ.lt_of_ne fun h ↦ hpc (Prod.ext ?_ ht)
      rw [← h, sq_sqrt (shape_fst_nonneg p)]
    refine ⟨fun q ↦ (shape q).2, δ ^ 2, {q | √(shape q).1 < χ δ},
      (isOpen_lt (continuous_sqrt.comp (continuous_fst.comp hsh)) continuous_const).mem_nhds
        hsχ', contDiff_shape.snd.contDiffAt, ?_, ?_, fun v hv _ _ ↦ ?_⟩
    · ext q
      simp only [mem_inter_iff, mem_surroundHypersurface_iff, mem_ofPred_eq, mem_preimage,
        mem_singleton_iff]
      refine and_congr_right fun hq ↦ ⟨?_, fun h ↦ Or.inl ⟨h, hq.le⟩⟩
      rintro (h | ⟨hqt, hqs⟩)
      · exact h.1
      · have := strictMonoOn_Ici_of_isConvexShapeAt hc hχ (mem_Ici.2 le_rfl)
          (mem_Ici.2 (hδ' hqt).le) (hδ' hqt)
        linarith
    · exact fderiv_shape_snd_ne_zero (by rw [ht]; positivity)
    · exact re_leviForm_shape_snd_pos p hv
  · -- On the curved part, `Σ` is the zero level of `shapeGraph χ ∘ shape` near `p`.
    set r := √(shape p).2
    have hr : δ < r := hδ' ht
    have hχr := hχ r hr
    have hχ₂ : ContDiffAt ℝ 2 χ r := hs.contDiffAt (Ioi_mem_nhds hr)
    have hp' : shape p = (χ r ^ 2, r ^ 2) :=
      Prod.ext (by rw [← hsχ, sq_sqrt (shape_fst_nonneg p)]) (sq_sqrt (shape_snd_nonneg p)).symm
    refine ⟨shapeGraph χ ∘ shape, 0, {q | δ ^ 2 < (shape q).2},
      (isOpen_lt continuous_const (continuous_snd.comp hsh)).mem_nhds ht, ?_, ?_,
      fderiv_shapeGraph_comp_shape_ne_zero (hχ₂.differentiableAt two_ne_zero) hχr.pos_value
        hχr.pos hp', fun v hv h₁ h₂ ↦ hχr.re_leviForm_pos hχ₂ hp' hv h₁ h₂⟩
    · refine ContDiffAt.comp p ?_ contDiff_shape.contDiffAt
      rw [hp']
      exact contDiffAt_shapeGraph (by rwa [sqrt_sq hχr.pos.le]) (pow_pos hχr.pos_value 2)
        (pow_pos hχr.pos 2)
    · ext q
      simp only [mem_inter_iff, mem_surroundHypersurface_iff, mem_ofPred_eq, mem_preimage,
        mem_singleton_iff, Function.comp_apply, shapeGraph_def, sub_eq_zero]
      refine and_congr_right fun hq ↦ ⟨?_, fun h ↦ Or.inr ⟨hq, h.symm⟩⟩
      rintro (h | h)
      · exact absurd h.1 hq.ne'
      · exact h.2.symm

end SymplecticGeometry

end
