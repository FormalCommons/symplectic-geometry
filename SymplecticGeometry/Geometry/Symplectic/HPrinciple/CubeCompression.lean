/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Diffeomorph.Prod.FiberScaling
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Compressing a cube onto a thin tube around its core

For a finite type `ι` and `D = (ι → ℝ) × F` with the sup norm, the core `ι → ℝ` may have any
dimension, the cube is `Q = closedBall 0 1` and the attaching faces are
`A = sphere 0 1 ×ˢ closedBall 0 1`. `SymplecticGeometry.exists_cubeCompression` gives, for
`0 < ε < 1` and `0 < δ`, a smooth `ψ : ℝ × (ι → ℝ) → ℝ` with positive values at most `1`
such that the fibre scalings `c s = prodFiberScaling (ψ (s, ·))` are the identity at `s = 0` and
near `A` (where `1 - ε / 2 < ‖u‖`) for every `s`, preserve `Q`, and such that `c 1` maps `Q` into
the union of the thin tube `‖v‖ < δ` around the core `closedBall 0 1 ×ˢ {0}` and the slab
`1 - ε < ‖u‖` next to `A`. The fibre scalings themselves, and their smoothness, are in
`SymplecticGeometry/Geometry/Manifold/Diffeomorph/Prod/FiberScaling.lean`.

## Forms

The handle-core lemma of McDuff–Salamon pulls two-forms back along the maps `c s`. Each `c s` is
a diffeomorphism (`SymplecticGeometry.prodFiberScalingDiffeomorph`), so the pullback of a two-form
is nondegenerate at `x` exactly when the form is nondegenerate at `c s x`, by
`TauCeti.SmoothTwoForm.nondegenerate_bilinFormAt_iff_of_isInvertible_mfderiv` and
`IsLocalDiffeomorph.isInvertible_mfderiv`. A smooth family of forms pulled back along
`(p, x) ↦ c (a p) x`, for a smooth function `a` of the parameter, is a smooth family by
`SymplecticGeometry.IsSmoothFamily.mpullback_family`, since `(s, x) ↦ c s x` is smooth
(`SymplecticGeometry.contMDiff_prodFiberScaling_family`). A form that is exact near `Q` pulls back
to a form exact near `Q`, by `TauCeti.SmoothForm.exists_mem_nhdsSet_mextDerivₗ_mpullback_eq`,
since `c s` maps `Q` into `Q`.

This compression replaces the zig-zag immersion of McDuff–Salamon's proof of Lemma 7.3.2: instead
of stretching the core so that primitives near its ends can be patched with a small error, the
cube is squeezed towards the core, where a single primitive along the fibres is close to the
given form.

## Main results

* `SymplecticGeometry.exists_cubeCompression`: the compression of the cube.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Lemma 7.3.2.
-/

public section

open Set Metric
open scoped ContDiff

namespace SymplecticGeometry

section Cube

variable {ι F : Type*} [Fintype ι] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The profile of the compression: a smooth `ψ` with values in `(0, 1]`,
equal to `1` at time `0` and where `1 - ε / 2 < ‖u‖`, and below `δ` at time `1` where
`‖u‖ ≤ 1 - ε`. -/
private theorem exists_cubeCompression_profile {ε δ : ℝ} (hε : 0 < ε) (hε₁ : ε < 1)
    (hδ : 0 < δ) :
    ∃ ψ : ℝ × (ι → ℝ) → ℝ, ContDiff ℝ ∞ ψ ∧ (∀ p, 0 < ψ p) ∧ (∀ p, ψ p ≤ 1) ∧
      (∀ u, ψ (0, u) = 1) ∧ (∀ s u, 1 - ε / 2 < ‖u‖ → ψ (s, u) = 1) ∧
      ∀ u, ‖u‖ ≤ 1 - ε → ψ (1, u) < δ := by
  set a := min (δ / 2) (1 / 2)
  have ha₀ : 0 < a := lt_min (half_pos hδ) one_half_pos
  have haδ : a < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  have ha₁ : a ≤ 1 / 2 := min_le_right _ _
  -- `χ u` is `1` where `‖u‖ ≤ 1 - ε` and `0` where `1 - ε / 2 ≤ ‖u‖`.
  let χ : ContDiffBump (0 : ι → ℝ) := ⟨1 - ε, 1 - ε / 2, by linarith, by linarith⟩
  let ψ : ℝ × (ι → ℝ) → ℝ := fun p ↦ 1 - Real.smoothTransition p.1 * χ p.2 * (1 - a)
  have hθχ (p : ℝ × (ι → ℝ)) :
      0 ≤ Real.smoothTransition p.1 * χ p.2 ∧ Real.smoothTransition p.1 * χ p.2 ≤ 1 :=
    ⟨mul_nonneg (Real.smoothTransition.nonneg _) (χ.nonneg),
      (mul_le_of_le_one_left (χ.nonneg) (Real.smoothTransition.le_one _)).trans χ.le_one⟩
  refine ⟨ψ, contDiff_const.sub (((Real.smoothTransition.contDiff.comp contDiff_fst).mul
      (χ.contDiff.comp contDiff_snd)).mul contDiff_const), fun p ↦ ?_, fun p ↦ ?_, fun u ↦ ?_,
      fun s u hu ↦ ?_, fun u hu ↦ ?_⟩
  · obtain ⟨_, h₁⟩ := hθχ p
    simp only [ψ]
    nlinarith
  · obtain ⟨h₀, _⟩ := hθχ p
    simp only [ψ]
    nlinarith
  · simp [ψ, Real.smoothTransition.zero]
  · have : χ u = 0 := χ.zero_of_le_dist (by rw [dist_zero_right]; exact hu.le)
    simp [ψ, this]
  · have : χ u = 1 := χ.one_of_mem_closedBall (mem_closedBall_zero_iff.2 hu)
    simp only [ψ, this, Real.smoothTransition.one_of_one_le le_rfl]
    linarith

/-- **Compression of the cube onto a thin tube around its core.** For a finite type `ι`, on
`D = (ι → ℝ) × F` with the sup norm, let `0 < ε < 1` and `0 < δ`. There is a smooth
`ψ : ℝ × (ι → ℝ) → ℝ` with values in `(0, 1]` such that the fibre scalings
`c s := prodFiberScaling (ψ (s, ·))`, `(u, v) ↦ (u, ψ (s, u) • v)`, which are diffeomorphisms of
`D` by `prodFiberScalingDiffeomorph`, satisfy:

* `c 0` is the identity, and every `c s` is the identity where `1 - ε / 2 < ‖u‖`, a neighbourhood
  of the attaching faces `sphere 0 1 ×ˢ closedBall 0 1`;
* every `c s` maps the cube `closedBall 0 1` into itself;
* `c 1` maps the cube into the union of the tube `‖v‖ < δ` and the slab `1 - ε < ‖u‖`. -/
theorem exists_cubeCompression {ε δ : ℝ} (hε : 0 < ε) (hε₁ : ε < 1) (hδ : 0 < δ) :
    ∃ ψ : ℝ × (ι → ℝ) → ℝ, ContDiff ℝ ∞ ψ ∧ (∀ p, 0 < ψ p ∧ ψ p ≤ 1) ∧
      (∀ x : (ι → ℝ) × F, prodFiberScaling (fun u ↦ ψ (0, u)) x = x) ∧
      (∀ s, ∀ x : (ι → ℝ) × F, 1 - ε / 2 < ‖x.1‖ →
        prodFiberScaling (fun u ↦ ψ (s, u)) x = x) ∧
      (∀ s, MapsTo (prodFiberScaling (fun u ↦ ψ (s, u)))
        (closedBall (0 : (ι → ℝ) × F) 1) (closedBall 0 1)) ∧
      MapsTo (prodFiberScaling (fun u ↦ ψ (1, u))) (closedBall (0 : (ι → ℝ) × F) 1)
        ({x | ‖x.2‖ < δ} ∪ {x | 1 - ε < ‖x.1‖}) := by
  obtain ⟨ψ, hψ, hpos, hle, h0, hA, h1⟩ := exists_cubeCompression_profile (ι := ι) hε hε₁ hδ
  have habs (p) : |ψ p| ≤ 1 := by rw [abs_of_pos (hpos p)]; exact hle p
  refine ⟨ψ, hψ, fun p ↦ ⟨hpos p, hle p⟩, fun x ↦ prodFiberScaling_of_eq_one (h0 x.1),
    fun s x hx ↦ prodFiberScaling_of_eq_one (hA s x.1 hx),
    fun s ↦ mapsTo_prodFiberScaling_closedBall (fun u ↦ habs (s, u)) 1, fun x hx ↦ ?_⟩
  rw [mem_closedBall_zero_iff] at hx
  rcases lt_or_ge (1 - ε) ‖x.1‖ with hu | hu
  · exact Or.inr (by simpa using hu)
  · left
    rw [mem_ofPred_eq, norm_prodFiberScaling_snd, abs_of_pos (hpos _)]
    calc ψ (1, x.1) * ‖x.2‖ ≤ ψ (1, x.1) * 1 :=
          mul_le_mul_of_nonneg_left ((norm_snd_le x).trans hx) (hpos _).le
      _ < δ := by simpa using h1 x.1 hu

end Cube

end SymplecticGeometry

end
