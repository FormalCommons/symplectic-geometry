/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Diffeomorphism.Diffeotopy.Translate
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Holonomic approximation in coordinates: conventions and wiggling

This file starts the coordinate treatment of holonomic approximation, following
[EliashbergMishachev2002], Chapter 3. The model is
`D := (Fin m → ℝ) × (Fin k → ℝ)`, with the core directions first and the transverse directions
second, and with sup norms, so that the cube `Iᵐ` is `Metric.closedBall (0 : Fin m → ℝ) 1` and
no cube needs a definition.

A formal section (a first jet over `D` with values in a normed space `F`) is a pair of maps
`f : D → F` and `G : D → D →L[ℝ] F`. It is holonomic on `s` when `∀ x ∈ s, fderiv ℝ f x = G x`.
Neither notion gets a definition: statements carry the two maps and this equation.

The file proves the one-dimensional *wiggling* lemma, the zig-zag diffeotopy that both
[EliashbergMishachev2002], §3.2, and the handle-core argument of [McDuffSalamon2017], Lemma 7.3.2,
use: a compactly supported diffeotopy that moves points by less than a given `δ`, stays in the
`δ`-neighbourhood of a compact set `K`, and on `K` itself pushes each point in a transverse
direction by `r sin (N u)`, where `u` is a core coordinate. As `N` grows the image of a segment
along that core coordinate oscillates more and more often between the heights `± r`, so its
length in the transverse direction is as large as wanted.

## Main results

* `SymplecticGeometry.exists_wiggling_diffeotopy`: the zig-zag on `D`. It is the case
  `g = sin (N uᵢ)`, `e = (0, r eⱼ)` of `SymplecticGeometry.exists_diffeotopy_apply_eq_add_smul`.

## References

* [Y. Eliashberg and N. Mishachev, *Introduction to the h-Principle*][EliashbergMishachev2002]
* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017]
-/

public section

open Set Metric
open scoped Manifold ContDiff

namespace SymplecticGeometry

/-- **The wiggling lemma.** On `D = (Fin m → ℝ) × (Fin k → ℝ)` with sup norms, let `K` be compact,
`i` a core direction, `j` a transverse direction, `0 ≤ r < δ` and `N : ℝ`. There is a smooth
diffeotopy `h` of `D` that is the identity off a compact subset of the `δ`-neighbourhood of `K`,
moves every point by less than `δ`, and sends each `(u, v) ∈ K` at time `t` to
`(u, v + t r sin (N uᵢ) eⱼ)`. Taking `N` large makes the image of a segment along the `i`-th core
direction zig-zag between the transverse heights `± r` as often as wanted. -/
theorem exists_wiggling_diffeotopy {m k : ℕ} {K : Set ((Fin m → ℝ) × (Fin k → ℝ))}
    (hK : IsCompact K) (i : Fin m) (j : Fin k) {r δ : ℝ} (hr : 0 ≤ r) (hrδ : r < δ) (N : ℝ) :
    ∃ h : TauCeti.Diffeotopy 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ)) ∞ ((Fin m → ℝ) × (Fin k → ℝ)),
      (∃ C, IsCompact C ∧ C ⊆ thickening δ K ∧ ∀ t, ∀ x ∉ C, h (t, x) = x) ∧
      (∀ t x, dist (h (t, x)) x < δ) ∧
      ∀ t, ∀ x ∈ K, h (t, x) = (x.1, x.2 + Pi.single j ((t : ℝ) * r * Real.sin (N * x.1 i))) := by
  set e : (Fin m → ℝ) × (Fin k → ℝ) := (0, Pi.single j r)
  have hne : ‖e‖ = r := by
    have h2 : ‖e‖ = ‖(Pi.single j r : Fin k → ℝ)‖ := by simp [e]
    rw [h2, ← coe_nnNorm, Pi.nnNorm_single, coe_nnNorm, Real.norm_of_nonneg hr]
  have hg : ContDiff ℝ ∞ fun x : (Fin m → ℝ) × (Fin k → ℝ) ↦ Real.sin (N * x.1 i) :=
    by fun_prop
  obtain ⟨h, hsupp, hsmall, hK'⟩ := exists_diffeotopy_apply_eq_add_smul hK hg
    (fun x ↦ Real.abs_sin_le_one _) (e := e) (fun x _ s ↦ by simp [e]) (hne ▸ hrδ)
  refine ⟨h, hsupp, fun t x ↦ ?_, fun t x hx ↦ ?_⟩
  · rw [dist_eq_norm]
    calc ‖h (t, x) - x‖ ≤ (t : ℝ) * ‖e‖ := hsmall t x
      _ ≤ 1 * r := by rw [hne]; gcongr; exact t.property.2
      _ < δ := by linarith
  · rw [hK' t x hx]
    ext l
    · simp [e]
    · simp only [e, Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rcases eq_or_ne l j with rfl | hl
      · simp; ring
      · simp [hl]

end SymplecticGeometry

end
