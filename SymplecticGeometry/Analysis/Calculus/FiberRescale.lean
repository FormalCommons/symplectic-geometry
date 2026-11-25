/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.UnitInterval
public import TauCeti.Analysis.Calculus.FDeriv.NormalSegment

import TauCeti.Analysis.Calculus.FDeriv.Prod

/-!
# Smooth rescaling of a map along the zero section

Let `P`, `F` and `G` be real normed spaces and `f : P × F → G`. Rescaling `f` in the fibre
variable gives `(p, v, t) ↦ t⁻¹ • f (p, t • v)` for `t ≠ 0`; at `t = 0` we put the fibre
derivative `fderiv ℝ (fun w ↦ f (p, w)) 0 v` (`fiberRescale`).

If `f` is `C^(n+1)` on an open set `U` and vanishes on `U ∩ (P × {0})`, then by Hadamard's lemma
in the fibre variable
`fiberRescale f ((p, v), t) = ∫ s in 0..1, fderiv ℝ (fun w ↦ f (p, w)) (s • t • v) v`
whenever the segment from `(p, 0)` to `(p, t • v)` lies in `U` (`fiberRescale_eq_integral`).
Differentiating under the integral sign, `fiberRescale f` is `C^n` on the open set of such
`(p, v, t)` (`contDiffOn_fiberRescale`), also at `t = 0`. If `U` is star-shaped in the fibre
variable, this set is that of all `(p, v, t)` with `(p, t • v) ∈ U`
(`contDiffOn_fiberRescale_of_starShaped`).

Both results are Tau Ceti's Hadamard lemma along normal segments
(`TauCeti/Analysis/Calculus/FDeriv/NormalSegment.lean`) in the coordinates of this file: the
formula for `t ≠ 0` is `TauCeti.inv_smul_sub_eq_integral_fderiv_of_mem_normalSegmentDomain`, and
the smoothness of the integral is `TauCeti.contDiffOn_integral_fderiv_normalSegmentDomain`; the
fibre derivative is the full derivative in the direction `(0, v)` by `TauCeti.fderiv_slice_right`.
The definition, its value lemmas and the open domain on which its regularity is stated follow Tau
Ceti's `TauCeti.zeroSectionRescale` and `TauCeti.continuousOn_zeroSectionRescale`
(`TauCeti/Topology/Homotopy/Isotopy/Linearization.lean`), the continuous counterpart of this
rescaling. Tau Ceti's private `linearizationMotion`
(`TauCeti/Geometry/Manifold/SmoothIsotopy/Linearization.lean`) is the smooth case of a map on the
whole space without parameters.

## Main definitions and results

* `fiberRescale f`: the rescaling of `f` in the fibre variable, extended at `t = 0` by the
  fibre derivative of `f` at the zero section.
* `fiberRescale_of_ne_zero`, `fiberRescale_zero`, `fiberRescale_one`: its values for `t ≠ 0`,
  at `t = 0` and at `t = 1`.
* `fiberRescale_eq_integral`: Hadamard's formula for the rescaling.
* `integral_fderiv_slice_right_eq_integral_fderiv`: the fibre derivative under that integral is
  the derivative of `f` in the direction `(0, v)`.
* `contDiffOn_fiberRescale`, `contDiffOn_fiberRescale_of_starShaped`: its smoothness.
* `fderiv_inv_smul_comp_smul`: for `t ≠ 0`, the derivative of `x ↦ t⁻¹ • f (t • x)` at `z` is
  that of `f` at `t • z`.

## References

* M. W. Hirsch, *Differential Topology*, Graduate Texts in Mathematics 33, Springer, 1976,
  Chapter 4, §5.
-/

public section

noncomputable section

open Set
open scoped ContDiff unitInterval

/-- The derivative of the rescaling `x ↦ s⁻¹ • f (s • x)` of `f` at `z` is the derivative of `f`
at `s • z`, for `s ≠ 0`. -/
theorem fderiv_inv_smul_comp_smul {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (f : E → F) {s : 𝕜} (hs : s ≠ 0) (z : E) :
    fderiv 𝕜 (fun x ↦ s⁻¹ • f (s • x)) z = fderiv 𝕜 f (s • z) := by
  let : Invertible s⁻¹ := invertibleOfNonzero (inv_ne_zero hs)
  have h : (fun x ↦ s⁻¹ • f (s • x)) = s⁻¹ • fun x ↦ f (s • x) :=
    funext fun x ↦ (Pi.smul_apply s⁻¹ (fun x ↦ f (s • x)) x).symm
  rw [h, fderiv_const_smul_of_invertible, fderiv_comp_smul, inv_smul_smul₀ hs]

variable {P F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
  [NormedSpace ℝ G]

/-- The rescaling of `f : P × F → G` in the fibre variable: at `((p, v), t)` it is
`t⁻¹ • f (p, t • v)` for `t ≠ 0`, and the fibre derivative `fderiv ℝ (fun w ↦ f (p, w)) 0 v` of
`f` at `(p, 0)` for `t = 0`. -/
def fiberRescale (f : P × F → G) (q : (P × F) × ℝ) : G :=
  if q.2 = 0 then fderiv ℝ (fun w ↦ f (q.1.1, w)) 0 q.1.2
  else q.2⁻¹ • f (q.1.1, q.2 • q.1.2)

theorem fiberRescale_def (f : P × F → G) (q : (P × F) × ℝ) :
    fiberRescale f q = if q.2 = 0 then fderiv ℝ (fun w ↦ f (q.1.1, w)) 0 q.1.2
      else q.2⁻¹ • f (q.1.1, q.2 • q.1.2) := (rfl)

/-- For `t ≠ 0` the rescaling is `t⁻¹ • f (p, t • v)`. -/
theorem fiberRescale_of_ne_zero (f : P × F → G) {q : (P × F) × ℝ} (hq : q.2 ≠ 0) :
    fiberRescale f q = q.2⁻¹ • f (q.1.1, q.2 • q.1.2) := by
  simp [fiberRescale_def, hq]

/-- At `t = 0` the rescaling is the fibre derivative of `f` at the zero section. -/
@[simp]
theorem fiberRescale_zero (f : P × F → G) (p : P × F) :
    fiberRescale f (p, 0) = fderiv ℝ (fun w ↦ f (p.1, w)) 0 p.2 := by
  simp [fiberRescale_def]

/-- At `t = 1` the rescaling is `f`. -/
@[simp]
theorem fiberRescale_one (f : P × F → G) (p : P × F) : fiberRescale f (p, 1) = f p := by
  simp [fiberRescale_of_ne_zero f (q := (p, 1)) one_ne_zero]

variable [NormedAddCommGroup P] [NormedSpace ℝ P] {f : P × F → G} {U : Set (P × F)}

/-- If `f` is differentiable on an open set `U` containing the segment from `(p, 0)` to
`(p, t • v)`, the average over `s ∈ [0, 1]` of the fibre derivative
`fderiv ℝ (fun w ↦ f (p, w)) (s • t • v) v` is that of the derivative
`fderiv ℝ f (p, s • t • v) (0, v)` of `f`, the form in which Tau Ceti's Hadamard lemma along
normal segments states it. -/
theorem integral_fderiv_slice_right_eq_integral_fderiv (hU : IsOpen U)
    (hf : DifferentiableOn ℝ f U) {p : P} {t : ℝ} {v : F}
    (hq : ∀ s ∈ Icc (0 : ℝ) 1, (p, s • t • v) ∈ U) :
    ∫ s in (0 : ℝ)..1, fderiv ℝ (fun w ↦ f (p, w)) (s • t • v) v =
      ∫ s in (0 : ℝ)..1, fderiv ℝ f (p, s • t • v) (0, v) := by
  refine intervalIntegral.integral_congr fun s hs ↦ ?_
  rw [uIcc_of_le zero_le_one] at hs
  simp [TauCeti.fderiv_slice_right (hf.differentiableAt (hU.mem_nhds (hq s hs)))]

/-- **Hadamard's formula for the rescaling.** If `f` is `C¹` on an open set `U`, vanishes on
`U ∩ (P × {0})`, and `U` contains the segment from `(p, 0)` to `(p, t • v)`, then the rescaling
of `f` at `((p, v), t)` is the average of `fderiv ℝ (fun w ↦ f (p, w)) (s • t • v) v` over
`s ∈ [0, 1]`. -/
theorem fiberRescale_eq_integral [CompleteSpace G] (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U)
    (hf0 : ∀ p, (p, (0 : F)) ∈ U → f (p, 0) = 0) {q : (P × F) × ℝ}
    (hq : ∀ s : I, (q.1.1, (s : ℝ) • q.2 • q.1.2) ∈ U) :
    fiberRescale f q =
      ∫ s in (0 : ℝ)..1, fderiv ℝ (fun w ↦ f (q.1.1, w)) (s • q.2 • q.1.2) q.1.2 := by
  obtain ⟨⟨p, v⟩, t⟩ := q
  dsimp only at hq ⊢
  by_cases ht : t = 0
  · subst ht
    simp
  have hs : ∀ s ∈ Icc (0 : ℝ) 1, (p, s • t • v) ∈ U := fun s hs ↦ hq ⟨s, hs⟩
  have hq' : (t, (p, v)) ∈ TauCeti.normalSegmentDomain U := TauCeti.mem_normalSegmentDomain.2 hs
  rw [fiberRescale_of_ne_zero f ht, integral_fderiv_slice_right_eq_integral_fderiv hU
    (hf.differentiableOn one_ne_zero) hs,
    ← TauCeti.inv_smul_sub_eq_integral_fderiv_of_mem_normalSegmentDomain hU hf ht hq',
    hf0 p (TauCeti.mk_zero_mem_of_mem_normalSegmentDomain hq'), sub_zero]

/-- **Smoothness of the rescaling.** If `f` is `C^(n+1)` on an open set `U` and vanishes on
`U ∩ (P × {0})`, its rescaling in the fibre variable is `C^n` on the set of `((p, v), t)` such
that `U` contains the segment from `(p, 0)` to `(p, t • v)`; this set is open. -/
theorem contDiffOn_fiberRescale [CompleteSpace G] {n : ℕ∞} (hU : IsOpen U)
    (hf : ContDiffOn ℝ (n + 1) f U)
    (hf0 : ∀ p, (p, (0 : F)) ∈ U → f (p, 0) = 0) :
    ContDiffOn ℝ n (fiberRescale f) {q | ∀ s : I, (q.1.1, (s : ℝ) • q.2 • q.1.2) ∈ U} := by
  refine ((TauCeti.contDiffOn_integral_fderiv_normalSegmentDomain hU hf).comp
    ((by fun_prop : ContDiff ℝ n fun q : (P × F) × ℝ ↦ (q.2, q.1)).contDiffOn
      (s := {q | ∀ s : I, (q.1.1, (s : ℝ) • q.2 • q.1.2) ∈ U}))
    fun q hq ↦ TauCeti.mem_normalSegmentDomain.2 fun s hs ↦ hq ⟨s, hs⟩).congr fun q hq ↦ ?_
  rw [fiberRescale_eq_integral hU (hf.of_le le_add_self) hf0 hq,
    integral_fderiv_slice_right_eq_integral_fderiv hU (hf.differentiableOn (by simp))
      fun s hs ↦ hq ⟨s, hs⟩]
  simp

/-- **Smoothness of the rescaling on a fibrewise star-shaped set.** If `U` is open and
star-shaped in the fibre variable, and `f` is `C^(n+1)` on `U` and vanishes on
`U ∩ (P × {0})`, then the rescaling of `f` in the fibre variable is `C^n` on the set of
`((p, v), t)` with `(p, t • v) ∈ U`. -/
theorem contDiffOn_fiberRescale_of_starShaped [CompleteSpace G] {n : ℕ∞} (hU : IsOpen U)
    (hstar : ∀ p v, (p, v) ∈ U → ∀ s ∈ Icc (0 : ℝ) 1, (p, s • v) ∈ U)
    (hf : ContDiffOn ℝ (n + 1) f U) (hf0 : ∀ p, (p, (0 : F)) ∈ U → f (p, 0) = 0) :
    ContDiffOn ℝ n (fiberRescale f) {q | (q.1.1, q.2 • q.1.2) ∈ U} :=
  (contDiffOn_fiberRescale hU hf hf0).mono fun _ hq s ↦ hstar _ _ hq s s.property

end
