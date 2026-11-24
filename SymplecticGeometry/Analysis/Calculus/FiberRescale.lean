/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Calculus.ParametricIntegral.Basic

import TauCeti.Analysis.Calculus.ParametricIntegral.Segment
import TauCeti.MeasureTheory.Constructions.UnitInterval

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

This is the local, parametrised form of Hadamard's factorization in Tau Ceti
(`hadamardFactor`, `ContDiff.sub_eq_hadamardFactor_apply`), whose statements need `f` to be
smooth everywhere; the rescaling formula and its smoothness follow those of Tau Ceti's private
`linearizationMotion` (`TauCeti/Geometry/Manifold/SmoothIsotopy/Linearization.lean`), adapted
from a map on the whole space without parameters to a map on an open set with parameters. The
definition, its value lemmas and the open domain on which its regularity is stated follow Tau
Ceti's `TauCeti.zeroSectionRescale` and `TauCeti.continuousOn_zeroSectionRescale`
(`TauCeti/Topology/Homotopy/Isotopy/Linearization.lean`), the continuous counterpart of this
rescaling. The segment formula is Tau Ceti's `StarConvex.sub_eq_intervalIntegral_lineMap_apply`
in the fibre, and the smoothness of the integral is
`TauCeti.contDiffOn_integral_smul_of_contDiffOn`.

## Main definitions and results

* `fiberRescale f`: the rescaling of `f` in the fibre variable, extended at `t = 0` by the
  fibre derivative of `f` at the zero section.
* `fiberRescale_of_ne_zero`, `fiberRescale_zero`, `fiberRescale_one`: its values for `t ≠ 0`,
  at `t = 0` and at `t = 1`.
* `ContDiffOn.fderiv_right_of_isOpen`: the partial derivative in the second variable of a map
  that is `C^(n+1)` on an open set of the product, not necessarily a product set, is `C^n` there.
* `fiberRescale_eq_integral`: Hadamard's formula for the rescaling.
* `contDiffOn_fiberRescale`, `contDiffOn_fiberRescale_of_starShaped`: its smoothness.

## References

* M. W. Hirsch, *Differential Topology*, Graduate Texts in Mathematics 33, Springer, 1976,
  Chapter 4, §5.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff unitInterval

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

/-- The partial derivative in the second variable of a map `f : E → F → G` that is `C^(n+1)` on
an open set `U ⊆ E × F` is `C^n` on `U`. Unlike `ContDiffOn.fderiv_right`, `U` need not be a
product of sets. -/
theorem ContDiffOn.fderiv_right_of_isOpen {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] {f : E → F → G} {U : Set (E × F)} (hU : IsOpen U)
    {n : ℕ∞ω} (hf : ContDiffOn 𝕜 (n + 1) (Function.uncurry f) U) :
    ContDiffOn 𝕜 n (fun x : E × F ↦ fderiv 𝕜 (f x.1) x.2) U := by
  intro x hx
  refine ContDiffAt.contDiffWithinAt ?_
  refine ContDiffAt.fderiv (f := fun (y : E × F) w ↦ f y.1 w) ?_ contDiffAt_snd le_rfl
  exact ContDiffAt.comp (g := Function.uncurry f) (f := fun y : (E × F) × F ↦ (y.1.1, y.2)) _
    (hf.contDiffAt (hU.mem_nhds hx)) (by fun_prop)

/-- The integrand of Hadamard's formula for `fiberRescale` is `C^n` in all of its variables. -/
private theorem contDiffOn_fiberRescale_integrand {n : ℕ∞} (hf : ContDiffOn ℝ (n + 1) f U)
    (hU : IsOpen U) :
    ContDiffOn ℝ n (fun x : ((P × F) × ℝ) × ℝ ↦
        fderiv ℝ (fun w ↦ f (x.1.1.1, w)) (x.2 • x.1.2 • x.1.1.2) x.1.1.2)
      {x | (x.1.1.1, x.2 • x.1.2 • x.1.1.2) ∈ U} :=
  ((ContDiffOn.fderiv_right_of_isOpen (f := fun p w ↦ f (p, w)) hU hf).comp
    (f := fun x : ((P × F) × ℝ) × ℝ ↦ (x.1.1.1, x.2 • x.1.2 • x.1.1.2))
    (by fun_prop) fun _ hx ↦ hx).clm_apply (by fun_prop)

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
  rw [fiberRescale_of_ne_zero f ht]
  dsimp only
  -- the open slice of `U` over `p`, which contains the segment from `0` to `t • v`
  set S : Set F := {w | (p, w) ∈ U}
  have hS : IsOpen S := hU.preimage (by fun_prop)
  have hgS : ContDiffOn ℝ 1 (fun w ↦ f (p, w)) S :=
    hf.comp (by fun_prop) fun _ hw ↦ hw
  have hseg : segment ℝ 0 (t • v) ⊆ S := by
    rw [segment_eq_image_lineMap]
    rintro _ ⟨s, hs, rfl⟩
    simpa [S, AffineMap.lineMap_apply_module'] using hq ⟨s, hs⟩
  have h := (convex_segment (0 : F) (t • v)).starConvex (left_mem_segment ℝ 0 (t • v))
    |>.sub_eq_intervalIntegral_lineMap_apply ((hgS.continuousOn_fderiv_of_isOpen hS
      le_rfl).mono hseg) (fun z hz ↦ ((hgS.contDiffAt (hS.mem_nhds (hseg hz))).differentiableAt
      one_ne_zero).hasFDerivAt.hasFDerivWithinAt) (right_mem_segment ℝ 0 (t • v))
  simp only [AffineMap.lineMap_apply_module', sub_zero, add_zero, map_smul,
    intervalIntegral.integral_smul, hf0 p (by simpa using hq 0)] at h
  rw [h, inv_smul_smul₀ ht]

/-- **Smoothness of the rescaling.** If `f` is `C^(n+1)` on an open set `U` and vanishes on
`U ∩ (P × {0})`, its rescaling in the fibre variable is `C^n` on the set of `((p, v), t)` such
that `U` contains the segment from `(p, 0)` to `(p, t • v)`; this set is open. -/
theorem contDiffOn_fiberRescale [CompleteSpace G] {n : ℕ∞} (hU : IsOpen U)
    (hf : ContDiffOn ℝ (n + 1) f U)
    (hf0 : ∀ p, (p, (0 : F)) ∈ U → f (p, 0) = 0) :
    ContDiffOn ℝ n (fiberRescale f) {q | ∀ s : I, (q.1.1, (s : ℝ) • q.2 • q.1.2) ∈ U} := by
  have hW : IsOpen {x : ((P × F) × ℝ) × ℝ | (x.1.1.1, x.2 • x.1.2 • x.1.1.2) ∈ U} :=
    hU.preimage (by fun_prop)
  have h := TauCeti.contDiffOn_integral_smul_of_contDiffOn (μ := (volume : Measure I))
    (g := fun _ ↦ (1 : ℝ)) (integrable_const 1) continuous_subtypeVal hW
    (contDiffOn_fiberRescale_integrand hf hU)
    (U := {q | ∀ s : I, (q.1.1, (s : ℝ) • q.2 • q.1.2) ∈ U})
    fun q hq s ↦ hq s
  refine h.congr fun q hq ↦ ?_
  rw [fiberRescale_eq_integral hU (hf.of_le le_add_self) hf0 hq,
    TauCeti.intervalIntegral_eq_integral_unitInterval]
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
