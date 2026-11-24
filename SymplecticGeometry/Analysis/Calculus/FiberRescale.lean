/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Calculus.Hadamard

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
smoothness of the integral is `TauCeti.contDiffOn_integral_smul_of_contDiffOn`.

## Main definitions and results

* `fiberRescale f`: the rescaling of `f` in the fibre variable, extended at `t = 0` by the
  fibre derivative of `f` at the zero section.
* `fiberRescale_of_ne_zero`, `fiberRescale_zero`, `fiberRescale_one`: its values for `t ≠ 0`,
  at `t = 0` and at `t = 1`.
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

/-- If `f` is `C^(n+1)` on an open set `U`, then `fderiv ℝ (fun w ↦ f (p, w)) (s • t • v) v`, the
integrand of Hadamard's formula for `fiberRescale`, is `C^n` in `(((p, v), t), s)` on the set where
`(p, s • t • v) ∈ U`. -/
theorem ContDiffOn.fderiv_snd_smul_smul_apply {n : ℕ∞} (hf : ContDiffOn ℝ (n + 1) f U)
    (hU : IsOpen U) :
    ContDiffOn ℝ n (fun x : ((P × F) × ℝ) × ℝ ↦
        fderiv ℝ (fun w ↦ f (x.1.1.1, w)) (x.2 • x.1.2 • x.1.1.2) x.1.1.2)
      {x | (x.1.1.1, x.2 • x.1.2 • x.1.1.2) ∈ U} := by
  intro x hx
  refine ContDiffAt.contDiffWithinAt ?_
  have hfx : ContDiffAt ℝ (n + 1) f (x.1.1.1, x.2 • x.1.2 • x.1.1.2) :=
    hf.contDiffAt (hU.mem_nhds hx)
  refine ContDiffAt.clm_apply (ContDiffAt.fderiv (f := fun (y : ((P × F) × ℝ) × ℝ) w ↦
      f (y.1.1.1, w)) ?_ (by fun_prop) le_rfl) (by fun_prop)
  exact ContDiffAt.comp (g := f) (f := fun y : (((P × F) × ℝ) × ℝ) × F ↦ (y.1.1.1.1, y.2)) _
    hfx (by fun_prop)

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
  set D : ℝ → G := fun s ↦ fderiv ℝ (fun w ↦ f (p, w)) (s • t • v) v
  have hmem : ∀ s ∈ uIcc (0 : ℝ) 1, (p, s • t • v) ∈ U := fun s hs ↦
    hq ⟨s, by simpa [uIcc_of_le zero_le_one] using hs⟩
  have hD : ContinuousOn D (uIcc 0 1) := by
    have h := (ContDiffOn.fderiv_snd_smul_smul_apply (n := 0) (by simpa using hf) hU).continuousOn
    exact h.comp (f := fun s : ℝ ↦ (((p, v), t), s)) (by fun_prop) fun s hs ↦ hmem s hs
  have hderiv : ∀ s ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ ↦ f (p, s • t • v)) (t • D s) s := by
    intro s hs
    have hdiff : DifferentiableAt ℝ (fun w ↦ f (p, w)) (s • t • v) :=
      ((hf.contDiffAt (hU.mem_nhds (hmem s hs))).differentiableAt one_ne_zero).comp _
        (by fun_prop)
    have h := hdiff.hasFDerivAt.comp_hasDerivAt s ((hasDerivAt_id s).smul_const (t • v))
    simpa [D, map_smul, Function.comp_def] using h
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((hD.const_smul t).intervalIntegrable)
  rw [intervalIntegral.integral_smul] at hFTC
  simp only [one_smul, zero_smul, sub_zero, hf0 p (by simpa using hmem 0 (by simp))] at hFTC
  rw [← hFTC, inv_smul_smul₀ ht]

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
    (hf.fderiv_snd_smul_smul_apply hU) (U := {q | ∀ s : I, (q.1.1, (s : ℝ) • q.2 • q.1.2) ∈ U})
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
