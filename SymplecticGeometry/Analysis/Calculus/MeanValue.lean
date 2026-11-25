/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import TauCeti.Analysis.Calculus.FDeriv.Remainder
import TauCeti.Topology.Compactness.Normed

/-!
# First-order Taylor estimates

For a map `f : E → F` and a field `G : E → E →L[ℝ] F` of linear maps, this file compares the
first-order Taylor maps `x ↦ f a + G a (x - a)` at different base points, and bounds the remainder
`f x - f a - G a (x - a)` uniformly over a compact set. When `G = fderiv ℝ f` these are the usual
first-order Taylor expansions; for a general `G` they are the holonomic sections used in the proof
of holonomic approximation in [EliashbergMishachev2002], Chapter 3.

## Main results

* `SymplecticGeometry.taylor_sub_taylor_eq` and `SymplecticGeometry.norm_taylor_sub_taylor_le`:
  the Taylor maps at `a` and at `b` differ at `x` by minus the remainder `f b - f a - G a (b - a)`
  plus `(G a - G b) (x - b)`.
* `IsCompact.exists_pos_norm_taylor_remainder_le`: over a compact set `K`, for a `C¹` map `f` and
  a continuous `G`, the remainder `f x - f a - G a (x - a)` is at most
  `(‖fderiv ℝ f a - G a‖ + η) * ‖x - a‖`, and `G x` is `η`-close to `G a`, for all `a ∈ K` and
  `x` in a ball of radius independent of `a`. It follows from Tau Ceti's uniform first-order
  estimate `IsCompact.exists_pos_forall_norm_sub_sub_fderiv_le`, applied to the constant family
  `fun _ ↦ f`, and its uniform continuity lemma `IsCompact.exists_pos_forall_norm_sub_le`.

## References

* [Y. Eliashberg and N. Mishachev, *Introduction to the h-Principle*][EliashbergMishachev2002]
-/

public section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

namespace SymplecticGeometry

/-- The first-order Taylor maps `x ↦ f a + G a (x - a)` and `x ↦ f b + G b (x - b)` differ by
minus the remainder `f b - f a - G a (b - a)` plus `(G a - G b) (x - b)`. -/
theorem taylor_sub_taylor_eq (f : E → F) (G : E → E →L[ℝ] F) (a b x : E) :
    (f a + G a (x - a)) - (f b + G b (x - b)) =
      -(f b - f a - G a (b - a)) + (G a - G b) (x - b) := by
  have : x - a = (b - a) + (x - b) := by abel
  rw [this, map_add, sub_apply]
  abel

/-- The first-order Taylor maps `x ↦ f a + G a (x - a)` and `x ↦ f b + G b (x - b)` differ at `x`
by at most `‖f b - f a - G a (b - a)‖ + ‖G a - G b‖ * ‖x - b‖`. -/
theorem norm_taylor_sub_taylor_le (f : E → F) (G : E → E →L[ℝ] F) (a b x : E) :
    ‖(f a + G a (x - a)) - (f b + G b (x - b))‖ ≤
      ‖f b - f a - G a (b - a)‖ + ‖G a - G b‖ * ‖x - b‖ := by
  rw [taylor_sub_taylor_eq, ← norm_neg (f b - f a - G a (b - a))]
  exact (norm_add_le _ _).trans (add_le_add_right ((G a - G b).le_opNorm _) _)

end SymplecticGeometry

/-- **Uniform Taylor estimate.** Let `f` be `C¹`, `G` continuous, `K` compact and `η > 0`. There
is `ρ > 0` such that for every `a ∈ K` and every `x` with `‖x - a‖ < ρ`, the remainder
`f x - f a - G a (x - a)` has norm at most `(‖fderiv ℝ f a - G a‖ + η) * ‖x - a‖`, and
`‖G x - G a‖ ≤ η`. -/
theorem IsCompact.exists_pos_norm_taylor_remainder_le {f : E → F} {G : E → E →L[ℝ] F}
    {K : Set E} (hK : IsCompact K) (hf : ContDiff ℝ 1 f) (hG : Continuous G) {η : ℝ}
    (hη : 0 < η) :
    ∃ ρ > 0, ∀ a ∈ K, ∀ x, ‖x - a‖ < ρ →
      ‖f x - f a - G a (x - a)‖ ≤ (‖fderiv ℝ f a - G a‖ + η) * ‖x - a‖ ∧ ‖G x - G a‖ ≤ η := by
  obtain ⟨ρ₁, hρ₁, h₁⟩ := hK.exists_pos_forall_norm_sub_sub_fderiv_le (F := fun _ ↦ f) (x := id)
    (fun _ _ ↦ (hf.comp contDiff_snd).contDiffAt) continuousOn_id hη
  obtain ⟨ρ₂, hρ₂, h₂⟩ := hK.exists_pos_forall_norm_sub_le (Φ := fun q : E × E ↦ G q.2)
    continuousOn_id (fun _ _ ↦ (hG.comp continuous_snd).continuousAt) hη
  refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, fun a ha x hx ↦
    ⟨?_, h₂ a ha x (hx.le.trans (min_le_right _ _))⟩⟩
  have hrem := h₁ a ha (x - a) (hx.le.trans (min_le_left _ _))
  simp only [id, add_sub_cancel] at hrem
  have heq : f x - f a - G a (x - a) =
      (f x - f a - fderiv ℝ f a (x - a)) + (fderiv ℝ f a - G a) (x - a) := by
    rw [sub_apply]
    abel
  rw [heq, add_mul, add_comm (‖fderiv ℝ f a - G a‖ * _)]
  exact (norm_add_le _ _).trans (add_le_add hrem ((fderiv ℝ f a - G a).le_opNorm _))

end
