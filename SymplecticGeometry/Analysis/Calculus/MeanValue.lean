/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Normed.Operator.Bilinear
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
* `IsCompact.exists_pos_norm_taylor_remainder_le`: over a compact set `K`, for a map `f` that is
  `C¹` at each point of `K` and a `G` that is continuous at each point of `K`, the remainder
  `f x - f a - G a (x - a)` is at most `(‖fderiv ℝ f a - G a‖ + η) * ‖x - a‖`, and `G x` is
  `η`-close to `G a`, for all `a ∈ K` and `x` in a ball of radius independent of `a`. It follows
  from Tau Ceti's uniform first-order estimate `IsCompact.exists_pos_forall_norm_sub_sub_fderiv_le`,
  applied to the constant family `fun _ ↦ f`, and its uniform continuity lemma
  `IsCompact.exists_pos_forall_norm_sub_le`.
* `IsCompact.exists_pos_norm_taylor_sub_le`: in the same setting, the Taylor map at `a` is
  `C¹`-close to `(f, G)` near `a`, and close to the Taylor maps at nearby base points.
* `SymplecticGeometry.contDiff_taylor` and `SymplecticGeometry.fderiv_taylor`: a Taylor map is
  smooth, with constant derivative `G a`.
* `SymplecticGeometry.norm_fderiv_taylor_affine_sub_le`: a Taylor map whose base point
  `L y + p₀` moves affinely with `y`, and whose linear part `Γ y` moves too, has derivative at
  `x` within `‖D Γ (x)‖ ‖x - (L x + p₀)‖` of `D f (L x + p₀) ∘ L + Γ x ∘ (1 - L)`.

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

/-- The first-order Taylor map `x ↦ f a + G a (x - a)` is smooth. -/
theorem contDiff_taylor (f : E → F) (G : E → E →L[ℝ] F) (a : E) {n : WithTop ℕ∞} :
    ContDiff ℝ n fun x ↦ f a + G a (x - a) :=
  contDiff_const.add ((G a).contDiff.comp (contDiff_id.sub contDiff_const))

/-- The first-order Taylor map `x ↦ f a + G a (x - a)` has derivative `G a` everywhere. -/
theorem hasFDerivAt_taylor (f : E → F) (G : E → E →L[ℝ] F) (a x : E) :
    HasFDerivAt (fun y ↦ f a + G a (y - a)) (G a) x := by
  simpa using ((G a).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const a)).const_add (f a)

/-- The derivative of the first-order Taylor map `x ↦ f a + G a (x - a)` is `G a`. -/
theorem fderiv_taylor (f : E → F) (G : E → E →L[ℝ] F) (a x : E) :
    fderiv ℝ (fun y ↦ f a + G a (y - a)) x = G a :=
  (hasFDerivAt_taylor f G a x).fderiv

/-- **The derivative of a Taylor map with a moving base point.** Let the base point `L y + p₀`
depend affinely on `y`, and let `Γ y` be a field of linear maps. The map
`y ↦ f (L y + p₀) + Γ y (y - (L y + p₀))` has derivative at `x` within
`‖D Γ (x)‖ ‖x - (L x + p₀)‖` of `D f (L x + p₀) ∘ L + Γ x ∘ (1 - L)`. -/
theorem norm_fderiv_taylor_affine_sub_le {f : E → F} {Γ : E → E →L[ℝ] F} (L : E →L[ℝ] E)
    (p₀ x : E) (hf : DifferentiableAt ℝ f (L x + p₀)) (hΓ : DifferentiableAt ℝ Γ x) :
    ‖fderiv ℝ (fun y ↦ f (L y + p₀) + Γ y (y - (L y + p₀))) x -
        ((fderiv ℝ f (L x + p₀)).comp L + (Γ x).comp (ContinuousLinearMap.id ℝ E - L))‖ ≤
      ‖fderiv ℝ Γ x‖ * ‖x - (L x + p₀)‖ := by
  have h₁ : HasFDerivAt (fun y ↦ L y + p₀) L x := L.hasFDerivAt.add_const p₀
  have h₂ : HasFDerivAt (fun y ↦ y - (L y + p₀)) (ContinuousLinearMap.id ℝ E - L) x :=
    (hasFDerivAt_id x).sub h₁
  have h₃ : HasFDerivAt (fun y ↦ f (L y + p₀) + Γ y (y - (L y + p₀)))
      ((fderiv ℝ f (L x + p₀)).comp L +
        ((Γ x).comp (ContinuousLinearMap.id ℝ E - L) + (fderiv ℝ Γ x).flip (x - (L x + p₀)))) x :=
    (hf.hasFDerivAt.comp x h₁).add (hΓ.hasFDerivAt.clm_apply h₂)
  rw [h₃.fderiv,
    ← add_assoc, add_sub_cancel_left, ← ContinuousLinearMap.opNorm_flip]
  exact ContinuousLinearMap.le_opNorm _ _

end SymplecticGeometry

/-- **Uniform Taylor estimate.** Let `K` be compact, `f` be `C¹` at each point of `K`, `G` be
continuous at each point of `K`, and `η > 0`. There is `ρ > 0` such that for every `a ∈ K` and
every `x` with `‖x - a‖ < ρ`, the remainder `f x - f a - G a (x - a)` has norm at most
`(‖fderiv ℝ f a - G a‖ + η) * ‖x - a‖`, and `‖G x - G a‖ ≤ η`. -/
theorem IsCompact.exists_pos_norm_taylor_remainder_le {f : E → F} {G : E → E →L[ℝ] F}
    {K : Set E} (hK : IsCompact K) (hf : ∀ a ∈ K, ContDiffAt ℝ 1 f a)
    (hG : ∀ a ∈ K, ContinuousAt G a) {η : ℝ} (hη : 0 < η) :
    ∃ ρ > 0, ∀ a ∈ K, ∀ x, ‖x - a‖ < ρ →
      ‖f x - f a - G a (x - a)‖ ≤ (‖fderiv ℝ f a - G a‖ + η) * ‖x - a‖ ∧ ‖G x - G a‖ ≤ η := by
  obtain ⟨ρ₁, hρ₁, h₁⟩ := hK.exists_pos_forall_norm_sub_sub_fderiv_le (F := fun _ ↦ f) (x := id)
    (fun a ha ↦ (hf a ha).comp _ contDiffAt_snd) continuousOn_id hη
  obtain ⟨ρ₂, hρ₂, h₂⟩ := hK.exists_pos_forall_norm_sub_le (Φ := fun q : E × E ↦ G q.2)
    continuousOn_id (fun a ha ↦ (hG a ha).comp continuousAt_snd) hη
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

/-- **Taylor maps are `C¹`-close to `(f, G)` near their base point, uniformly on a compact set.**
Let `K` be compact, `f` be `C¹` at each point of `K`, `G` be continuous at each point of `K`, and
`η > 0`. There is `ρ > 0` such that for every `a ∈ K` and every `x` with `‖x - a‖ < ρ`, writing
`Tₐ y = f a + G a (y - a)` for the Taylor map at `a`:
* `‖Tₐ x - f x‖ ≤ (‖fderiv ℝ f a - G a‖ + η) * ‖x - a‖`;
* `‖D Tₐ (x) - G x‖ ≤ η`;
* for every `y`, `‖Tₐ y - Tₓ y‖ ≤ (‖fderiv ℝ f a - G a‖ + η) * ‖x - a‖ + η * ‖y - x‖`. -/
theorem IsCompact.exists_pos_norm_taylor_sub_le {f : E → F} {G : E → E →L[ℝ] F}
    {K : Set E} (hK : IsCompact K) (hf : ∀ a ∈ K, ContDiffAt ℝ 1 f a)
    (hG : ∀ a ∈ K, ContinuousAt G a) {η : ℝ} (hη : 0 < η) :
    ∃ ρ > 0, ∀ a ∈ K, ∀ x, ‖x - a‖ < ρ →
      ‖(f a + G a (x - a)) - f x‖ ≤ (‖fderiv ℝ f a - G a‖ + η) * ‖x - a‖ ∧
      ‖fderiv ℝ (fun y ↦ f a + G a (y - a)) x - G x‖ ≤ η ∧
      ∀ y, ‖(f a + G a (y - a)) - (f x + G x (y - x))‖ ≤
        (‖fderiv ℝ f a - G a‖ + η) * ‖x - a‖ + η * ‖y - x‖ := by
  obtain ⟨ρ, hρ, h⟩ := hK.exists_pos_norm_taylor_remainder_le hf hG hη
  refine ⟨ρ, hρ, fun a ha x hx ↦ ?_⟩
  obtain ⟨h₁, h₂⟩ := h a ha x hx
  refine ⟨?_, ?_, fun y ↦ ?_⟩
  · rw [← norm_neg, show -(f a + G a (x - a) - f x) = f x - f a - G a (x - a) by abel]
    exact h₁
  · rw [SymplecticGeometry.fderiv_taylor, norm_sub_rev]
    exact h₂
  · refine (SymplecticGeometry.norm_taylor_sub_taylor_le f G a x y).trans ?_
    rw [norm_sub_rev (G a)]
    gcongr

end
