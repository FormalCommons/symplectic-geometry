/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Foliation.Leaf
import SymplecticGeometry.Geometry.Manifold.MFDeriv.Constancy

/-!
# Maps constant along the leaves of a foliation

Let `𝓕` be a foliation of a real manifold `M` and `f : M → N` a map whose derivative vanishes on
the tangent spaces of `𝓕`. Along a curve tangent to `𝓕`, the derivative of `f ∘ γ` is then zero,
so by the mean value theorem `f ∘ γ` is constant. This holds locally, on a piece of the curve
that stays where the hypotheses on `f` hold, and so globally: `f` is constant on each leaf.

## Main results

* `TauCeti.Foliation.apply_eq_of_contMDiffOn_of_tangent`: a real map whose derivative vanishes
  on the tangent spaces of a foliation over a set `U` is constant along each convex piece of a
  tangent curve that stays in `U`.
* `TauCeti.Foliation.SameLeaf.apply_eq_of_le_ker`: a differentiable real map whose derivative
  vanishes on the tangent spaces of a foliation is constant on each leaf.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 19
  (distributions and foliations).
-/

public section

noncomputable section

open Set TauCeti
open scoped Manifold ContDiff

namespace TauCeti.Foliation

open TauCeti.Manifold

variable {E F H G M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω} [IsManifold I (n + 1) M] {f : M → N} {x y : M}

/-- Let `f` be a real map, differentiable at each point of a set `U`, whose derivative at each
point of `U` kills the tangent space of a foliation there. Let `γ` be a `C¹` curve on `[0, 1]`
and `S` a convex subset of `[0, 1]` that `γ` maps into `U`, with `γ` tangent to the foliation at
each point of `S`. Then `f ∘ γ` is constant on `S`. -/
theorem apply_eq_of_contMDiffOn_of_tangent [IsManifold J 1 N] {k : ℕ} {𝓕 : Foliation I n M k}
    {U : Set M} (hf : ∀ x ∈ U, MDifferentiableAt I J f x)
    (hD : ∀ x ∈ U, 𝓕.distribution x ≤ (mfderiv I J f x).ker) {γ : ℝ → M}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc 0 1)) {S : Set ℝ} (hS : Convex ℝ S)
    (hS₁ : S ⊆ Icc 0 1) (hγS : MapsTo γ S U)
    (htan : ∀ t ∈ S, curveVelocityWithin I γ (Icc 0 1) t ∈ 𝓕.distribution (γ t)) {a b : ℝ}
    (ha : a ∈ S) (hb : b ∈ S) : f (γ a) = f (γ b) := by
  -- Along `γ`, the derivative of `f ∘ γ` vanishes.
  refine Convex.apply_eq_of_hasMFDerivWithinAt_zero (J := J) (g := f ∘ γ) hS
    (fun t ht ↦ ?_) ha hb
  have hft : MDifferentiableAt I J f (γ t) := hf (γ t) (hγS ht)
  have hγt := hγ.mdifferentiableOn one_ne_zero t (hS₁ ht)
  have hv := hD (γ t) (hγS ht) (htan t ht)
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hv
  have hd := hasMFDerivWithinAt_curveVelocityWithin (hft.comp_mdifferentiableWithinAt t hγt)
  rw [curveVelocityWithin_map hft (uniqueDiffOn_Icc zero_lt_one t (hS₁ ht)) hγt, hv,
    ContinuousLinearMap.smulRight_zero] at hd
  exact hd.mono hS₁

/-- A differentiable real map whose derivative kills the tangent spaces of a foliation is constant
on each leaf of the foliation. -/
theorem SameLeaf.apply_eq_of_le_ker [IsManifold J 1 N] {k : ℕ} {𝓕 : Foliation I n M k}
    (hf : MDifferentiable I J f) (hD : ∀ x, 𝓕.distribution x ≤ (mfderiv I J f x).ker)
    (h : 𝓕.SameLeaf x y) : f x = f y := by
  refine sameLeaf_le (r := fun x y ↦ f x = f y) ⟨fun _ ↦ rfl, Eq.symm, Eq.trans⟩
    (fun x y hxy ↦ ?_) x y h
  obtain ⟨γ, hγ, htan, rfl, rfl⟩ := joinedByTangentCurve_iff.mp hxy
  exact apply_eq_of_contMDiffOn_of_tangent (U := univ) (fun x _ ↦ hf x) (fun x _ ↦ hD x) hγ
    (convex_Icc 0 1) subset_rfl (mapsTo_univ _ _) htan (left_mem_Icc.2 zero_le_one)
    (right_mem_Icc.2 zero_le_one)

end TauCeti.Foliation

end
