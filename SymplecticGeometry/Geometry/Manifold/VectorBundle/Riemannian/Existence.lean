/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Existence

/-!
# Riemannian metrics satisfying a convex fibrewise condition

Let `c b` be a convex set of continuous bilinear forms on the fibre `E b` of a vector bundle with
finite-dimensional fibres over a σ-compact Hausdorff smooth manifold modelled on a
finite-dimensional space. If near each point there is a local `C^n` field of symmetric positive
definite forms lying in `c`, then some `C^n` Riemannian metric lies in `c b` over every point `b`
(`TauCeti.exists_contMDiffRiemannianMetric_inner_mem_of_local`).

This is the case of Tau Ceti's
`TauCeti.exists_contMDiffRiemannianMetric_inner_eq_and_inner_mem_of_locallyFinite` with no
prescribed values, stated so that callers need not pass an empty family of closed sets. The
declaration is in the namespace `TauCeti`, next to that lemma, since it concerns only Tau Ceti's
and Mathlib's notions.

## Main results

* `TauCeti.exists_contMDiffRiemannianMetric_inner_mem_of_local`: local metrics satisfying a convex
  fibrewise condition glue to a global metric satisfying it.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Proposition 13.3
  (existence of Riemannian metrics, by partitions of unity).
-/

public section

noncomputable section

open Bundle Set
open scoped ContDiff Manifold Topology

namespace TauCeti

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : ℕ∞}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ b, TopologicalSpace (E b)] [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E]

/-- **Gluing local metrics under a convex fibrewise condition.** Let `c b` be a convex set of
bilinear forms on the fibre over `b` of a vector bundle with finite-dimensional fibres over a
σ-compact Hausdorff smooth manifold modelled on a finite-dimensional space. Suppose that near each
point there is a local `C^n` field of symmetric positive definite forms lying in `c`. Then there is
a `C^n` Riemannian metric lying in `c b` over every point `b`. -/
theorem exists_contMDiffRiemannianMetric_inner_mem_of_local
    [FiniteDimensional ℝ EB] [T2Space B] [SigmaCompactSpace B] [IsManifold IB ∞ B]
    [FiniteDimensional ℝ F] {c : (b : B) → Set (E b →L[ℝ] E b →L[ℝ] ℝ)}
    (hc : ∀ b, Convex ℝ (c b))
    (hloc : ∀ x₀, ∃ V ∈ 𝓝 x₀, ∃ s : (b : B) → E b →L[ℝ] E b →L[ℝ] ℝ,
      ContMDiffOn IB (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
        (fun b ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) b (s b)) V ∧
      ∀ b ∈ V, ((∀ v w, s b v w = s b w v) ∧ ∀ v, v ≠ 0 → 0 < s b v v) ∧ s b ∈ c b) :
    ∃ g : ContMDiffRiemannianMetric IB n F E, ∀ b, g.inner b ∈ c b := by
  obtain ⟨g, -, hg⟩ := exists_contMDiffRiemannianMetric_inner_eq_and_inner_mem_of_locallyFinite
    (A := (Empty.elim : Empty → Set B)) (U := Empty.elim) (β := Empty.elim)
    (fun i ↦ i.elim) (locallyFinite_of_finite _) (fun i ↦ i.elim) (fun i ↦ i.elim)
    (fun i ↦ i.elim) (fun i ↦ i.elim) (fun i ↦ i.elim) (fun i ↦ i.elim) hc (fun i ↦ i.elim)
    fun x₀ _ ↦ hloc x₀
  exact ⟨g, hg⟩

end TauCeti
