/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Existence
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# Smooth nowhere-zero sections

A smooth real vector bundle `V` with finite-dimensional fibres over a σ-compact Hausdorff manifold
`M` (possibly with boundary or corners) modelled on a finite-dimensional space has a smooth
nowhere-zero section as soon as it has a continuous one
(`SymplecticGeometry.exists_contMDiffSection_forall_ne_zero_of_continuous`). Compact manifolds,
with or without boundary, are the main case.

The proof fixes a Riemannian metric `g` on `V` and the continuous nowhere-zero section `s`. In each
fibre, the vectors `v` with `0 < g x v (s x)` form an open half-space, which is convex and does not
contain `0`. Near each point `x₀`, a smooth section through `s x₀` lies in these half-spaces, by
continuity of `g`. Mathlib's `exists_contMDiffSection_forall_mem_convex_of_local` glues such local
sections with a smooth partition of unity into a global smooth section lying in every half-space,
hence nowhere zero.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.6
  (where nowhere-zero sections of bundles over surfaces are used to build unitary frames)
-/

public section

open Bundle
open scoped Manifold ContDiff Topology

namespace SymplecticGeometry

variable {EB HB M : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
  [TopologicalSpace HB] {I : ModelWithCorners ℝ EB HB}
  [TopologicalSpace M] [ChartedSpace HB M] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, ContinuousConstSMul ℝ (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V] {n : ℕ∞} [ContMDiffVectorBundle n F V I]

/-- A `C^n` real vector bundle with finite-dimensional fibres over a σ-compact Hausdorff manifold
modelled on a finite-dimensional space, for instance a compact manifold with or without boundary,
has a `C^n` nowhere-zero section if it has a continuous nowhere-zero section. -/
theorem exists_contMDiffSection_forall_ne_zero_of_continuous {s : ∀ x, V x}
    (hs : Continuous fun x ↦ TotalSpace.mk' F x (s x)) (hs₀ : ∀ x, s x ≠ 0) :
    ∃ t : ContMDiffSection I F n V, ∀ x, t x ≠ 0 := by
  obtain ⟨g⟩ := TauCeti.nonempty_contMDiffRiemannianMetric (IB := I) (n := n) (F := F) (E := V)
  have hg : Continuous fun x ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ)
      (E := fun x ↦ V x →L[ℝ] V x →L[ℝ] ℝ) x (g.inner x) := g.contMDiff.continuous
  obtain ⟨t, ht⟩ := exists_contMDiffSection_forall_mem_convex_of_local (n := n) I V
    (fun x ↦ {v : V x | 0 < g.inner x v (s x)})
    (fun x ↦ convex_halfSpace_gt ⟨fun v w ↦ by simp, fun c v ↦ by simp⟩ 0) fun x₀ ↦ by
      let σ := FiberBundle.contMDiffExtend I F (s x₀)
      have hσ : CMDiff n (T% σ) := FiberBundle.contMDiff_contMDiffExtend I F (s x₀)
      have hcont : ContinuousAt (fun y ↦ TotalSpace.mk' ℝ (E := Trivial M ℝ) y
          (g.inner y (σ y) (s y))) x₀ :=
        hg.continuousAt.clm_bundle_apply₂ hσ.continuous.continuousAt hs.continuousAt
      rw [FiberBundle.continuousAt_totalSpace] at hcont
      refine ⟨_, hcont.2.eventually (lt_mem_nhds ?_), σ, hσ.contMDiffOn, fun y hy ↦ hy⟩
      simpa [σ] using g.pos x₀ _ (hs₀ x₀)
  exact ⟨t, fun x h ↦ by simpa [h] using ht x⟩

end SymplecticGeometry

end
