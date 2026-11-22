/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Topology.Algebra.Module.Complement
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic

/-!
# Smooth maps into a complemented submodule

A map `f : M → p` into a submodule `p` of a normed space `F` is `C^n` exactly when its composite
with the inclusion `p.subtypeL` is, provided `p` has a closed complement
(`Submodule.ClosedComplemented`): a continuous linear projection onto `p` recovers `f` from
that composite. This holds for every order `n`, the analytic order `ω` included, and for a source
manifold with any model. The submodule may be a submodule over a ring `𝕜'` other than the
field `𝕜` of smoothness, through a scalar tower. A finite-dimensional submodule of a real or
complex normed space is closed complemented (`Submodule.ClosedComplemented.of_finiteDimensional`).

The global form `contMDiff_iff_subtypeL_comp` comes from Tau Ceti: the projection is a
continuous left inverse of the inclusion, so `ContinuousLinearMap.HasLeftInverse.isSmoothEmbedding`
makes the inclusion a `C^n` embedding, and `Manifold.IsSmoothEmbedding.contMDiff_iff_comp` gives
the equivalence. The forms within a set, at a point and on a set are new here. For maps between
normed spaces and orders `n : ℕ∞` (not `ω`), Tau Ceti's `LinearIsometry.comp_contDiff_iff` gives
the analogous statement for a linear isometry with closed range.

## Main results

* `Submodule.ClosedComplemented.contMDiffWithinAt_iff_subtypeL_comp`, and its variants
  `contMDiffAt_iff_subtypeL_comp`, `contMDiffOn_iff_subtypeL_comp` and
  `contMDiff_iff_subtypeL_comp`: smoothness of a map into `p` is smoothness of its composite
  with the inclusion.
-/

public section

open Set
open scoped Manifold ContDiff

namespace Submodule.ClosedComplemented

variable {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [Ring 𝕜'] [SMul 𝕜 𝕜']
  {F : Type*} [NormedAddCommGroup F] [Module 𝕜' F] [NormedSpace 𝕜 F] [IsScalarTower 𝕜 𝕜' F]
  {p : Submodule 𝕜' F} (hp : p.ClosedComplemented)
  {E H M : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}
  {f : M → p} {s : Set M} {x : M}

include hp

/-- A map into a closed complemented submodule `p` is `C^n` within a set at a point exactly
when its composite with the inclusion of `p` is. -/
theorem contMDiffWithinAt_iff_subtypeL_comp :
    ContMDiffWithinAt I 𝓘(𝕜, p) n f s x ↔
      ContMDiffWithinAt I 𝓘(𝕜, F) n (fun y ↦ p.subtypeL (f y)) s x := by
  refine ⟨fun h ↦ (p.subtypeL.restrictScalars 𝕜).contMDiff.contMDiffAt.comp_contMDiffWithinAt x h,
    fun h ↦ ?_⟩
  obtain ⟨P, hP⟩ := hp
  have hf : (P ∘ fun y ↦ p.subtypeL (f y)) = f := funext fun y ↦ hP (f y)
  exact hf ▸ (P.restrictScalars 𝕜).contMDiff.contMDiffAt.comp_contMDiffWithinAt x h

/-- A map into a closed complemented submodule `p` is `C^n` at a point exactly when its
composite with the inclusion of `p` is. -/
theorem contMDiffAt_iff_subtypeL_comp :
    ContMDiffAt I 𝓘(𝕜, p) n f x ↔ ContMDiffAt I 𝓘(𝕜, F) n (fun y ↦ p.subtypeL (f y)) x :=
  hp.contMDiffWithinAt_iff_subtypeL_comp

/-- A map into a closed complemented submodule `p` is `C^n` on a set exactly when its composite
with the inclusion of `p` is. -/
theorem contMDiffOn_iff_subtypeL_comp :
    ContMDiffOn I 𝓘(𝕜, p) n f s ↔ ContMDiffOn I 𝓘(𝕜, F) n (fun y ↦ p.subtypeL (f y)) s :=
  forall₂_congr fun _ _ ↦ hp.contMDiffWithinAt_iff_subtypeL_comp

/-- A map into a closed complemented submodule `p` is `C^n` exactly when its composite with the
inclusion of `p` is. -/
theorem contMDiff_iff_subtypeL_comp :
    ContMDiff I 𝓘(𝕜, p) n f ↔ ContMDiff I 𝓘(𝕜, F) n (fun y ↦ p.subtypeL (f y)) := by
  obtain ⟨P, hP⟩ := hp
  exact (ContinuousLinearMap.HasLeftInverse.isSmoothEmbedding (n := n)
    (f := p.subtypeL.restrictScalars 𝕜) ⟨P.restrictScalars 𝕜, fun x ↦ hP x⟩).contMDiff_iff_comp

end Submodule.ClosedComplemented

end
