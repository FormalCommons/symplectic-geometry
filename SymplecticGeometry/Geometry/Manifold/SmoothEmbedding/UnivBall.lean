/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import TauCeti.Geometry.Manifold.Orientation.Preserving
import SymplecticGeometry.Analysis.Normed.Module.Ball.Homeomorph
import SymplecticGeometry.Geometry.Manifold.Orientation.Preserving
import TauCeti.Analysis.InnerProductSpace.Calculus
import TauCeti.Geometry.Manifold.Immersion.LocalDiffeomorph
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Geometry.Manifold.Orientation.Pullback
import TauCeti.Topology.Algebra.Module.Determinant

/-!
# Smooth embeddings precomposed with `univBall`

In an inner product space `E` over `ℝ`, Mathlib's `OpenPartialHomeomorph.univBall c ρ` maps `E`
onto the ball `ball c ρ` when `0 < ρ`, smoothly and with smooth inverse on the ball, and is a
translation when `ρ ≤ 0`. So it is a local diffeomorphism of `E`
(`OpenPartialHomeomorph.isLocalDiffeomorph_univBall`), and a smooth
embedding of an open set containing the ball, precomposed with it, is a smooth embedding of all
of `E` (`Manifold.IsSmoothEmbedding.comp_univBall`).

The first proof is that of the local diffeomorphism step inside Tau Ceti's
`TauCeti.exists_isOpenEmbedding_isLocalDiffeomorph`, stated on its own; that step assumes
`0 < ρ`, and the case `ρ ≤ 0`, where `univBall c ρ` is a translation, is added here.

For a chart `φ` of a manifold modelled on `E` whose target contains `ball c r`, the map
`φ.symm ∘ univBall c r` is an open embedding of `E` and a local diffeomorphism
(`OpenPartialHomeomorph.isOpenEmbedding_symm_comp_univBall`,
`OpenPartialHomeomorph.isLocalDiffeomorph_symm_comp_univBall`): a coordinate ball. This is the
rest of the proof of Tau Ceti's `TauCeti.exists_isOpenEmbedding_isLocalDiffeomorph`, for any chart
of the maximal atlas instead of `chartAt`. At `0`, the map `univBall c ρ` has derivative
`ρ • id`, so for `0 < ρ` it preserves every orientation of `E` there
(`OpenPartialHomeomorph.isOrientationPreservingAt_univBall`), and so at every point, since it is
a local diffeomorphism of the connected space `E`
(`OpenPartialHomeomorph.isOrientationPreservingAt_univBall_of_pos`, through Tau Ceti's
`IsPreconnected.isOrientationPreservingAt_iff`).

## Main results

* `OpenPartialHomeomorph.isLocalDiffeomorph_univBall`: `univBall c ρ` is a `C^n` local
  diffeomorphism, for `n ≤ ∞`.
* `OpenPartialHomeomorph.isOpenEmbedding_symm_comp_univBall`,
  `OpenPartialHomeomorph.isLocalDiffeomorph_symm_comp_univBall`: a chart inverse after
  `univBall c r` is a coordinate ball.
* `OpenPartialHomeomorph.isOrientationPreservingAt_univBall`: `univBall c ρ` preserves
  orientations at `0`.
* `OpenPartialHomeomorph.isOrientationPreservingAt_univBall_of_pos`: `univBall c ρ` preserves
  orientations at every point.
* `Manifold.IsSmoothEmbedding.comp_univBall`: a smooth embedding of an open set containing
  `ball c ρ`, precomposed with `univBall c ρ`, is a smooth embedding of `E`.
-/

public section

open Set Metric OpenPartialHomeomorph TauCeti
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ∞ω} {c : E} {ρ : ℝ}

namespace OpenPartialHomeomorph

/-- For `n ≤ ∞`, Mathlib's map `univBall c ρ` is a `C^n` local diffeomorphism of `E`. It maps
`E` onto the ball `ball c ρ` if `0 < ρ`, and is the translation by `c` otherwise. -/
theorem isLocalDiffeomorph_univBall (hn : n ≤ ∞) :
    IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) n (univBall c ρ) := by
  have hsymm : ContDiffOn ℝ n (univBall c ρ).symm (univBall c ρ).target := by
    by_cases hρ : 0 < ρ
    · exact univBall_target c hρ ▸ (contDiffOn_univBall_symm (n := ⊤)).of_le hn
    · have : ⇑(univBall c ρ).symm = fun x ↦ x - c := by
        ext x
        simp [univBall, hρ]
      rw [this]
      exact (contDiff_id.sub contDiff_const).contDiffOn
  let Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E n :=
    PartialDiffeomorph.ofOpenPartialHomeomorph (univBall c ρ)
      ((contDiff_univBall (n := ⊤)).of_le hn).contDiffOn hsymm
  exact fun x ↦
    isLocalDiffeomorphAt_of_eqOn (Φ := Φ) (by simp [Φ, univBall_source]) fun _ _ ↦ by simp [Φ]

section Chart

variable {N : Type*} [TopologicalSpace N] {φ : OpenPartialHomeomorph N E} {r : ℝ}

/-- A homeomorphism `φ` from an open subset of `N` onto an open subset of `E` whose target
contains the ball `ball c r`, with `0 < r`, gives an open embedding of `E` into `N`: `φ.symm`
after Mathlib's map `univBall c r` of `E` onto that ball. -/
theorem isOpenEmbedding_symm_comp_univBall (hr : 0 < r) (h : ball c r ⊆ φ.target) :
    Topology.IsOpenEmbedding (φ.symm ∘ univBall c r) := by
  have hb (v : E) : univBall c r v ∈ φ.target :=
    h (univBall_target c hr ▸ (univBall c r).map_source (by simp))
  have hψ : ((univBall c r).trans φ.symm).source = univ := by
    rw [trans_source, univBall_source, symm_source, univ_inter]
    exact eq_univ_of_forall hb
  rw [← coe_trans]
  exact ((univBall c r).trans φ.symm).isOpenEmbedding hψ

/-- For a chart `φ` of the maximal `C^n` atlas of a manifold `N` modelled on `E`, with `n ≤ ∞`,
whose target contains the ball `ball c r`, with `0 < r`, the map `φ.symm ∘ univBall c r : E → N`
is a `C^n` local diffeomorphism. -/
theorem isLocalDiffeomorph_symm_comp_univBall [ChartedSpace E N] [IsManifold 𝓘(ℝ, E) n N]
    (hn : n ≤ ∞) (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) n N) (hr : 0 < r)
    (h : ball c r ⊆ φ.target) :
    IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) n (φ.symm ∘ univBall c r) := fun v ↦
  (isLocalDiffeomorph_univBall hn v).comp (hg := φ.isLocalDiffeomorphAt_symm_of_mem_maximalAtlas hφ
    (h (univBall_target c hr ▸ (univBall c r).map_source (by simp))))

end Chart

/-- For `0 < ρ`, Mathlib's map `univBall c ρ` of a finite-dimensional `E` onto the ball
`ball c ρ` preserves every orientation of `E` at `0`: its derivative there is `ρ • id`. -/
theorem isOrientationPreservingAt_univBall [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι]
    (hρ : 0 < ρ) (o : Manifold.Orientation 𝓘(ℝ, E) E ι) :
    o.IsOrientationPreservingAt o (univBall c ρ) 0 := by
  refine Manifold.Orientation.isOrientationPreservingAt_of_det_fderiv_pos o ?_
  rw [(hasFDerivAt_univBall hρ c 0).fderiv]
  simpa using pow_pos hρ (Module.finrank ℝ E)

/-- For `0 < ρ`, Mathlib's map `univBall c ρ` of a finite-dimensional `E` onto the ball
`ball c ρ` preserves every orientation of `E` at every point `x`. -/
theorem isOrientationPreservingAt_univBall_of_pos [FiniteDimensional ℝ E] {ι : Type*}
    [Fintype ι] (hρ : 0 < ρ) (o : Manifold.Orientation 𝓘(ℝ, E) E ι) (x : E) :
    o.IsOrientationPreservingAt o (univBall c ρ) x :=
  (isPreconnected_univ.isOrientationPreservingAt_iff
    (fun z _ ↦ (isLocalDiffeomorph_univBall (n := 1) (by simp) z).contMDiffAt)
    (fun z _ ↦ (isLocalDiffeomorph_univBall (n := 1) (by simp) z).isInvertible_mfderiv
      one_ne_zero) o o (mem_univ 0) (mem_univ x)).1 (isOrientationPreservingAt_univBall hρ o)

end OpenPartialHomeomorph

namespace Manifold.IsSmoothEmbedding

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {H : Type*} [TopologicalSpace H]
  {J : ModelWithCorners ℝ F H} {N : Type*} [TopologicalSpace N] [ChartedSpace H N]

/-- Let `n ≤ ∞`. If `f` restricts to a `C^n` embedding of an open set `V` containing the ball
`ball c ρ`, with `0 < ρ`, then `f` precomposed with Mathlib's map `univBall c ρ` of `E` onto that
ball is a `C^n` embedding of `E`. -/
theorem comp_univBall {f : E → N} {V : TopologicalSpace.Opens E}
    (hf : IsSmoothEmbedding 𝓘(ℝ, E) J n (fun x : V ↦ f x)) (hρ : 0 < ρ)
    (hV : ball c ρ ⊆ V) (hn : n ≤ ∞) : IsSmoothEmbedding 𝓘(ℝ, E) J n (f ∘ univBall c ρ) := by
  have hmem (x : E) : univBall c ρ x ∈ V :=
    hV (range_univBall c hρ ▸ mem_range_self x)
  -- The same map, with values in `V`.
  let g : E → V := fun x ↦ ⟨univBall c ρ x, hmem x⟩
  have hg : IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) n g := fun x ↦
    (isLocalDiffeomorph_univBall hn x).of_comp_left (f := Subtype.val) (e := g)
      (isLocalDiffeomorph_subtype_val _) ((continuous_univBall c ρ).subtype_mk hmem).continuousAt
  have hge : Topology.IsEmbedding g := Topology.IsEmbedding.subtypeVal.of_comp_iff.1
    ((univBall c ρ).isOpenEmbedding (univBall_source c ρ)).isEmbedding
  exact isSmoothEmbedding_comp_isLocalDiffeomorph (f := fun x : V ↦ f x) hg hge hf

end Manifold.IsSmoothEmbedding

end
