/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Geometry.Manifold.SmoothEmbedding
import TauCeti.Geometry.Manifold.Immersion.LocalDiffeomorph
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset

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

## Main results

* `OpenPartialHomeomorph.univBall_mem_ball`: for `0 < ρ`, `univBall c ρ` maps into `ball c ρ`.
* `OpenPartialHomeomorph.isLocalDiffeomorph_univBall`: `univBall c ρ` is a `C^n` local
  diffeomorphism, for `n ≤ ∞`.
* `Manifold.IsSmoothEmbedding.comp_univBall`: a smooth embedding of an open set containing
  `ball c ρ`, precomposed with `univBall c ρ`, is a smooth embedding of `E`.
-/

public section

open Set Metric OpenPartialHomeomorph TauCeti
open scoped Manifold ContDiff

namespace OpenPartialHomeomorph

/-- For `0 < ρ`, Mathlib's map `univBall c ρ` takes its values in the ball `ball c ρ`. -/
theorem univBall_mem_ball {E P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [PseudoMetricSpace P] [NormedAddTorsor E P] {c : P} {ρ : ℝ} (hρ : 0 < ρ) (x : E) :
    univBall c ρ x ∈ ball c ρ :=
  univBall_target c hρ ▸ (univBall c ρ).map_source (by simp [univBall_source])

end OpenPartialHomeomorph

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
    hV (univBall_mem_ball hρ x)
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
