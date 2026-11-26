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

* `OpenPartialHomeomorph.range_univBall`: the range of `univBall c r` is `ball c r`, for `0 < r`.
* `OpenPartialHomeomorph.strictMono_univBall_real`, `tendsto_univBall_real_atBot` and
  `image_univBall_real_Iic`: on the real line, `univBall c r` is increasing, tends to `c - r` at
  `-∞`, and sends `Iic T` onto `Ioc (c - r) (univBall c r T)`, for `0 < r`.
* `OpenPartialHomeomorph.isLocalDiffeomorph_univBall`: `univBall c ρ` is a `C^n` local
  diffeomorphism, for `n ≤ ∞`.
* `Manifold.IsSmoothEmbedding.comp_univBall`: a smooth embedding of an open set containing
  `ball c ρ`, precomposed with `univBall c ρ`, is a smooth embedding of `E`.
-/

public section

open Set Metric OpenPartialHomeomorph TauCeti
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ∞ω} {c : E} {ρ : ℝ}

namespace OpenPartialHomeomorph

section Range

variable {P : Type*} [PseudoMetricSpace P] [NormedAddTorsor E P]

/-- For `0 < r`, Mathlib's map `univBall c r : E → P` has as range the ball `ball c r`. -/
theorem range_univBall (c : P) {r : ℝ} (hr : 0 < r) :
    range (univBall (E := E) c r) = ball c r := by
  rw [← univBall_target c hr, ← image_univ, ← univBall_source c r,
    (univBall c r).image_source_eq_target]

end Range

section Real

open Filter Topology

variable {r : ℝ}

/-- On the real line, for `0 < r`, Mathlib's map `univBall c r` is
`x ↦ c + r * (x / √(1 + x ^ 2))`. -/
theorem univBall_real_apply (c : ℝ) (hr : 0 < r) (x : ℝ) :
    univBall c r x = c + r * (x / √(1 + x ^ 2)) := by
  simp [univBall, hr, unitBallBall, univUnitBall_apply]
  ring

/-- On the real line, for `0 < r`, Mathlib's map `univBall c r` is strictly increasing. -/
theorem strictMono_univBall_real (c : ℝ) (hr : 0 < r) : StrictMono (univBall c r) := by
  refine ((continuous_univBall c r).strictMono_of_inj
    fun x y h ↦ (univBall c r).injOn (by simp) (by simp) h).resolve_right fun h ↦ ?_
  have h1 := h zero_lt_one
  rw [univBall_real_apply c hr, univBall_real_apply c hr, zero_div, mul_zero, add_zero] at h1
  have : 0 < r * (1 / √(1 + 1 ^ 2)) := by positivity
  linarith

/-- On the real line, for `0 < r`, Mathlib's map `univBall c r` tends to the left end `c - r` of
its range at `-∞`. -/
theorem tendsto_univBall_real_atBot (c : ℝ) (hr : 0 < r) :
    Tendsto (univBall c r) atBot (𝓝 (c - r)) := by
  have hrange : range (univBall c r) = Ioo (c - r) (c + r) := by
    rw [range_univBall c hr, Real.ball_eq_Ioo]
  have := tendsto_atBot_ciInf (strictMono_univBall_real c hr).monotone
    (hrange ▸ bddBelow_Ioo)
  rwa [iInf, hrange, csInf_Ioo (by linarith)] at this

/-- On the real line, for `0 < r`, Mathlib's map `univBall c r` sends the half-line `Iic T` onto
the interval `Ioc (c - r) (univBall c r T)`. -/
theorem image_univBall_real_Iic (c : ℝ) (hr : 0 < r) (T : ℝ) :
    univBall c r '' Iic T = Ioc (c - r) (univBall c r T) := by
  have hmono := strictMono_univBall_real c hr
  have hrange : range (univBall c r) = Ioo (c - r) (c + r) := by
    rw [range_univBall c hr, Real.ball_eq_Ioo]
  refine Subset.antisymm ?_ fun y hy ↦ ?_
  · rintro _ ⟨t, ht, rfl⟩
    exact ⟨(hrange.subset (mem_range_self t)).1, hmono.monotone ht⟩
  · obtain ⟨t₀, ht₀T, ht₀⟩ := ((eventually_le_atBot T).and
      ((tendsto_univBall_real_atBot c hr).eventually (eventually_lt_nhds hy.1))).exists
    obtain ⟨t, ht, rfl⟩ := intermediate_value_Icc ht₀T (continuous_univBall c r).continuousOn
      ⟨ht₀.le, hy.2⟩
    exact ⟨t, ht.2, rfl⟩

end Real

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
