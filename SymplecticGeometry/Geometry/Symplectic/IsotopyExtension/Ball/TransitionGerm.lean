/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.IsotopyExtension.Ball.Basic
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.Parametric

/-!
# Transition germs of a family of symplectic ball embeddings with a fixed centre

Let `ψ` be a smooth family over `[0, 1]` of symplectic embeddings of the closed ball `B(r)`,
`0 < r`, of `StdSpace (Fin n)` into a manifold `(M, σ)` of the same dimension, all with the same
centre `ψ (t, 0) = ψ (0, 0)`. Then near `0` the transition maps `κ_t = ψ_t⁻¹ ∘ ψ_0` form a
smooth family of symplectic embeddings of a small ball `B(δ)` of `StdSpace (Fin n)` into itself,
with `ω₀` on both sides (`SymplecticGeometry.IsSymplecticBallFamily.exists_transitionGerm`).

The family `κ` is the jointly smooth inverse of
`SymplecticGeometry.exists_contMDiffOn_apply_eq_apply_zero`, applied on the open ball `ball 0 r`,
where every slice of `ψ` is injective and an immersion. On the open set `V` where `κ` is defined,
`ψ_t ∘ κ_t = ψ_0`, so by the chain rule `mpullback_comp_at` the form `κ_t^* ω₀ = κ_t^* ψ_t^* σ` is
`ψ_0^* σ = ω₀`. Each `κ_t` is injective on `V` since `ψ_0` is, and
`SymplecticGeometry.exists_lt_isSymplecticBallFamily_of_injOn` makes `κ` a family of symplectic
ball embeddings.

## Main results

* `SymplecticGeometry.IsSymplecticBallFamily.exists_transitionGerm`: the transition germs
  `ψ_t⁻¹ ∘ ψ_0` near the common centre form a smooth family of symplectic ball embeddings.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Proposition 7.1.22 (second part).
-/

public section

open Set Filter Metric
open scoped ContDiff Manifold Topology

namespace SymplecticGeometry

open TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {n : ℕ} {σ : SmoothTwoForm I M}

/-- **Transition germs of a family of symplectic ball embeddings with a fixed centre.** Let `ψ`
satisfy `IsSymplecticBallFamily σ r ψ` with `0 < r`, into a manifold whose model has
the dimension of `StdSpace (Fin n)`, with `ψ (t, 0) = ψ (0, 0)` for every `t`. Then for every
`ε > 0` there are `0 < δ ≤ ε` and a smooth family `κ` of symplectic embeddings of `B(δ)` into
`StdSpace (Fin n)` with `ω₀`, such that `κ (t, 0) = 0`, `κ (0, z) = z` on `B(δ)`, and
`ψ (t, κ (t, z)) = ψ (0, z)` on `B(δ)`; moreover `κ (t, z) = z` at each `z ∈ B(δ)` with
`ψ (t, z) = ψ (0, z)`. So `κ_t` is the germ of `ψ_t⁻¹ ∘ ψ_0` at `0`. -/
theorem IsSymplecticBallFamily.exists_transitionGerm {r : ℝ}
    {ψ : unitInterval × StdSpace (Fin n) → M}
    (hdim : Module.finrank ℝ (StdSpace (Fin n)) = Module.finrank ℝ E) (hr : 0 < r)
    (hψ : IsSymplecticBallFamily σ r ψ) (hfix : ∀ t, ψ (t, 0) = ψ (0, 0)) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ δ, 0 < δ ∧ δ ≤ ε ∧ ∃ κ : unitInterval × StdSpace (Fin n) → StdSpace (Fin n),
      IsSymplecticBallFamily (stdForm (Fin n)).constSmooth δ κ ∧
      (∀ t, κ (t, 0) = 0) ∧ (∀ z ∈ closedBall 0 δ, κ (0, z) = z) ∧
      (∀ t, ∀ z ∈ closedBall 0 δ, ψ (t, κ (t, z)) = ψ (0, z)) ∧
      ∀ t, ∀ z ∈ closedBall 0 δ, ψ (t, z) = ψ (0, z) → κ (t, z) = z := by
  obtain ⟨W, hWo, hrW, hψW⟩ := hψ.exists_contMDiffOn
  have hBW : ball (0 : StdSpace (Fin n)) r ⊆ W := ball_subset_closedBall.trans hrW
  have h0 : (0 : StdSpace (Fin n)) ∈ closedBall 0 r := mem_closedBall_self hr.le
  obtain ⟨δ, hδ, hδε, V, hVo, hVB, hδV, κ, hκ, hκV⟩ :=
    exists_contMDiffOn_apply_eq_apply_zero hdim isOpen_ball (mem_ball_self hr)
      (hψW.mono (prod_mono subset_rfl hBW))
      (fun t ↦ (hψ.isSymplecticBallEmbedding t).injOn.mono ball_subset_closedBall)
      (fun t ↦ (hψ.isSymplecticBallEmbedding t).injective_mfderiv hr h0) hfix hε
  have hδ0 : (0 : StdSpace (Fin n)) ∈ closedBall 0 δ := mem_closedBall_self hδ.le
  -- Each `κ_t` pulls `ω₀` back to itself on `V`.
  have hpull (t : unitInterval) (z : StdSpace (Fin n)) (hz : z ∈ V) :
      mpullback 𝓘(ℝ, StdSpace (Fin n)) 𝓘(ℝ, StdSpace (Fin n)) (fun z ↦ κ (t, z))
        (stdForm (Fin n)).constSmooth.val z = (stdForm (Fin n)).constSmooth.val z := by
    obtain ⟨hκB, -, -⟩ := hκV t z hz
    have hκz : MDifferentiableAt 𝓘(ℝ, StdSpace (Fin n)) 𝓘(ℝ, StdSpace (Fin n))
        (fun z ↦ κ (t, z)) z :=
      ((hκ.comp (contMDiffOn_const.prodMk contMDiffOn_id) fun _ hy ↦ ⟨mem_univ _, hy⟩).contMDiffAt
        (hVo.mem_nhds hz)).mdifferentiableAt (by simp)
    have hψz : MDifferentiableAt 𝓘(ℝ, StdSpace (Fin n)) I (fun y ↦ ψ (t, y)) (κ (t, z)) :=
      ((hψW.comp (contMDiffOn_const.prodMk contMDiffOn_id) fun _ hy ↦ ⟨mem_univ _, hy⟩).contMDiffAt
        (hWo.mem_nhds (hBW hκB))).mdifferentiableAt (by simp)
    have hcomp : (fun y ↦ ψ (t, y)) ∘ (fun y ↦ κ (t, y)) =ᶠ[𝓝 z] fun y ↦ ψ (0, y) :=
      eventually_of_mem (hVo.mem_nhds hz) fun y hy ↦ (hκV t y hy).2.1
    rw [← mpullback_apply_congr (f := fun y ↦ κ (t, y))
        ((hψ.isSymplecticBallEmbedding t).mpullback_eq hκB),
      ← mpullback_comp_at hκz hψz, hcomp.mpullback_eq,
      (hψ.isSymplecticBallEmbedding 0).mpullback_eq (hVB hz)]
  -- Each `κ_t` is injective on `V`, since `ψ_t ∘ κ_t = ψ_0` there.
  have hinj (t : unitInterval) : InjOn (fun z ↦ κ (t, z)) (closedBall 0 δ) := fun x hx y hy h ↦
    (hψ.isSymplecticBallEmbedding 0).injOn (ball_subset_closedBall (hVB (hδV hx)))
      (ball_subset_closedBall (hVB (hδV hy))) <| by
        simp only at h ⊢
        rw [← (hκV t x (hδV hx)).2.1, ← (hκV t y (hδV hy)).2.1, h]
  obtain ⟨δ', hδδ', hκe⟩ := exists_lt_isSymplecticBallFamily_of_injOn hVo hδV hκ hinj hpull
  refine ⟨δ, hδ, hδε, κ, hκe.mono hδδ'.le,
    fun t ↦ (hκV t 0 (hδV hδ0)).2.2 (hfix t), fun z hz ↦ (hκV 0 z (hδV hz)).2.2 rfl,
    fun t z hz ↦ (hκV t z (hδV hz)).2.1, fun t z hz ↦ (hκV t z (hδV hz)).2.2⟩

end SymplecticGeometry

end
