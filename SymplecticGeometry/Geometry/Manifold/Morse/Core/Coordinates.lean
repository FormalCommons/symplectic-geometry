/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Topology.Algebra.Module.Equiv.Prod
import SymplecticGeometry.Geometry.Manifold.Instances.OpenBall.Reparametrization
import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.Comp
import TauCeti.Geometry.Manifold.SmoothEmbedding.Diffeomorph
import TauCeti.Geometry.Manifold.SmoothEmbedding.LocalDiffeomorph

/-!
# Cube coordinates from an open embedding near a closed ball

Write `D = (Fin m → ℝ) × (Fin k → ℝ)` with sup norms, so that `closedBall 0 1 ×ˢ {0}` is the
core cube of `D` and `sphere 0 1 ×ˢ {0}` its boundary. This file turns an open embedding that is
only defined near a closed ball times `{0}` into a smooth open embedding of the whole of `D`.

## Main results

* `SymplecticGeometry.exists_cubeChart_of_isSmoothEmbedding`: let `N` be a finite-dimensional
  real inner product space of dimension `m` and `S` a finite-dimensional real normed space of
  dimension `k`, let `V` be an open subset of `N × S` containing `closedBall 0 ρ ×ˢ {0}`, with
  `ρ > 0`, and let `Ψ : V → M` be a smooth embedding with open range. For every compact subset `K`
  of `ball 0 ρ` there is a smooth embedding `χ : D → M` with open range, with `χ 0 = Ψ 0`, which
  sends the cube into the image of `ball 0 ρ ×ˢ {0}` and its boundary into the image of
  `(ball 0 ρ \ K) ×ˢ {0}`, and whose image of the cube contains the image of `K ×ˢ {0}`.

The chart is `Ψ` composed with `ψ` and with the map `(a, b) ↦ (ρ • a, e b)`, where `ψ` is
the reparametrization `SymplecticGeometry.exists_isSmoothEmbedding_prod_range_eq_ball_prod_ball`
of `D` onto the open unit ball of `N` times a small box, chosen so that the image of the open cube
contains `ρ⁻¹ • K`, and `e : (Fin k → ℝ) ≃L[ℝ] S` is a linear isomorphism. The box is small enough
that the image lies in `V`, by the tube lemma (`generalized_tube_lemma`). A point of the boundary
of the cube is not sent into the image of `K`, since `ψ` is injective and already reaches
`ρ⁻¹ • K` from the open cube.

The balls of `N` are those of its inner product norm, while the cube of `D` is that of the sup
norm. This is the form in which the cube of a critical point of a Morse function is read off its
unstable disc, `N` being the Euclidean space of the coordinates of negative weight of a Morse chart.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Part I, §3.
-/

public section

open Function Manifold Metric Set Topology
open scoped ContDiff Pointwise

namespace SymplecticGeometry

variable {N S E H M : Type*}
  [NormedAddCommGroup N] [InnerProductSpace ℝ N] [FiniteDimensional ℝ N]
  [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Cube coordinates from an open embedding near a closed ball.** Let `N` be a
finite-dimensional real inner product space of dimension `m`, `S` a finite-dimensional real
normed space of dimension `k`, `V` an open subset of `N × S` containing `closedBall 0 ρ ×ˢ {0}`
with `ρ > 0`, and `Ψ : V → M` a smooth embedding with open range into a boundaryless manifold.
For every compact subset `K` of `ball 0 ρ` there is a smooth embedding
`χ : (Fin m → ℝ) × (Fin k → ℝ) → M` (sup norms) with open range such that `χ 0 = Ψ 0`, `χ` maps
`closedBall 0 1 ×ˢ {0}` into the image under `Ψ` of `ball 0 ρ ×ˢ {0}` and `sphere 0 1 ×ˢ {0}`
into the image of `(ball 0 ρ \ K) ×ˢ {0}`, and the image of `K ×ˢ {0}` under `Ψ` lies in the
image of `closedBall 0 1 ×ˢ {0}` under `χ`. -/
theorem exists_cubeChart_of_isSmoothEmbedding {m k : ℕ} (hm : Module.finrank ℝ N = m)
    (hk : Module.finrank ℝ S = k) {V : TopologicalSpace.Opens (N × S)} {Ψ : V → M}
    (hΨ : IsSmoothEmbedding 𝓘(ℝ, N × S) I ∞ Ψ) (hΨo : IsOpen (range Ψ)) {ρ : ℝ} (hρ : 0 < ρ)
    (hV : closedBall (0 : N) ρ ×ˢ ({0} : Set S) ⊆ V) {K : Set N} (hK : IsCompact K)
    (hKρ : K ⊆ ball 0 ρ) :
    ∃ χ : (Fin m → ℝ) × (Fin k → ℝ) → M,
      IsSmoothEmbedding 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ)) I ∞ χ ∧ IsOpen (range χ) ∧
      χ 0 = Ψ ⟨0, hV ⟨mem_closedBall_self hρ.le, rfl⟩⟩ ∧
      MapsTo χ (closedBall 0 1 ×ˢ {0}) (Ψ '' (Subtype.val ⁻¹' (ball 0 ρ ×ˢ {0}))) ∧
      MapsTo χ (sphere 0 1 ×ˢ {0}) (Ψ '' (Subtype.val ⁻¹' ((ball 0 ρ \ K) ×ˢ {0}))) ∧
      Ψ '' (Subtype.val ⁻¹' (K ×ˢ {0})) ⊆ χ '' (closedBall 0 1 ×ˢ {0}) := by
  -- A box `ball 0 δ` of `Fin k → ℝ` whose image under `e` keeps the closed ball inside `V`.
  let e : (Fin k → ℝ) ≃L[ℝ] S := ContinuousLinearEquiv.ofFinrankEq (by simp [hk])
  obtain ⟨u, v, -, hv, hu, h0v, huv⟩ := generalized_tube_lemma (isCompact_closedBall 0 ρ)
    isCompact_singleton V.isOpen hV
  obtain ⟨δ, hδ, hδv⟩ := Metric.mem_nhds_iff.1
    (e.continuous.continuousAt.preimage_mem_nhds (hv.mem_nhds (by simpa using h0v)) :
      e ⁻¹' v ∈ nhds (0 : Fin k → ℝ))
  -- The reparametrization of `D` onto the unit ball of `N` times the box, reaching `ρ⁻¹ • K`.
  have hKρ' : ρ⁻¹ • K ⊆ ball 0 1 := by
    rintro _ ⟨x, hx, rfl⟩
    have hx := mem_ball_zero_iff.1 (hKρ hx)
    rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hρ.le),
      inv_mul_lt_one₀ hρ]
    exact hx
  obtain ⟨ψ, hψ, hψr, hψ0, hψ2, hψK⟩ :=
    exists_isSmoothEmbedding_prod_range_eq_ball_prod_ball (ι := Fin k) (V := Fin m → ℝ)
      (by simp [hm]) (hK.smul ρ⁻¹) hKρ' hδ
  let L : (N × (Fin k → ℝ)) ≃L[ℝ] (N × S) :=
    (ContinuousLinearEquiv.smulLeft (Units.mk0 ρ hρ.ne')).prodCongr e
  have hL (q : N × (Fin k → ℝ)) : L q = (ρ • q.1, e q.2) := by
    simp [L, Units.smul_def]
  have hLV (x : (Fin m → ℝ) × (Fin k → ℝ)) : L (ψ x) ∈ V := by
    obtain ⟨h1, h2⟩ : ψ x ∈ ball 0 1 ×ˢ ball 0 δ := hψr ▸ mem_range_self x
    rw [hL]
    refine huv ⟨hu (mem_closedBall_zero_iff.2 ?_), hδv h2⟩
    rw [norm_smul, Real.norm_of_nonneg hρ.le]
    nlinarith [mem_ball_zero_iff.1 h1, norm_nonneg (ψ x).1]
  have hj : IsSmoothEmbedding 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ)) 𝓘(ℝ, N × S) ∞ (L ∘ ψ) :=
    (TauCeti.isSmoothEmbedding_continuousLinearEquiv L).comp_of_boundaryless hψ (by simp)
  let j : (Fin m → ℝ) × (Fin k → ℝ) → V := fun x ↦ ⟨L (ψ x), hLV x⟩
  have hjv (x : (Fin m → ℝ) × (Fin k → ℝ)) : (j x : N × S) = (ρ • (ψ x).1, e (ψ x).2) :=
    hL (ψ x)
  -- The points `(x, 0)` go to `(ρ • (ψ (x, 0)).1, 0)`.
  have hj0 (x : Fin m → ℝ) : (j (x, 0) : N × S) = (ρ • (ψ (x, 0)).1, 0) := by
    rw [hjv, hψ2, map_zero]
  refine ⟨Ψ ∘ j, hΨ.comp_of_boundaryless (hj.codRestrict V hLV) (by simp), ?_, ?_, ?_, ?_, ?_⟩
  · -- `Ψ` is an open embedding, and the range of `j` is open in `V`.
    rw [range_comp]
    refine (IsOpenEmbedding.isOpenMap ⟨hΨ.isEmbedding, hΨo⟩) _ ?_
    have hr : range j = Subtype.val ⁻¹' (L '' (ball 0 1 ×ˢ ball 0 δ)) := by
      ext q
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨ψ x, hψr ▸ mem_range_self x, rfl⟩
      · rintro ⟨y, hy, hLy⟩
        rw [← hψr] at hy
        obtain ⟨x, rfl⟩ := hy
        exact ⟨x, Subtype.ext hLy⟩
    rw [hr]
    exact (L.toHomeomorph.isOpenMap _ (isOpen_ball.prod isOpen_ball)).preimage
      continuous_subtypeVal
  · simp only [comp_apply]
    congr 1
    exact Subtype.ext (by rw [hjv, hψ0]; simp)
  · rintro ⟨x, _⟩ ⟨-, rfl⟩
    obtain ⟨h1, -⟩ : ψ (x, 0) ∈ ball 0 1 ×ˢ ball 0 δ := hψr ▸ mem_range_self _
    refine ⟨j (x, 0), ?_, rfl⟩
    rw [mem_preimage, hj0]
    refine ⟨mem_ball_zero_iff.2 ?_, rfl⟩
    rw [norm_smul, Real.norm_of_nonneg hρ.le]
    nlinarith [mem_ball_zero_iff.1 h1, norm_nonneg (ψ (x, 0)).1]
  · rintro ⟨x, _⟩ ⟨hx, rfl⟩
    obtain ⟨h1, -⟩ : ψ (x, 0) ∈ ball 0 1 ×ˢ ball 0 δ := hψr ▸ mem_range_self _
    refine ⟨j (x, 0), ?_, rfl⟩
    rw [mem_preimage, hj0]
    refine ⟨⟨mem_ball_zero_iff.2 ?_, fun hK' ↦ ?_⟩, rfl⟩
    · rw [norm_smul, Real.norm_of_nonneg hρ.le]
      nlinarith [mem_ball_zero_iff.1 h1, norm_nonneg (ψ (x, 0)).1]
    · -- Otherwise `ψ (x, 0)` is also `ψ (x', 0)` for some `x'` in the open cube.
      have hmem : ((ψ (x, 0)).1, (0 : Fin k → ℝ)) ∈ (ρ⁻¹ • K) ×ˢ ({0} : Set (Fin k → ℝ)) :=
        ⟨(mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero hρ.ne') _ _).2 (by rwa [inv_inv]), rfl⟩
      obtain ⟨⟨x', _⟩, ⟨hx', rfl⟩, hψx'⟩ := hψK hmem
      have hxx' : ψ (x', 0) = ψ (x, 0) := hψx'.trans (Prod.ext rfl (hψ2 x).symm)
      obtain rfl := congrArg Prod.fst (hψ.isEmbedding.injective hxx')
      exact (ne_of_lt (mem_ball_zero_iff.1 hx')) (mem_sphere_zero_iff_norm.1 hx)
  · rintro _ ⟨⟨⟨c, _⟩, _⟩, ⟨hc, rfl⟩, rfl⟩
    have hmem : (ρ⁻¹ • c, (0 : Fin k → ℝ)) ∈ (ρ⁻¹ • K) ×ˢ ({0} : Set (Fin k → ℝ)) :=
      ⟨smul_mem_smul_set hc, rfl⟩
    obtain ⟨⟨x, _⟩, ⟨hx, rfl⟩, hψx⟩ := hψK hmem
    refine ⟨(x, 0), ⟨ball_subset_closedBall hx, rfl⟩, ?_⟩
    simp only [comp_apply]
    congr 1
    exact Subtype.ext (by rw [hj0, hψx, smul_inv_smul₀ hρ.ne'])

end SymplecticGeometry

end
