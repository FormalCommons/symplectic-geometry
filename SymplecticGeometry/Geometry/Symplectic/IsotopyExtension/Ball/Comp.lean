/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.IsotopyExtension.Ball.Basic
public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Basic

/-!
# Composing a symplectic ball embedding with a symplectic map

If `j` is a symplectic embedding of the closed ball `B(r)` into `(M, σ)` and `f : M → N` is a
smooth injective map with `f^* τ = σ`, then `f ∘ j` is a symplectic embedding of `B(r)` into
`(N, τ)`. In particular every slice `Φ_s` of a diffeotopy of `M` whose slices preserve `σ`, such
as a compactly supported Hamiltonian diffeotopy, carries symplectic ball embeddings to symplectic
ball embeddings. This is a step of the proof of McDuff–Salamon, Proposition 7.1.22 (second part),
where the diffeotopy moreover fixes every point outside a compact subset of the open ball, so that
its slices map `B(r)` onto itself (Mathlib's `Set.image_perm`, applied to the slice as an
equivalence).

## Main results

* `SymplecticGeometry.IsSymplecticBallEmbedding.comp`: `f ∘ j` is a symplectic ball embedding
  for a smooth injective `f` with `f^* τ = σ`.
* `SymplecticGeometry.IsSymplecticBallEmbedding.diffeotopy_comp`: `z ↦ Φ (s, j z)` is a
  symplectic ball embedding when the slice `Φ_s` preserves `σ`.
* `TauCeti.SymplecticForm.IsSymplectomorphism.isSymplecticBallEmbedding`: a continuous linear
  equivalence `e : StdSpace (Fin n) ≃L[ℝ] W` that pulls a symplectic form `σ` on `W` back to the
  standard form is a symplectic embedding of every closed ball for the constant form of `σ`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Proposition 7.1.22.
-/

public section

open Function Metric
open scoped ContDiff Manifold

namespace SymplecticGeometry

open TauCeti

variable {E H M E' H' N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' ∞ N]
  {n : ℕ} {σ : SmoothTwoForm I M} {r : ℝ} {j : StdSpace (Fin n) → M}

/-- If `j` is a symplectic embedding of `B(r)` into `(M, σ)` and `f : M → N` is smooth,
injective and pulls `τ` back to `σ`, then `f ∘ j` is a symplectic embedding of `B(r)` into
`(N, τ)`. -/
theorem IsSymplecticBallEmbedding.comp (hj : IsSymplecticBallEmbedding σ r j)
    {τ : SmoothTwoForm I' N} {f : M → N} (hf : ContMDiff I I' ∞ f) (hfi : Injective f)
    (hfτ : mpullback I I' f τ.val = σ.val) : IsSymplecticBallEmbedding τ r (f ∘ j) := by
  obtain ⟨U, hU, hrU, hjU⟩ := hj.exists_contMDiffOn
  refine (isSymplecticBallEmbedding_def _ _ _).2
    ⟨⟨U, hU, hrU, hf.comp_contMDiffOn hjU⟩, hfi.comp_injOn hj.injOn, fun z hz ↦ ?_⟩
  have hjz : MDifferentiableAt 𝓘(ℝ, StdSpace (Fin n)) I j z :=
    (hjU.contMDiffAt (hU.mem_nhds (hrU (ball_subset_closedBall hz)))).mdifferentiableAt
      (by simp)
  rw [mpullback_comp_at hjz (hf.mdifferentiableAt (by simp)), hfτ]
  exact hj.mpullback_eq hz

/-- If `j` is a symplectic embedding of `B(r)` into `(M, σ)` and the slice `Φ_s` of a diffeotopy
`Φ` of `M` preserves `σ`, then `z ↦ Φ (s, j z)` is a symplectic embedding of `B(r)`. Every slice
of a compactly supported Hamiltonian diffeotopy preserves `σ`
(`TauCeti.Diffeotopy.IsCompactlySupportedHamiltonian`). -/
theorem IsSymplecticBallEmbedding.diffeotopy_comp (hj : IsSymplecticBallEmbedding σ r j)
    {Φ : Diffeotopy I ∞ M} {s : unitInterval}
    (hΦ : Φ.timeSlice s ∈ SmoothForm.diffeomorphStabilizer σ) :
    IsSymplecticBallEmbedding σ r fun z ↦ Φ (s, j z) := by
  have h := hj.comp (Φ.timeSlice s).contMDiff (Φ.timeSlice s).injective
    (by rw [← SmoothForm.coe_mpullback _ (Φ.timeSlice s).contMDiff,
      SmoothForm.mem_diffeomorphStabilizer.1 hΦ])
  simpa only [comp_def, Diffeotopy.timeSlice_apply] using h

/-- A continuous linear equivalence `e : StdSpace (Fin n) ≃L[ℝ] W` that pulls a symplectic form
`σ` on `W` back to the standard form is a symplectic embedding of the closed ball `B(r)` into `W`
with the constant form of `σ`, for every radius `r`. -/
theorem _root_.TauCeti.SymplecticForm.IsSymplectomorphism.isSymplecticBallEmbedding
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    {σ : SymplecticForm W} {e : StdSpace (Fin n) ≃L[ℝ] W}
    (he : (stdForm (Fin n)).IsSymplectomorphism σ e.toLinearEquiv) (r : ℝ) :
    IsSymplecticBallEmbedding σ.constSmooth r e :=
  (isSymplecticBallEmbedding_id r).comp e.contDiff.contMDiff e.injective
    (by
      rw [← he.mpullback_constSmooth (e := e), SmoothForm.coe_mpullback,
        ContinuousLinearEquiv.coe_toDiffeomorph])

end SymplecticGeometry

end
