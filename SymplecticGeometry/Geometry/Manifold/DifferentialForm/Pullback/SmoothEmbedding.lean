/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.Diffeomorph

/-!
# Pullback of forms along an embedding moved by a diffeomorphism

Let `f : N → M` be a smooth embedding and `ψ : M ≃ M'` a diffeomorphism onto a manifold on
another model, so that `ψ ∘ f` is the embedding
`TauCeti.SmoothEmbedding.transDiffeomorphOfBoundaryless f ψ`. If `ψ` pulls a form `σ'` on `M'`
back to `σ`, then `ψ ∘ f` pulls `σ'` back to the pullback of `σ` along `f`
(`TauCeti.SmoothEmbedding.mpullback_transDiffeomorphOfBoundaryless`). This holds for forms of
any degree with values in any normed space; it follows from Tau Ceti's
`TauCeti.SmoothForm.mpullback_mpullback` and `TauCeti.SmoothForm.mpullback_congr`.

## Main results

* `TauCeti.SmoothEmbedding.mpullback_transDiffeomorphOfBoundaryless`: `(ψ ∘ f)^* σ' = f^* σ`
  when `ψ^* σ' = σ`.
-/

public section

open scoped Manifold ContDiff

namespace TauCeti.SmoothEmbedding

variable {E E' E'' H H' H'' N M M' F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup E''] [NormedSpace ℝ E'']
  [FiniteDimensional ℝ E''] [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H'']
  {J : ModelWithCorners ℝ E H} {I : ModelWithCorners ℝ E' H'} {I' : ModelWithCorners ℝ E'' H''}
  [J.Boundaryless] [I'.Boundaryless]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N]
  [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I ∞ M]
  [TopologicalSpace M'] [ChartedSpace H'' M'] [IsManifold I' ∞ M']
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- An embedding `f` followed by a diffeomorphism `ψ` pulls a form `σ'` back to the pull-back
along `f` of `σ = ψ^* σ'`. -/
theorem mpullback_transDiffeomorphOfBoundaryless (f : SmoothEmbedding J I ∞ N M)
    (ψ : M ≃ₘ⟮I, I'⟯ M') {σ : SmoothForm I M F k}
    {σ' : SmoothForm I' M' F k} (hψ : SmoothForm.mpullback ψ ψ.contMDiff σ' = σ) :
    SmoothForm.mpullback (f.transDiffeomorphOfBoundaryless ψ (by simp))
        (f.transDiffeomorphOfBoundaryless ψ (by simp)).contMDiff σ' =
      SmoothForm.mpullback f f.contMDiff σ := by
  rw [← hψ, SmoothForm.mpullback_mpullback]
  exact SmoothForm.mpullback_congr _ _ (coe_transDiffeomorphOfBoundaryless f ψ _) _

end TauCeti.SmoothEmbedding

end
