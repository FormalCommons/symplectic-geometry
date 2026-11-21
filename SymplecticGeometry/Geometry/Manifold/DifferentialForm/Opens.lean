/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Opens
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth

/-!
# Pull-back of restricted forms along a partial diffeomorphism of open subsets

Let `Φ` be a partial diffeomorphism from an open subset `U` of `M` to an open subset `V` of `M'`.
Tau Ceti reads `Φ` in the ambient manifolds as `PartialDiffeomorph.liftOpens`, and a partial
diffeomorphism as a diffeomorphism between its source and its target as
`PartialDiffeomorph.toDiffeomorphSourceTarget`. Composing the two gives a diffeomorphism `φ`
between open subsets of `M` and `M'`.

This file shows that an identity `Φ^* (σ|_V) = τ|_U` between forms, known at the points of the
source of `Φ`, becomes the identity `φ^* (σ|_{target}) = τ|_{source}` between the smooth forms
restricted to the source and the target of `φ`
(`PartialDiffeomorph.mpullback_toDiffeomorphSourceTarget_liftOpens`). This is how a construction
carried out on an open submanifold, such as a Moser flow defined only on part of a tube, gives a
diffeomorphism of open subsets of the ambient manifold that pulls one form back to another.

The proof combines Tau Ceti's `TauCeti.mpullback_liftOpens_apply_coe` with the functoriality of
pull-backs at a point (`TauCeti.mpullback_comp_at`). The relative Moser theorem
`TauCeti.SmoothEmbedding.exists_diffeomorph_opens_of_eq_along` uses it.

## Main results

* `PartialDiffeomorph.mpullback_toDiffeomorphSourceTarget_liftOpens`: the pull-back of a
  restricted form along `(Φ.liftOpens hU hV).toDiffeomorphSourceTarget`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2013, Chapter 14.
-/

public section

open TopologicalSpace
open scoped Manifold ContDiff

namespace PartialDiffeomorph

variable {E H M E' H' M' F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- Let `Φ` be a partial diffeomorphism from an open subset `U` of `M` to an open subset `V` of
`M'`, and let `φ` be its reading in the ambient manifolds as a diffeomorphism between its source
and its target. If, at every point of the source of `Φ`, `Φ` pulls the restriction of a form `σ`
on `M'` to `V` back to the value of a form `τ` on `M`, then `φ` pulls the restriction of `σ` to
the target of `φ` back to the restriction of `τ` to the source of `φ`. -/
theorem mpullback_toDiffeomorphSourceTarget_liftOpens {U : Opens M} {V : Opens M'}
    (Φ : PartialDiffeomorph I I' U V ∞) (hU : Nonempty U) (hV : Nonempty V)
    {σ : TauCeti.SmoothForm I' M' F k} {τ : TauCeti.SmoothForm I M F k}
    (h : ∀ x ∈ Φ.source, TauCeti.mpullback I I' Φ
      (TauCeti.mpullback I' I' (Subtype.val : V → M') σ.val) x = τ.val x) :
    TauCeti.SmoothForm.mpullback (Φ.liftOpens hU hV).toDiffeomorphSourceTarget
        (Φ.liftOpens hU hV).toDiffeomorphSourceTarget.contMDiff
        (TauCeti.SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ) =
      TauCeti.SmoothForm.mpullback Subtype.val contMDiff_subtypeVal τ := by
  set Ψ := Φ.liftOpens hU hV
  set φ := Ψ.toDiffeomorphSourceTarget
  have hφΨ : Subtype.val ∘ ⇑φ = ⇑Ψ ∘ Subtype.val := funext Ψ.toDiffeomorphSourceTarget_apply_coe
  -- At a point `z` of the source of `Ψ`, `φ^* σ` is `Φ^* σ` at the point of `U` that `z` is.
  apply Subtype.ext
  funext z
  obtain ⟨y, hy, hyz⟩ : (z : M) ∈ Subtype.val '' Φ.source :=
    Φ.liftOpens_source hU hV ▸ z.property
  have hφz : MDifferentiableAt I I' φ z := φ.contMDiff.mdifferentiableAt (by simp)
  have hΨz : MDifferentiableAt I I' Ψ z := Ψ.mdifferentiableAt (by simp) z.property
  have hval {N : Opens M'} (x : N) : MDifferentiableAt I' I' (Subtype.val : N → M') x :=
    (contMDiff_subtypeVal (n := 1)).mdifferentiableAt one_ne_zero
  rw [TauCeti.SmoothForm.coe_mpullback_subtype_val_apply τ z, TauCeti.SmoothForm.coe_mpullback,
    TauCeti.SmoothForm.coe_mpullback, ← TauCeti.mpullback_comp_at hφz (hval _), hφΨ,
    TauCeti.mpullback_comp_at ((contMDiff_subtypeVal (n := 1)).mdifferentiableAt one_ne_zero)
      hΨz, TauCeti.mpullback_subtype_val_apply, ← hyz,
    TauCeti.mpullback_liftOpens_apply_coe Φ (by simp) hU hV _ hy, h y hy]

end PartialDiffeomorph

end
