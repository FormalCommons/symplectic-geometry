/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Basic

/-!
# Wirtinger derivatives of `z + f z`

Adding a complex-differentiable map does not change the conjugate Wirtinger derivative
(`DifferentiableAt.conjWirtingerDeriv_add_left`); in particular `\bar∂(z + f) = \bar∂f`
(`TauCeti.conjWirtingerDeriv_id_add`), and `∂(z + f) = 1 + ∂f` for real-differentiable `f`
(`TauCeti.wirtingerDeriv_id_add`).

These declarations are a part of Tau Ceti's file
`TauCeti/Analysis/Complex/Wirtinger/Basic.lean`, on its main branch, as of the commit
`0fef288e2f0539135f050168f1153e762b0189a8` (Tau Ceti's pull request #40860), and are not yet in
the pinned release. They keep their Tau Ceti names, namespaces, statements and proofs unchanged,
so that moving Tau Ceti past them deletes this file without renames.
-/

public section

namespace TauCeti

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- Adding a complex differentiable map does not change the conjugate Wirtinger derivative:
`\bar∂(g + f) = \bar∂f`. Where `f` is not real-differentiable, neither is `g + f`, and both sides
vanish. -/
theorem _root_.DifferentiableAt.conjWirtingerDeriv_add_left {g f : V → W} {y : V}
    (hg : DifferentiableAt ℂ g y) :
    conjWirtingerDeriv (fun z ↦ g z + f z) y = conjWirtingerDeriv f y := by
  have hgR : DifferentiableAt ℝ g y := hg.restrictScalars ℝ
  by_cases hf : DifferentiableAt ℝ f y
  · exact (conjWirtingerDeriv_add hgR hf).trans (by rw [hg.conjWirtingerDeriv_eq_zero, zero_add])
  · have hf' : ¬DifferentiableAt ℝ (fun z ↦ g z + f z) y := fun h ↦
      hf (by simpa using h.fun_sub hgR)
    ext v
    simp only [conjWirtingerDeriv_apply, fderiv_zero_of_not_differentiableAt hf,
      fderiv_zero_of_not_differentiableAt hf']

/-- Adding the identity does not change the conjugate Wirtinger derivative:
`\bar∂(z + f) = \bar∂f`. -/
@[simp]
theorem conjWirtingerDeriv_id_add (f : V → V) (y : V) :
    conjWirtingerDeriv (fun z ↦ z + f z) y = conjWirtingerDeriv f y :=
  (differentiableAt_id (𝕜 := ℂ)).conjWirtingerDeriv_add_left

/-- Adding the identity adds the identity to the Wirtinger derivative of a real-differentiable
function: `∂(z + f) = 1 + ∂f`. -/
theorem wirtingerDeriv_id_add {f : V → V} {y : V} (hf : DifferentiableAt ℝ f y) :
    wirtingerDeriv (fun z ↦ z + f z) y = ContinuousLinearMap.id ℂ V + wirtingerDeriv f y :=
  (wirtingerDeriv_add differentiableAt_id hf).trans (by rw [wirtingerDeriv_id])

end TauCeti

end
