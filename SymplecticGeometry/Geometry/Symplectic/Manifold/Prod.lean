/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.Prod
public import Mathlib.Geometry.Manifold.Algebra.SMul

/-!
# Invariance of the product form under a diagonal action

For two-forms `σ` on `M` and `τ` on `N` and an element `g` of a monoid acting smoothly on both,
`TauCeti.SmoothTwoForm.mpullback_smul_prod` says that if `g` preserves `σ` and `τ`, it preserves
the product form `σ.prod τ` for the diagonal action on `M × N`. This is the naturality of the
product form, `TauCeti.SmoothTwoForm.mpullback_prodMap_prod`, for the product map `g × g`, which is
the diagonal action of `g`. The proof is the one of the field `mpullback_smul` in Tau Ceti's
`TauCeti.SmoothTwoForm.HamiltonianTorusData.prod`
(`TauCeti/Geometry/Symplectic/Hamiltonian/EquivariantMomentMap/Torus.lean`), for any monoid in
place of a torus.
-/

public section

open scoped Manifold ContDiff

namespace TauCeti.SmoothTwoForm

variable {EG HG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [TopologicalSpace HG]
  {IG : ModelWithCorners ℝ EG HG} {G : Type*} [TopologicalSpace G] [ChartedSpace HG G] [Monoid G]
  {E H M F H' N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  [MulAction G M] [MulAction G N] [ContMDiffSMul IG I ∞ G M] [ContMDiffSMul IG J ∞ G N]

/-- **The diagonal action preserves the product form.** If `g` preserves the two-forms `σ` on `M`
and `τ` on `N`, it preserves the product form `σ.prod τ` on `M × N` for the diagonal action. -/
theorem mpullback_smul_prod {σ : SmoothTwoForm I M} {τ : SmoothTwoForm J N} (g : G)
    (hσ : SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := IG) g) σ = σ)
    (hτ : SmoothForm.mpullback (fun y : N ↦ g • y)
      (ContMDiffSMul.contMDiff_const_smul (I := IG) g) τ = τ) :
    SmoothForm.mpullback (fun p : M × N ↦ g • p)
      (ContMDiffSMul.contMDiff_const_smul (I := IG) g) (σ.prod τ) = σ.prod τ := by
  have hg := mpullback_prodMap_prod (ContMDiffSMul.contMDiff_const_smul (I := IG) (I' := I) g)
    (ContMDiffSMul.contMDiff_const_smul (I := IG) (I' := J) g) σ τ
  rw [hσ, hτ] at hg
  -- On `M × N`, `g` acts by definition as the product map of its actions on the factors.
  exact hg

end TauCeti.SmoothTwoForm

end
