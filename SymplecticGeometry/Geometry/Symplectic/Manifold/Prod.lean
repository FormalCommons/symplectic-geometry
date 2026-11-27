/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.Prod
public import Mathlib.Geometry.Manifold.Algebra.SMul
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.Smooth

/-!
# Pull-backs of the product form

For two-forms `σ` on `M` and `τ` on `N` and an element `g` of a monoid acting smoothly on both,
`TauCeti.SmoothTwoForm.mpullback_smul_prod` says that if `g` preserves `σ` and `τ`, it preserves
the product form `σ.prod τ` for the diagonal action on `M × N`. This is the naturality of the
product form, `TauCeti.SmoothTwoForm.mpullback_prodMap_prod`, for the product map `g × g`, which is
the diagonal action of `g`. The proof is the one of the field `mpullback_smul` in Tau Ceti's
`TauCeti.SmoothTwoForm.HamiltonianTorusData.prod`
(`TauCeti/Geometry/Symplectic/Hamiltonian/EquivariantMomentMap/Torus.lean`), for any monoid in
place of a torus.

Along any smooth map `F : X → M × N`, the product form pulls back to
`(pr₁ ∘ F)^* σ + (pr₂ ∘ F)^* τ` (`TauCeti.SmoothTwoForm.mpullback_prod`), which generalizes
`mpullback_prodMap_prod` from product maps to all maps into the product. Its proof takes the
first rewriting steps of Tau Ceti's `TauCeti.integralTopForm_mpullback_prod`
(`TauCeti/Geometry/Symplectic/Manifold/Prod/Area.lean`), stated for the forms instead of for
their integrals.

On a slice `x ↦ (x, c)` of `M × N` the product form restricts to `σ`
(`TauCeti.SmoothTwoForm.mpullback_prodMk_left_prod`). On two tangent vectors of `M × N`, which
are pairs, the product form is the sum of the factor forms on their components
(`TauCeti.SmoothTwoForm.eval₂_prod_eq_add`).
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

/-- **Pull-back of the product form along a map into a product.** For a smooth map
`F : X → M × N`, the pull-back of `pr₁^* σ + pr₂^* τ` along `F` is
`(pr₁ ∘ F)^* σ + (pr₂ ∘ F)^* τ`. -/
theorem mpullback_prod {E₀ H₀ X : Type*} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]
    [TopologicalSpace H₀] {I₀ : ModelWithCorners ℝ E₀ H₀} [TopologicalSpace X]
    [ChartedSpace H₀ X] [IsManifold I₀ 1 X] {F : X → M × N} (hF : ContMDiff I₀ (I.prod J) ∞ F)
    (σ : SmoothTwoForm I M) (τ : SmoothTwoForm J N) :
    SmoothForm.mpullback F hF (σ.prod τ) =
      SmoothForm.mpullback (Prod.fst ∘ F) (contMDiff_fst.comp hF) σ +
        SmoothForm.mpullback (Prod.snd ∘ F) (contMDiff_snd.comp hF) τ := by
  rw [prod_def, map_add, SmoothForm.mpullback_mpullback, SmoothForm.mpullback_mpullback]

/-- The product form `σ ⊕ τ` restricts to `σ` on each slice `x ↦ (x, c)` of `M × N`: the pull-back
of `pr₂^* τ` along a slice vanishes, since `pr₂` is constant on it. -/
theorem mpullback_prodMk_left_prod (σ : SmoothTwoForm I M) (τ : SmoothTwoForm J N) (c : N) :
    SmoothForm.mpullback (fun x : M ↦ (x, c)) (contMDiff_id.prodMk contMDiff_const)
      (σ.prod τ) = σ := by
  simp only [mpullback_prod, Function.comp_def, SmoothForm.mpullback_const, add_zero]
  exact LinearMap.congr_fun SmoothForm.mpullback_id σ

/-- The product form evaluates on two tangent vectors of `M × N`, which are pairs, as the sum of
the factor forms on their components. -/
theorem eval₂_prod_eq_add (σ : SmoothTwoForm I M) (τ : SmoothTwoForm J N) (p : M × N)
    (v w : TangentSpace (I.prod J) p) :
    (σ.prod τ).eval₂ p v w = σ.eval₂ p.1 v.1 w.1 + τ.eval₂ p.2 v.2 w.2 := by
  rw [eval₂_prod, Manifold.tangentSpaceProdEquiv_apply, Manifold.tangentSpaceProdEquiv_apply]

end TauCeti.SmoothTwoForm

end
