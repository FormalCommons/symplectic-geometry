/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Topology.VectorBundle.Complex.ChernClass.Basic
import SymplecticGeometry.Topology.VectorBundle.Complex.ChernClass.Whitney
import SymplecticGeometry.Topology.VectorBundle.Orientation.Complex.Whitney
import SymplecticGeometry.Topology.VectorBundle.ProjectiveBundle.Splitting
import SymplecticGeometry.Topology.VectorBundle.Complex.ChernClass.Naturality

/-!
# The top Chern class is the Euler class

For a complex vector bundle `E → B` of rank `r + 1` over a compact Hausdorff base, the top Chern
class `c_{r+1}(E)` is Tau Ceti's Euler class `TauCeti.complexEulerClass` of `E`, read in integral
cohomology through `TopCat.uliftIntegralCohomologyIso`
(`SymplecticGeometry.Bundle.chernClass_finrank_eq_complexEulerClass`).

The proof is by induction on `r` with the splitting principle. For a line bundle it is
`chernClass_one_eq_complexEulerClass`. For `E` of rank `r + 2`, let `π : P(E) → B` be its projective
bundle, which is again compact Hausdorff, with `π^*` injective on cohomology
(`injective_projectiveBundle_proj`). The pull-back `π^* E` is isomorphic to `S ⊕ Q`, the
tautological line `S` plus a bundle `Q` of rank `r + 1`
(`ProjectiveBundle.pullbackEquivTautologicalProdComplement`). Both classes are natural and
invariant under isomorphism, and both are multiplicative on `S ⊕ Q`: by the Whitney sum formula
`chernClass_prod`, whose only nonzero term in degree `2 (r + 2)` is `c₁(S) ⌣ c_{r+1}(Q)`, and by
the Whitney formula for Euler classes `TauCeti.complexEulerClass_prod`, compared through
`TopCat.uliftIntegralCohomologyIso_singularCup`. The induction hypothesis for `Q` concludes.

## Main results

* `chernClass_finrank_eq_complexEulerClass`: `c_{r+1}(E) = e(E)` for `E` of rank `r + 1`.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton University Press (1974), §14 (the top Chern class of a complex bundle as the Euler
  class of its underlying real bundle).
* [R. Bott, L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §20 (the
  splitting principle).
-/

public section

open Bundle Module TauCeti CategoryTheory

namespace SymplecticGeometry.Bundle

variable {B : Type} [TopologicalSpace B]

section Prod

variable {G₁ : Type} [NormedAddCommGroup G₁] [NormedSpace ℂ G₁] [FiniteDimensional ℂ G₁]
  {E₁ : B → Type} [∀ b, AddCommGroup (E₁ b)] [∀ b, Module ℂ (E₁ b)] [∀ b, Module ℝ (E₁ b)]
  [∀ b, IsScalarTower ℝ ℂ (E₁ b)] [∀ b, TopologicalSpace (E₁ b)]
  [TopologicalSpace (TotalSpace G₁ E₁)] [FiberBundle G₁ E₁] [VectorBundle ℂ G₁ E₁]
  {G₂ : Type} [NormedAddCommGroup G₂] [NormedSpace ℂ G₂] [FiniteDimensional ℂ G₂]
  {E₂ : B → Type} [∀ b, AddCommGroup (E₂ b)] [∀ b, Module ℂ (E₂ b)] [∀ b, Module ℝ (E₂ b)]
  [∀ b, IsScalarTower ℝ ℂ (E₂ b)] [∀ b, TopologicalSpace (E₂ b)]
  [TopologicalSpace (TotalSpace G₂ E₂)] [FiberBundle G₂ E₂] [VectorBundle ℂ G₂ E₂]
  [CompactSpace B]

/-- The top Chern class of a line bundle plus a bundle of rank `r + 1` is the cup product of
their top classes, with the degrees of `TauCeti.complexEulerClass`. -/
private theorem chernClass_prod_of_finrank_eq_one {r : ℕ} (h₁ : finrank ℂ G₁ = 1)
    (h₂ : finrank ℂ G₂ = r + 1) :
    chernClass (G₁ × G₂) (E₁ ×ᵇ E₂) (r + 2) =
      (TopCat.of B).integralCup (2 * 0 + 2) (2 * r + 2) (2 * (r + 1) + 2) (by omega)
        (chernClass G₁ E₁ 1) (chernClass G₂ E₂ (r + 1)) := by
  rw [chernClass_prod, Fin.sum_univ_succ, Fin.sum_univ_succ, Finset.sum_eq_zero, add_zero,
    chernClass_eq_zero_of_finrank_lt G₂ E₂ (by simp; omega), map_zero, zero_add]
  · -- The index `↑(Fin.succ 0)` is `1` and `r + 2 - 1` is `r + 1` by computation, and so are the
    -- degrees.
    rfl
  · intro i _
    rw [chernClass_eq_zero_of_finrank_lt G₁ E₁ (by simp [h₁]), map_zero, LinearMap.zero_apply]

end Prod

variable {G : Type} [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  {E : B → Type} [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)] [∀ b, Module ℝ (E b)]
  [∀ b, IsScalarTower ℝ ℂ (E b)] [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace G E)]
  [FiberBundle G E] [VectorBundle ℂ G E] [CompactSpace B] [T2Space B]

/-- **The top Chern class is the Euler class.** Over a compact Hausdorff base, for `E` of rank
`r + 1`, the top Chern class `c_{r+1}(E)` is the Euler class of `E`, read in integral cohomology
(of degree `2 (r + 1) = 2 r + 2`). -/
theorem chernClass_finrank_eq_complexEulerClass {r : ℕ} (hG : finrank ℂ G = r + 1) :
    chernClass G E (r + 1) =
      ((TopCat.of B).uliftIntegralCohomologyIso (2 * r + 2)).hom (complexEulerClass G E hG) := by
  induction r generalizing B G E with
  | zero => exact chernClass_one_eq_complexEulerClass G E hG
  | succ r ih =>
    have hQ : finrank ℂ (Fin (finrank ℂ G - 1) → ℂ) = r + 1 := by simp [hG]
    -- Pull back to the projective bundle, where `E` splits as `S ⊕ Q` with `Q` of rank `r + 1`.
    apply injective_projectiveBundle_proj G E (by omega) _
    rw [← chernClass_pullback (ProjectiveBundle.projection ℂ G E),
      chernClass_congr (ProjectiveBundle.pullbackEquivTautologicalProdComplement ℂ G E)
        ProjectiveBundle.continuous_pullbackEquivTautologicalProdComplement,
      chernClass_prod_of_finrank_eq_one (finrank_self ℂ) hQ, ih hQ,
      chernClass_one_eq_complexEulerClass _ _ (finrank_self ℂ),
      ← TopCat.uliftIntegralCohomologyIso_singularCup,
      ← complexEulerClass_prod (finrank_self ℂ) hQ (by omega),
      ← complexEulerClass_eq_of_fiberwise (E' := ⇑(ProjectiveBundle.projection ℂ G E) *ᵖ E) _ _
        ProjectiveBundle.continuous_pullbackEquivTautologicalProdComplement,
      complexEulerClass_pullback]
    exact TopCat.uliftIntegralCohomologyIso_naturality_apply _ _ _

end SymplecticGeometry.Bundle

end
