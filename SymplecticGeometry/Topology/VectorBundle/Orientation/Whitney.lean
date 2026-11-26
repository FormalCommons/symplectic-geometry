/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.VectorBundle.Orientation.Whitney
public import TauCeti.LinearAlgebra.Dimension.Prod
public import TauCeti.AlgebraicTopology.Cohomology.IntegralCup
public import TauCeti.Algebra.Category.ModuleCat.Monoidal.Unit
import SymplecticGeometry.AlgebraicTopology.Cohomology.Local.CrossOrientation

/-!
# Integral Thom and Euler classes of a direct sum of oriented bundles

Let `E₁` and `E₂` be real vector bundles over a common base `B`, with model fibres of dimensions
`m + 1` and `n + 1` and orientations `o₁` and `o₂`. Their fibrewise direct sum `E₁ ×ᵇ E₂` carries
the orientation `o₁.prod o₂`, the first factor before the second, which we reindex along
`m + 1 + (n + 1) = d + 1`. Integral classes take values in `ULift ℤ`, and the products below use
the diagonal `TauCeti.integralCoeffComul` of the chain coefficients and the multiplication
`ModuleCat.uliftTensorSelfIso ℤ` of the values, as Tau Ceti's integral cup product does.
The integral cohomology takes the `ℤ`-linear structure that `ModuleCat ℤ` has as a preadditive
category (`CategoryTheory.MonoidalPreadditive.monoidalLinearInt`), as there.

* `TauCeti.VectorBundleOrientation.thomClass_prod`: the integral Thom class of the direct sum is
  `(-1) ^ ((m + 1) * (n + 1))` times the product `TauCeti.thomPairCup` of the Thom classes of the
  two factors, `p₁^* U(E₁) ⌣ p₂^* U(E₂)`.
* `TauCeti.VectorBundleOrientation.eulerClass_prod`: the Euler class of the direct sum is the cup
  product of the Euler classes of the factors, with no sign.

The sign in `thomClass_prod` is that of `Orientation.complZeroPairCross_localCohomologyClass`,
which compares the product of the local generators selected by orientations of the model fibres
with the generator selected by their product orientation. It is `1` as soon as one of the two
ranks is even, in particular for complex bundles. It drops out of `eulerClass_prod`: when both
ranks are odd, the Euler class of each factor is `2`-torsion
(`TauCeti.VectorBundleOrientation.two_smul_eulerClass`), so it equals its negative.

The proof of `thomClass_prod` reads both sides on the fibre over each point in the product of the
preferred trivializations of the two factors, following Tau Ceti's proof of
`TauCeti.VectorBundleOrientation.thomClassOfModel_prod`, with the local generators of
`Orientation.complZeroPairCross_localCohomologyClass` in place of arbitrary model classes.

## Main results

* `TauCeti.VectorBundleOrientation.thomClass_prod`: the Thom class of a direct sum.
* `TauCeti.VectorBundleOrientation.eulerClass_prod`: the Euler class of a direct sum.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton University Press, 1974, §9, Property 9.6.
-/

public section

noncomputable section

open Bundle CategoryTheory Module

attribute [local instance] MonoidalPreadditive.monoidalLinearInt

namespace TauCeti.VectorBundleOrientation

variable {B : Type} [TopologicalSpace B]
  {F₁ : Type} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
  {E₁ : B → Type} [TopologicalSpace (TotalSpace F₁ E₁)] [∀ b, AddCommGroup (E₁ b)]
  [∀ b, Module ℝ (E₁ b)] [∀ b, TopologicalSpace (E₁ b)] [FiberBundle F₁ E₁] [VectorBundle ℝ F₁ E₁]
  {F₂ : Type} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]
  {E₂ : B → Type} [TopologicalSpace (TotalSpace F₂ E₂)] [∀ b, AddCommGroup (E₂ b)]
  [∀ b, Module ℝ (E₂ b)] [∀ b, TopologicalSpace (E₂ b)] [FiberBundle F₂ E₂] [VectorBundle ℝ F₂ E₂]
  {m n d : ℕ}

/-- **The integral Thom class of a direct sum of oriented bundles.** For orientations `o₁` and
`o₂` of real vector bundles `E₁` and `E₂` over a common base, of ranks `m + 1` and `n + 1`, the
Thom class of `E₁ ⊕ E₂` with the orientation `o₁.prod o₂`, reindexed by
`Fin (m + 1 + (n + 1)) ≃ Fin (d + 1)`, is `(-1) ^ ((m + 1) * (n + 1))` times the product
`p₁^* U(E₁) ⌣ p₂^* U(E₂)` (`TauCeti.thomPairCup`) of the Thom classes of `o₁` and `o₂`. -/
theorem thomClass_prod (o₁ : VectorBundleOrientation F₁ E₁ (Fin (m + 1)))
    (o₂ : VectorBundleOrientation F₂ E₂ (Fin (n + 1))) (hF₁ : finrank ℝ F₁ = m + 1)
    (hF₂ : finrank ℝ F₂ = n + 1) (h : m + 1 + (n + 1) = d + 1) :
    (reindex (finCongr h) (o₁.prod o₂ hF₁ hF₂)).thomClass (finrank_prod_eq_succ hF₁ hF₂ h) =
      (-1 : ℤ) ^ ((m + 1) * (n + 1)) •
        thomPairCup ℤ F₁ E₁ F₂ E₂ integralCoeffComul (ModuleCat.uliftTensorSelfIso ℤ).hom
          (m + 1) (n + 1) (d + 1) h (o₁.thomClass hF₁) (o₂.thomClass hF₂) := by
  symm
  refine (eq_thomClass_iff _ _ _).2 fun e _ b hb ↦ ?_
  let e₁ := trivializationAt F₁ E₁ b
  let e₂ := trivializationAt F₂ E₂ b
  have hb₁ : b ∈ e₁.baseSet := FiberBundle.mem_baseSet_trivializationAt' b
  have hb₂ : b ∈ e₂.baseSet := FiberBundle.mem_baseSet_trivializationAt' b
  have hb' : b ∈ (e₁.prod e₂).baseSet := ⟨hb₁, hb₂⟩
  -- The fibres are T1, being homeomorphic to the model fibres.
  have : T1Space (E₁ b) :=
    (e₁.continuousLinearEquivAt ℝ b hb₁).toHomeomorph.isEmbedding.t1Space
  have : T1Space (E₂ b) :=
    (e₂.continuousLinearEquivAt ℝ b hb₂).toHomeomorph.isEmbedding.t1Space
  -- On the fibre over `b`, read each factor in its preferred trivialization and the product in
  -- the product trivialization: the product of the local generators is the sign times the
  -- generator selected by the product orientation.
  rw [map_zsmul, singularCohomologyMap_fiberThomPairMap_thomPairCup_eq_complZeroPairCross,
    o₁.singularCohomologyMap_fiberThomPairMap_thomClass hF₁ e₁ hb₁,
    o₂.singularCohomologyMap_fiberThomPairMap_thomClass hF₂ e₂ hb₂,
    complZeroPairCross_singularCohomologyMap_complZeroPairIso_hom,
    Orientation.complZeroPairCross_localCohomologyClass, map_zsmul, smul_smul, ← mul_pow,
    neg_one_mul, neg_neg, one_pow, one_smul,
    ← Trivialization.mapOrientation_prod e₁ e₂ hb₁ hb₂ _ _ hF₁ hF₂, ← prod_apply o₁ o₂ hF₁ hF₂ b,
    ← Trivialization.mapOrientation_reindex, reindex_apply,
    ← Trivialization.continuousLinearEquivAt_prod (𝕜 := ℝ) hb', Trivialization.mapOrientation_apply,
    Trivialization.mapOrientation_apply]
  -- The generator read through a linear trivialization does not depend on the trivialization.
  exact Orientation.singularCohomologyMap_localCohomologyClass_map_eq _ _ _ _ _

/-- **The integral Euler class of a direct sum of oriented bundles.** For orientations `o₁` and
`o₂` of real vector bundles `E₁` and `E₂` over a common base, of ranks `m + 1` and `n + 1`, the
Euler class of `E₁ ⊕ E₂` with the orientation `o₁.prod o₂`, reindexed by
`Fin (m + 1 + (n + 1)) ≃ Fin (d + 1)`, is the cup product `e(E₁) ⌣ e(E₂)` of the Euler classes
of `o₁` and `o₂`. -/
theorem eulerClass_prod (o₁ : VectorBundleOrientation F₁ E₁ (Fin (m + 1)))
    (o₂ : VectorBundleOrientation F₂ E₂ (Fin (n + 1))) (hF₁ : finrank ℝ F₁ = m + 1)
    (hF₂ : finrank ℝ F₂ = n + 1) (h : m + 1 + (n + 1) = d + 1) :
    (reindex (finCongr h) (o₁.prod o₂ hF₁ hF₂)).eulerClass (finrank_prod_eq_succ hF₁ hF₂ h) =
      (TopCat.of B).singularCup ℤ integralCoeffComul (ModuleCat.uliftTensorSelfIso ℤ).hom
        (m + 1) (n + 1) (d + 1) h (o₁.eulerClass hF₁) (o₂.eulerClass hF₂) := by
  rw [eulerClass_def, thomClass_prod, map_zsmul, eulerClass_thomPairCup, ← eulerClass_def,
    ← eulerClass_def]
  rcases Nat.even_or_odd m with hm | hm
  · rcases Nat.even_or_odd n with hn | hn
    · -- Both ranks are odd: the sign is `-1`, and `e(E₁)` is `2`-torsion, so `-e(E₁) = e(E₁)`.
      have h₁ : -o₁.eulerClass hF₁ = o₁.eulerClass hF₁ :=
        neg_eq_iff_add_eq_zero.2 (by rw [← two_nsmul, o₁.two_smul_eulerClass hF₁ hm])
      rw [Odd.neg_one_pow (hm.add_one.mul hn.add_one), neg_one_zsmul, ← LinearMap.neg_apply,
        ← map_neg, h₁]
    · rw [Even.neg_one_pow (hn.add_one.mul_left _), one_smul]
  · rw [Even.neg_one_pow (hm.add_one.mul_right _), one_smul]

end TauCeti.VectorBundleOrientation

end
