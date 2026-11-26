/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.VectorBundle.Orientation.Complex.EulerClass
public import SymplecticGeometry.LinearAlgebra.Complex.Finrank
public import SymplecticGeometry.Topology.VectorBundle.Orientation.Whitney
public import SymplecticGeometry.Topology.VectorBundle.Complex.RestrictScalars
public import SymplecticGeometry.LinearAlgebra.Complex.FiniteDimensional
public import TauCeti.AlgebraicTopology.Cohomology.IntegralCup
public import TauCeti.Algebra.Category.ModuleCat.Monoidal.Unit

/-!
# The Whitney formula for Euler classes of complex vector bundles

Let `E₁` and `E₂` be complex vector bundles over a common base `B`, of complex ranks `r₁ + 1` and
`r₂ + 1`. Their underlying real bundles carry the canonical orientations
`TauCeti.VectorBundleOrientation.complex`, and so does the underlying real bundle of their
fibrewise direct sum `E₁ ×ᵇ E₂`.

* `TauCeti.VectorBundleOrientation.reindex_prod_complex`: the canonical orientation of `E₁ ×ᵇ E₂`
  is the direct-sum orientation of the canonical orientations of `E₁` and `E₂`, `E₁` first, once
  all three are indexed by `Fin _` of the right lengths. This is the bundle form of Tau Ceti's
  fibrewise `TauCeti.VectorBundleOrientation.prod_complex`.
* `TauCeti.complexEulerClass_prod`: the integral Euler class of `E₁ ×ᵇ E₂` is the cup product
  `e(E₁) ⌣ e(E₂)` of the Euler classes of the factors, the cup product being
  `TopCat.singularCup ℤ TauCeti.integralCoeffComul (ModuleCat.uliftTensorSelfIso ℤ).hom` on
  classes with values in `ULift ℤ`. It follows from the first result and
  `TauCeti.VectorBundleOrientation.eulerClass_prod`, the Whitney formula for oriented real
  bundles.

## Main results

* `TauCeti.VectorBundleOrientation.reindex_prod_complex`: the canonical orientation of a direct
  sum.
* `TauCeti.complexEulerClass_prod`: the Euler class of a direct sum of complex vector bundles.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton University Press, 1974, §9, Property 9.6, and §14.
-/

public section

noncomputable section

open Bundle CategoryTheory Module

attribute [local instance] MonoidalPreadditive.monoidalLinearInt

namespace TauCeti

section Orientation

variable {B : Type*} [TopologicalSpace B]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [NormedSpace ℂ F₁]
  [IsScalarTower ℝ ℂ F₁] [FiniteDimensional ℂ F₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [NormedSpace ℂ F₂]
  [IsScalarTower ℝ ℂ F₂] [FiniteDimensional ℂ F₂]
  {E₁ : B → Type*} [TopologicalSpace (TotalSpace F₁ E₁)] [∀ b, AddCommGroup (E₁ b)]
  [∀ b, Module ℝ (E₁ b)] [∀ b, Module ℂ (E₁ b)] [∀ b, IsScalarTower ℝ ℂ (E₁ b)]
  [∀ b, TopologicalSpace (E₁ b)] [FiberBundle F₁ E₁] [VectorBundle ℂ F₁ E₁]
  {E₂ : B → Type*} [TopologicalSpace (TotalSpace F₂ E₂)] [∀ b, AddCommGroup (E₂ b)]
  [∀ b, Module ℝ (E₂ b)] [∀ b, Module ℂ (E₂ b)] [∀ b, IsScalarTower ℝ ℂ (E₂ b)]
  [∀ b, TopologicalSpace (E₂ b)] [FiberBundle F₂ E₂] [VectorBundle ℂ F₂ E₂]

open scoped VectorBundle.ComplexToReal Module.ComplexToReal

namespace VectorBundleOrientation

/-- **The canonical orientation of a direct sum of complex vector bundles.** With the canonical
orientations of `E₁` and `E₂` indexed by `Fin m` and `Fin n` (`2 * finrank ℂ F₁ = m`,
`2 * finrank ℂ F₂ = n`), their direct-sum orientation, `E₁` first, indexed by `Fin d` along
`m + n = d`, is the canonical orientation of `E₁ ×ᵇ E₂`, indexed by `Fin d`. -/
theorem reindex_prod_complex {m n d : ℕ} (h₁ : 2 * finrank ℂ F₁ = m)
    (h₂ : 2 * finrank ℂ F₂ = n) (h : m + n = d) :
    reindex (finCongr h)
        ((reindex (finCongr h₁) (complex F₁ E₁)).prod (reindex (finCongr h₂) (complex F₂ E₂))
          (by rw [finrank_real_eq_two_mul_finrank_complex, h₁])
          (by rw [finrank_real_eq_two_mul_finrank_complex, h₂])) =
      reindex (finCongr (by rw [finrank_prod, ← h, ← h₁, ← h₂]; ring))
        (complex (F₁ × F₂) (E₁ ×ᵇ E₂)) := by
  subst h₁ h₂ h
  ext b
  simpa using prod_complex b

end VectorBundleOrientation

end Orientation

section EulerClass

/-! `VectorBundleOrientation.eulerClass_prod` is stated over `Type`, and so is this section. -/

variable {B : Type} [TopologicalSpace B]
  {F₁ : Type} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [NormedSpace ℂ F₁]
  [IsScalarTower ℝ ℂ F₁] [FiniteDimensional ℂ F₁]
  {F₂ : Type} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [NormedSpace ℂ F₂]
  [IsScalarTower ℝ ℂ F₂] [FiniteDimensional ℂ F₂]
  {E₁ : B → Type} [TopologicalSpace (TotalSpace F₁ E₁)] [∀ b, AddCommGroup (E₁ b)]
  [∀ b, Module ℝ (E₁ b)] [∀ b, Module ℂ (E₁ b)] [∀ b, IsScalarTower ℝ ℂ (E₁ b)]
  [∀ b, TopologicalSpace (E₁ b)] [FiberBundle F₁ E₁] [VectorBundle ℂ F₁ E₁]
  {E₂ : B → Type} [TopologicalSpace (TotalSpace F₂ E₂)] [∀ b, AddCommGroup (E₂ b)]
  [∀ b, Module ℝ (E₂ b)] [∀ b, Module ℂ (E₂ b)] [∀ b, IsScalarTower ℝ ℂ (E₂ b)]
  [∀ b, TopologicalSpace (E₂ b)] [FiberBundle F₂ E₂] [VectorBundle ℂ F₂ E₂]

open scoped VectorBundle.ComplexToReal Module.ComplexToReal

/-- **The Whitney formula for Euler classes of complex vector bundles.** For complex vector
bundles `E₁` and `E₂` over a common base, of complex ranks `r₁ + 1` and `r₂ + 1`, the Euler class
of `E₁ ×ᵇ E₂`, of complex rank `r + 1 = r₁ + 1 + (r₂ + 1)`, is the cup product `e(E₁) ⌣ e(E₂)` of
the Euler classes of `E₁` and `E₂`, with values in `ULift ℤ`. -/
theorem complexEulerClass_prod {r₁ r₂ r : ℕ} (hF₁ : finrank ℂ F₁ = r₁ + 1)
    (hF₂ : finrank ℂ F₂ = r₂ + 1) (h : r₁ + 1 + (r₂ + 1) = r + 1) :
    complexEulerClass (F₁ × F₂) (E₁ ×ᵇ E₂) (by rw [finrank_prod, hF₁, hF₂, h]) =
      (TopCat.of B).singularCup ℤ integralCoeffComul (ModuleCat.uliftTensorSelfIso ℤ).hom
        (2 * r₁ + 2) (2 * r₂ + 2) (2 * r + 2) (by omega)
        (complexEulerClass F₁ E₁ hF₁) (complexEulerClass F₂ E₂ hF₂) := by
  rw [complexEulerClass_def, complexEulerClass_def, complexEulerClass_def,
    ← VectorBundleOrientation.eulerClass_prod (m := 2 * r₁ + 1) (n := 2 * r₂ + 1)
      (d := 2 * r + 1) _ _ (SymplecticGeometry.finrank_real_of_finrank_complex_eq_add_one hF₁)
      (SymplecticGeometry.finrank_real_of_finrank_complex_eq_add_one hF₂) (by omega),
    VectorBundleOrientation.reindex_prod_complex (by omega) (by omega) (by omega)]

end EulerClass

end TauCeti

end
