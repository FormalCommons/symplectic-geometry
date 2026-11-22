/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Topology.VectorBundle.Complex.ChernClass.Whitney
public import SymplecticGeometry.Topology.VectorBundle.Complex.FirstChernClass
public import SymplecticGeometry.Topology.VectorBundle.Orientation.Complex.Tensor
public import SymplecticGeometry.Topology.VectorBundle.ProjectiveBundle.Splitting

/-!
# The first Chern class `c₁` is the class of the determinant line

There are two first Chern classes of a complex vector bundle `E → B` in the library: the Chern
class `chernClass G E 1`, from the projective bundle of `E`, and
`SymplecticGeometry.Bundle.firstChernClass G E`, the Euler class of the determinant line of `E`,
with values in `ULift ℤ`. This file shows that over a compact Hausdorff base they agree, through
`TopCat.uliftIntegralCohomologyIso` (`chernClass_one_eq_firstChernClass`), so that they are one
notion.

Both are additive on direct sums. For the Chern class this is the Whitney sum formula in degree
two (`chernClass_one_prod`, in `ChernClass/Whitney.lean`). For `firstChernClass` it is
`firstChernClass_prod`: the determinant line of `E₁ ⊕ E₂` is the tensor product of the
determinant lines (`SymplecticGeometry.Bundle.detCoreProdIso`), and the Euler class of a tensor
product of complex lines over a compact normal base is the sum of their Euler classes
(`TauCeti.complexEulerClass_tensorProduct`). On lines both are the Euler class of the bundle
(`chernClass_one_eq_complexEulerClass`, `firstChernClass_eq_complexEulerClass`), and in rank zero
both vanish (`chernClass_eq_zero_of_finrank_lt`, `firstChernClass_eq_zero_of_finrank_eq_zero`).
The comparison then goes by induction on the rank with the splitting principle: the
pull-back of `E` to its projective bundle `π : P(E) → B` splits as the tautological line plus a
bundle of smaller rank (`ProjectiveBundle.pullbackEquivTautologicalProdComplement`), `P(E)` is
again compact Hausdorff, and `π^*` is injective on cohomology (`injective_projectiveBundle_proj`).

## Main results

* `firstChernClass_prod`: `firstChernClass` is additive on direct sums, over a compact normal
  base.
* `chernClass_one_eq_firstChernClass`: `c₁(E)` is `firstChernClass G E`, read in integral
  cohomology, over a compact Hausdorff base.

## References

* [R. Bott, L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §20 (the
  splitting principle).
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton University Press (1974), §14 (the first Chern class through the determinant line).
-/

public section

open Bundle Module TauCeti CategoryTheory
open scoped TensorProduct TauCeti.ModuleTopology

namespace SymplecticGeometry.Bundle

variable {B : Type} [TopologicalSpace B]

/-! ### Additivity on direct sums -/

section FirstChernClass

variable [CompactSpace B] [NormalSpace B]
  {G₁ : Type*} [NormedAddCommGroup G₁] [NormedSpace ℂ G₁] [FiniteDimensional ℂ G₁]
  {E₁ : B → Type*} [∀ b, AddCommMonoid (E₁ b)] [∀ b, Module ℂ (E₁ b)]
  [∀ b, TopologicalSpace (E₁ b)] [TopologicalSpace (TotalSpace G₁ E₁)]
  [FiberBundle G₁ E₁] [VectorBundle ℂ G₁ E₁]
  {G₂ : Type*} [NormedAddCommGroup G₂] [NormedSpace ℂ G₂] [FiniteDimensional ℂ G₂]
  {E₂ : B → Type*} [∀ b, AddCommMonoid (E₂ b)] [∀ b, Module ℂ (E₂ b)]
  [∀ b, TopologicalSpace (E₂ b)] [TopologicalSpace (TotalSpace G₂ E₂)]
  [FiberBundle G₂ E₂] [VectorBundle ℂ G₂ E₂]

/-- **The first Chern class of the determinant line is additive.** Over a compact normal base,
such as a compact Hausdorff one, `firstChernClass` of `E₁ ⊕ E₂` is the sum of those of `E₁` and
`E₂`: the determinant line of the sum is the tensor product of the determinant lines, whose Euler
class is the sum of their Euler classes. -/
theorem firstChernClass_prod :
    firstChernClass (G₁ × G₂) (E₁ ×ᵇ E₂) = firstChernClass G₁ E₁ + firstChernClass G₂ E₂ := by
  rw [firstChernClass_def, firstChernClass_def, firstChernClass_def,
    complexEulerClass_eq_of_fiberwise _ _ (continuous_detCoreProdFiberEquiv ℂ E₁ E₂)]
  exact complexEulerClass_tensorProduct (by simp) (by simp)

end FirstChernClass

/-! ### The comparison -/

variable {G : Type} [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  {E : B → Type} [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)] [∀ b, Module ℝ (E b)]
  [∀ b, IsScalarTower ℝ ℂ (E b)] [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace G E)]
  [FiberBundle G E] [VectorBundle ℂ G E] [CompactSpace B] [T2Space B]

/-- **The first Chern class is the class of the determinant line.** Over a compact Hausdorff base,
the Chern class `c₁(E)` is `firstChernClass G E`, the Euler class of the determinant line of `E`,
read in integral cohomology. -/
theorem chernClass_one_eq_firstChernClass :
    chernClass G E 1 = ((TopCat.of B).uliftIntegralCohomologyIso 2).hom (firstChernClass G E) := by
  obtain ⟨n, hn⟩ : ∃ n, finrank ℂ G = n := ⟨_, rfl⟩
  induction n generalizing B G E with
  | zero =>
    rw [chernClass_eq_zero_of_finrank_lt G E (by omega),
      firstChernClass_eq_zero_of_finrank_eq_zero G E hn, map_zero]
  | succ n ih =>
    have hS : finrank ℂ ℂ = 0 + 1 := finrank_self ℂ
    -- Pull back to the projective bundle, where `E` splits as `S ⊕ Q` with `Q` of rank `n`.
    apply injective_projectiveBundle_proj G E (by omega) _
    rw [← chernClass_pullback (ProjectiveBundle.projection ℂ G E),
      chernClass_congr (ProjectiveBundle.pullbackEquivTautologicalProdComplement ℂ G E)
        ProjectiveBundle.continuous_pullbackEquivTautologicalProdComplement,
      chernClass_one_prod,
      ih (E := ProjectiveBundle.tautologicalComplement ℂ G E) (by simp [hn]),
      chernClass_one_eq_complexEulerClass _ _ hS,
      ← firstChernClass_eq_complexEulerClass _ hS, ← map_add, ← firstChernClass_prod,
      ← firstChernClass_congr (E := ⇑(ProjectiveBundle.projection ℂ G E) *ᵖ E)
        _ ProjectiveBundle.continuous_pullbackEquivTautologicalProdComplement,
      firstChernClass_pullback]
    exact ConcreteCategory.congr_hom (TopCat.uliftIntegralCohomologyIso_naturality _ _) _

end SymplecticGeometry.Bundle

end
