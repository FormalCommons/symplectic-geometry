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
`firstChernClass_prod_of_hasFiniteTrivializingCover`: the determinant line of `E₁ ⊕ E₂` is the
tensor product of the determinant lines (`SymplecticGeometry.Bundle.detCoreProdIso`), and the
Euler class of a tensor product of complex lines with finite trivializing covers over a normal
base is the sum of their Euler classes
(`TauCeti.complexEulerClass_tensorProduct`). On lines both are the Euler class of the bundle
(`chernClass_one_eq_complexEulerClass`, `firstChernClass_eq_complexEulerClass`), and in rank zero
both vanish (`chernClass_eq_zero_of_finrank_lt`, `firstChernClass_eq_zero_of_finrank_eq_zero`).
The comparison then goes by induction on the rank with the splitting principle: the
pull-back of `E` to its projective bundle `π : P(E) → B` splits as the tautological line plus a
bundle of smaller rank (`ProjectiveBundle.pullbackEquivTautologicalProdComplement`), `P(E)` is
again compact Hausdorff, and `π^*` is injective on cohomology (`injective_projectiveBundle_proj`).

## Main results

* `firstChernClass_prod_of_hasFiniteTrivializingCover`: `firstChernClass` is additive on direct
  sums, over a normal base on which both determinant lines have finite trivializing covers;
* `firstChernClass_prod`: its case over a compact normal base;
  hence `chernNumber_prod`, the additivity of the first Chern number over a compact oriented
  surface.
* `chernClass_one_eq_firstChernClass`: `c₁(E)` is `firstChernClass G E`, read in integral
  cohomology, over a compact Hausdorff base.
* `Projectivization.firstChernClass_tautological`: `firstChernClass` of the tautological line of
  `ℙ ℂ V` is minus the hyperplane class `Projectivization.hyperplaneClass V`, as both are the
  Euler class of that line up to sign.

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

variable [NormalSpace B]
  {G₁ : Type*} [NormedAddCommGroup G₁] [NormedSpace ℂ G₁] [FiniteDimensional ℂ G₁]
  {E₁ : B → Type*} [∀ b, AddCommMonoid (E₁ b)] [∀ b, Module ℂ (E₁ b)]
  [∀ b, TopologicalSpace (E₁ b)] [TopologicalSpace (TotalSpace G₁ E₁)]
  [FiberBundle G₁ E₁] [VectorBundle ℂ G₁ E₁]
  {G₂ : Type*} [NormedAddCommGroup G₂] [NormedSpace ℂ G₂] [FiniteDimensional ℂ G₂]
  {E₂ : B → Type*} [∀ b, AddCommMonoid (E₂ b)] [∀ b, Module ℂ (E₂ b)]
  [∀ b, TopologicalSpace (E₂ b)] [TopologicalSpace (TotalSpace G₂ E₂)]
  [FiberBundle G₂ E₂] [VectorBundle ℂ G₂ E₂]

/-- **The first Chern class is additive on direct sums.** Over a normal base on which the
determinant lines of `E₁` and `E₂` each have a finite trivializing cover, `firstChernClass` of
`E₁ ⊕ E₂` is the sum of those of `E₁` and `E₂`: the determinant line of the sum is the tensor
product of the determinant lines, whose Euler class is the sum of their Euler classes. -/
theorem firstChernClass_prod_of_hasFiniteTrivializingCover
    (h₁ : HasFiniteTrivializingCover ℂ (Fin (detCore ℂ G₁ E₁).rank → ℂ)
      (detCore ℂ G₁ E₁).core.Fiber)
    (h₂ : HasFiniteTrivializingCover ℂ (Fin (detCore ℂ G₂ E₂).rank → ℂ)
      (detCore ℂ G₂ E₂).core.Fiber) :
    firstChernClass (G₁ × G₂) (E₁ ×ᵇ E₂) = firstChernClass G₁ E₁ + firstChernClass G₂ E₂ := by
  rw [firstChernClass_def, firstChernClass_def, firstChernClass_def,
    complexEulerClass_eq_of_fiberwise _ _ (continuous_detCoreProdFiberEquiv ℂ E₁ E₂)]
  exact complexEulerClass_tensorProduct (by simp) (by simp) h₁ h₂

/-- **The first Chern class of the determinant line is additive.** Over a compact normal base,
such as a compact Hausdorff one, `firstChernClass` of `E₁ ⊕ E₂` is the sum of those of `E₁` and
`E₂`. -/
theorem firstChernClass_prod [CompactSpace B] :
    firstChernClass (G₁ × G₂) (E₁ ×ᵇ E₂) = firstChernClass G₁ E₁ + firstChernClass G₂ E₂ :=
  firstChernClass_prod_of_hasFiniteTrivializingCover .of_compactSpace .of_compactSpace

end FirstChernClass

section ChernNumber

variable {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  {EM : Type} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [FiniteDimensional ℝ EM]
  [ChartedSpace EM M] (o : HomologicalOrientation M EM 2) (hn : finrank ℝ EM = 2)
  {G₁ : Type*} [NormedAddCommGroup G₁] [NormedSpace ℂ G₁] [FiniteDimensional ℂ G₁]
  {E₁ : M → Type*} [∀ x, AddCommMonoid (E₁ x)] [∀ x, Module ℂ (E₁ x)]
  [∀ x, TopologicalSpace (E₁ x)] [TopologicalSpace (TotalSpace G₁ E₁)]
  [FiberBundle G₁ E₁] [VectorBundle ℂ G₁ E₁]
  {G₂ : Type*} [NormedAddCommGroup G₂] [NormedSpace ℂ G₂] [FiniteDimensional ℂ G₂]
  {E₂ : M → Type*} [∀ x, AddCommMonoid (E₂ x)] [∀ x, Module ℂ (E₂ x)]
  [∀ x, TopologicalSpace (E₂ x)] [TopologicalSpace (TotalSpace G₂ E₂)]
  [FiberBundle G₂ E₂] [VectorBundle ℂ G₂ E₂]

/-- **The first Chern number is additive.** Over a compact surface with a homological
orientation, the first Chern number of `E₁ ⊕ E₂` is the sum of those of `E₁` and `E₂`. -/
theorem chernNumber_prod :
    chernNumber o hn (G₁ × G₂) (E₁ ×ᵇ E₂) = chernNumber o hn G₁ E₁ + chernNumber o hn G₂ E₂ := by
  rw [chernNumber_def, chernNumber_def, chernNumber_def, firstChernClass_prod, map_add,
    ULift.add_down]

end ChernNumber

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
    exact TopCat.uliftIntegralCohomologyIso_naturality_apply _ _ _

end SymplecticGeometry.Bundle

namespace Projectivization

open SymplecticGeometry.Bundle
open scoped LinearAlgebra.Projectivization

/-- **The first Chern class of the tautological line.** For a complex normed space `V`, the first
Chern class of the tautological line of `ℙ ℂ V`, read in integral cohomology, is minus the
hyperplane class.

Milestone: *First Chern class of a complex vector bundle*. -/
theorem firstChernClass_tautological (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] :
    ((TopCat.of (ℙ ℂ V)).uliftIntegralCohomologyIso 2).hom
        (firstChernClass ℂ (Tautological ℂ V)) = -hyperplaneClass V := by
  rw [hyperplaneClass_def, neg_neg, firstChernClass_eq_complexEulerClass _ (finrank_self ℂ)]

end Projectivization

end
