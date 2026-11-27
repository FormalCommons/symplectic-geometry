/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.FundamentalClass
public import TauCeti.Topology.VectorBundle.Determinant.Conjugate
public import TauCeti.Topology.VectorBundle.Orientation.Complex.Conjugate
public import TauCeti.Topology.VectorBundle.Orientation.Complex.FiberwiseEquiv
public import TauCeti.Topology.VectorBundle.Orientation.Complex.FirstChernClass
public import TauCeti.Topology.VectorBundle.Complex.Structure
import SymplecticGeometry.Topology.ContinuousMap.Defs
import SymplecticGeometry.Topology.VectorBundle.Complex.Structure
import SymplecticGeometry.Topology.VectorBundle.DetBundle.CongrModel

/-!
# The first Chern class and the first Chern number

For a complex vector bundle `E → B` with finite-dimensional model `G`, the first Chern class
`c₁(E) ∈ H²(B; ℤ)` is Tau Ceti's `TauCeti.firstChernClass G E`, the first Chern class of the
determinant line `TauCeti.DetBundle ℂ G E`. Tau Ceti proves its naturality
(`TauCeti.firstChernClass_pullback`), its invariance under isomorphisms with the same model
(`TauCeti.firstChernClass_eq_of_fiberwise`) and its vanishing for a trivial bundle and in rank zero
(`TauCeti.firstChernClass_trivial`, `TauCeti.firstChernClass_eq_zero_of_finrank_eq_zero`). This
file adds what Tau Ceti does not have, and defines the first Chern number over a compact
homologically oriented surface `M`, the integer `⟨c₁(E), [M]⟩`.

## Main definitions and results

* `firstChernClass_congr`: isomorphic bundles have the same class, even with different models
  (from `TauCeti.DetBundle.congrModelHomeomorph`);
* `TauCeti.Bundle.ContinuousComplexStructure.firstChernClass_congr_model`: the class of the
  complex bundle of a continuous complex structure does not depend on the complex model;
* `firstChernClass_pullback_coe`: naturality along a map of any type `K` with
  `[ContinuousMapClass K X B]`, from `TauCeti.firstChernClass_pullback` along `(f : C(X, B))`;
* `firstChernClass_eq_complexEulerClass`: for a line bundle it is the Euler class of the bundle
  (from `TauCeti.firstChernClass_eq_lineFirstChernClass`);
* `firstChernClass_conj`: the conjugate bundle has the opposite class
  (from `TauCeti.DetBundle.conjugateHomeomorph`);
* `chernNumber o hn G E`: the first Chern number over a compact oriented surface, with
  `chernNumber_neg_orientation`, `chernNumber_congr`, `chernNumber_trivial`, `chernNumber_conj`
  and `chernNumber_pullback` (the number of a pull-back is the degree times the number).

## Implementation notes

Tau Ceti's Euler classes take the fibres in the universe of the base, so the fibres `E x` are in
`Type`, like the base.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §14 (the top Chern class of a complex bundle as the Euler class of its
  realification, and the first Chern class through the determinant line).
* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.7.
-/

public section

open Bundle CategoryTheory Module TauCeti TauCeti.Conjugate

namespace SymplecticGeometry

namespace Bundle

/-! ### The first Chern class -/

section Class

variable {B : Type} [TopologicalSpace B]
  (G : Type*) [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  (E : B → Type) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace G E)]
  [FiberBundle G E] [VectorBundle ℂ G E]

variable {G E} in
/-- **Isomorphic complex bundles have the same first Chern class.** The isomorphism is a family
of complex-linear equivalences of the fibres, continuous on total spaces; the two models may
differ. -/
theorem firstChernClass_congr
    {G' : Type*} [NormedAddCommGroup G'] [NormedSpace ℂ G'] [FiniteDimensional ℂ G']
    {E' : B → Type} [∀ x, AddCommGroup (E' x)] [∀ x, Module ℂ (E' x)]
    [∀ x, TopologicalSpace (E' x)] [TopologicalSpace (TotalSpace G' E')]
    [FiberBundle G' E'] [VectorBundle ℂ G' E'] (Φ : ∀ x, E x ≃L[ℂ] E' x)
    (hΦ : Continuous fun p : TotalSpace G E ↦ TotalSpace.mk' G' (E := E') p.proj (Φ p.proj p.snd)) :
    firstChernClass G E = firstChernClass G' E' := by
  rw [firstChernClass_def, firstChernClass_def, lineFirstChernClass_def, lineFirstChernClass_def]
  exact complexEulerClass_eq_of_fiberwise _ _
    (φ := DetBundle.congrModelEquiv (F₁ := G) (F' := G') Φ)
    ((DetBundle.congrModelHomeomorph Φ hΦ).continuous.congr fun p ↦
      DetBundle.congrModelHomeomorph_apply Φ hΦ p)

/-- **Naturality of the first Chern class along a map of any `ContinuousMapClass`**:
`c₁(f* E) = f* c₁(E)` for `f : K` with `[ContinuousMapClass K X B]`. The pull-back `(⇑f) *ᵖ E`
carries the instances found through `K`, not those of `⇑(f : C(X, B)) *ᵖ E` in
`TauCeti.firstChernClass_pullback`.

Milestone: *First Chern class of a complex vector bundle*. -/
theorem firstChernClass_pullback_coe {X : Type} [TopologicalSpace X] {K : Type*} [FunLike K X B]
    [ContinuousMapClass K X B] (f : K) :
    firstChernClass G ((⇑f) *ᵖ E) =
      TopCat.singularCohomologyMap (TopCat.ofHom (f : C(X, B))) 2 (firstChernClass G E) := by
  -- Pass to `(f : C(X, B))` through the identity of each fibre.
  rw [← firstChernClass_pullback]
  exact firstChernClass_eq_of_fiberwise (φ := fun _ ↦ ContinuousLinearEquiv.refl ℂ _)
    (continuous_id.congr fun _ ↦ rfl)

/-- **The first Chern class of a complex structure does not depend on the complex model.** For a
continuous complex structure `J` on a real vector bundle `V`, the complex bundle `J.Fiber` has the
same first Chern class with the complex model `G` as with the complex model `G'`. -/
theorem _root_.TauCeti.Bundle.ContinuousComplexStructure.firstChernClass_congr_model
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {V : B → Type} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
    [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
    [∀ x, ContinuousSMul ℝ (V x)] [TopologicalSpace (TotalSpace F V)]
    [FiberBundle F V] [VectorBundle ℝ F V] (J : TauCeti.Bundle.ContinuousComplexStructure F V)
    [Fact (finrank ℝ F = 2 * finrank ℂ G)]
    (G' : Type*) [NormedAddCommGroup G'] [NormedSpace ℂ G'] [FiniteDimensional ℂ G']
    [Fact (finrank ℝ F = 2 * finrank ℂ G')] :
    firstChernClass G' J.Fiber = firstChernClass G J.Fiber := by
  -- The identity of `V` intertwines `J` with itself.
  have hc : ∀ x v, ContinuousLinearEquiv.refl ℝ (V x) (J x v) =
      J x (ContinuousLinearEquiv.refl ℝ (V x) v) := fun _ _ ↦ rfl
  exact (firstChernClass_congr (J.fiberEquivOfCommute J _ hc)
    (J.continuous_fiberEquivOfCommute J _ hc (continuous_id.congr fun _ ↦ rfl))).symm

/-- **The first Chern class of a line bundle** is the Euler class of the bundle itself, with the
orientation of a complex line.

Milestone: *First Chern class of a complex vector bundle*. -/
theorem firstChernClass_eq_complexEulerClass
    {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace ℂ G] [IsScalarTower ℝ ℂ G]
    [FiniteDimensional ℂ G]
    (E : B → Type) [TopologicalSpace (TotalSpace G E)] [∀ x, AddCommGroup (E x)]
    [∀ x, Module ℝ (E x)] [∀ x, Module ℂ (E x)] [∀ x, IsScalarTower ℝ ℂ (E x)]
    [∀ x, TopologicalSpace (E x)] [FiberBundle G E] [VectorBundle ℂ G E]
    (hG : finrank ℂ G = 0 + 1) :
    firstChernClass G E = complexEulerClass G E hG := by
  rw [firstChernClass_eq_lineFirstChernClass hG, lineFirstChernClass_def]

/-- **The first Chern class of the conjugate bundle** is the opposite of that of the bundle:
`c₁(Ē) = -c₁(E)`. -/
@[simp]
theorem firstChernClass_conj :
    firstChernClass (Conjugate G) (ConjugateBundle E) = -firstChernClass G E := by
  -- The determinant line of `Ē` is the conjugate of the determinant line of `E`.
  rw [firstChernClass_def, firstChernClass_def, lineFirstChernClass_def, lineFirstChernClass_def,
    complexEulerClass_eq_of_fiberwise (finrank_complex.trans (finrank_self ℂ)) _
      (φ := DetBundle.conjugateEquiv (F := G) (E := E))
      ((DetBundle.conjugateHomeomorph (F := G) (E := E)).continuous.congr fun p ↦
        DetBundle.conjugateHomeomorph_apply p)]
  exact complexEulerClass_conjugateBundle_eq_neg_of_finrank_eq_one _

end Class

/-! ### The first Chern number over a surface -/

section Number

variable {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  {EM : Type} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [FiniteDimensional ℝ EM]
  [ChartedSpace EM M] (o : HomologicalOrientation M EM 2) (hn : finrank ℝ EM = 2)
  (G : Type*) [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  (E : M → Type) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace G E)]
  [FiberBundle G E] [VectorBundle ℂ G E]

/-- The **first Chern number** `⟨c₁(E), [M]⟩ ∈ ℤ` of a complex vector bundle `E` over a compact
surface `M` with homological orientation `o`: the first Chern class evaluated on the fundamental
class. -/
noncomputable def chernNumber : ℤ :=
  (o.evalFundamentalClass hn (ModuleCat.of ℤ (ULift ℤ)) (ContinuousMap.id M)
    (firstChernClass G E)).down

theorem chernNumber_def :
    chernNumber o hn G E =
      (o.evalFundamentalClass hn (ModuleCat.of ℤ (ULift ℤ)) (ContinuousMap.id M)
        (firstChernClass G E)).down := (rfl)

/-- Reversing the orientation of the surface negates the first Chern number. -/
@[simp] theorem chernNumber_neg_orientation : chernNumber (-o) hn G E = -chernNumber o hn G E := by
  rw [chernNumber_def, chernNumber_def, HomologicalOrientation.evalFundamentalClass_neg,
    LinearMap.neg_apply, ULift.neg_down]

variable {G E} in
/-- **Isomorphic complex bundles have the same first Chern number.** -/
theorem chernNumber_congr
    {G' : Type*} [NormedAddCommGroup G'] [NormedSpace ℂ G'] [FiniteDimensional ℂ G']
    {E' : M → Type} [∀ x, AddCommGroup (E' x)] [∀ x, Module ℂ (E' x)]
    [∀ x, TopologicalSpace (E' x)] [TopologicalSpace (TotalSpace G' E')]
    [FiberBundle G' E'] [VectorBundle ℂ G' E'] (Φ : ∀ x, E x ≃L[ℂ] E' x)
    (hΦ : Continuous fun p : TotalSpace G E ↦ TotalSpace.mk' G' (E := E') p.proj (Φ p.proj p.snd)) :
    chernNumber o hn G E = chernNumber o hn G' E' := by
  rw [chernNumber_def, chernNumber_def, firstChernClass_congr Φ hΦ]

/-- **The trivial bundle has first Chern number zero.** -/
@[simp] theorem chernNumber_trivial (G : Type) [NormedAddCommGroup G] [NormedSpace ℂ G]
    [FiniteDimensional ℂ G] : chernNumber o hn G (Bundle.Trivial M G) = 0 := by
  rw [chernNumber_def, firstChernClass_trivial, map_zero, ULift.zero_down]

/-- **The first Chern number of the conjugate bundle** is the opposite of that of the bundle. -/
@[simp]
theorem chernNumber_conj :
    chernNumber o hn (Conjugate G) (ConjugateBundle E) = -chernNumber o hn G E := by
  rw [chernNumber_def, chernNumber_def, firstChernClass_conj, map_neg, ULift.neg_down]

/-- **The first Chern number of a pull-back** along a continuous map `f : M' → M` of compact
oriented surfaces, `M` preconnected, is the degree of `f` times the number of the bundle:
`⟨c₁(f* E), [M']⟩ = deg f * ⟨c₁(E), [M]⟩`. -/
theorem chernNumber_pullback [PreconnectedSpace M]
    {M' : Type} [TopologicalSpace M'] [T2Space M'] [CompactSpace M']
    {EM' : Type} [NormedAddCommGroup EM'] [NormedSpace ℝ EM'] [FiniteDimensional ℝ EM']
    [ChartedSpace EM' M'] (o' : HomologicalOrientation M' EM' 2) (hn' : finrank ℝ EM' = 2)
    {K : Type*} [FunLike K M' M] [ContinuousMapClass K M' M] (f : K) :
    chernNumber o' hn' G ((⇑f) *ᵖ E) = o'.degree o hn' (f : C(M', M)) * chernNumber o hn G E := by
  rw [chernNumber_def, chernNumber_def, firstChernClass_pullback_coe,
    HomologicalOrientation.evalFundamentalClass_id_singularCohomologyMap_eq_degree_smul o' hn' _
      o hn (f : C(M', M)), ULift.smul_down, smul_eq_mul]

end Number

end Bundle

end SymplecticGeometry
