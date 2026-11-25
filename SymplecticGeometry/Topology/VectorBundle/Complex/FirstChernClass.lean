/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Cohomology.Empty
public import SymplecticGeometry.Topology.ContinuousMap.Defs
public import SymplecticGeometry.Topology.VectorBundle.Complex.Structure
public import SymplecticGeometry.Topology.VectorBundle.Determinant
public import SymplecticGeometry.Topology.VectorBundle.FiniteRank.EulerClass
public import SymplecticGeometry.Topology.VectorBundle.ModelEquiv
public import TauCeti.AlgebraicTopology.Cohomology.FundamentalClass
public import TauCeti.Topology.VectorBundle.Orientation.Complex.FiberwiseEquiv

/-!
# The first Chern class and the first Chern number

For a complex vector bundle `E → B` with finite-dimensional model `G`, the first Chern class
`c₁(E) ∈ H²(B; ℤ)` is the Euler class of the realification of its determinant line
`Λ^top_ℂ E`, oriented as a complex line: `SymplecticGeometry.Bundle.firstChernClass G E` is Tau
Ceti's `TauCeti.complexEulerClass` of `SymplecticGeometry.Bundle.detCore ℂ G E`. Over a compact
homologically oriented surface `M`, the first Chern number `SymplecticGeometry.Bundle.chernNumber`
is the integer `⟨c₁(E), [M]⟩`.

## Main definitions and results

* `firstChernClass G E`: the first Chern class of a complex vector bundle;
* `firstChernClass_pullback`: it is natural under pull-back along continuous maps;
* `firstChernClass_congr`: isomorphic bundles have the same class;
* `TauCeti.Bundle.ContinuousComplexStructure.firstChernClass_congr_model`: the class of the
  complex bundle of a continuous complex structure does not depend on the complex model;
* `firstChernClass_trivial`: the trivial bundle has class zero;
* `firstChernClass_eq_zero_of_finrank_eq_zero`: so has a bundle of rank zero;
* `firstChernClass_eq_complexEulerClass`: for a line bundle it is the Euler class of the bundle;
* `firstChernClass_conj`: the conjugate bundle has the opposite class;
* `chernNumber o hn G E`: the first Chern number over a compact oriented surface, with
  `chernNumber_neg_orientation`, `chernNumber_congr`, `chernNumber_trivial`, `chernNumber_conj`
  and `chernNumber_pullback` (the number of a pull-back is the degree times the number).

## Implementation notes

The class is the class of `complexEulerClass` with `r = 0`, of degree `2 * 0 + 2`, which is `2`
by computation. The argument `r := 0` is given explicitly: otherwise elaborating against the
expected degree `2` must solve `2 * ?r + 2 = 2`, which does not terminate quickly.

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

open TauCeti.FiniteRankBundleCore

/-! ### The first Chern class -/

section Class

variable {B : Type} [TopologicalSpace B]
  (G : Type*) [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  (E : B → Type*) [∀ x, AddCommMonoid (E x)] [∀ x, Module ℂ (E x)]
  [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace G E)]
  [FiberBundle G E] [VectorBundle ℂ G E]

/-- The **first Chern class** `c₁(E) ∈ H²(B; ℤ)` of a complex vector bundle `E` with
finite-dimensional model `G`: the Euler class of the determinant line `Λ^top_ℂ E`, with the
orientation of a complex line. -/
noncomputable def firstChernClass :
    (TopCat.of B).singularCohomology (ModuleCat.of ℤ (ULift ℤ)) ℤ (ModuleCat.of ℤ (ULift ℤ)) 2 :=
  complexEulerClass (r := 0) (Fin (detCore ℂ G E).rank → ℂ) (detCore ℂ G E).core.Fiber
    (finrank_detCore ℂ G E)

theorem firstChernClass_def :
    firstChernClass G E = complexEulerClass (r := 0) (Fin (detCore ℂ G E).rank → ℂ)
      (detCore ℂ G E).core.Fiber (finrank_detCore ℂ G E) := (rfl)

variable {G E} in
/-- **Isomorphic complex bundles have the same first Chern class.** The isomorphism is a family
of complex-linear equivalences of the fibres, continuous on total spaces; the two models may
differ. -/
theorem firstChernClass_congr
    {G' : Type*} [NormedAddCommGroup G'] [NormedSpace ℂ G'] [FiniteDimensional ℂ G']
    {E' : B → Type*} [∀ x, AddCommMonoid (E' x)] [∀ x, Module ℂ (E' x)]
    [∀ x, TopologicalSpace (E' x)] [TopologicalSpace (TotalSpace G' E')]
    [FiberBundle G' E'] [VectorBundle ℂ G' E'] (Φ : ∀ x, E x ≃L[ℂ] E' x)
    (hΦ : Continuous fun p : TotalSpace G E ↦ TotalSpace.mk' G' (E := E') p.proj (Φ p.proj p.snd)) :
    firstChernClass G E = firstChernClass G' E' := by
  rcases isEmpty_or_nonempty B with hB | hB
  · exact Subsingleton.elim _ _
  exact complexEulerClass_eq_of_iso (detCoreMap (VectorBundle.finrank_model_eq Φ) Φ hΦ) _ _

/-- **Naturality of the first Chern class**: `c₁(f* E) = f* c₁(E)` for a continuous map
`f : X → B`, of any type `K` with `[ContinuousMapClass K X B]`.

Milestone: *First Chern class of a complex vector bundle*. -/
theorem firstChernClass_pullback {X : Type} [TopologicalSpace X] {K : Type*} [FunLike K X B]
    [ContinuousMapClass K X B] (f : K) :
    firstChernClass G ((⇑f) *ᵖ E) =
      TopCat.singularCohomologyMap (TopCat.ofHom (f : C(X, B))) 2 (firstChernClass G E) := by
  -- The instances on `f *ᵖ E` depend on the type of `f`: pass to `(f : C(X, B))` through the
  -- identity of each fibre.
  rw [← firstChernClass_congr (E := ⇑(f : C(X, B)) *ᵖ E) (E' := (⇑f) *ᵖ E)
    (fun _ ↦ ContinuousLinearEquiv.refl ℂ _)
    (continuous_id.congr fun _ ↦ rfl), firstChernClass_def, firstChernClass_def,
    ← complexEulerClass_pullback (detCore ℂ G E) (f : C(X, B)) (finrank_detCore ℂ G E)]
  exact complexEulerClass_eq_of_iso (eqToIso (detCore_pullback ℂ G E (f : C(X, B)))) _ _

/-- **The first Chern class of a complex structure does not depend on the complex model.** For a
continuous complex structure `J` on a real vector bundle `V`, the complex bundle `J.Fiber` has the
same first Chern class with the complex model `G` as with the complex model `G'`. -/
theorem _root_.TauCeti.Bundle.ContinuousComplexStructure.firstChernClass_congr_model
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {V : B → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
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

variable (B) in
/-- **The trivial bundle has first Chern class zero.** -/
@[simp] theorem firstChernClass_trivial : firstChernClass G (Bundle.Trivial B G) = 0 := by
  rw [firstChernClass_def, complexEulerClass_eq_of_iso (detCoreTrivialIso ℂ B G) _
    (by simp : finrank ℂ (Fin (trivial ℂ B 1).rank → ℂ) = 0 + 1)]
  refine complexEulerClass_eq_zero_of_forall_ne_zero _ _ _ (s := fun _ _ ↦ 1)
    (continuous_trivial_iff.2 ⟨continuous_id, continuous_const⟩)
    fun _ h ↦ one_ne_zero (congrFun h ⟨0, Nat.one_pos⟩)

/-- **A bundle of rank zero has first Chern class zero.** -/
theorem firstChernClass_eq_zero_of_finrank_eq_zero (hG : finrank ℂ G = 0) :
    firstChernClass G E = 0 := by
  have : Subsingleton G := Module.finrank_zero_iff.1 hG
  -- A bundle of rank zero is isomorphic to the trivial bundle, through any trivializations.
  let φ (b : B) : E b ≃L[ℂ] Bundle.Trivial B G b :=
    VectorBundle.continuousLinearEquivAt ℂ G E b
  have hφ : Continuous fun v : TotalSpace G E ↦
      TotalSpace.mk' G (E := Bundle.Trivial B G) v.proj (φ v.proj v.snd) :=
    ((Trivial.homeomorphProd B G).symm.continuous.comp
      ((FiberBundle.continuous_proj G E).prodMk (continuous_const (y := (0 : G))))).congr
      fun v ↦ congrArg (TotalSpace.mk v.proj) (Subsingleton.elim _ _)
  rw [firstChernClass_congr φ hφ, firstChernClass_trivial]

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
  rw [firstChernClass_def,
    complexEulerClass_eq_of_iso (detCoreIsoOfFinrankEqOne ℂ E (by simpa using hG)) _
    (by simpa using hG : finrank ℂ (Fin (ofBundleOfFinrankEq ℂ G E rfl).rank → ℂ) = 0 + 1)]
  refine complexEulerClass_eq_of_fiberwise hG _
    (φ := ofBundleOfFinrankEqFiberEquiv ℂ G E rfl) ?_
  exact (ofBundleOfFinrankEqHomeomorph ℂ G E rfl).continuous.congr fun p ↦ by
    rw [ofBundleOfFinrankEqHomeomorph_apply]

/-- **The first Chern class of the conjugate bundle** is the opposite of that of the bundle:
`c₁(Ē) = -c₁(E)`. -/
@[simp]
theorem firstChernClass_conj
    (E : B → Type*) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace G E)]
    [FiberBundle G E] [VectorBundle ℂ G E] :
    firstChernClass (Conjugate G) (ConjugateBundle E) = -firstChernClass G E :=
  complexEulerClass_eq_neg_of_finrank_eq_one_of_conjugateFiberwise _ _
    (continuous_detCoreConjugateFiberwise E)

end Class

/-! ### The first Chern number over a surface -/

section Number

variable {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  {EM : Type} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [FiniteDimensional ℝ EM]
  [ChartedSpace EM M] (o : HomologicalOrientation M EM 2) (hn : finrank ℝ EM = 2)
  (G : Type*) [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  (E : M → Type*) [∀ x, AddCommMonoid (E x)] [∀ x, Module ℂ (E x)]
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
    {E' : M → Type*} [∀ x, AddCommMonoid (E' x)] [∀ x, Module ℂ (E' x)]
    [∀ x, TopologicalSpace (E' x)] [TopologicalSpace (TotalSpace G' E')]
    [FiberBundle G' E'] [VectorBundle ℂ G' E'] (Φ : ∀ x, E x ≃L[ℂ] E' x)
    (hΦ : Continuous fun p : TotalSpace G E ↦ TotalSpace.mk' G' (E := E') p.proj (Φ p.proj p.snd)) :
    chernNumber o hn G E = chernNumber o hn G' E' := by
  rw [chernNumber_def, chernNumber_def, firstChernClass_congr Φ hΦ]

/-- **The trivial bundle has first Chern number zero.** -/
@[simp] theorem chernNumber_trivial : chernNumber o hn G (Bundle.Trivial M G) = 0 := by
  rw [chernNumber_def, firstChernClass_trivial, map_zero, ULift.zero_down]

/-- **The first Chern number of the conjugate bundle** is the opposite of that of the bundle. -/
@[simp]
theorem chernNumber_conj
    (E : M → Type*) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace G E)]
    [FiberBundle G E] [VectorBundle ℂ G E] :
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
  rw [chernNumber_def, chernNumber_def, firstChernClass_pullback,
    HomologicalOrientation.evalFundamentalClass_id_singularCohomologyMap_eq_degree_smul o' hn' _
      o hn (f : C(M', M)), ULift.smul_down, smul_eq_mul]

end Number

end Bundle

end SymplecticGeometry
