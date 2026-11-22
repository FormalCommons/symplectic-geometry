/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.EulerClass
public import TauCeti.Topology.VectorBundle.Thom.Connectivity
public import SymplecticGeometry.Topology.VectorBundle.Smul

/-!
# The exact sequence of the Thom pair with the base in place of the total space

This file is a part of Tau Ceti's file `TauCeti/Topology/VectorBundle/EulerClass.lean`, copied
from Tau Ceti's main branch at commit `aa1b4e9e2a`, which the pinned version of Tau Ceti does not
yet have. It contains only the declarations below; the rest of Tau Ceti's file is in the pinned
version, which this file imports. The changes are these:

* `TauCeti.zeroSectionComplProj` and `TauCeti.zeroSectionComplProj_apply`, which Tau Ceti's file
  declares in its section `ThomClass`, are left out: the pinned version has them in
  `TauCeti/Topology/VectorBundle/Thom/Connectivity.lean`, which this file imports.
* The pinned version exposes the bodies of neither `TauCeti.thomPairProj` nor
  `TauCeti.zeroSectionComplProj`, so `TauCeti.zeroSectionComplProjHom_def`, proved by `rfl` in
  Tau Ceti, is proved pointwise from `TauCeti.zeroSectionComplProj_apply` and
  `TauCeti.thomPairProj_apply`, and `TauCeti.zeroSectionComplProjHom_apply`, proved from
  `TauCeti.thomPairProj_apply` in Tau Ceti, is proved from `TauCeti.zeroSectionComplProj_apply`.
* The paragraph below leaves out Tau Ceti's citations of
  `TauCeti.isIso_singularCohomologyMap_zeroSectionHom` and
  `TauCeti.isIso_singularCohomologyMap_thomPairProj`, which this file does not copy.
* `TauCeti.VectorBundle.totalSpaceHomotopyEquiv` comes from
  `SymplecticGeometry.Topology.VectorBundle.Smul`, the copy of Tau Ceti's main branch.

The projection `π : E → B` is a homotopy equivalence with homotopy inverse the zero section
(`TauCeti.VectorBundle.totalSpaceHomotopyEquiv`), so pullback along the zero section is an
isomorphism `Hⁿ(E) ≅ Hⁿ(B)` with inverse `π^*`
(`TauCeti.singularCohomologyMap_zeroSectionHom_comp_singularCohomologyMap_thomPairProj`).
Replacing `Hⁿ(E)` by `Hⁿ(B)` in the long exact sequence of the Thom pair gives the exact sequence

`⋯ ⟶ Hᵐ(E, E₀) ⟶ Hᵐ(B) ⟶ Hᵐ(E₀) ⟶ Hᵐ⁺¹(E, E₀) ⟶ Hᵐ⁺¹(B) ⟶ ⋯`

of the Euler class maps, the pullback along the restriction `π₀ : E₀ → B` of the projection
(`TauCeti.zeroSectionComplProjHom`) and the connecting morphisms of the pair
(`TauCeti.exact_eulerClass_singularCohomologyMap_zeroSectionComplProjHom`,
`TauCeti.exact_singularCohomologyMap_zeroSectionComplProjHom_singularCohomologyδ`,
`TauCeti.exact_singularCohomologyδ_eulerClass`), the start of the Gysin sequence.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §9 (the fundamental class `u ∈ Hⁿ(E, E₀; ℤ)` of an oriented bundle, the Euler
  class, its naturality and its vanishing for a bundle with a nowhere-zero section), §10 (the
  Thom isomorphism) and §12 (the exact sequence of the pair `(E, E₀)` in the proof of the Gysin
  sequence, Theorem 12.2).
* A. Hatcher, *Vector Bundles and K-Theory*, §4.D (Thom classes).
-/

public section

noncomputable section

open Bundle CategoryTheory Limits Set Module

universe w v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] {R : C}
  {k : Type*} [Ring k] [Linear k C] {M : C}

section ThomClass

variable {B : Type w} [TopologicalSpace B] (F : Type*) [TopologicalSpace F] (E : B → Type w)
  [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  [∀ b, Zero (E b)]

/-- The projection `π₀ : E₀ → B` (`TauCeti.zeroSectionComplProj`) as a morphism of topological
spaces out of the subspace of the Thom pair. -/
def zeroSectionComplProjHom : (thomPair F E).snd ⟶ TopCat.of B :=
  TopCat.ofHom (zeroSectionComplProj F E)

theorem zeroSectionComplProjHom_def :
    zeroSectionComplProjHom F E = (thomPair F E).map ≫ thomPairProj F E :=
  TopCat.ext fun _ ↦ (zeroSectionComplProj_apply F E _).trans (thomPairProj_apply F E _).symm

@[simp]
theorem zeroSectionComplProjHom_apply (v : zeroSectionCompl F E) :
    zeroSectionComplProjHom F E v = (v : TotalSpace F E).proj :=
  zeroSectionComplProj_apply F E v

end ThomClass

section EulerClass

variable {B : Type w} [TopologicalSpace B] (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
  (E : B → Type w) [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]

/-- The zero section followed by the projection is the identity of the base. -/
@[reassoc (attr := simp)]
theorem zeroSectionHom_comp_thomPairProj : zeroSectionHom F E ≫ thomPairProj F E = 𝟙 _ :=
  TopCat.ext fun b ↦ by
    rw [ConcreteCategory.comp_apply, zeroSectionHom_apply, thomPairProj_apply]
    rfl

variable (R k M) in
/-- Pulling a class of the base back to the total space and then along the zero section gives the
class back. -/
@[reassoc (attr := simp)]
theorem singularCohomologyMap_thomPairProj_comp_singularCohomologyMap_zeroSectionHom (n : ℕ) :
    TopCat.singularCohomologyMap (R := R) (k := k) (M := M) (thomPairProj F E) n ≫
      TopCat.singularCohomologyMap (zeroSectionHom F E) n = 𝟙 _ := by
  rw [← TopCat.singularCohomologyMap_comp, zeroSectionHom_comp_thomPairProj,
    TopCat.singularCohomologyMap_id]

variable (R k M) in
/-- **The zero section induces an isomorphism on cohomology**, with inverse the pullback along the
projection (`TauCeti.VectorBundle.totalSpaceHomotopyEquiv`): pulling a class of the total space
back along the zero section and then to the total space gives the class back. -/
@[reassoc (attr := simp)]
theorem singularCohomologyMap_zeroSectionHom_comp_singularCohomologyMap_thomPairProj (n : ℕ) :
    TopCat.singularCohomologyMap (R := R) (k := k) (M := M) (zeroSectionHom F E) n ≫
      TopCat.singularCohomologyMap (thomPairProj F E) n = 𝟙 _ := by
  let e := VectorBundle.totalSpaceHomotopyEquiv F E
  have hπ : TopCat.ofHom e.toFun = thomPairProj F E :=
    TopCat.ext fun v ↦ (congrFun (VectorBundle.coe_totalSpaceHomotopyEquiv F E) v).trans
      (thomPairProj_apply F E v).symm
  have hs : TopCat.ofHom e.invFun = zeroSectionHom F E :=
    TopCat.ext fun b ↦ (congrFun (VectorBundle.coe_totalSpaceHomotopyEquiv_symm F E) b).trans
      (zeroSectionHom_apply F E b).symm
  have h := (e.singularCohomologyIso R k M n).inv_hom_id
  rwa [ContinuousMap.HomotopyEquiv.singularCohomologyIso_hom,
    ContinuousMap.HomotopyEquiv.singularCohomologyIso_inv, hπ, hs] at h

variable {F E} in
@[simp]
theorem singularCohomologyMap_zeroSectionHom_singularCohomologyMap_thomPairProj_apply {n : ℕ}
    (x : (TopCat.of B).singularCohomology R k M n) :
    TopCat.singularCohomologyMap (zeroSectionHom F E) n
      (TopCat.singularCohomologyMap (thomPairProj F E) n x) = x := by
  rw [← ConcreteCategory.comp_apply,
    singularCohomologyMap_thomPairProj_comp_singularCohomologyMap_zeroSectionHom,
    ConcreteCategory.id_apply]

variable {F E} in
@[simp]
theorem singularCohomologyMap_thomPairProj_singularCohomologyMap_zeroSectionHom_apply {n : ℕ}
    (x : (thomPair F E).fst.singularCohomology R k M n) :
    TopCat.singularCohomologyMap (thomPairProj F E) n
      (TopCat.singularCohomologyMap (zeroSectionHom F E) n x) = x := by
  rw [← ConcreteCategory.comp_apply,
    singularCohomologyMap_zeroSectionHom_comp_singularCohomologyMap_thomPairProj,
    ConcreteCategory.id_apply]

variable (R k M)

/-- **Exactness at the cohomology of the base**: `Hᵐ(E, E₀) ⟶ Hᵐ(B) ⟶ Hᵐ(E₀)`, the Euler class map
followed by the pullback along `π₀ : E₀ → B`, is exact. -/
theorem exact_eulerClass_singularCohomologyMap_zeroSectionComplProjHom (m : ℕ) :
    Function.Exact (eulerClass R k M F E m)
      (TopCat.singularCohomologyMap (zeroSectionComplProjHom F E) m) := by
  have hex : Function.Exact ((thomPair F E).singularCohomologyπ R k M m)
      (TopCat.singularCohomologyMap (thomPair F E).map m) :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      ((thomPair F E).singularCohomology_exact_space R k M m)
  -- Transport exactness of `Hᵐ(E, E₀) ⟶ Hᵐ(E) ⟶ Hᵐ(E₀)` along `π^* : Hᵐ(B) ≅ Hᵐ(E)`.
  intro y
  rw [zeroSectionComplProjHom_def, TopCat.singularCohomologyMap_comp, ConcreteCategory.comp_apply,
    hex]
  refine ⟨fun ⟨x, hx⟩ ↦ ⟨x, ?_⟩, fun ⟨x, hx⟩ ↦ ⟨x, ?_⟩⟩
  · rw [eulerClass_def, ConcreteCategory.comp_apply, hx,
      singularCohomologyMap_zeroSectionHom_singularCohomologyMap_thomPairProj_apply]
  · rw [← hx, eulerClass_def, ConcreteCategory.comp_apply,
      singularCohomologyMap_thomPairProj_singularCohomologyMap_zeroSectionHom_apply]

/-- **Exactness at the cohomology of `E₀`**: `Hˡ(B) ⟶ Hˡ(E₀) ⟶ Hᵐ(E, E₀)`, the pullback along
`π₀ : E₀ → B` followed by the connecting morphism of the pair `(E, E₀)`, is exact, for
`l + 1 = m`. -/
theorem exact_singularCohomologyMap_zeroSectionComplProjHom_singularCohomologyδ (l m : ℕ)
    (hl : l + 1 = m) :
    Function.Exact (TopCat.singularCohomologyMap (zeroSectionComplProjHom F E) l)
      ((thomPair F E).singularCohomologyδ R k M l m hl) := by
  have hex : Function.Exact (TopCat.singularCohomologyMap (thomPair F E).map l)
      ((thomPair F E).singularCohomologyδ R k M l m hl) :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      ((thomPair F E).singularCohomology_exact_subspace R k M l m hl)
  -- Transport exactness of `Hˡ(E) ⟶ Hˡ(E₀) ⟶ Hᵐ(E, E₀)` along `π^* : Hˡ(B) ≅ Hˡ(E)`.
  intro y
  rw [hex, zeroSectionComplProjHom_def, TopCat.singularCohomologyMap_comp]
  refine ⟨fun ⟨x, hx⟩ ↦ ⟨TopCat.singularCohomologyMap (zeroSectionHom F E) l x, ?_⟩,
    fun ⟨x, hx⟩ ↦ ⟨TopCat.singularCohomologyMap (thomPairProj F E) l x, hx⟩⟩
  rwa [ConcreteCategory.comp_apply,
    singularCohomologyMap_thomPairProj_singularCohomologyMap_zeroSectionHom_apply]

/-- **Exactness at relative cohomology**: `Hˡ(E₀) ⟶ Hᵐ(E, E₀) ⟶ Hᵐ(B)`, the connecting morphism of
the pair `(E, E₀)` followed by the Euler class map, is exact, for `l + 1 = m`. -/
theorem exact_singularCohomologyδ_eulerClass (l m : ℕ) (hl : l + 1 = m) :
    Function.Exact ((thomPair F E).singularCohomologyδ R k M l m hl) (eulerClass R k M F E m) := by
  have hex : Function.Exact ((thomPair F E).singularCohomologyδ R k M l m hl)
      ((thomPair F E).singularCohomologyπ R k M m) :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      ((thomPair F E).singularCohomology_exact_relative R k M l m hl)
  -- The Euler class map is `Hᵐ(E, E₀) ⟶ Hᵐ(E)` followed by the isomorphism `s^*`.
  intro y
  rw [← hex y, eulerClass_def, ConcreteCategory.comp_apply]
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, map_zero]⟩
  rw [← singularCohomologyMap_thomPairProj_singularCohomologyMap_zeroSectionHom_apply
    ((thomPair F E).singularCohomologyπ R k M m y), h, map_zero]

end EulerClass

end TauCeti
