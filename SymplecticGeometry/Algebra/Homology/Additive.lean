/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Algebra.Homology.HomologicalComplex.Basic

/-!
# Chain maps into and out of a complex mapped along a functor

Let `F : C ⥤ D` be an additive functor, `K` a homological complex in `C`, `L` one in `D`, and
`φ : F(K) ⟶ L` a chain map from the complex `K` mapped along `F`. Through the identification
`ShortComplex.mapCyclesIso` of the cycles of `F(K)` with `F` applied to the cycles of `K`:

* `HomologicalComplex.mapCyclesIso_inv_comp_cyclesMap_comp_iCycles`: when `F` preserves the left
  homology of `K` in the degree considered, the map that `φ` induces on cycles is `φ` on the
  underlying chains;
* `map_homologyπ_comp_mapHomologicalComplexCompHomologyFunctorIso_inv_app_comp_homologyMap`:
  when both categories have homology and `F` preserves it, the map that `φ` induces on homology,
  after the comparison `Functor.mapHomologicalComplexCompHomologyFunctorIso`, sends `F` applied
  to the class of a cycle to the class of its image under `φ`.

For a chain map `ψ : K ⟶ F(L)` into the complex `L` mapped along `F`, in the other direction:

* `HomologicalComplex.cyclesMap_comp_mapCyclesIso_hom_comp_map_iCycles`: when `F` preserves the
  left homology of `L` in the degree considered, the map that `ψ` induces on cycles, read in `F`
  applied to the cycles of `L`, is `ψ` on the underlying chains;
* `homologyπ_comp_homologyMap_comp_mapHomologicalComplexCompHomologyFunctorIso_hom_app`: when both
  categories have homology and `F` preserves it, the map that `ψ` induces on homology, after the
  comparison `Functor.mapHomologicalComplexCompHomologyFunctorIso`, sends the class of a cycle to
  `F` applied to the class of its image under `ψ`.

These are Tau Ceti's
`CategoryTheory.Functor.mapCyclesIso_inv_comp_cyclesMap_comp_mapCyclesIso_hom_comp_map_iCycles`
and `HomologicalComplex.cyclesComparison_homologyπ`, for a source or a target that is not itself
mapped along a functor, proved by the same steps.
-/

public section

open CategoryTheory

namespace HomologicalComplex

section Cycles

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  (F : C ⥤ D) [F.Additive] {ι : Type*} {c : ComplexShape ι} {K : HomologicalComplex C c}
  {L : HomologicalComplex D c} (φ : (F.mapHomologicalComplex c).obj K ⟶ L) (i : ι)
  [K.HasHomology i] [F.PreservesLeftHomologyOf (K.sc i)]
  [((F.mapHomologicalComplex c).obj K).HasHomology i] [L.HasHomology i]

/-- A chain map `φ : F(K) ⟶ L` acts on cycles as on chains: through the identification
`ShortComplex.mapCyclesIso` of the cycles of `F(K)` with `F` applied to the cycles of `K`, the
map `φ` induces on cycles followed by the inclusion of the cycles of `L` is `F` applied to the
inclusion of the cycles of `K` followed by `φ`. -/
@[reassoc, elementwise nosimp]
theorem mapCyclesIso_inv_comp_cyclesMap_comp_iCycles :
    ((K.sc i).mapCyclesIso F).inv ≫ cyclesMap φ i ≫ L.iCycles i =
      F.map (K.iCycles i) ≫ φ.f i := by
  rw [cyclesMap_i]
  exact (K.sc i).mapCyclesIso_inv_comp_iCycles_assoc F _

end Cycles

section CyclesInto

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  (F : C ⥤ D) [F.Additive] {ι : Type*} {c : ComplexShape ι} {K : HomologicalComplex D c}
  {L : HomologicalComplex C c} (ψ : K ⟶ (F.mapHomologicalComplex c).obj L) (i : ι)
  [L.HasHomology i] [F.PreservesLeftHomologyOf (L.sc i)]
  [((F.mapHomologicalComplex c).obj L).HasHomology i] [K.HasHomology i]

/-- A chain map `ψ : K ⟶ F(L)` acts on cycles as on chains: the map `ψ` induces on cycles, read
through the identification `ShortComplex.mapCyclesIso` of the cycles of `F(L)` with `F` applied
to the cycles of `L`, followed by `F` applied to the inclusion of the cycles of `L`, is the
inclusion of the cycles of `K` followed by `ψ`. -/
@[reassoc, elementwise nosimp]
theorem cyclesMap_comp_mapCyclesIso_hom_comp_map_iCycles :
    cyclesMap ψ i ≫ ((L.sc i).mapCyclesIso F).hom ≫ F.map (L.iCycles i) =
      K.iCycles i ≫ ψ.f i :=
  -- `(L.sc i).map F` is the short complex of `F(L)` in degree `i` only up to unfolding.
  (congrArg (cyclesMap ψ i ≫ ·) ((L.sc i).mapCyclesIso_hom_iCycles F)).trans (cyclesMap_i ψ i)

end CyclesInto

section Homology

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  [CategoryWithHomology C] [CategoryWithHomology D] (F : C ⥤ D) [F.Additive]
  [F.PreservesHomology] {ι : Type*} {c : ComplexShape ι} {K : HomologicalComplex C c}
  {L : HomologicalComplex D c} (φ : (F.mapHomologicalComplex c).obj K ⟶ L) (i : ι)
/-- A chain map `φ : F(K) ⟶ L` acts on classes as on cycles: the map `φ` induces on homology,
after the comparison `Functor.mapHomologicalComplexCompHomologyFunctorIso` of the homology of
`F(K)` with `F` applied to the homology of `K`, sends `F` applied to the class of a cycle of `K`
to the class of the cycle of `L` that `φ` gives. -/
@[reassoc, elementwise nosimp]
theorem map_homologyπ_comp_mapHomologicalComplexCompHomologyFunctorIso_inv_app_comp_homologyMap :
    F.map (K.homologyπ i) ≫ (F.mapHomologicalComplexCompHomologyFunctorIso c i).inv.app K ≫
        homologyMap φ i =
      ((K.sc i).mapCyclesIso F).inv ≫ cyclesMap φ i ≫ L.homologyπ i := by
  rw [Functor.map_homologyπ_comp_mapHomologicalComplexCompHomologyFunctorIso_inv_app_assoc,
    homologyπ_naturality]

/-- A chain map `ψ : K ⟶ F(L)` acts on classes as on cycles: the map `ψ` induces on homology,
followed by the comparison `Functor.mapHomologicalComplexCompHomologyFunctorIso` of the homology
of `F(L)` with `F` applied to the homology of `L`, sends the class of a cycle of `K` to `F`
applied to the class of the cycle of `L` that `ψ` gives. -/
@[reassoc, elementwise nosimp]
theorem homologyπ_comp_homologyMap_comp_mapHomologicalComplexCompHomologyFunctorIso_hom_app
    {K : HomologicalComplex D c} {L : HomologicalComplex C c}
    (ψ : K ⟶ (F.mapHomologicalComplex c).obj L) :
    K.homologyπ i ≫ homologyMap ψ i ≫
        (F.mapHomologicalComplexCompHomologyFunctorIso c i).hom.app L =
      cyclesMap ψ i ≫ ((L.sc i).mapCyclesIso F).hom ≫ F.map (L.homologyπ i) := by
  rw [homologyπ_naturality_assoc,
    Functor.homologyπ_comp_mapHomologicalComplexCompHomologyFunctorIso_hom_app]

end Homology

end HomologicalComplex

end
