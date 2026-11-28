/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Algebra.Homology.HomologicalComplex.Basic

/-!
# Chain maps out of a complex mapped along a functor

Let `F : C ⥤ D` be an additive functor that preserves homology, `K` a homological complex in `C`,
`L` one in `D`, and `φ : F(K) ⟶ L` a chain map from the complex `K` mapped along `F`. Through the
identification `ShortComplex.mapCyclesIso` of the cycles of `F(K)` with `F` applied to the cycles
of `K`:

* `HomologicalComplex.mapCyclesIso_inv_comp_cyclesMap_comp_iCycles`: the map that `φ` induces on
  cycles is `φ` on the underlying chains;
* `map_homologyπ_comp_mapHomologicalComplexCompHomologyFunctorIso_inv_app_comp_homologyMap`:
  the map that `φ` induces on homology, after the comparison
  `Functor.mapHomologicalComplexCompHomologyFunctorIso`, sends `F` applied to the class of a
  cycle to the class of its image under `φ`.

These are Tau Ceti's
`CategoryTheory.Functor.mapCyclesIso_inv_comp_cyclesMap_comp_mapCyclesIso_hom_comp_map_iCycles`
and `HomologicalComplex.cyclesComparison_homologyπ`, for a target `L` that is not itself mapped
along a functor, proved by the same steps.
-/

public section

open CategoryTheory

namespace HomologicalComplex

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  [CategoryWithHomology C] [CategoryWithHomology D] (F : C ⥤ D) [F.Additive]
  [F.PreservesHomology] {ι : Type*} {c : ComplexShape ι} {K : HomologicalComplex C c}
  {L : HomologicalComplex D c} (φ : (F.mapHomologicalComplex c).obj K ⟶ L) (i : ι)

/-- A chain map `φ : F(K) ⟶ L` acts on cycles as on chains: through the identification
`ShortComplex.mapCyclesIso` of the cycles of `F(K)` with `F` applied to the cycles of `K`, the
map `φ` induces on cycles followed by the inclusion of the cycles of `L` is `F` applied to the
inclusion of the cycles of `K` followed by `φ`. -/
@[reassoc, elementwise nosimp]
theorem mapCyclesIso_inv_comp_cyclesMap_comp_iCycles :
    ((K.sc i).mapCyclesIso F).inv ≫ cyclesMap φ i ≫ L.iCycles i =
      F.map (K.iCycles i) ≫ φ.f i := by
  rw [cyclesMap_i, Functor.mapCyclesIso_inv_comp_iCycles_assoc]

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

end HomologicalComplex

end
