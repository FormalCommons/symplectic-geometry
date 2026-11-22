/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# Class maps and functors preserving homology

For a short complex `S` and a functor `F` preserving its homology, Tau Ceti's
`CategoryTheory.ShortComplex.homologyπ_comp_mapHomologyIso_hom` compares the class map of
`S.map F` with the image under `F` of the class map of `S`. This file gives the same square read
with the inverse identifications,
`CategoryTheory.ShortComplex.map_homologyπ_comp_mapHomologyIso_inv`, which is the form needed to
compute a map out of `F (S.homology)` on classes.
-/

public section

namespace CategoryTheory.ShortComplex

variable {C D : Type*} [Category* C] [Category* D] [Limits.HasZeroMorphisms C]
  [Limits.HasZeroMorphisms D] (S : ShortComplex C) (F : C ⥤ D) [F.PreservesZeroMorphisms]

/-- Under the inverse identifications `mapCyclesIso` and `mapHomologyIso`, the image under `F` of
the class map of `S` is the class map of `S.map F`. -/
@[reassoc]
theorem map_homologyπ_comp_mapHomologyIso_inv [S.HasHomology] [(S.map F).HasHomology]
    [F.PreservesLeftHomologyOf S] :
    F.map S.homologyπ ≫ (S.mapHomologyIso F).inv =
      (S.mapCyclesIso F).inv ≫ (S.map F).homologyπ := by
  rw [Iso.comp_inv_eq, Category.assoc, homologyπ_comp_mapHomologyIso_hom, Iso.inv_hom_id_assoc]

end CategoryTheory.ShortComplex

end
