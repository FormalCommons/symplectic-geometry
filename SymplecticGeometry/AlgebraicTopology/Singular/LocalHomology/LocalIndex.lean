/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.LocalIndex

/-!
# The local index on the whole source

This file is a part of Tau Ceti's
`TauCeti/AlgebraicTopology/Singular/LocalHomology/LocalIndex.lean`, as of the commit
`692639ca06f41589e290f90f10e3c3b0a514e342`, which added the lemma below after the pinned release.
It holds only `TauCeti.HomologicalOrientation.localIndex_eq_iff_of_preimage_subset`, under its
Tau Ceti name and namespace, so that moving Tau Ceti past that commit deletes this file without
renames. Its statement, docstring and proof are Tau Ceti's, unchanged, and so is the variable
block; the `open` line keeps only the namespaces the lemma uses.

## Main results

* `TauCeti.HomologicalOrientation.localIndex_eq_iff_of_preimage_subset`: when `x` is the only
  point of its fibre, the local index of `f` at `x` is read off the map of local homology induced
  by `f` itself, with no isolating neighbourhood.

## References

* A. Dold, *Lectures on Algebraic Topology*, Springer, 1972, Chapter VIII, §4 (the degree as a
  sum of local indices).
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2, Proposition 2.30 (the degree of a map of spheres as a sum of local degrees).
-/

public section

noncomputable section

open CategoryTheory Module Set

namespace TauCeti

namespace HomologicalOrientation

variable {M N E F : Type} [TopologicalSpace M] [T2Space M] [TopologicalSpace N] [T2Space N]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [ChartedSpace F N]
  {n : ℕ} (o : HomologicalOrientation M E n) (o' : HomologicalOrientation N F n)
  (hE : finrank ℝ E = n) (hF : finrank ℝ F = n)

include hF in
/-- **The local index in the whole source.** If `x` is the only point of `M` sent to `y = f x`,
the local index of `f` at `x` is the integer `c` such that `f` carries the local orientation `o x`
to `c • o' y`, with no isolating neighbourhood to choose. -/
theorem localIndex_eq_iff_of_preimage_subset (f : C(M, N)) {x : M} {y : N} (hxy : f x = y)
    (h : f ⁻¹' {y} ⊆ {x}) {c : ℤ} :
    o.localIndex o' f x = c ↔
      localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) f h n (o x).val = c • (o' y).val := by
  have hincl : (⟨Subtype.val, continuous_subtypeVal⟩ : C((univ : Set M), M)) ⁻¹' {x} ⊆
      {⟨x, mem_univ x⟩} := fun z hz ↦ Subtype.ext hz
  rw [o.localIndex_eq_iff o' hF f hxy isOpen_univ (mem_univ x) fun z _ hz ↦ h hz,
    ← isOpen_univ.isOpenEmbedding_subtypeVal.localHomologyMap_localOrientationEquiv_symm
      ⟨x, mem_univ x⟩ (o x) hincl, ← ConcreteCategory.comp_apply, localHomologyMap_comp]
  rfl

end HomologicalOrientation

end TauCeti

end
