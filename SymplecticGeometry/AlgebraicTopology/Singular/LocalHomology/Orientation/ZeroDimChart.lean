/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Basic
public import TauCeti.Topology.Category.TopPair.ContinuousLinearEquiv
public import Mathlib.LinearAlgebra.Orientation
import SymplecticGeometry.Topology.Category.TopPair
import SymplecticGeometry.LinearAlgebra.Orientation.Basic
import TauCeti.AlgebraicTopology.Singular.ReducedRelative

/-!
# Zero-dimensional local orientations under isomorphisms of pairs

At a point `x` with a zero-dimensional chart, Tau Ceti's
`TauCeti.localOrientationOfZeroDimChart` is the class of `x` in `H₀(M, M ∖ {x}; ℤ)`. An
isomorphism of pairs `(M, M ∖ {x}) ≅ (N, N ∖ {y})` always sends `x` to `y`
(`TopPair.iso_ofSubset_compl_singleton_hom_fst_apply`), so it carries the class of `x`
to the class of `y`. Hence it carries this local orientation at `x` to the one at `y`,
whichever zero-dimensional charts select them (`TauCeti.localOrientationOfZeroDimChart_map`).
This is the rank-zero counterpart of Tau Ceti's `Orientation.localOrientation_map`, where in
positive rank the local orientation is selected by an orientation of the model space. For
instance, through `h.complZeroPairIso`, a continuous linear equivalence `h : P ≃L[ℝ] P'` of
zero-dimensional spaces carries the local orientation of the identity chart of `P` at the
origin to that of `P'`.

An orientation `ω` of a zero-dimensional real normed space `P` is either the positive orientation
of the empty index type or its negative. It selects the local orientation
`Orientation.localOrientationOfZeroDim ω hP` of `P` at the origin: the class of the origin when
`ω` is positive, and its negative otherwise. This is the rank-zero counterpart of Tau Ceti's
`Orientation.localOrientation`, and, like it, it is natural under continuous linear equivalences
(`Orientation.localOrientationOfZeroDim_map`) and reverses with `ω`
(`Orientation.localOrientationOfZeroDim_neg`).

## Main definitions

* `Orientation.localOrientationOfZeroDim`: the local orientation at the origin selected by an
  orientation of a zero-dimensional space.

## Main results

* `TauCeti.localOrientationOfZeroDimChart_map`: the point-class local orientation of a
  zero-dimensional chart is natural under isomorphisms of pairs.
* `Orientation.localOrientationOfZeroDim_map`: the local orientation selected by an orientation
  of a zero-dimensional space is natural under continuous linear equivalences.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3.
-/

public section

open CategoryTheory Module

universe w

namespace TauCeti

/-- Let `x ∈ M` and `y ∈ N` have zero-dimensional charts `φ` and `ψ`. An isomorphism of pairs
`e : (M, M ∖ {x}) ≅ (N, N ∖ {y})` carries the local orientation of `φ` at `x`, the class of
`x`, to the local orientation of `ψ` at `y`. -/
theorem localOrientationOfZeroDimChart_map {M N E F : Type w} [TopologicalSpace M] [T2Space M]
    [TopologicalSpace N] [T2Space N]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (φ : OpenPartialHomeomorph M E) (ψ : OpenPartialHomeomorph N F) {x : M} {y : N}
    (hx : x ∈ φ.source) (hy : y ∈ ψ.source) (hE : finrank ℝ E = 0) (hF : finrank ℝ F = 0)
    (e : TopPair.ofSubset ({x}ᶜ : Set (TopCat.of M)) ≅
      TopPair.ofSubset ({y}ᶜ : Set (TopCat.of N))) :
    (localOrientationOfZeroDimChart φ hx hE).map e = localOrientationOfZeroDimChart ψ hy hF := by
  refine Subtype.ext ?_
  rw [LocalOrientation.coe_map, localOrientationOfZeroDimChart_coe,
    localOrientationOfZeroDimChart_coe, localHomologyPointClass_def, localHomologyPointClass_def]
  exact ConcreteCategory.congr_hom (TopPair.singularHomology₀Section_singularHomologyMap _
    (ModuleCat.of ℤ (ULift.{w} ℤ)) e.hom x y
    (TopPair.iso_ofSubset_compl_singleton_hom_fst_apply e)) 1

end TauCeti

namespace Orientation

open TauCeti

variable {P Q : Type w} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]

open Classical in
/-- **The local orientation selected by an orientation of a zero-dimensional space.** An
orientation `ω` of a real normed space `P` of dimension zero selects the local orientation of `P`
at the origin given by the class of the origin (the local orientation of the identity chart),
when `ω` is the positive orientation of the empty index type, and its negative otherwise. -/
noncomputable def localOrientationOfZeroDim (ω : Orientation ℝ P (Fin 0)) (hP : finrank ℝ P = 0) :
    LocalOrientation P 0 0 :=
  if ω = positiveOrientation then
    localOrientationOfZeroDimChart (OpenPartialHomeomorph.refl P)
      (OpenPartialHomeomorph.mem_refl_source _) hP
  else -localOrientationOfZeroDimChart (OpenPartialHomeomorph.refl P)
      (OpenPartialHomeomorph.mem_refl_source _) hP

open Classical in
theorem localOrientationOfZeroDim_def (ω : Orientation ℝ P (Fin 0)) (hP : finrank ℝ P = 0) :
    ω.localOrientationOfZeroDim hP =
      if ω = positiveOrientation then
        localOrientationOfZeroDimChart (OpenPartialHomeomorph.refl P)
          (OpenPartialHomeomorph.mem_refl_source _) hP
      else -localOrientationOfZeroDimChart (OpenPartialHomeomorph.refl P)
          (OpenPartialHomeomorph.mem_refl_source _) hP :=
  (rfl)

/-- The positive orientation of a zero-dimensional space selects the class of the origin. -/
@[simp]
theorem localOrientationOfZeroDim_positiveOrientation (hP : finrank ℝ P = 0) :
    (positiveOrientation : Orientation ℝ P (Fin 0)).localOrientationOfZeroDim hP =
      localOrientationOfZeroDimChart (OpenPartialHomeomorph.refl P)
        (OpenPartialHomeomorph.mem_refl_source _) hP := by
  rw [localOrientationOfZeroDim_def, ite_eq_left rfl]

/-- Reversing an orientation of a zero-dimensional space reverses the local orientation it
selects. -/
@[simp]
theorem localOrientationOfZeroDim_neg (ω : Orientation ℝ P (Fin 0)) (hP : finrank ℝ P = 0) :
    (-ω).localOrientationOfZeroDim hP = -ω.localOrientationOfZeroDim hP := by
  rcases eq_or_eq_neg_of_isEmpty ω with rfl | rfl
  · rw [localOrientationOfZeroDim_def, ite_eq_right (Module.Ray.ne_neg_self _).symm,
      localOrientationOfZeroDim_positiveOrientation]
  · rw [neg_neg (G := Orientation ℝ P (Fin 0)), localOrientationOfZeroDim_def (-_),
      ite_eq_right (Module.Ray.ne_neg_self _).symm, localOrientationOfZeroDim_positiveOrientation,
      neg_neg]

open Classical in
/-- The local orientation selected by `ω` is the class of the origin of `P`, with the sign `+`
when `ω` is the positive orientation and `-` otherwise. -/
theorem coe_localOrientationOfZeroDim (ω : Orientation ℝ P (Fin 0)) (hP : finrank ℝ P = 0) :
    (ω.localOrientationOfZeroDim hP).val =
      if ω = positiveOrientation then
        localHomologyPointClass (ModuleCat.of ℤ (ULift.{w} ℤ)) {(0 : P)} 0 1
      else -localHomologyPointClass (ModuleCat.of ℤ (ULift.{w} ℤ)) {(0 : P)} 0 1 := by
  rw [localOrientationOfZeroDim_def]
  split_ifs <;> simp

/-- **Naturality of the selected local orientations in dimension zero.** A continuous linear
equivalence `f : P ≃L[ℝ] Q` of zero-dimensional spaces carries the local orientation selected by
`ω` to the local orientation selected by the transported orientation `ω.map f`. -/
theorem localOrientationOfZeroDim_map (f : P ≃L[ℝ] Q) (ω : Orientation ℝ P (Fin 0))
    (hP : finrank ℝ P = 0) (hQ : finrank ℝ Q = 0) :
    (ω.map _ f.toLinearEquiv).localOrientationOfZeroDim hQ =
      (ω.localOrientationOfZeroDim hP).map f.complZeroPairIso := by
  have hpt := localOrientationOfZeroDimChart_map (OpenPartialHomeomorph.refl P)
    (OpenPartialHomeomorph.refl Q) (OpenPartialHomeomorph.mem_refl_source _)
    (OpenPartialHomeomorph.mem_refl_source _) hP hQ f.complZeroPairIso
  rw [localOrientationOfZeroDim_def, localOrientationOfZeroDim_def,
    map_eq_positiveOrientation_iff]
  split_ifs
  · exact hpt.symm
  · rw [LocalOrientation.map_neg, hpt]

end Orientation

end
