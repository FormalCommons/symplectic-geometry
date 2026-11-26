/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.FundamentalGroup.Basic

import SymplecticGeometry.Algebra.Category.Grp.Pushout
import TauCeti.AlgebraicTopology.FundamentalGroup.VanKampen.Basic

/-!
# Van Kampen with a surjective leg

Let the interiors of `A` and `B` cover a space `X`, with `A`, `B` and `A ∩ B` path connected and
containing `x`. If the inclusion `A ∩ B → B` induces a surjection of fundamental groups at `x`,
then so does `A → X`, and if the kernel of the first map is the normal closure of a set `S`, the
kernel of the second is the normal closure of the image of `S` in `π₁(A, x)`.

These follow from Tau Ceti's `TauCeti.isPushout_fundamentalGroup`, read with `A` and `B`
exchanged, together with `CategoryTheory.IsPushout.surjective_inr_of_surjective` and
`CategoryTheory.IsPushout.ker_inr_eq_normalClosure_image_of_ker_eq`.

## Main results

* `FundamentalGroup.map_subtypeVal_surjective_of_map_inclusion_surjective`: surjectivity.
* `FundamentalGroup.ker_map_subtypeVal_eq_normalClosure_image`: the kernel.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Cambridge University Press, 2002, Theorem 1.20.
-/

public section

open Set

namespace FundamentalGroup

variable {X : Type*} [TopologicalSpace X] {A B : Set X} {x : X}

/-- **Van Kampen with a surjective overlap leg, surjectivity.** Let the interiors of `A` and `B`
cover `X`, with `A`, `B` and `A ∩ B` path connected and `x ∈ A ∩ B`. If the inclusion
`A ∩ B → B` induces a surjection of fundamental groups at `x`, then so does `A → X`. -/
theorem map_subtypeVal_surjective_of_map_inclusion_surjective
    (hCover : interior A ∪ interior B = univ) (hA : IsPathConnected A) (hB : IsPathConnected B)
    (hAB : IsPathConnected (A ∩ B)) (hxA : x ∈ A) (hxB : x ∈ B)
    (h : Function.Surjective
      (map (ContinuousMap.inclusion inter_subset_right) (⟨x, hxA, hxB⟩ : ↥(A ∩ B)))) :
    Function.Surjective (map (ContinuousMap.subtypeVal A) ⟨x, hxA⟩) :=
  (TauCeti.isPushout_fundamentalGroup hCover hA hB hAB hxA hxB).flip.surjective_inr_of_surjective h

/-- **Van Kampen with a surjective overlap leg, the kernel.** Let the interiors of `A` and `B`
cover `X`, with `A`, `B` and `A ∩ B` path connected and `x ∈ A ∩ B`. If the inclusion
`A ∩ B → B` induces a surjection of fundamental groups at `x` whose kernel is the normal closure
of `S`, then the kernel of the map induced by `A → X` is the normal closure of the image of `S`
under the map induced by `A ∩ B → A`. -/
theorem ker_map_subtypeVal_eq_normalClosure_image
    (hCover : interior A ∪ interior B = univ) (hA : IsPathConnected A) (hB : IsPathConnected B)
    (hAB : IsPathConnected (A ∩ B)) (hxA : x ∈ A) (hxB : x ∈ B)
    (h : Function.Surjective
      (map (ContinuousMap.inclusion inter_subset_right) (⟨x, hxA, hxB⟩ : ↥(A ∩ B))))
    {S : Set (FundamentalGroup ↥(A ∩ B) ⟨x, hxA, hxB⟩)}
    (hS : (map (ContinuousMap.inclusion inter_subset_right) (⟨x, hxA, hxB⟩ : ↥(A ∩ B))).ker =
      Subgroup.normalClosure S) :
    (map (ContinuousMap.subtypeVal A) ⟨x, hxA⟩).ker = Subgroup.normalClosure
      (map (ContinuousMap.inclusion inter_subset_left) (⟨x, hxA, hxB⟩ : ↥(A ∩ B)) '' S) :=
  (TauCeti.isPushout_fundamentalGroup hCover hA hB hAB hxA hxB).flip
    |>.ker_inr_eq_normalClosure_image_of_ker_eq h hS

end FundamentalGroup

end
