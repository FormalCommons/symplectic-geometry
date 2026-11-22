/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.ModuleChains.Basic

/-!
# Mathlib's singular homology functor and Tau Ceti's induced maps

Mathlib's `AlgebraicTopology.singularHomologyFunctor` and Tau Ceti's
`ContinuousMap.singularHomologyMap` both describe singular homology with coefficients in a ring
`k`. Tau Ceti compares them on objects (`TauCeti.singularHomologyFunctor_obj_obj`). This file
compares them on maps: with coefficients `ModuleCat.of k k`, the map that Mathlib's functor
induces from a continuous map `g` is `ContinuousMap.singularHomologyMap k n g`.

## Main results

* `AlgebraicTopology.singularHomologyFunctor_obj_map_ofHom_hom`: with coefficients `k`, the
  singular homology functor induces `ContinuousMap.singularHomologyMap`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §2.1 (singular homology
  and induced homomorphisms).
-/

public section

universe u

namespace AlgebraicTopology

/-- With coefficients `k`, the map induced by Mathlib's singular homology functor is Tau Ceti's
`ContinuousMap.singularHomologyMap`. -/
theorem singularHomologyFunctor_obj_map_ofHom_hom {k : Type u} [Ring k] (n : ℕ)
    {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z] (g : C(Y, Z)) :
    (((singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).map
      (TopCat.ofHom g)).hom = ContinuousMap.singularHomologyMap k n g :=
  -- Both sides are the homology map of the chain map of `g`, by definition of
  -- `TauCeti.singularChains`.
  rfl

end AlgebraicTopology

end
