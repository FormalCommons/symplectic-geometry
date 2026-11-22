/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
public import Mathlib.Topology.Homotopy.Contractible
public import TauCeti.AlgebraicTopology.Cohomology.Point

/-!
# Nullhomotopic maps on singular homology and cohomology

A nullhomotopic map `f : X ⟶ Y` in `TopCat` induces the zero map on singular homology
`Hₙ(-; R)` in every positive degree `n`
(`TopCat.singularHomologyFunctor_map_eq_zero_of_nullhomotopic`). By homotopy invariance
(`TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor`), `f` induces the same map as a
constant map, which factors through a point, and the positive-degree homology of a point vanishes
(`AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace`). In
particular, a constant map induces zero in positive degree
(`TopCat.singularHomologyFunctor_map_const_eq_zero`), and likewise in singular cohomology
(`TopCat.singularCohomologyMap_const_eq_zero`, from Tau Ceti's
`TopCat.singularCohomologyMap_eq_zero_of_nullhomotopic`).

## Sources

The statement is the homology counterpart of Tau Ceti's
`TopCat.singularCohomologyMap_eq_zero_of_nullhomotopic`, in
`TauCeti/AlgebraicTopology/Cohomology/Point`, and its proof follows that one, with the homotopy
invariance of singular homology in place of that of cohomology. The same factorization through a
point proves Tau Ceti's `TauCeti.isZero_singularHomologyFunctor_of_contractibleSpace`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §2.1, Corollary 2.11
  (homotopy invariance) and Proposition 2.8 (the homology of a point).
-/

public section

open CategoryTheory Limits AlgebraicTopology

namespace TopCat

universe w v u

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]
  [CategoryWithHomology C] (R : C)

/-- **A nullhomotopic map induces zero on positive-degree singular homology**: for a
nullhomotopic `f : X ⟶ Y` and `n ≠ 0`, the map `Hₙ(X; R) ⟶ Hₙ(Y; R)` induced by `f` is zero. -/
theorem singularHomologyFunctor_map_eq_zero_of_nullhomotopic {X Y : TopCat.{w}} {f : X ⟶ Y}
    (hf : f.hom.Nullhomotopic) {n : ℕ} (hn : n ≠ 0) :
    ((singularHomologyFunctor C n).obj R).map f = 0 := by
  obtain ⟨y, ⟨H⟩⟩ := hf
  let p : X ⟶ of PUnit.{w + 1} := ofHom (ContinuousMap.const X PUnit.unit)
  let s : of PUnit.{w + 1} ⟶ Y := ofHom (ContinuousMap.const _ y)
  have hfs : ((singularHomologyFunctor C n).obj R).map f =
      ((singularHomologyFunctor C n).obj R).map (p ≫ s) :=
    -- The underlying continuous map of `p ≫ s` is `ContinuousMap.const X y` by definition, so
    -- `H` is a homotopy from `f` to `p ≫ s`.
    Homotopy.congr_homologyMap_singularChainComplexFunctor (f := f) (g := p ≫ s) H R n
  have hpt : IsZero (((singularHomologyFunctor C n).obj R).obj (of PUnit.{w + 1})) :=
    isZero_singularHomologyFunctor_of_totallyDisconnectedSpace C n R _ hn
  rw [hfs, Functor.map_comp, hpt.eq_of_src (((singularHomologyFunctor C n).obj R).map s) 0,
    comp_zero]

/-- In positive degree, singular homology sends a constant map to zero. -/
lemma singularHomologyFunctor_map_const_eq_zero {X Y : TopCat.{w}} (x₀ : X) {n : ℕ}
    (hn : n ≠ 0) :
    ((singularHomologyFunctor C n).obj R).map (TopCat.const x₀ : Y ⟶ X) = 0 := by
  refine singularHomologyFunctor_map_eq_zero_of_nullhomotopic R ?_ hn
  have h : (TopCat.const x₀ : Y ⟶ X).hom = ContinuousMap.const Y x₀ := by
    ext
    simp
  exact h ▸ ContinuousMap.nullhomotopic_of_constant x₀

/-- In positive degree, singular cohomology sends a constant map to zero. -/
lemma singularCohomologyMap_const_eq_zero {C : Type u} [Category.{v} C] [HasCoproducts.{w} C]
    [Abelian C] {R : C} {k : Type*} [Ring k] [Linear k C] {M : C} {X Y : TopCat.{w}} (x₀ : X)
    {n : ℕ} (hn : n ≠ 0) :
    TopCat.singularCohomologyMap (R := R) (k := k) (M := M) (TopCat.const x₀ : Y ⟶ X) n = 0 := by
  refine singularCohomologyMap_eq_zero_of_nullhomotopic ?_ hn
  have h : (TopCat.const x₀ : Y ⟶ X).hom = ContinuousMap.const Y x₀ := by
    ext
    simp
  exact h ▸ ContinuousMap.nullhomotopic_of_constant x₀

end TopCat

end
