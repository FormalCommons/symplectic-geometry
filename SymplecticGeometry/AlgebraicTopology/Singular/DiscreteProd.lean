/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import TauCeti.AlgebraicTopology.Singular.Additivity
public import TauCeti.AlgebraicTopology.Singular.Contractible
public import SymplecticGeometry.Topology.Category.TopCat.Monoidal

/-!
# Singular homology of a product with a discrete factor

For a discrete space `ι` and a space `X`, the product `ι ⊗ X` in `TopCat` is the disjoint union of
the fibres `{i} × X`. Hence, in every degree `n` and whenever coproducts indexed by `ι` are exact
in the coefficient category, `Hₙ(ι ⊗ X)` is the coproduct of copies of `Hₙ(X)`, one for each
`i : ι`, with the maps induced by the fibre inclusions `TopCat.prodFiberInclusion ι X i` as legs
(`TopCat.isColimitCofanSingularHomologyProd`).

For a point `x₀ : X` and `i : ι`, the retraction `TopCat.prodFiberRetraction ι x₀ i : ι ⊗ X ⟶ X`
of `SymplecticGeometry/Topology/Category/TopCat/Monoidal`
is the identity on the fibre over `i` and sends every other fibre to `x₀`. When `ι` is finite and
`n ≠ 0`, the composites "retract onto the fibre over `i`, then include it again" add up to the
identity of `Hₙ(ι ⊗ X)` (`TopCat.sum_singularHomologyFunctor_map_prodFiberRetraction_comp`). Only
finite coproducts are involved there, which are exact in every abelian category. On the fibre
over `j`, the term of index `j` is the identity, and every other term vanishes, since the fibre
inclusion followed by the retraction onto another fibre is constant, so it induces zero in
positive degree (`TauCeti.singularHomologyFunctor_map_const_eq_zero`).

## Main results

* `TopCat.isColimitCofanSingularHomologyProd`: `Hₙ(ι ⊗ X)` is the coproduct of copies of `Hₙ(X)`
  indexed by the points of the discrete space `ι`.
* `TopCat.singularHomologyFunctor_map_prodFiberInclusion_comp_prodFiberRetraction`: for `n ≠ 0`,
  `(σⱼ)_* ≫ (ρᵢ)_*` is the identity if `j = i` and `0` otherwise.
* `TopCat.sum_singularHomologyFunctor_map_prodFiberRetraction_comp`: for finite `ι` and `n ≠ 0`,
  the composites `(ρᵢ)_* ≫ (σᵢ)_*` of the fibre retractions and inclusions sum to the identity.

## Sources

The proof of the coproduct statement follows that of Tau Ceti's
`TopCat.singularCohomology_prod_ext_of_discreteTopology`, in
`TauCeti/AlgebraicTopology/Cohomology/Additivity/Basic`, which transports the additivity of
singular cohomology along `TopCat.sigmaConstIsoProd`; here the additivity of singular homology,
`TauCeti.isColimitCofanSingularHomology` in `TauCeti/AlgebraicTopology/Singular/Additivity`, is
transported along the same isomorphism.

## References

* S. Eilenberg and N. Steenrod, *Foundations of Algebraic Topology*, Princeton University Press,
  1952, Chapter I, Section 3 (the additivity axiom).
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §2.1, Proposition 2.6
  (homology of a disjoint union).
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicTopology

universe w v u

namespace TopCat

section Coproduct

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C) (n : ℕ)
  (ι X : TopCat.{w}) [DiscreteTopology ι]

/-- **Singular homology of a product with a discrete factor.** For a discrete space `ι`, if
coproducts indexed by `ι` are exact in `C`, then in every degree `n` the singular homology of
`ι ⊗ X` with coefficients in `R` is the coproduct of copies of `Hₙ(X; R)` indexed by `ι`, with the
maps induced by the fibre inclusions `x ↦ (i, x)` as the cofan legs. -/
def isColimitCofanSingularHomologyProd [HasExactColimitsOfShape (Discrete ι) C] :
    IsColimit (Cofan.mk (((singularHomologyFunctor C n).obj R).obj (ι ⊗ X))
      (fun i : ι ↦ ((singularHomologyFunctor C n).obj R).map (prodFiberInclusion ι X i))) :=
  IsColimit.ofIsoColimit (TauCeti.isColimitCofanSingularHomology (fun _ : ι ↦ X) C R n)
    (Cofan.ext (((singularHomologyFunctor C n).obj R).mapIso (sigmaConstIsoProd ι X))
      fun i ↦ by
        simp only [cofan_mk_inj, Functor.mapIso_hom, ← Functor.map_comp,
          sigmaι_comp_sigmaConstIsoProd_hom])

end Coproduct

section FiberComp

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]
  [CategoryWithHomology C] (R : C) (ι : TopCat.{w}) [DiscreteTopology ι] {X : TopCat.{w}}

/-- In positive degree, the map on `Hₙ` induced by including the fibre over `j` and then
retracting onto the fibre over `i` is the identity if `j = i` and `0` otherwise. -/
theorem singularHomologyFunctor_map_prodFiberInclusion_comp_prodFiberRetraction [DecidableEq ι]
    (x₀ : X) {n : ℕ} (hn : n ≠ 0) (i j : ι) :
    ((singularHomologyFunctor C n).obj R).map (prodFiberInclusion ι X j) ≫
      ((singularHomologyFunctor C n).obj R).map (prodFiberRetraction ι x₀ i) =
      if j = i then 𝟙 _ else 0 := by
  rw [← Functor.map_comp]
  split_ifs with h
  · subst h
    rw [prodFiberInclusion_comp_prodFiberRetraction, CategoryTheory.Functor.map_id]
  · rw [prodFiberInclusion_comp_prodFiberRetraction_of_ne ι x₀ h]
    -- `TopCat.const x₀` is `TopCat.ofHom (ContinuousMap.const _ x₀)` up to unfolding, and Mathlib
    -- has no lemma that states it
    exact TauCeti.singularHomologyFunctor_map_const_eq_zero R x₀ hn

end FiberComp

section Sum

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
  (ι : TopCat.{w}) [DiscreteTopology ι] {X : TopCat.{w}}

/-- **Decomposition of the identity of `Hₙ(ι ⊗ X)`.** For a finite discrete space `ι`, a point
`x₀ : X` and `n ≠ 0`, the endomorphisms of `Hₙ(ι ⊗ X; R)` induced by retracting onto the fibre
over `i` and including it again sum, over `i : ι`, to the identity. -/
theorem sum_singularHomologyFunctor_map_prodFiberRetraction_comp [Fintype ι] (x₀ : X) {n : ℕ}
    (hn : n ≠ 0) :
    ∑ i : ι, ((singularHomologyFunctor C n).obj R).map (prodFiberRetraction ι x₀ i) ≫
      ((singularHomologyFunctor C n).obj R).map (prodFiberInclusion ι X i) = 𝟙 _ := by
  classical
  have := Abelian.hasFiniteBiproducts (C := C)
  refine Cofan.IsColimit.hom_ext (isColimitCofanSingularHomologyProd R n ι X) _ _ fun j ↦ ?_
  rw [cofan_mk_inj, Preadditive.comp_sum,
    Finset.sum_eq_single_of_mem j (Finset.mem_univ j) fun i _ hij ↦ by
      rw [← Category.assoc,
        singularHomologyFunctor_map_prodFiberInclusion_comp_prodFiberRetraction R ι x₀ hn,
        ite_eq_right (Ne.symm hij), zero_comp],
    ← Category.assoc,
    singularHomologyFunctor_map_prodFiberInclusion_comp_prodFiberRetraction R ι x₀ hn,
    ite_eq_left rfl, Category.id_comp]
  exact (Category.comp_id _).symm

end Sum

end TopCat

end
