/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import TauCeti.AlgebraicTopology.Singular.Additivity
public import TauCeti.Topology.Category.TopCat.Monoidal

/-!
# Singular homology of a product with a discrete factor

For a discrete space `ι` and a space `X`, the product `ι ⊗ X` in `TopCat` is the disjoint union of
the fibres `{i} × X`. Hence, in every degree `n` and whenever coproducts indexed by `ι` are exact
in the coefficient category, `Hₙ(ι ⊗ X)` is the coproduct of copies of `Hₙ(X)`, one for each
`i : ι`, with the maps induced by the fibre inclusions `TopCat.prodFiberInclusion ι X i` as legs
(`TopCat.isColimitCofanSingularHomologyProd`).

For a point `x₀ : X` and `i : ι`, the retraction `TopCat.prodFiberRetraction ι x₀ i : ι ⊗ X ⟶ X`
is the identity on the fibre over `i` and sends every other fibre to `x₀`. When `ι` is finite and
`n ≠ 0`, the composites "retract onto the fibre over `i`, then include it again" add up to the
identity of `Hₙ(ι ⊗ X)` (`TopCat.sum_singularHomologyFunctor_map_prodFiberRetraction_comp`). Only
finite coproducts are involved there, which are exact in every abelian category. On the fibre
over `j`, the term of index `j` is the identity, and every other term vanishes, since the fibre
inclusion followed by the retraction onto another fibre is constant, so it factors through a
point, whose homology vanishes in positive degree.

## Main results

* `TopCat.isColimitCofanSingularHomologyProd`: `Hₙ(ι ⊗ X)` is the coproduct of copies of `Hₙ(X)`
  indexed by the points of the discrete space `ι`.
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

section Retraction

variable (ι : TopCat.{w}) [DiscreteTopology ι] {X : TopCat.{w}}

open Classical in
/-- For a discrete space `ι`, a point `x₀ : X` and `i : ι`, the retraction of `ι ⊗ X` onto the
fibre over `i`: it sends `(i, x)` to `x`, and `(j, x)` to `x₀` for `j ≠ i`. -/
def prodFiberRetraction (x₀ : X) (i : ι) : ι ⊗ X ⟶ X :=
  ofHom ⟨fun p ↦ if p.1 = i then p.2 else x₀,
    continuous_prod_of_discrete_left.2 fun j ↦ by
      by_cases h : j = i <;> simp only [h, ↓reduceIte] <;> fun_prop⟩

open Classical in
lemma prodFiberRetraction_apply (x₀ : X) (i : ι) (p : ↑(ι ⊗ X)) :
    prodFiberRetraction ι x₀ i p = if p.1 = i then p.2 else x₀ :=
  (rfl)

@[simp]
lemma prodFiberRetraction_apply_self (x₀ : X) (i : ι) (x : X) :
    prodFiberRetraction ι x₀ i ((i, x) : ↑(ι ⊗ X)) = x :=
  (prodFiberRetraction_apply ι x₀ i _).trans (by simp)

lemma prodFiberRetraction_apply_of_ne (x₀ : X) {i j : ι} (h : j ≠ i) (x : X) :
    prodFiberRetraction ι x₀ i ((j, x) : ↑(ι ⊗ X)) = x₀ :=
  (prodFiberRetraction_apply ι x₀ i _).trans (by simp [h])

/-- The retraction onto the fibre over `i` is a left inverse of the inclusion of that fibre. -/
@[reassoc (attr := simp)]
lemma prodFiberInclusion_comp_prodFiberRetraction (x₀ : X) (i : ι) :
    prodFiberInclusion ι X i ≫ prodFiberRetraction ι x₀ i = 𝟙 X := by
  ext x
  simp

/-- The inclusion of the fibre over `j`, followed by the retraction onto another fibre, is the
constant map at the base point. -/
lemma prodFiberInclusion_comp_prodFiberRetraction_of_ne (x₀ : X) {i j : ι} (h : j ≠ i) :
    prodFiberInclusion ι X j ≫ prodFiberRetraction ι x₀ i = TopCat.const x₀ := by
  ext x
  simp [prodFiberRetraction_apply_of_ne ι x₀ h]

end Retraction

section Sum

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)

/-- In positive degree, singular homology sends a constant map to zero, since it factors through
a point. -/
lemma singularHomologyFunctor_map_const_eq_zero {X Y : TopCat.{w}} (x₀ : X) {n : ℕ}
    (hn : n ≠ 0) :
    ((singularHomologyFunctor C n).obj R).map (TopCat.const x₀ : Y ⟶ X) = 0 := by
  let pt : TopCat.{w} := TopCat.of PUnit
  have h : (TopCat.const x₀ : Y ⟶ X) =
      (TopCat.const (PUnit.unit : pt) : Y ⟶ pt) ≫ TopCat.const x₀ := by
    ext
    simp
  rw [h, Functor.map_comp,
    (isZero_singularHomologyFunctor_of_totallyDisconnectedSpace C n R pt hn).eq_of_src
      (((singularHomologyFunctor C n).obj R).map (TopCat.const x₀)) 0, comp_zero]

variable (ι : TopCat.{w}) [DiscreteTopology ι] {X : TopCat.{w}}

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
      rw [← Category.assoc, ← Functor.map_comp,
        prodFiberInclusion_comp_prodFiberRetraction_of_ne ι x₀ (Ne.symm hij),
        singularHomologyFunctor_map_const_eq_zero R x₀ hn, zero_comp],
    ← Category.assoc, ← Functor.map_comp, prodFiberInclusion_comp_prodFiberRetraction,
    CategoryTheory.Functor.map_id, Category.id_comp]
  exact (Category.comp_id _).symm

end Sum

end TopCat

end
