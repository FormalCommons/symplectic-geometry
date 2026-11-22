/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
public import TauCeti.AlgebraicTopology.SimplicialSet.TopAdj
public import TauCeti.Geometry.Convex.ConvexSpace.Defs
public import TauCeti.Topology.Homotopy.Path

/-!
# Singular `1`-simplices of paths: closed paths and concatenation

Tau Ceti reads a map `g : C(I, X)` as the singular `1`-simplex `TauCeti.TopCat.simplex₁ g`. This
file proves two facts about these simplices, with coefficients in any preadditive category with
coproducts.

* If `g 0 = g 1`, the two faces of `simplex₁ g` agree, so it is a `1`-cycle
  (`TauCeti.TopCat.δ_zero_simplex₁_eq_δ_one_simplex₁`).
* For paths `γ` from `a` to `b` and `δ` from `b` to `c`, the singular `2`-simplex
  `TauCeti.TopCat.transSimplex γ δ`, the composite of `γ.trans δ` with the affine map of the
  standard `2`-simplex onto `I` that sends its vertices to `0`, `1/2` and `1`, has faces `δ`,
  `γ.trans δ` and `γ`. So the chain `γ + δ - γ.trans δ` is its boundary
  (`TauCeti.TopCat.ιChainComplex_transSimplex_d`).

The second fact is the one Tau Ceti proves for integer chains as
`TauCeti.HurewiczOne.pathChain_add_sub_trans_mem_boundaries₁`; the `2`-simplex and the
computation of its faces are adapted from that proof.

## Main definitions and results

* `TauCeti.TopCat.δ_zero_simplex₁_eq_δ_one_simplex₁`: the singular `1`-simplex of a closed path
  has equal faces.
* `TauCeti.TopCat.transSimplex`: the singular `2`-simplex of a concatenation of paths.
* `TauCeti.TopCat.ιChainComplex_transSimplex_d`: its boundary is `γ + δ - γ.trans δ`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Theorem 2A.1.
-/

public section

noncomputable section

open CategoryTheory Limits Convexity Simplicial unitInterval

universe u v w

namespace TauCeti.TopCat

variable {X : _root_.TopCat.{u}}

/-- **The singular `1`-simplex of a closed path is closed**: if `g 0 = g 1`, the two faces of
`simplex₁ g` agree. -/
lemma δ_zero_simplex₁_eq_δ_one_simplex₁ {g : C(I, X)} (h : g 0 = g 1) :
    (_root_.TopCat.toSSet.obj X).δ 0 (simplex₁ g) =
      (_root_.TopCat.toSSet.obj X).δ 1 (simplex₁ g) := by
  rw [δ_zero_simplex₁, δ_one_simplex₁, h]

/-- The affine map of the standard `2`-simplex onto the unit interval that sends the vertices to
`0`, `1/2` and `1`. -/
private def concatProj : C(StdSimplex ℝ (Fin 3), I) :=
  ⟨fun w ↦ ⟨w.weights 1 / 2 + w.weights 2,
    add_nonneg (div_nonneg (w.weights_nonneg 1) zero_le_two) (w.weights_nonneg 2),
    by linarith [w.weights_one_add_weights_two_le_one, w.weights_nonneg 1]⟩,
    (by fun_prop :
      Continuous fun w : StdSimplex ℝ (Fin 3) ↦ w.weights 1 / 2 + w.weights 2).subtype_mk _⟩

/-- The singular `2`-simplex of a concatenation of paths `γ` from `a` to `b` and `δ` from `b` to
`c`: the composite of `γ.trans δ` with the affine map of the standard `2`-simplex onto the unit
interval that sends the vertices to `0`, `1/2` and `1`. Its faces are `δ`, `γ.trans δ` and `γ`
(`δ_zero_transSimplex`, `δ_one_transSimplex`, `δ_two_transSimplex`). -/
def transSimplex {a b c : X} (γ : Path a b) (δ : Path b c) :
    (_root_.TopCat.toSSet.obj X) _⦋2⦌ :=
  (X.toSSetObjEquiv _).symm ((γ.trans δ).toContinuousMap.comp concatProj)

/-- The `i`-th face of `transSimplex γ δ` is the singular `1`-simplex of `g`, as soon as the
parameter of the concatenation along that face is the one of `g`. -/
private lemma δ_transSimplex {a b c : X} (γ : Path a b) (δ : Path b c) (i : Fin 3) (g : C(I, X))
    (h : ∀ w : StdSimplex ℝ (Fin 2),
      (γ.trans δ) (concatProj (StdSimplex.map i.succAbove w)) = g (StdSimplex.homeomorphI w)) :
    (_root_.TopCat.toSSet.obj X).δ i (transSimplex γ δ) = simplex₁ g := by
  apply (X.toSSetObjEquiv _).injective
  ext w
  rw [_root_.TopCat.toSSetObjEquiv_δ_apply, toSSetObjEquiv_simplex₁, transSimplex,
    Equiv.apply_symm_apply]
  exact h w

/-- The `0`-th face of the singular `2`-simplex of a concatenation is the second path. -/
@[simp]
lemma δ_zero_transSimplex {a b c : X} (γ : Path a b) (δ : Path b c) :
    (_root_.TopCat.toSSet.obj X).δ 0 (transSimplex γ δ) = simplex₁ δ.toContinuousMap := by
  refine δ_transSimplex γ δ 0 _ fun w ↦ Path.trans_apply_of_eq_two_mul_sub_one γ δ _ ?_
  have h₁ := StdSimplex.weights_map_succAbove_of_eq (j := (0 : Fin 3)) (k := 1) (i := 0) rfl w
  have h₂ := StdSimplex.weights_map_succAbove_of_eq (j := (0 : Fin 3)) (k := 2) (i := 1) rfl w
  simp only [concatProj, ContinuousMap.coe_mk, h₁, h₂, StdSimplex.homeomorphI_apply_eq_mk]
  linarith [w.total_fin_two]

/-- The `1`-st face of the singular `2`-simplex of a concatenation is the concatenation. -/
@[simp]
lemma δ_one_transSimplex {a b c : X} (γ : Path a b) (δ : Path b c) :
    (_root_.TopCat.toSSet.obj X).δ 1 (transSimplex γ δ) = simplex₁ (γ.trans δ).toContinuousMap := by
  refine δ_transSimplex γ δ 1 _ fun w ↦ congrArg (γ.trans δ) (Subtype.ext ?_)
  have h₁ := StdSimplex.weights_map_succAbove_self (1 : Fin 3) w
  have h₂ := StdSimplex.weights_map_succAbove_of_eq (j := (1 : Fin 3)) (k := 2) (i := 1) rfl w
  simp only [concatProj, ContinuousMap.coe_mk, h₁, h₂, StdSimplex.homeomorphI_apply_eq_mk]
  ring

/-- The `2`-nd face of the singular `2`-simplex of a concatenation is the first path. -/
@[simp]
lemma δ_two_transSimplex {a b c : X} (γ : Path a b) (δ : Path b c) :
    (_root_.TopCat.toSSet.obj X).δ 2 (transSimplex γ δ) = simplex₁ γ.toContinuousMap := by
  refine δ_transSimplex γ δ 2 _ fun w ↦ Path.trans_apply_of_eq_two_mul γ δ _ ?_
  have h₁ := StdSimplex.weights_map_succAbove_of_eq (j := (2 : Fin 3)) (k := 1) (i := 1) rfl w
  have h₂ := StdSimplex.weights_map_succAbove_self (2 : Fin 3) w
  simp only [concatProj, ContinuousMap.coe_mk, h₁, h₂, StdSimplex.homeomorphI_apply_eq_mk]
  ring

variable {C : Type v} [Category.{w} C] [HasCoproducts.{u} C] [Preadditive C] (R : C)

/-- **Concatenation of paths, up to a boundary**: with coefficients in any preadditive category
with coproducts, the boundary of the singular `2`-simplex `transSimplex γ δ` is the chain
`γ + δ - γ.trans δ`. -/
lemma ιChainComplex_transSimplex_d {a b c : X} (γ : Path a b) (δ : Path b c) :
    (_root_.TopCat.toSSet.obj X).ιChainComplex (R := R) (transSimplex γ δ) ≫
        ((_root_.TopCat.toSSet.obj X).chainComplex R).d 2 1 =
      (_root_.TopCat.toSSet.obj X).ιChainComplex (simplex₁ γ.toContinuousMap) +
        (_root_.TopCat.toSSet.obj X).ιChainComplex (simplex₁ δ.toContinuousMap) -
          (_root_.TopCat.toSSet.obj X).ιChainComplex (simplex₁ (γ.trans δ).toContinuousMap) := by
  rw [SSet.ιChainComplex_d, Fin.sum_univ_three, δ_zero_transSimplex, δ_one_transSimplex,
    δ_two_transSimplex]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul, Fin.val_two]
  rw [neg_one_sq, one_smul]
  abel

end TauCeti.TopCat

end
