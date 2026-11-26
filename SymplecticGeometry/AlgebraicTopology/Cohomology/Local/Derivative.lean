/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Topology.Homotopy.Affine
public import SymplecticGeometry.AlgebraicTopology.Singular.PairMap
public import TauCeti.AlgebraicTopology.Cohomology.Excision
public import TauCeti.AlgebraicTopology.Cohomology.HomotopyInvariance
public import TauCeti.Analysis.Normed.Operator.Basic

/-!
# Linearization in relative singular cohomology

Let `E` and `F` be real normed spaces, `U ⊆ E` a neighbourhood of a point `x`, and `f : E → F` a
map that is continuous on `U` and differentiable at `x`, with an antilipschitz derivative `f'`. If
`x` is the only point of `U` that `f` sends to `f x`, then `f` is a map of pairs
`(U, U ∖ {x}) ⟶ (F, F ∖ {f x})`, and so is its affine linearization `y ↦ f x + f' (y - x)`. The
two induce the same map `Hⁿ(F, F ∖ {f x}) ⟶ Hⁿ(U, U ∖ {x})` on relative singular cohomology, in
every degree and for all coefficients
(`TopPair.singularCohomologyMap_ofSubsetMap_eq_affine_of_hasFDerivAt`).

The proof adapts Tau Ceti's `TauCeti.localHomologyMap_domRestrict_eq_affine_of_hasFDerivAt`, its
homology counterpart, to cohomology. On a small ball about `x` inside `U`, the remainder
`f y - f x - f' (y - x)` is at most a small multiple of `‖y - x‖`, and since `‖f' v‖` is bounded
below by a multiple of `‖v‖`, the straight-line homotopy from `f` to its linearization does not
take the value `f x` on the ball away from `x`. So the two maps agree on the cohomology of the
ball relative to the ball minus `x` (`TopPair.Homotopy.congr_singularCohomologyMap`), and
restriction to the ball is an isomorphism on relative cohomology by excision
(`TopPair.isIso_singularCohomologyMap_excisionMap_of_isClosed_subset`).

## Main results

* `TopPair.singularCohomologyMap_ofSubsetMap_eq_affine_of_hasFDerivAt`: a map with antilipschitz
  derivative at `x` and its affine linearization induce the same map on the relative cohomology of
  `(U, U ∖ {x})`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2 (local degree) and Section 3.1 (excision and homotopy invariance in cohomology).
-/

public section

noncomputable section

open CategoryTheory Limits Metric Set Topology

universe w v u

namespace TopPair

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
  (k : Type*) [Ring k] [Linear k C] (M : C)
  {E F : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- **A map with antilipschitz derivative induces the same map on relative cohomology as its
affine linearization.** Let `U ⊆ E` be a neighbourhood of `x` and `f : E → F` a map continuous on
`U` and differentiable at `x`, with an antilipschitz derivative `f'`, such that `x` is the only
point of `U` sent to `f x`. Then `f` and its affine linearization `y ↦ f x + f' (y - x)`, as maps
of pairs `(U, U ∖ {x}) ⟶ (F, F ∖ {f x})`, induce the same map
`Hⁿ(F, F ∖ {f x}) ⟶ Hⁿ(U, U ∖ {x})`. -/
theorem singularCohomologyMap_ofSubsetMap_eq_affine_of_hasFDerivAt {f : E → F}
    {f' : E →L[ℝ] F} {x : E} {U : Set E} (hU : U ∈ 𝓝 x) (hfU : ContinuousOn f U)
    (hf : HasFDerivAt f f' x) {K : NNReal} (hf' : AntilipschitzWith K f')
    (hfx : ∀ y ∈ U, f y = f x → y = x) (n : ℕ) :
    TopPair.singularCohomologyMap (R := R) (k := k) (M := M)
        (ofSubsetMap (X := TopCat.of U) (Y := TopCat.of F)
          (TopCat.ofHom ⟨U.domRestrict f, hfU.domRestrict⟩)
          (B := {⟨x, mem_of_mem_nhds hU⟩}ᶜ) (B' := {f x}ᶜ)
          fun y hy h ↦ hy (Subtype.ext (hfx y y.property h))) n =
      TopPair.singularCohomologyMap
        (ofSubsetMap (X := TopCat.of U) (Y := TopCat.of F)
          (TopCat.ofHom ⟨fun y : U ↦ f x + f' (y - x), by fun_prop⟩)
          (B := {⟨x, mem_of_mem_nhds hU⟩}ᶜ) (B' := {f x}ᶜ)
          fun y hy h ↦ hy (Subtype.ext <| sub_eq_zero.1 <| hf'.injective <|
            (add_eq_left.1 h).trans (map_zero f').symm)) n := by
  have hx := mem_of_mem_nhds hU
  have hC := ZeroHomClass.bound_of_antilipschitz f' hf'
  -- On a ball `B` about `x` inside `U`, the remainder is at most `ε * ‖y - x‖` with `K * ε < 1`.
  set ε : ℝ := (2 * (K + 1))⁻¹
  have hε : 0 < ε := by positivity
  have hKε : (K : ℝ) * ε < 1 := by
    rw [← div_eq_mul_inv, div_lt_one (by positivity)]
    linarith [K.coe_nonneg]
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem hU (hf.isLittleO.def hε))
  -- Restriction from `(U, U ∖ {x})` to the ball is an isomorphism on cohomology, by excision.
  set A : Set (TopCat.of U) := Subtype.val ⁻¹' ball x r
  set S : Set (TopCat.of U) := {⟨x, hx⟩}
  have := isIso_singularCohomologyMap_excisionMap_of_isClosed_subset R k M (U := A) (K := S)
    -- `S` is a set of `TopCat.of U`, whose points are those of `U` only up to unfolding.
    (isOpen_ball.preimage continuous_subtypeVal) (by exact isClosed_singleton (X := U))
    (singleton_subset_iff.2 (mem_preimage.2 (mem_ball_self hr))) n
  rw [← cancel_mono (TopPair.singularCohomologyMap (excisionMap A Sᶜ) n),
    ← singularCohomologyMap_comp, ← singularCohomologyMap_comp]
  -- After the excision map, both maps of pairs come from maps of ambient spaces on the ball.
  have hcomp (g : TopCat.of U ⟶ TopCat.of F) (hg : MapsTo g Sᶜ {f x}ᶜ) :
      excisionMap A Sᶜ ≫ ofSubsetMap g hg =
        ofSubsetMap (X := TopCat.of A) (B := Subtype.val ⁻¹' Sᶜ)
          (TopCat.ofHom (ContinuousMap.subtypeVal A) ≫ g) fun y hy ↦ hg hy := by
    rw [excisionMap_eq_ofSubsetMap]
    exact ofSubsetMap_comp_ofSubsetMap_of_comp_eq _ _ _ rfl
  refine (congrArg (TopPair.singularCohomologyMap · n) (hcomp _ _)).trans
    (Eq.trans ?_ (congrArg (TopPair.singularCohomologyMap · n) (hcomp _ _)).symm)
  -- On the ball, the straight-line homotopy from `f` to its linearization avoids `f x` off `x`.
  refine (ofSubsetHomotopy (ContinuousMap.Homotopy.affine _ _)
    (fun t y hy ↦ ?_)).congr_singularCohomologyMap R k M n
  have hrem : ‖f y - f x - f' (y - x)‖ ≤ ε * ‖((y : U) : E) - x‖ := (hrU y.property).2
  -- The point of the segment is `f x + f' (y - x) + (1 - t) • (f y - f x - f' (y - x))`.
  have hseg : (1 - (t : ℝ)) • f y + (t : ℝ) • (f x + f' (y - x)) - f x =
      f' (y - x) + (1 - (t : ℝ)) • (f y - f x - f' (y - x)) := by
    module
  rw [ContinuousMap.Homotopy.affine_apply, AffineMap.lineMap_apply_module]
  refine fun h ↦ f'.apply_add_ne_zero_of_forall_norm_le hC hKε
    (x := ((y : U) : E) - x) (sub_ne_zero.2 fun h ↦ hy (Subtype.ext h)) ?_
    (hseg.symm.trans (sub_eq_zero.2 (Set.mem_singleton_iff.1 h)))
  rw [norm_smul, Real.norm_of_nonneg (by linarith [t.property.2])]
  exact (mul_le_of_le_one_left (norm_nonneg _) (by linarith [t.property.1])).trans hrem

end TopPair

end
