/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Projectivization.ProdZeroLocus.Basic
public import SymplecticGeometry.Geometry.Manifold.Projectivization.ProdZeroLocus.Chart
public import TauCeti.Analysis.Calculus.ImplicitFunction.Basic
public import TauCeti.Geometry.Manifold.Instances.Projectivization
public import TauCeti.Geometry.Manifold.LinearSlice
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Level

import SymplecticGeometry.Geometry.Manifold.Instances.Projectivization

/-!
# Regular bihomogeneous zero sets in a product of two projective spaces are complex manifolds

Let `p : ι → MvPolynomial (Fin (m + 1) ⊕ Fin (n + 1)) ℂ` be a finite family of bihomogeneous
polynomials, with zero set `X = complexProjectiveProdZeroLocus p` in
`ℙ ℂ (Fin (m + 1) → ℂ) × ℙ ℂ (Fin (n + 1) → ℂ)`, and let `s = X ∩ V` for an open set `V` of the
product, such that the cone Jacobian `jacobiMatrixAt p (Sum.elim x.1.rep x.2.rep)` is surjective
at every point `x` of `s`. Then `s` is a complex analytic submanifold of the product, of pure
dimension `k`, where `k + |ι| = m + n`. The constructions take `k` with a proof
`hk : k + Fintype.card ι = m + n`, so that a specialization can pass a literal `k`.

Near a point `x` of `X` lying in the product of the standard affine opens `affineOpen i` and
`affineOpen j`, the set `X` is cut out by the chart equations `prodChartEquations i j p` read in
the product of the two affine charts. By the regularity test
`surjective_fderiv_prodChartEquations_affineChart_iff` their derivative at the chart coordinates
of `x` is surjective. The complemented-kernel implicit function theorem then gives analytic
coordinates `u ↦ (g u, P (u - u_x))` on a neighbourhood of the chart coordinates `u_x` of `x`,
where `g` is the family of chart equations and `P` projects onto the kernel of its derivative at
`u_x`. Composing with the product of the affine charts, reading the kernel in
`Fin k → ℂ` and putting the equations last gives an analytic chart of the product
whose second component is `g`, so that it flattens `X` onto the slice where that component
vanishes. The atlas of `s` is the one that these charts, restricted to `V`, induce through
`TauCeti.linearSliceChartedSpace`.

## Main definitions

* `SymplecticGeometry.complexProjectiveProdZeroLocusSliceChart`: the analytic chart of the product
  that flattens the zero set near a point where the cone Jacobian is surjective.
* `SymplecticGeometry.complexProjectiveProdZeroLocusChartedSpace`: the atlas of `s`, modelled on
  `Fin k → ℂ`, whose dimension `Module.finrank_fin_fun` gives.
* `SymplecticGeometry.complexProjectiveProdZeroLocusEmbedding`: the inclusion of `s` into the
  product as a bundled `C^r` embedding, for the model
  `𝓘(ℂ, Fin m → ℂ).prod 𝓘(ℂ, Fin n → ℂ)` of the product.

## Main results

* `SymplecticGeometry.mem_complexProjectiveProdZeroLocus_iff_prodChartEquations`: in the product of
  two affine opens, the zero set is the zero set of the chart equations.
* `SymplecticGeometry.isSliceChart_complexProjectiveProdZeroLocusSliceChart`,
  `SymplecticGeometry.contMDiffOn_complexProjectiveProdZeroLocusSliceChart` and
  `SymplecticGeometry.contMDiffOn_complexProjectiveProdZeroLocusSliceChart_symm`: the slice chart
  flattens the zero set and is analytic in both directions.
* `SymplecticGeometry.isManifold_complexProjectiveProdZeroLocus`: `s` is an analytic manifold.
* `SymplecticGeometry.isImmersionOfComplement_subtypeVal_complexProjectiveProdZeroLocus` and
  `SymplecticGeometry.isSmoothEmbedding_subtypeVal_complexProjectiveProdZeroLocus`: its inclusion
  is an analytic immersion with complement `ι → ℂ` and an analytic embedding.
* `SymplecticGeometry.surjective_mfderiv_prodChartEquations_affineChart_iff`: the manifold
  derivative of the chart equations, read in the product of two affine charts, is surjective at a
  point of the zero set exactly when the cone Jacobian is.
* `SymplecticGeometry.tangentRange_complexProjectiveProdZeroLocusEmbedding` and
  `SymplecticGeometry.exact_mfderiv_subtypeVal_complexProjectiveProdZeroLocus`: the tangent space
  of `s` at a point is the kernel of the differential of the chart equations there, so that the
  differentials of the inclusion and of the chart equations form an exact sequence. Both follow
  from `TauCeti.SmoothEmbedding.tangentRange_eq_ker_mfderiv`.

The construction adapts Tau Ceti's `TauCeti.complexProjectiveZeroLocusSliceChart`,
`TauCeti.complexProjectiveZeroLocusChartedSpace`, `TauCeti.isManifold_complexProjectiveZeroLocus`,
`TauCeti.isSmoothEmbedding_subtypeVal_complexProjectiveZeroLocus`,
`TauCeti.complexProjectiveZeroLocusEmbedding`,
`TauCeti.tangentRange_complexProjectiveZeroLocusEmbedding` and
`TauCeti.exact_mfderiv_subtypeVal_complexProjectiveZeroLocus`
(`Geometry/Manifold/Projectivization/ZeroLocus.lean`), and
`TauCeti.surjective_mfderiv_eval_dehomogenize_affineChart_iff`
(`Geometry/Manifold/Projectivization/Polynomial.lean`),
which treat one projective space, to the product of two, with the product of two standard affine
charts in place of one. A bihomogeneous equation is not a global function on the product, so
Tau Ceti's regular-level atlas does not apply directly; the slice charts are built in the affine
charts instead.

## References

* [P. Griffiths and J. Harris, *Principles of Algebraic Geometry*][GriffithsHarris1978],
  Chapter 0, §2, for complex submanifolds cut out by equations of maximal rank.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Theorem 5.8 and Corollary 5.14, for slice charts and regular level sets.
-/

public section

open MvPolynomial Set Projectivization TauCeti
open scoped ContDiff Manifold LinearAlgebra.Projectivization

namespace SymplecticGeometry

variable {ι : Type*} {m n k : ℕ} {p : ι → MvPolynomial (Fin (m + 1) ⊕ Fin (n + 1)) ℂ}
  {d₁ d₂ : ι → ℕ} {i : Fin (m + 1)} {j : Fin (n + 1)}
  {x : ℙ ℂ (Fin (m + 1) → ℂ) × ℙ ℂ (Fin (n + 1) → ℂ)}

/-- In the product of the standard affine opens `affineOpen i` and `affineOpen j`, a point lies in
the zero set of a bihomogeneous family exactly when the chart equations vanish at its pair of
affine coordinates. -/
theorem mem_complexProjectiveProdZeroLocus_iff_prodChartEquations
    (hp₁ : ∀ l, (p l).IsWeightedHomogeneous (Sum.elim 1 0) (d₁ l))
    (hp₂ : ∀ l, (p l).IsWeightedHomogeneous (Sum.elim 0 1) (d₂ l))
    (hi : x.1 ∈ affineOpen i) (hj : x.2 ∈ affineOpen j) :
    x ∈ complexProjectiveProdZeroLocus p ↔
      ∀ k, prodChartEquations i j p (affineChart i x.1, affineChart j x.2) k = 0 := by
  obtain ⟨x₁, x₂⟩ := x
  have h₁ : (affineChart i).symm (affineChart i x₁) = x₁ :=
    (affineChart i).left_inv (by rwa [affineChart_source])
  have h₂ : (affineChart j).symm (affineChart j x₂) = x₂ :=
    (affineChart j).left_inv (by rwa [affineChart_source])
  conv_lhs => rw [← h₁, ← h₂, affineChart_symm_apply, affineChart_symm_apply,
    mk_mem_complexProjectiveProdZeroLocus_iff hp₁ hp₂]
  simp only [prodChartEquations_apply]

/-- At a point of the zero set of a bihomogeneous family in the product of the affine opens
`affineOpen i` and `affineOpen j`, the derivative of the chart equations at its affine coordinates
is surjective exactly when the cone Jacobian at the chosen representatives is. -/
theorem surjective_fderiv_prodChartEquations_affineChart_iff_rep
    (hp₁ : ∀ l, (p l).IsWeightedHomogeneous (Sum.elim 1 0) (d₁ l))
    (hp₂ : ∀ l, (p l).IsWeightedHomogeneous (Sum.elim 0 1) (d₂ l))
    (hx : x ∈ complexProjectiveProdZeroLocus p) (hi : x.1 ∈ affineOpen i)
    (hj : x.2 ∈ affineOpen j) :
    Function.Surjective
        (fderiv ℂ (prodChartEquations i j p) (affineChart i x.1, affineChart j x.2)) ↔
      Function.Surjective (jacobiMatrixAt p (Sum.elim x.1.rep x.2.rep)).mulVec := by
  have h := surjective_fderiv_prodChartEquations_affineChart_iff hp₁ hp₂ x.1.rep_ne_zero
    x.2.rep_ne_zero ((mem_affineOpen_iff i _).1 hi) ((mem_affineOpen_iff j _).1 hj)
    ((mem_complexProjectiveProdZeroLocus_iff_eval_rep hp₁ hp₂ x).1 hx)
  rwa [mk_rep, mk_rep] at h

/-- At a point of the zero set of a bihomogeneous family in the product of the affine opens
`affineOpen i` and `affineOpen j`, the manifold derivative of the chart equations read in the
product of the two affine charts is surjective exactly when the cone Jacobian at the chosen
representatives is. -/
theorem surjective_mfderiv_prodChartEquations_affineChart_iff [Fintype ι]
    (hp₁ : ∀ l, (p l).IsWeightedHomogeneous (Sum.elim 1 0) (d₁ l))
    (hp₂ : ∀ l, (p l).IsWeightedHomogeneous (Sum.elim 0 1) (d₂ l))
    (hx : x ∈ complexProjectiveProdZeroLocus p) (hi : x.1 ∈ affineOpen i)
    (hj : x.2 ∈ affineOpen j) :
    Function.Surjective (mfderiv (𝓘(ℂ, Fin m → ℂ).prod 𝓘(ℂ, Fin n → ℂ)) 𝓘(ℂ, ι → ℂ)
      (fun y : ℙ ℂ (Fin (m + 1) → ℂ) × ℙ ℂ (Fin (n + 1) → ℂ) ↦
        prodChartEquations i j p (affineChart i y.1, affineChart j y.2)) x) ↔
      Function.Surjective (jacobiMatrixAt p (Sum.elim x.1.rep x.2.rep)).mulVec := by
  -- The differential of the product of the two affine charts is bijective, so the chain rule
  -- reduces the claim to the Fréchet derivative.
  have h := (hasMFDerivAt_comp_affineChart_prodMap
    (hasStrictFDerivAt_prodChartEquations i j p _).hasFDerivAt hi hj).mfderiv
  simp only [Function.comp_def, Prod.map_apply'] at h
  rw [h]
  exact (congrArg Function.Surjective (ContinuousLinearMap.coe_comp
    (fderiv ℂ (prodChartEquations i j p) (affineChart i x.1, affineChart j x.2)) _)).to_iff.trans <|
    (Function.Surjective.of_comp_iff _
      (bijective_mfderiv_affineChart_prodMap hi hj).surjective).trans
      (surjective_fderiv_prodChartEquations_affineChart_iff_rep hp₁ hp₂ hx hi hj)

namespace ComplexProjectiveProdZeroLocus

/-- At a point of the zero set where the cone Jacobian is surjective, so is the derivative of the
chart equations. -/
private theorem range_fderiv (hp₁ : ∀ l, (p l).IsWeightedHomogeneous (Sum.elim 1 0) (d₁ l))
    (hp₂ : ∀ l, (p l).IsWeightedHomogeneous (Sum.elim 0 1) (d₂ l))
    (hx : x ∈ complexProjectiveProdZeroLocus p) (hi : x.1 ∈ affineOpen i)
    (hj : x.2 ∈ affineOpen j)
    (hrank : Function.Surjective (jacobiMatrixAt p (Sum.elim x.1.rep x.2.rep)).mulVec) :
    (fderiv ℂ (prodChartEquations i j p) (affineChart i x.1, affineChart j x.2)).range = ⊤ :=
  LinearMap.range_eq_top.2
    ((surjective_fderiv_prodChartEquations_affineChart_iff_rep hp₁ hp₂ hx hi hj).2 hrank)

variable [Fintype ι]

/-- Rank–nullity for the surjective derivative of the chart equations. -/
private theorem card_add_finrank_ker
    (hp₁ : ∀ l, (p l).IsWeightedHomogeneous (Sum.elim 1 0) (d₁ l))
    (hp₂ : ∀ l, (p l).IsWeightedHomogeneous (Sum.elim 0 1) (d₂ l))
    (hx : x ∈ complexProjectiveProdZeroLocus p) (hi : x.1 ∈ affineOpen i)
    (hj : x.2 ∈ affineOpen j)
    (hrank : Function.Surjective (jacobiMatrixAt p (Sum.elim x.1.rep x.2.rep)).mulVec) :
    Fintype.card ι + Module.finrank ℂ
      (fderiv ℂ (prodChartEquations i j p) (affineChart i x.1, affineChart j x.2)).ker = m + n := by
  have h := LinearMap.finrank_range_add_finrank_ker
    (fderiv ℂ (prodChartEquations i j p) (affineChart i x.1, affineChart j x.2) :
      (Fin m → ℂ) × (Fin n → ℂ) →ₗ[ℂ] ι → ℂ)
  rwa [range_fderiv hp₁ hp₂ hx hi hj hrank, finrank_top, Module.finrank_fintype_fun_eq_card,
    Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_fin_fun] at h

/-- The implicit-function chart `u ↦ (g u, P (u - u_x))` of the chart equations `g` at the affine
coordinates `u_x` of `x`. -/
private noncomputable def implicitChart
    (hp₁ : ∀ l, (p l).IsWeightedHomogeneous (Sum.elim 1 0) (d₁ l))
    (hp₂ : ∀ l, (p l).IsWeightedHomogeneous (Sum.elim 0 1) (d₂ l))
    (hx : x ∈ complexProjectiveProdZeroLocus p) (hi : x.1 ∈ affineOpen i)
    (hj : x.2 ∈ affineOpen j)
    (hrank : Function.Surjective (jacobiMatrixAt p (Sum.elim x.1.rep x.2.rep)).mulVec) :
    OpenPartialHomeomorph ((Fin m → ℂ) × (Fin n → ℂ)) ((ι → ℂ) ×
      (fderiv ℂ (prodChartEquations i j p) (affineChart i x.1, affineChart j x.2)).ker) :=
  (hasStrictFDerivAt_prodChartEquations i j p _).implicitToOpenPartialHomeomorphOfComplemented _ _
    (range_fderiv hp₁ hp₂ hx hi hj hrank)
    (ContinuousLinearMap.ker_closedComplemented_of_finiteDimensional_range _)

/-- The neighbourhood of the affine coordinates of `x` on which the implicit-function chart keeps
an invertible derivative. -/
private noncomputable def implicitSource
    (hp₁ : ∀ l, (p l).IsWeightedHomogeneous (Sum.elim 1 0) (d₁ l))
    (hp₂ : ∀ l, (p l).IsWeightedHomogeneous (Sum.elim 0 1) (d₂ l))
    (hx : x ∈ complexProjectiveProdZeroLocus p) (hi : x.1 ∈ affineOpen i)
    (hj : x.2 ∈ affineOpen j)
    (hrank : Function.Surjective (jacobiMatrixAt p (Sum.elim x.1.rep x.2.rep)).mulVec) :
    Set ((Fin m → ℂ) × (Fin n → ℂ)) :=
  (hasStrictFDerivAt_prodChartEquations i j p _).implicitCoordSource
    (range_fderiv hp₁ hp₂ hx hi hj hrank)
    (ContinuousLinearMap.ker_closedComplemented_of_finiteDimensional_range _)

private theorem isOpen_implicitSource
    (hp₁ : ∀ l, (p l).IsWeightedHomogeneous (Sum.elim 1 0) (d₁ l))
    (hp₂ : ∀ l, (p l).IsWeightedHomogeneous (Sum.elim 0 1) (d₂ l))
    (hx : x ∈ complexProjectiveProdZeroLocus p) (hi : x.1 ∈ affineOpen i)
    (hj : x.2 ∈ affineOpen j)
    (hrank : Function.Surjective (jacobiMatrixAt p (Sum.elim x.1.rep x.2.rep)).mulVec) :
    IsOpen (implicitSource hp₁ hp₂ hx hi hj hrank) :=
  (hasStrictFDerivAt_prodChartEquations i j p _).isOpen_implicitCoordSource _ _

/-- Reading the kernel in `Fin k → ℂ`, for `k + |ι| = m + n`, and putting the equations
last. -/
private noncomputable def coordEquiv (hk : k + Fintype.card ι = m + n)
    (hp₁ : ∀ l, (p l).IsWeightedHomogeneous (Sum.elim 1 0) (d₁ l))
    (hp₂ : ∀ l, (p l).IsWeightedHomogeneous (Sum.elim 0 1) (d₂ l))
    (hx : x ∈ complexProjectiveProdZeroLocus p) (hi : x.1 ∈ affineOpen i)
    (hj : x.2 ∈ affineOpen j)
    (hrank : Function.Surjective (jacobiMatrixAt p (Sum.elim x.1.rep x.2.rep)).mulVec) :
    ((ι → ℂ) × (fderiv ℂ (prodChartEquations i j p) (affineChart i x.1, affineChart j x.2)).ker)
      ≃L[ℂ] (Fin k → ℂ) × (ι → ℂ) :=
  (ContinuousLinearEquiv.prodComm ℂ _ _).trans
    ((ContinuousLinearEquiv.ofFinrankEq (by
      have := card_add_finrank_ker hp₁ hp₂ hx hi hj hrank
      rw [Module.finrank_fin_fun]
      omega)).prodCongr (ContinuousLinearEquiv.refl ℂ _))

/-- The identification of the slice-chart model with the model of the product, when
`k + |ι| = m + n`. -/
private noncomputable def modelEquiv (hk : k + Fintype.card ι = m + n) :
    ((Fin k → ℂ) × (ι → ℂ)) ≃L[ℂ] (Fin m → ℂ) × (Fin n → ℂ) :=
  ContinuousLinearEquiv.ofFinrankEq (by
    simp only [Module.finrank_prod, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    omega)

private theorem coordEquiv_apply_snd (hk : k + Fintype.card ι = m + n)
    (hp₁ : ∀ l, (p l).IsWeightedHomogeneous (Sum.elim 1 0) (d₁ l))
    (hp₂ : ∀ l, (p l).IsWeightedHomogeneous (Sum.elim 0 1) (d₂ l))
    (hx : x ∈ complexProjectiveProdZeroLocus p) (hi : x.1 ∈ affineOpen i)
    (hj : x.2 ∈ affineOpen j)
    (hrank : Function.Surjective (jacobiMatrixAt p (Sum.elim x.1.rep x.2.rep)).mulVec)
    (v : (ι → ℂ) ×
      (fderiv ℂ (prodChartEquations i j p) (affineChart i x.1, affineChart j x.2)).ker) :
    (coordEquiv hk hp₁ hp₂ hx hi hj hrank v).2 = v.1 :=
  (rfl)

end ComplexProjectiveProdZeroLocus

open ComplexProjectiveProdZeroLocus

variable [Fintype ι]

/-- **The slice chart of a regular bihomogeneous zero set.** Let `x` be a point of the zero set of
a bihomogeneous family `p`, in the product of the standard affine opens `affineOpen i` and
`affineOpen j`, at which the cone Jacobian of `p` is surjective. This is an analytic chart of
`ℙ ℂ (Fin (m + 1) → ℂ) × ℙ ℂ (Fin (n + 1) → ℂ)` around `x`, modelled on
`(Fin k → ℂ) × (ι → ℂ)` for `k + |ι| = m + n`, whose second component is the family of chart
equations `prodChartEquations i j p` read in the product of the two affine charts
(`SymplecticGeometry.complexProjectiveProdZeroLocusSliceChart_apply_snd`), and which therefore
flattens the zero set onto the slice where that component vanishes
(`SymplecticGeometry.isSliceChart_complexProjectiveProdZeroLocusSliceChart`). -/
noncomputable def complexProjectiveProdZeroLocusSliceChart (hk : k + Fintype.card ι = m + n)
    (hp₁ : ∀ l, (p l).IsWeightedHomogeneous (Sum.elim 1 0) (d₁ l))
    (hp₂ : ∀ l, (p l).IsWeightedHomogeneous (Sum.elim 0 1) (d₂ l))
    (hx : x ∈ complexProjectiveProdZeroLocus p) (hi : x.1 ∈ affineOpen i)
    (hj : x.2 ∈ affineOpen j)
    (hrank : Function.Surjective (jacobiMatrixAt p (Sum.elim x.1.rep x.2.rep)).mulVec) :
    OpenPartialHomeomorph (ℙ ℂ (Fin (m + 1) → ℂ) × ℙ ℂ (Fin (n + 1) → ℂ))
      ((Fin k → ℂ) × (ι → ℂ)) :=
  ((affineOpenPartialHomeomorph i).prod (affineOpenPartialHomeomorph j)).trans
    (((implicitChart hp₁ hp₂ hx hi hj hrank).restrOpen (implicitSource hp₁ hp₂ hx hi hj hrank)
      (isOpen_implicitSource hp₁ hp₂ hx hi hj hrank)).transHomeomorph
      (coordEquiv hk hp₁ hp₂ hx hi hj hrank).toHomeomorph)

section SliceChart

variable (hk : k + Fintype.card ι = m + n)
  (hp₁ : ∀ l, (p l).IsWeightedHomogeneous (Sum.elim 1 0) (d₁ l))
  (hp₂ : ∀ l, (p l).IsWeightedHomogeneous (Sum.elim 0 1) (d₂ l))
  (hx : x ∈ complexProjectiveProdZeroLocus p) (hi : x.1 ∈ affineOpen i)
  (hj : x.2 ∈ affineOpen j)
  (hrank : Function.Surjective (jacobiMatrixAt p (Sum.elim x.1.rep x.2.rep)).mulVec)

/-- The slice chart unfolded: the product of the affine charts, then the implicit-function chart
of the chart equations, then the linear identification of its target with the model. -/
private theorem coe_complexProjectiveProdZeroLocusSliceChart :
    ⇑(complexProjectiveProdZeroLocusSliceChart hk hp₁ hp₂ hx hi hj hrank) =
      coordEquiv hk hp₁ hp₂ hx hi hj hrank ∘ implicitChart hp₁ hp₂ hx hi hj hrank ∘
        fun y ↦ (affineChart i y.1, affineChart j y.2) := by
  rw [complexProjectiveProdZeroLocusSliceChart, OpenPartialHomeomorph.coe_trans,
    OpenPartialHomeomorph.transHomeomorph_apply, OpenPartialHomeomorph.coe_restrOpen,
    OpenPartialHomeomorph.prod_apply, coe_affineOpenPartialHomeomorph,
    coe_affineOpenPartialHomeomorph, ContinuousLinearEquiv.coe_toHomeomorph, Function.comp_assoc]

private theorem coe_complexProjectiveProdZeroLocusSliceChart_symm :
    ⇑(complexProjectiveProdZeroLocusSliceChart hk hp₁ hp₂ hx hi hj hrank).symm =
      (fun v ↦ ((affineChart i).symm v.1, (affineChart j).symm v.2)) ∘
        (implicitChart hp₁ hp₂ hx hi hj hrank).symm ∘
          (coordEquiv hk hp₁ hp₂ hx hi hj hrank).symm := by
  rw [complexProjectiveProdZeroLocusSliceChart, OpenPartialHomeomorph.coe_trans_symm,
    OpenPartialHomeomorph.transHomeomorph_symm_apply, OpenPartialHomeomorph.coe_restrOpen_symm,
    OpenPartialHomeomorph.prod_symm, OpenPartialHomeomorph.prod_apply,
    coe_affineOpenPartialHomeomorph_symm, coe_affineOpenPartialHomeomorph_symm,
    ContinuousLinearEquiv.coe_symm_toHomeomorph]

/-- The source of the slice chart: points of the product of the two affine opens whose affine
coordinates lie in the source of the implicit-function chart, restricted to where its derivative
stays invertible. -/
private theorem complexProjectiveProdZeroLocusSliceChart_source :
    (complexProjectiveProdZeroLocusSliceChart hk hp₁ hp₂ hx hi hj hrank).source =
      affineOpen i ×ˢ affineOpen j ∩ (fun y ↦ (affineChart i y.1, affineChart j y.2)) ⁻¹'
        ((implicitChart hp₁ hp₂ hx hi hj hrank).source ∩
          implicitSource hp₁ hp₂ hx hi hj hrank) := by
  rw [complexProjectiveProdZeroLocusSliceChart, OpenPartialHomeomorph.trans_source,
    OpenPartialHomeomorph.transHomeomorph_source, OpenPartialHomeomorph.restrOpen_source,
    OpenPartialHomeomorph.prod_source, OpenPartialHomeomorph.prod_apply,
    coe_affineOpenPartialHomeomorph, coe_affineOpenPartialHomeomorph]
  simp only [affineOpenPartialHomeomorph_toPartialEquiv, affineChart_source]

/-- The target of the slice chart: the points whose image under the inverse linear identification
lies in the target of the implicit-function chart, with inverse image in the neighbourhood where
its derivative stays invertible. -/
private theorem complexProjectiveProdZeroLocusSliceChart_target :
    (complexProjectiveProdZeroLocusSliceChart hk hp₁ hp₂ hx hi hj hrank).target =
      (coordEquiv hk hp₁ hp₂ hx hi hj hrank).symm ⁻¹'
        ((implicitChart hp₁ hp₂ hx hi hj hrank).target ∩
          (implicitChart hp₁ hp₂ hx hi hj hrank).symm ⁻¹'
            implicitSource hp₁ hp₂ hx hi hj hrank) := by
  rw [complexProjectiveProdZeroLocusSliceChart, OpenPartialHomeomorph.trans_target,
    OpenPartialHomeomorph.transHomeomorph_target, OpenPartialHomeomorph.restrOpen_toPartialEquiv]
  simp

/-- The second component of the slice chart is the family of chart equations, read in the product
of the standard affine charts `i` and `j`. -/
@[simp]
theorem complexProjectiveProdZeroLocusSliceChart_apply_snd
    (y : ℙ ℂ (Fin (m + 1) → ℂ) × ℙ ℂ (Fin (n + 1) → ℂ)) :
    (complexProjectiveProdZeroLocusSliceChart hk hp₁ hp₂ hx hi hj hrank y).2 =
      prodChartEquations i j p (affineChart i y.1, affineChart j y.2) := by
  rw [coe_complexProjectiveProdZeroLocusSliceChart, Function.comp_apply, coordEquiv_apply_snd,
    Function.comp_apply, implicitChart,
    HasStrictFDerivAt.implicitToOpenPartialHomeomorphOfComplemented_fst]

/-- The source of the slice chart lies in the product of the affine opens `affineOpen i` and
`affineOpen j`. -/
theorem complexProjectiveProdZeroLocusSliceChart_source_subset :
    (complexProjectiveProdZeroLocusSliceChart hk hp₁ hp₂ hx hi hj hrank).source ⊆
      affineOpen i ×ˢ affineOpen j := by
  rw [complexProjectiveProdZeroLocusSliceChart_source]
  exact inter_subset_left

/-- The slice chart is defined at its base point. -/
theorem mem_complexProjectiveProdZeroLocusSliceChart_source :
    x ∈ (complexProjectiveProdZeroLocusSliceChart hk hp₁ hp₂ hx hi hj hrank).source := by
  rw [complexProjectiveProdZeroLocusSliceChart_source]
  refine ⟨⟨hi, hj⟩, ?_, ?_⟩
  · exact (hasStrictFDerivAt_prodChartEquations i j p _
      ).mem_implicitToOpenPartialHomeomorphOfComplemented_source _ _
  · exact (hasStrictFDerivAt_prodChartEquations i j p _).mem_implicitCoordSource _ _

/-- **The slice chart flattens the zero set.** On its source, a point lies in the zero set exactly
when its slice-chart coordinates lie in the slice `Fin k → ℂ` times `0`. -/
theorem isSliceChart_complexProjectiveProdZeroLocusSliceChart :
    IsSliceChart (complexProjectiveProdZeroLocusSliceChart hk hp₁ hp₂ hx hi hj hrank)
      ((univ : Set (Fin k → ℂ)) ×ˢ ({0} : Set (ι → ℂ)))
      (complexProjectiveProdZeroLocus p) := by
  refine isSliceChart_iff.2 fun y hy ↦ ?_
  have hy' := complexProjectiveProdZeroLocusSliceChart_source_subset hk hp₁ hp₂ hx hi hj hrank hy
  rw [mem_complexProjectiveProdZeroLocus_iff_prodChartEquations hp₁ hp₂ hy'.1 hy'.2]
  simp [funext_iff]

/-- The slice chart is analytic, indeed `C^r` for every `r`, on its source. -/
theorem contMDiffOn_complexProjectiveProdZeroLocusSliceChart (r : ℕ∞ω) :
    ContMDiffOn (𝓘(ℂ, Fin m → ℂ).prod 𝓘(ℂ, Fin n → ℂ))
      𝓘(ℂ, (Fin k → ℂ) × (ι → ℂ)) r
      (complexProjectiveProdZeroLocusSliceChart hk hp₁ hp₂ hx hi hj hrank)
      (complexProjectiveProdZeroLocusSliceChart hk hp₁ hp₂ hx hi hj hrank).source := by
  intro y hy
  have hy' := complexProjectiveProdZeroLocusSliceChart_source_subset hk hp₁ hp₂ hx hi hj hrank hy
  have hchart := contMDiffAt_affineChart_prodMap (r := r) hy'.1 hy'.2
  rw [Prod.map_def] at hchart
  have himplicit : ContDiffAt ℂ r
      (coordEquiv hk hp₁ hp₂ hx hi hj hrank ∘ implicitChart hp₁ hp₂ hx hi hj hrank)
      (affineChart i y.1, affineChart j y.2) :=
    (coordEquiv hk hp₁ hp₂ hx hi hj hrank).contDiff.contDiffAt.comp _
      ((hasStrictFDerivAt_prodChartEquations i j p _
        ).contDiffAt_implicitToOpenPartialHomeomorphOfComplemented
        (contDiff_prodChartEquations i j p).contDiffAt _ _)
  rw [coe_complexProjectiveProdZeroLocusSliceChart]
  exact (himplicit.contMDiffAt.comp y hchart).contMDiffWithinAt

/-- The inverse of the slice chart is analytic, indeed `C^r` for every `r`, on its target. -/
theorem contMDiffOn_complexProjectiveProdZeroLocusSliceChart_symm (r : ℕ∞ω) :
    ContMDiffOn 𝓘(ℂ, (Fin k → ℂ) × (ι → ℂ))
      (𝓘(ℂ, Fin m → ℂ).prod 𝓘(ℂ, Fin n → ℂ)) r
      (complexProjectiveProdZeroLocusSliceChart hk hp₁ hp₂ hx hi hj hrank).symm
      (complexProjectiveProdZeroLocusSliceChart hk hp₁ hp₂ hx hi hj hrank).target := by
  intro v hv
  -- The target of the slice chart sits over the restricted target of the implicit chart.
  rw [complexProjectiveProdZeroLocusSliceChart_target] at hv
  obtain ⟨hvt, hvs⟩ := hv
  have hinv : ContDiffAt ℂ r
      ((implicitChart hp₁ hp₂ hx hi hj hrank).symm ∘
        (coordEquiv hk hp₁ hp₂ hx hi hj hrank).symm) v :=
    ((hasStrictFDerivAt_prodChartEquations i j p _
      ).contDiffAt_implicitToOpenPartialHomeomorphOfComplemented_symm_of_mem _ _ hvt hvs
      (contDiff_prodChartEquations i j p).contDiffAt).comp v
      (coordEquiv hk hp₁ hp₂ hx hi hj hrank).symm.contDiff.contDiffAt
  have hchart : ContMDiff 𝓘(ℂ, (Fin m → ℂ) × (Fin n → ℂ))
      (𝓘(ℂ, Fin m → ℂ).prod 𝓘(ℂ, Fin n → ℂ)) r
      (fun u : (Fin m → ℂ) × (Fin n → ℂ) ↦ ((affineChart i).symm u.1, (affineChart j).symm u.2)) :=
    ((contMDiff_affineChart_symm i r).comp contDiff_fst.contMDiff).prodMk
      ((contMDiff_affineChart_symm j r).comp contDiff_snd.contMDiff)
  rw [coe_complexProjectiveProdZeroLocusSliceChart_symm]
  exact ((hchart _).comp v hinv.contMDiffAt).contMDiffWithinAt

end SliceChart

/-! ### The submanifold structure -/

section Submanifold

variable (hk : k + Fintype.card ι = m + n)
  (hp₁ : ∀ l, (p l).IsWeightedHomogeneous (Sum.elim 1 0) (d₁ l))
  (hp₂ : ∀ l, (p l).IsWeightedHomogeneous (Sum.elim 0 1) (d₂ l))
  {s V : Set (ℙ ℂ (Fin (m + 1) → ℂ) × ℙ ℂ (Fin (n + 1) → ℂ))}
  (hV : IsOpen V) (hs : s = complexProjectiveProdZeroLocus p ∩ V)
  (hrank : ∀ x ∈ s, Function.Surjective (jacobiMatrixAt p (Sum.elim x.1.rep x.2.rep)).mulVec)

/-- The slice chart at a point `z` of `s`, taken in the standard affine charts that `chartAt`
uses for the two projective spaces at the components of `z`. -/
private noncomputable abbrev sliceChartAt (z : s) :
    OpenPartialHomeomorph (ℙ ℂ (Fin (m + 1) → ℂ) × ℙ ℂ (Fin (n + 1) → ℂ))
      ((Fin k → ℂ) × (ι → ℂ)) :=
  complexProjectiveProdZeroLocusSliceChart hk hp₁ hp₂ (hs.subset z.property).1
    (exists_mem_affineOpen (z : ℙ ℂ (Fin (m + 1) → ℂ) × ℙ ℂ (Fin (n + 1) → ℂ)).1).choose_spec
    (exists_mem_affineOpen (z : ℙ ℂ (Fin (m + 1) → ℂ) × ℙ ℂ (Fin (n + 1) → ℂ)).2).choose_spec
    (hrank z z.property)

/-- The slice chart at `z`, restricted to the open set cutting `s` out of the zero set. -/
private noncomputable def restrSliceChart (z : s) :
    OpenPartialHomeomorph (ℙ ℂ (Fin (m + 1) → ℂ) × ℙ ℂ (Fin (n + 1) → ℂ))
      ((Fin k → ℂ) × (ι → ℂ)) :=
  (sliceChartAt hk hp₁ hp₂ hs hrank z).restrOpen V hV

private theorem restrSliceChart_source (z : s) :
    (restrSliceChart hk hp₁ hp₂ hV hs hrank z).source =
      (sliceChartAt hk hp₁ hp₂ hs hrank z).source ∩ V :=
  OpenPartialHomeomorph.restrOpen_source _ _ _

private theorem isSliceChart_restrSliceChart (z : s) :
    IsSliceChart (restrSliceChart hk hp₁ hp₂ hV hs hrank z)
      ((univ : Set (Fin k → ℂ)) ×ˢ ({0} : Set (ι → ℂ))) s := by
  simpa only [restrSliceChart, ← hs] using
    (isSliceChart_complexProjectiveProdZeroLocusSliceChart hk hp₁ hp₂ _ _ _ _).restrOpen hV

private theorem mem_restrSliceChart_source (z : s) :
    (z : ℙ ℂ (Fin (m + 1) → ℂ) × ℙ ℂ (Fin (n + 1) → ℂ)) ∈
      (restrSliceChart hk hp₁ hp₂ hV hs hrank z).source := by
  rw [restrSliceChart_source]
  exact ⟨mem_complexProjectiveProdZeroLocusSliceChart_source hk hp₁ hp₂ _ _ _ _,
    (hs.subset z.property).2⟩

private theorem contMDiffOn_restrSliceChart (r : ℕ∞ω) (z : s) :
    ContMDiffOn (𝓘(ℂ, Fin m → ℂ).prod 𝓘(ℂ, Fin n → ℂ))
      𝓘(ℂ, (Fin k → ℂ) × (ι → ℂ)) r
      (restrSliceChart hk hp₁ hp₂ hV hs hrank z)
      (restrSliceChart hk hp₁ hp₂ hV hs hrank z).source := by
  rw [restrSliceChart_source]
  exact (contMDiffOn_complexProjectiveProdZeroLocusSliceChart hk hp₁ hp₂ _ _ _ _ r).mono
    inter_subset_left

private theorem contMDiffOn_restrSliceChart_symm (r : ℕ∞ω) (z : s) :
    ContMDiffOn 𝓘(ℂ, (Fin k → ℂ) × (ι → ℂ))
      (𝓘(ℂ, Fin m → ℂ).prod 𝓘(ℂ, Fin n → ℂ)) r
      (restrSliceChart hk hp₁ hp₂ hV hs hrank z).symm
      (restrSliceChart hk hp₁ hp₂ hV hs hrank z).target :=
  (contMDiffOn_complexProjectiveProdZeroLocusSliceChart_symm hk hp₁ hp₂ _ _ _ _ r).mono
    fun _ hv ↦ hv.1

/-- **The complex manifold structure of a regular part of a bihomogeneous zero set.** Let `s` be a
relatively open subset of the zero set of a bihomogeneous family `p` in
`ℙ ℂ (Fin (m + 1) → ℂ) × ℙ ℂ (Fin (n + 1) → ℂ)`, that is `s = complexProjectiveProdZeroLocus p ∩ V`
for an open set `V`, at every point `x` of which the cone Jacobian of `p` at
`Sum.elim x.1.rep x.2.rep` is surjective. Then `s`, with the topology induced from the product,
carries the atlas induced by the slice charts
`SymplecticGeometry.complexProjectiveProdZeroLocusSliceChart`, modelled on
`Fin k → ℂ` for `k + |ι| = m + n`. At a point `z` the chart is taken in the standard affine
charts that `chartAt` uses for the two projective spaces at the components of `z`
(`SymplecticGeometry.complexProjectiveProdZeroLocusChartedSpace_chartAt_apply`). -/
@[instance_reducible]
noncomputable def complexProjectiveProdZeroLocusChartedSpace :
    ChartedSpace (Fin k → ℂ) s :=
  linearSliceChartedSpace (restrSliceChart hk hp₁ hp₂ hV hs hrank)
    (isSliceChart_restrSliceChart hk hp₁ hp₂ hV hs hrank)
    (mem_restrSliceChart_source hk hp₁ hp₂ hV hs hrank)

/-- The chart of `s` at `z` reads the first coordinate of the slice chart at `z`. -/
theorem complexProjectiveProdZeroLocusChartedSpace_chartAt_apply (z w : s) :
    @chartAt _ _ _ _ (complexProjectiveProdZeroLocusChartedSpace hk hp₁ hp₂ hV hs hrank) z w =
      (complexProjectiveProdZeroLocusSliceChart hk hp₁ hp₂ (hs.subset z.property).1
        (exists_mem_affineOpen (z : ℙ ℂ (Fin (m + 1) → ℂ) × ℙ ℂ (Fin (n + 1) → ℂ)).1).choose_spec
        (exists_mem_affineOpen (z : ℙ ℂ (Fin (m + 1) → ℂ) × ℙ ℂ (Fin (n + 1) → ℂ)).2).choose_spec
        (hrank z z.property) w).1 := by
  rw [complexProjectiveProdZeroLocusChartedSpace, linearSliceChartedSpace_chartAt,
    linearSliceChart_apply, restrSliceChart, OpenPartialHomeomorph.coe_restrOpen]

/-- The chart of `s` at `z` is defined on the part of `s` in the source of the slice chart at
`z`. -/
theorem complexProjectiveProdZeroLocusChartedSpace_chartAt_source (z : s) :
    (@chartAt _ _ _ _
      (complexProjectiveProdZeroLocusChartedSpace hk hp₁ hp₂ hV hs hrank) z).source =
      Subtype.val ⁻¹' (complexProjectiveProdZeroLocusSliceChart hk hp₁ hp₂ (hs.subset z.property).1
        (exists_mem_affineOpen (z : ℙ ℂ (Fin (m + 1) → ℂ) × ℙ ℂ (Fin (n + 1) → ℂ)).1).choose_spec
        (exists_mem_affineOpen (z : ℙ ℂ (Fin (m + 1) → ℂ) × ℙ ℂ (Fin (n + 1) → ℂ)).2).choose_spec
        (hrank z z.property)).source := by
  rw [complexProjectiveProdZeroLocusChartedSpace, linearSliceChartedSpace_chartAt,
    linearSliceChart_source, restrSliceChart_source, preimage_inter, inter_eq_left]
  exact fun w _ ↦ (hs.subset w.property).2

/-- **A regular part of a bihomogeneous zero set is a complex manifold.** With the atlas
`SymplecticGeometry.complexProjectiveProdZeroLocusChartedSpace`, a relatively open subset of the
zero set on which the cone Jacobian is surjective is an analytic manifold of pure dimension
`k`, where `k + |ι| = m + n`; it is `C^r` for every `r`. -/
theorem isManifold_complexProjectiveProdZeroLocus (r : ℕ∞ω) :
    letI := complexProjectiveProdZeroLocusChartedSpace hk hp₁ hp₂ hV hs hrank
    IsManifold 𝓘(ℂ, Fin k → ℂ) r s :=
  isManifold_linearSliceChartedSpace _ _
    (fun z _ hw ↦ (contMDiffOn_restrSliceChart hk hp₁ hp₂ hV hs hrank r z).contMDiffAt
      ((OpenPartialHomeomorph.open_source _).mem_nhds hw))
    (fun z _ hv ↦ (contMDiffOn_restrSliceChart_symm hk hp₁ hp₂ hV hs hrank r z).contMDiffAt
      ((OpenPartialHomeomorph.open_target _).mem_nhds hv)) _

/-- **The inclusion of a regular part of a bihomogeneous zero set is an immersion with normal
model `ι → ℂ`.** For the atlas `SymplecticGeometry.complexProjectiveProdZeroLocusChartedSpace`,
the inclusion into the product of the two projective spaces is a `C^r` immersion, for every `r`,
whose complement is the space `ι → ℂ` of values of the equations. -/
theorem isImmersionOfComplement_subtypeVal_complexProjectiveProdZeroLocus (r : ℕ∞ω) :
    letI := complexProjectiveProdZeroLocusChartedSpace hk hp₁ hp₂ hV hs hrank
    Manifold.IsImmersionOfComplement (ι → ℂ) 𝓘(ℂ, Fin k → ℂ)
      (𝓘(ℂ, Fin m → ℂ).prod 𝓘(ℂ, Fin n → ℂ)) r
      (Subtype.val : s → ℙ ℂ (Fin (m + 1) → ℂ) × ℙ ℂ (Fin (n + 1) → ℂ)) :=
  isImmersionOfComplement_subtypeVal_linearSliceChartedSpace
    (I := 𝓘(ℂ, Fin m → ℂ).prod 𝓘(ℂ, Fin n → ℂ)) (restrSliceChart hk hp₁ hp₂ hV hs hrank)
    (isSliceChart_restrSliceChart hk hp₁ hp₂ hV hs hrank)
    (fun _ ↦ modelEquiv hk)
    (contMDiffOn_restrSliceChart hk hp₁ hp₂ hV hs hrank r)
    (contMDiffOn_restrSliceChart_symm hk hp₁ hp₂ hV hs hrank r)
    (mem_restrSliceChart_source hk hp₁ hp₂ hV hs hrank)

/-- **A regular part of a bihomogeneous zero set is an embedded complex submanifold.** For the
atlas `SymplecticGeometry.complexProjectiveProdZeroLocusChartedSpace`, the inclusion into the
product of the two projective spaces is a `C^r` embedding for every `r`. -/
theorem isSmoothEmbedding_subtypeVal_complexProjectiveProdZeroLocus (r : ℕ∞ω) :
    letI := complexProjectiveProdZeroLocusChartedSpace hk hp₁ hp₂ hV hs hrank
    Manifold.IsSmoothEmbedding 𝓘(ℂ, Fin k → ℂ)
      (𝓘(ℂ, Fin m → ℂ).prod 𝓘(ℂ, Fin n → ℂ)) r
      (Subtype.val : s → ℙ ℂ (Fin (m + 1) → ℂ) × ℙ ℂ (Fin (n + 1) → ℂ)) :=
  isSmoothEmbedding_subtypeVal_linearSliceChartedSpace
    (I := 𝓘(ℂ, Fin m → ℂ).prod 𝓘(ℂ, Fin n → ℂ)) (restrSliceChart hk hp₁ hp₂ hV hs hrank)
    (isSliceChart_restrSliceChart hk hp₁ hp₂ hV hs hrank)
    (fun _ ↦ modelEquiv hk)
    (contMDiffOn_restrSliceChart hk hp₁ hp₂ hV hs hrank r)
    (contMDiffOn_restrSliceChart_symm hk hp₁ hp₂ hV hs hrank r)
    (mem_restrSliceChart_source hk hp₁ hp₂ hV hs hrank)

/-- **A regular part of a bihomogeneous zero set as a bundled embedding.** The inclusion of a
relatively open subset `s` of the zero set on which the cone Jacobian is surjective, with the
atlas `SymplecticGeometry.complexProjectiveProdZeroLocusChartedSpace`, into the product of the two
projective spaces as a `C^r` embedding. Its coercion is `Subtype.val` by definition
(`SymplecticGeometry.coe_complexProjectiveProdZeroLocusEmbedding`). -/
noncomputable def complexProjectiveProdZeroLocusEmbedding (r : ℕ∞ω) :
    letI := complexProjectiveProdZeroLocusChartedSpace hk hp₁ hp₂ hV hs hrank
    SmoothEmbedding 𝓘(ℂ, Fin k → ℂ)
      (𝓘(ℂ, Fin m → ℂ).prod 𝓘(ℂ, Fin n → ℂ)) r s
      (ℙ ℂ (Fin (m + 1) → ℂ) × ℙ ℂ (Fin (n + 1) → ℂ)) :=
  letI := complexProjectiveProdZeroLocusChartedSpace hk hp₁ hp₂ hV hs hrank
  { toContMDiffMap :=
      ⟨Subtype.val,
        (isSmoothEmbedding_subtypeVal_complexProjectiveProdZeroLocus hk hp₁ hp₂ hV hs hrank r
          ).contMDiff⟩
    isSmoothEmbedding_toFun :=
      isSmoothEmbedding_subtypeVal_complexProjectiveProdZeroLocus hk hp₁ hp₂ hV hs hrank r }

/-- The bundled embedding of a regular part of a bihomogeneous zero set is the inclusion. -/
@[simp]
theorem coe_complexProjectiveProdZeroLocusEmbedding (r : ℕ∞ω) :
    letI := complexProjectiveProdZeroLocusChartedSpace hk hp₁ hp₂ hV hs hrank
    ⇑(complexProjectiveProdZeroLocusEmbedding hk hp₁ hp₂ hV hs hrank r) = Subtype.val :=
  (rfl)

/-! ### The tangent space -/

variable {r : ℕ∞ω}

/-- **The tangent space of a regular part of a bihomogeneous zero set.** At a point `z` of `s`
whose components lie in the standard affine opens `affineOpen i` and `affineOpen j`, the image of
the differential of the inclusion into the product of the two projective spaces is the kernel of
the differential of the chart equations `prodChartEquations i j p` read in the product of the two
affine charts. -/
theorem tangentRange_complexProjectiveProdZeroLocusEmbedding (hr : r ≠ 0) (z : s)
    (hi : (z : ℙ ℂ (Fin (m + 1) → ℂ) × ℙ ℂ (Fin (n + 1) → ℂ)).1 ∈ affineOpen i)
    (hj : (z : ℙ ℂ (Fin (m + 1) → ℂ) × ℙ ℂ (Fin (n + 1) → ℂ)).2 ∈ affineOpen j) :
    letI := complexProjectiveProdZeroLocusChartedSpace hk hp₁ hp₂ hV hs hrank
    (complexProjectiveProdZeroLocusEmbedding hk hp₁ hp₂ hV hs hrank r).isImmersion.tangentRange
        z hr =
      (mfderiv (𝓘(ℂ, Fin m → ℂ).prod 𝓘(ℂ, Fin n → ℂ)) 𝓘(ℂ, ι → ℂ)
        (fun y : ℙ ℂ (Fin (m + 1) → ℂ) × ℙ ℂ (Fin (n + 1) → ℂ) ↦
          prodChartEquations i j p (affineChart i y.1, affineChart j y.2)) z).ker := by
  let := complexProjectiveProdZeroLocusChartedSpace hk hp₁ hp₂ hV hs hrank
  refine SmoothEmbedding.tangentRange_eq_ker_mfderiv (c := 0) _ z hr ?_
    (isRegularPoint_iff.2 ((surjective_mfderiv_prodChartEquations_affineChart_iff hp₁ hp₂
      (hs.subset z.property).1 hi hj).2 (hrank z z.property))) ?_
  · -- The chart equations vanish on the part of `s` in the product of the two affine opens.
    filter_upwards [continuous_subtypeVal.continuousAt.preimage_mem_nhds
      (((isOpen_affineOpen i).prod (isOpen_affineOpen j)).mem_nhds ⟨hi, hj⟩)] with w hw
    rw [coe_complexProjectiveProdZeroLocusEmbedding]
    exact funext ((mem_complexProjectiveProdZeroLocus_iff_prodChartEquations hp₁ hp₂ hw.1
      hw.2).1 (hs.subset w.property).1)
  · simp only [Module.finrank_prod, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    omega

/-- **The tangent sequence of a regular part of a bihomogeneous zero set is exact.** At a point
`z` of `s` whose components lie in the standard affine opens `affineOpen i` and `affineOpen j`,
the differentials of the inclusion into the product of the two projective spaces and of the chart
equations `prodChartEquations i j p` read in the product of the two affine charts form an exact
sequence `T_z s → T_z (ℙᵐ × ℙⁿ) → (ι → ℂ)`. -/
theorem exact_mfderiv_subtypeVal_complexProjectiveProdZeroLocus (z : s)
    (hi : (z : ℙ ℂ (Fin (m + 1) → ℂ) × ℙ ℂ (Fin (n + 1) → ℂ)).1 ∈ affineOpen i)
    (hj : (z : ℙ ℂ (Fin (m + 1) → ℂ) × ℙ ℂ (Fin (n + 1) → ℂ)).2 ∈ affineOpen j) :
    letI := complexProjectiveProdZeroLocusChartedSpace hk hp₁ hp₂ hV hs hrank
    Function.Exact
      (mfderiv 𝓘(ℂ, Fin k → ℂ) (𝓘(ℂ, Fin m → ℂ).prod 𝓘(ℂ, Fin n → ℂ))
        (Subtype.val : s → ℙ ℂ (Fin (m + 1) → ℂ) × ℙ ℂ (Fin (n + 1) → ℂ)) z)
      (mfderiv (𝓘(ℂ, Fin m → ℂ).prod 𝓘(ℂ, Fin n → ℂ)) 𝓘(ℂ, ι → ℂ)
        (fun y : ℙ ℂ (Fin (m + 1) → ℂ) × ℙ ℂ (Fin (n + 1) → ℂ) ↦
          prodChartEquations i j p (affineChart i y.1, affineChart j y.2)) z) :=
  letI := complexProjectiveProdZeroLocusChartedSpace hk hp₁ hp₂ hV hs hrank
  -- The tangent range of the bundled embedding is by definition the range of the differential of
  -- its coercion, which is `Subtype.val`.
  LinearMap.exact_iff.2 (tangentRange_complexProjectiveProdZeroLocusEmbedding hk hp₁ hp₂ hV hs
    hrank (r := 1) one_ne_zero z hi hj).symm

end Submanifold

end SymplecticGeometry

end
