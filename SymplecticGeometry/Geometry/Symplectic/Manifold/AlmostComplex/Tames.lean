/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.VectorBundle.CauchyRiemann.Basic
public import SymplecticGeometry.Geometry.Symplectic.AlmostComplex
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Chart
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Dual

/-!
# Two almost complex structures tamed by a common form

Let `σ` be a smooth two-form on a manifold `M` that tames two smooth almost complex structures
`J` and `K`. Tau Ceti's `TauCeti.SmoothTwoForm.Tames.injective_add` shows that `J + K` is
injective on every tangent space. This file draws pointwise consequences.

* At no point is `J` equal to `-K`, as soon as the tangent spaces are nonzero
  (`TauCeti.SmoothAlmostComplexStructure.ne_neg_of_tames`). For the Riemann sphere, with `K` the
  complex structure, this says that `J` is nowhere `-i`.
* If the tangent spaces are finite-dimensional, then at every point the `(0,1)`-projection
  `TauCeti.SmoothAlmostComplexStructure.zeroOnePart` for `K` is injective on the `(0,1)`-forms
  for `J`, with values in any complex vector bundle
  (`TauCeti.SmoothAlmostComplexStructure.injOn_zeroOnePart_of_tames`). This comes from the linear
  statement `TauCeti.SymplecticForm.Tames.eq_zero_of_isComplexAntilinear_of_isComplexLinear`: a
  one-form in the kernel of the difference is complex antilinear for `J` and complex linear for
  `K`, so it vanishes.

On a complex curve `N`, with `K` the complex structure of `N`, this file shows that the two
structures also induce the same orientation in every holomorphic chart: `J`, read in the chart,
sends `1` to the open upper half plane
(`TauCeti.SmoothAlmostComplexStructure.im_inChart_apply_one_pos_of_tames`). With `D` the
derivative of the inverse chart, the complex structure of `N` sends `D 1` to `D i`
(Tau Ceti's `ofComplexManifold_apply_mfderivWithin_extChartAt_symm_one`),
and expanding `σ` in the basis `D 1`, `D i` gives
`σ(D 1, J D 1) = Im (J.inChart y z 1) · σ(D 1, D i)`. In particular `J.inChart y z 1 ≠ -i`
(`TauCeti.SmoothAlmostComplexStructure.inChart_apply_one_ne_neg_I_of_tames`).

## Main results

* `TauCeti.SmoothAlmostComplexStructure.ne_neg_of_tames`.
* `TauCeti.SmoothAlmostComplexStructure.injOn_zeroOnePart_of_tames`.
* `TauCeti.SmoothAlmostComplexStructure.im_inChart_apply_one_pos_of_tames`.
* `TauCeti.SmoothAlmostComplexStructure.inChart_apply_one_ne_neg_I_of_tames`.

## References

* [D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*][McDuffSalamon2012],
  Appendix C.1.
-/

public section

open scoped ContDiff Manifold

namespace TauCeti.SmoothAlmostComplexStructure

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {σ : SmoothTwoForm I M} {J K : SmoothAlmostComplexStructure I M}

/-- If a smooth two-form tames the smooth almost complex structures `J` and `K`, and the tangent
spaces are nonzero, then at no point is `J` equal to `-K`. -/
theorem ne_neg_of_tames [Nontrivial E] (hJ : σ.Tames J) (hK : σ.Tames K) (x : M) :
    J.toEndomorphism x ≠ -K.toEndomorphism x := by
  intro h
  obtain ⟨v, hv⟩ := exists_ne (0 : TangentSpace I x)
  have hv' : J.toEndomorphism x v = -K.toEndomorphism x v := by simp [h]
  exact hv (hJ.injective_add hK x (by simp [hv']))

variable {V : M → Type*} [∀ x, TopologicalSpace (V x)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℂ (V x)] [∀ x, Module ℝ (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)]
  [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, ContinuousSMul ℂ (V x)]

/-- If a smooth two-form tames the smooth almost complex structures `J` and `K`, and the tangent
spaces are finite-dimensional, then at every point the `(0,1)`-projection for `K` is injective on
the `(0,1)`-forms for `J` with values in a complex vector bundle `V`. -/
theorem injOn_zeroOnePart_of_tames [FiniteDimensional ℝ E] (hJ : σ.Tames J) (hK : σ.Tames K)
    (x : M) :
    Set.InjOn (K.zeroOnePart (V := V) (x := x)) {η | J.IsZeroOneForm η} := by
  intro η hη η' hη' h
  have : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  have hK₀ : K.zeroOnePart (η - η') = 0 := by
    have h' := K.zeroOnePart_add (η - η') η'
    rw [sub_add_cancel, h] at h'
    exact add_eq_right.1 h'.symm
  rw [← sub_eq_zero, ← ContinuousLinearMap.coe_inj, ContinuousLinearMap.toLinearMap_zero]
  refine (hJ.isNondegenerate.tames_iff.1 hJ x).eq_zero_of_isComplexAntilinear_of_isComplexLinear
    (hJ.isNondegenerate.tames_iff.1 hK x)
    (J' := DistribSMul.toLinearMap ℝ (V x) Complex.I) (isComplexAntilinear_of_apply fun v ↦ ?_)
    (isComplexLinear_of_apply fun v ↦ by simpa using zeroOnePart_eq_zero_iff.1 hK₀ v)
  simp [isZeroOneForm_iff.1 hη v, isZeroOneForm_iff.1 hη' v, smul_sub, neg_add_eq_sub]

end TauCeti.SmoothAlmostComplexStructure

namespace TauCeti.SmoothAlmostComplexStructure

open Set
open scoped TauCeti.ComplexManifold

variable {N : Type*} [TopologicalSpace N] [ChartedSpace ℂ N] [IsManifold 𝓘(ℂ) ∞ N]

/-- On a complex curve `N`, let a smooth two-form `σ` tame a smooth almost complex structure `J`
and the complex structure of `N`. Then `J`, read in the chart at `y` at a point `z` of the chart
target, sends `1` to the open upper half plane. -/
theorem im_inChart_apply_one_pos_of_tames {σ : SmoothTwoForm 𝓘(ℝ, ℂ) N}
    {J : SmoothAlmostComplexStructure 𝓘(ℝ, ℂ) N} (hJ : σ.Tames J)
    (hi : σ.Tames (ofComplexManifold ℂ N)) (y : N) {z : ℂ}
    (hz : z ∈ (extChartAt 𝓘(ℝ, ℂ) y).target) :
    0 < (J.inChart y z 1).im := by
  -- The derivative of the inverse chart, as an endomorphism of `ℂ`.
  set D : ℂ →L[ℝ] ℂ :=
    mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (extChartAt 𝓘(ℝ, ℂ) y).symm (range 𝓘(ℝ, ℂ)) z
  set x := (extChartAt 𝓘(ℝ, ℂ) y).symm z
  set k := J.inChart y z 1 with hkdef
  have hd : D 1 ≠ 0 := by
    obtain ⟨e, he⟩ := isInvertible_mfderivWithin_extChartAt_symm hz
    exact fun h0 ↦ one_ne_zero (α := ℂ)
      (e.injective ((congrArg (· (1 : ℂ)) he).trans (h0.trans e.map_zero.symm)))
  -- `D` carries the value at `1` of `J` read in the chart to `J (D 1)`.
  have hk : D k = J x (D 1) := by
    rw [hkdef, J.inChart_apply_eq_mfderiv y hz]
    exact congr($(mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt hz) _)
  -- The complex structure of `N` sends `D 1` to `D i`, since the charts are holomorphic.
  have hI : D Complex.I = ofComplexManifold ℂ N x (D 1) :=
    (ofComplexManifold_apply_mfderivWithin_extChartAt_symm_one hz).symm
  -- In the basis `D 1, D i` of the tangent space at `x`, the value of `σ` on `D 1` and `D k`
  -- is `Im k` times its value on `D 1` and `D i`.
  have h3 : SmoothBundleForm.eval₂ σ x (D 1) (D k) =
      k.im * SmoothBundleForm.eval₂ σ x (D 1) (D Complex.I) := by
    have ha : D 1 = (1 : ℝ) • D 1 + (0 : ℝ) • D Complex.I := by simp
    refine (congrArg₂ (fun a b ↦ SmoothBundleForm.eval₂ σ x a b) ha
      (D.apply_eq_re_smul_one_add_im_smul_I k)).trans ?_
    refine (SmoothTwoForm.eval₂_smul_add_smul σ x (D 1) (D Complex.I) 1 0 k.re k.im).trans ?_
    ring
  have h1 := SmoothTwoForm.tames_iff.1 hJ x (D 1) hd
  have h2 := SmoothTwoForm.tames_iff.1 hi x (D 1) hd
  rw [← hk, h3, hI] at h1
  exact pos_of_mul_pos_left h1 h2.le

/-- On a complex curve `N`, let a smooth two-form `σ` tame a smooth almost complex structure `J`
and the complex structure of `N`. Then `J`, read in the chart at `y` at a point `z` of the chart
target, does not send `1` to `-i`. -/
theorem inChart_apply_one_ne_neg_I_of_tames {σ : SmoothTwoForm 𝓘(ℝ, ℂ) N}
    {J : SmoothAlmostComplexStructure 𝓘(ℝ, ℂ) N} (hJ : σ.Tames J)
    (hi : σ.Tames (ofComplexManifold ℂ N)) (y : N) {z : ℂ}
    (hz : z ∈ (extChartAt 𝓘(ℝ, ℂ) y).target) :
    J.inChart y z 1 ≠ -Complex.I := fun h ↦ by
  have := im_inChart_apply_one_pos_of_tames hJ hi y hz
  rw [h] at this
  norm_num at this

end TauCeti.SmoothAlmostComplexStructure
