/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.VectorBundle.CauchyRiemann.Basic
public import SymplecticGeometry.Geometry.Symplectic.AlmostComplex
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm

/-!
# Two almost complex structures tamed by a common form

Let `σ` be a smooth two-form on a manifold `M` that tames two smooth almost complex structures
`J` and `K`. Tau Ceti's `TauCeti.SmoothTwoForm.Tames.injective_add` shows that `J + K` is
injective on every tangent space. This file draws two pointwise consequences.

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

## Main results

* `TauCeti.SmoothAlmostComplexStructure.ne_neg_of_tames`.
* `TauCeti.SmoothAlmostComplexStructure.injOn_zeroOnePart_of_tames`.

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
  have : Nontrivial (TangentSpace I x) := inferInstanceAs (Nontrivial E)
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
