/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Complex.Plurisubharmonic
public import SymplecticGeometry.Geometry.Manifold.Morse.GradientLike
public import TauCeti.Geometry.Symplectic.Hamiltonian.SymplecticVectorField
public import TauCeti.Geometry.Symplectic.Liouville.VectorField
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.CompatibleMetric
public import TauCeti.Geometry.Symplectic.Manifold.Flat
public import TauCeti.Geometry.Symplectic.TameMetric
public import TauCeti.Geometry.Manifold.Flow.Complete
import SymplecticGeometry.Analysis.SpecialFunctions.ExpDeriv

/-!
# The Liouville field of a Stein function

Let `M` be a complex manifold modelled on `E`, seen as a real manifold, with complex structure
`J = ofComplexManifold E M`. For a smooth real function `φ`, write `λ_φ = -dφ ∘ J`, Tau Ceti's
`J.covectorComplexStructure (mextDerivₗ 𝓘(ℝ, E) 0 (SmoothForm.ofFunction φ))`, and
`ω_φ = dλ_φ`. The vector field `dCLiouvilleField φ` is `(ω_φ♭)⁻¹ λ_φ`, the vector field `X`
with `ι_X ω_φ = λ_φ` wherever `ω_φ` is nondegenerate, and zero at the points where the flat
map of `ω_φ` is not invertible.

For `φ` strictly plurisubharmonic at every point, as a Stein function is, `ω_φ` is a Kähler
form, so `X` is smooth, it is a Liouville field of `ω_φ` (`L_X ω_φ = dλ_φ = ω_φ`), and it
is the gradient of `φ` for the Kähler metric `g(u, w) = ω_φ(u, J w)`: indeed
`g(X, w) = ω_φ(X, J w) = λ_φ(J w) = -dφ(J J w) = dφ(w)`. Hence it is
gradient-like for `φ`, with `δ = 1 / 2`. This is the Weinstein manifold of a Stein function of
Cieliebak–Eliashberg, §11.5.

The field need not be complete, but it becomes complete after a convex reparametrization of `φ`
(Cieliebak–Eliashberg, Remark 11.16), and `h = exp` serves for every Stein function. For
`ψ = h ∘ φ` the composition formulas give `λ_ψ = h'(φ) λ_φ` and
`ω_ψ = h'(φ) ω_φ + h''(φ) dφ ∧ λ_φ`, and evaluating `ι_X ω_ψ = λ_ψ` on `J X` for the field `X`
of `ψ` gives `h'(φ) dφ(X) = h'(φ) ω_φ(X, J X) + h''(φ) (dφ(X)² + dφ(J X)²)`. For `h = exp`
this forces `0 ≤ dφ(X) ≤ 1`, so the proper function `φ` changes at a bounded rate along `X`,
and Tau Ceti's `TauCeti.isCompleteVectorField_of_isProperMap_of_abs_mvfderiv_le` makes `X`
complete.

## Main declarations

* `SymplecticGeometry.dCLiouvilleField`: the field `(ω_φ♭)⁻¹ λ_φ`, with
  `SymplecticGeometry.dCLiouvilleField_def`.
* `SymplecticGeometry.apply_dCLiouvilleField_of_isInvertible`: `ω_φ(X, w) = λ_φ(w)` at a point
  where the flat map of `ω_φ` is invertible.
* `SymplecticGeometry.interior_dCLiouvilleField`: `ι_X ω_φ = λ_φ` when `ω_φ` is nondegenerate,
  as it is for a Stein function by `SymplecticGeometry.IsSteinFunction.isSymplectic`.
* `SymplecticGeometry.contMDiff_dCLiouvilleField`: the field is smooth when `ω_φ` is
  nondegenerate.
* `SymplecticGeometry.isLiouvilleVectorField_dCLiouvilleField`: when `ω_φ` is nondegenerate,
  the field is a Liouville field of `ω_φ`, by Tau Ceti's
  `TauCeti.SmoothTwoForm.IsSymplectic.mlieDerivForm_interiorEquiv_symm`.
* `SymplecticGeometry.dCLiouvilleField_eq_mgradient`: for `φ` strictly plurisubharmonic at
  every point, the field is the gradient of `φ` for the metric of the compatible pair `(ω_φ, J)`.
* `SymplecticGeometry.isGradientLike_dCLiouvilleField`: for `φ` strictly plurisubharmonic at
  every point, the field is gradient-like for `φ`, by `TauCeti.isGradientLike_mgradient`.
* `SymplecticGeometry.mul_mvfderiv_dCLiouvilleField_comp`: the identity above, for any
  `ψ = g ∘ φ`.
* `SymplecticGeometry.mvfderiv_dCLiouvilleField_exp_comp_mem_Icc`: `0 ≤ dφ(X) ≤ 1` for the
  field `X` of `exp ∘ φ`.
* `SymplecticGeometry.isCompleteVectorField_dCLiouvilleField_exp_comp`: the field of `exp ∘ φ`
  is complete for a Stein function `φ`.
* `SymplecticGeometry.IsSteinFunction.exists_comp_isCompleteVectorField`: a smooth `h` with
  `h' > 0` and `h'' ≥ 0` for which the field of `h ∘ φ` is complete.

## Implementation notes

The field is defined pointwise with `ContinuousLinearMap.inverse`, as Tau Ceti's
`TauCeti.SmoothTwoForm.hamiltonianVectorField`, rather than through Tau Ceti's
`TauCeti.SmoothTwoForm.IsNondegenerate.interiorEquiv`, which needs nondegeneracy everywhere to
be stated. Where `ω_φ` is nondegenerate the two agree
(`SymplecticGeometry.dCLiouvilleField_eq_interiorEquiv_symm`), which gives the contraction
identity and the smoothness.

## References

* [K. Cieliebak, Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  §11.5, Remark 11.16
-/

public section

noncomputable section

open Bundle
open scoped Manifold ContDiff TauCeti.ComplexManifold

namespace SymplecticGeometry

open TauCeti TauCeti.Manifold TauCeti.SmoothAlmostComplexStructure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

/-- The **Liouville field of a function** `φ` on a complex manifold: the vector field
`X = (ω_φ♭)⁻¹ λ_φ`, where `λ_φ = -dφ ∘ J` and `ω_φ = dλ_φ`. Where the flat map of `ω_φ` is
invertible, `X` is the vector with `ι_X ω_φ = λ_φ`; elsewhere it is `0`. -/
def dCLiouvilleField (φ : C^∞⟮𝓘(ℝ, E), M; ℝ⟯) (x : M) : TangentSpace 𝓘(ℝ, E) x :=
  (SmoothTwoForm.flat (mextDerivₗ 𝓘(ℝ, E) 1
      ((ofComplexManifold E M).covectorComplexStructure
        (mextDerivₗ 𝓘(ℝ, E) 0 (SmoothForm.ofFunction φ)))) x).inverse
    (SmoothForm.degreeOneEquiv ((ofComplexManifold E M).covectorComplexStructure
      (mextDerivₗ 𝓘(ℝ, E) 0 (SmoothForm.ofFunction φ))) x)

/-- The Liouville field of `φ` unfolds as the inverse flat map of `ω_φ` applied to `λ_φ`. -/
theorem dCLiouvilleField_def (φ : C^∞⟮𝓘(ℝ, E), M; ℝ⟯) (x : M) :
    dCLiouvilleField φ x =
      (SmoothTwoForm.flat (mextDerivₗ 𝓘(ℝ, E) 1
          ((ofComplexManifold E M).covectorComplexStructure
            (mextDerivₗ 𝓘(ℝ, E) 0 (SmoothForm.ofFunction φ)))) x).inverse
        (SmoothForm.degreeOneEquiv ((ofComplexManifold E M).covectorComplexStructure
          (mextDerivₗ 𝓘(ℝ, E) 0 (SmoothForm.ofFunction φ))) x) :=
  (rfl)

/-- At a point where the flat map of `ω_φ` is invertible, `ω_φ(X, w) = λ_φ(w)` for the
Liouville field `X` of `φ`. -/
theorem apply_dCLiouvilleField_of_isInvertible (φ : C^∞⟮𝓘(ℝ, E), M; ℝ⟯) {x : M}
    (hx : (SmoothTwoForm.flat (mextDerivₗ 𝓘(ℝ, E) 1
      ((ofComplexManifold E M).covectorComplexStructure
        (mextDerivₗ 𝓘(ℝ, E) 0 (SmoothForm.ofFunction φ)))) x).IsInvertible)
    (w : TangentSpace 𝓘(ℝ, E) x) :
    (mextDerivₗ 𝓘(ℝ, E) 1 ((ofComplexManifold E M).covectorComplexStructure
        (mextDerivₗ 𝓘(ℝ, E) 0 (SmoothForm.ofFunction φ)))).val x ![dCLiouvilleField φ x, w] =
      ((ofComplexManifold E M).covectorComplexStructure
        (mextDerivₗ 𝓘(ℝ, E) 0 (SmoothForm.ofFunction φ))).val x ![w] := by
  rw [← SmoothBundleForm.eval₂_apply, ← SmoothTwoForm.flat_apply, dCLiouvilleField_def,
    hx.self_apply_inverse, SmoothForm.degreeOneEquiv_apply_apply_vec]

/-- **The rate of change of `φ` along the Liouville field of `g ∘ φ`.** Let `ψ = g ∘ φ`, where the
derivative of `g` at `φ x` is `g' (φ x)` and that of `g'` is `g'' (φ x)`, and let the smooth
functions `a` and `b` be `g' ∘ φ` and `g'' ∘ φ`. At a point where the flat map of `ω_ψ` is
invertible, the Liouville field `X` of `ψ` satisfies
`a dφ(X) = a ω_φ(X, J X) + b (dφ(X)² + dφ(J X)²)`. -/
theorem mul_mvfderiv_dCLiouvilleField_comp {g g' g'' : ℝ → ℝ} {φ ψ a b : C^∞⟮𝓘(ℝ, E), M; ℝ⟯}
    (hψ : ∀ x, ψ x = g (φ x)) (ha : ∀ x, a x = g' (φ x)) (hb : ∀ x, b x = g'' (φ x))
    (hg : ∀ x, HasDerivAt g (g' (φ x)) (φ x)) (hg' : ∀ x, HasDerivAt g' (g'' (φ x)) (φ x))
    {x : M} (hx : (SmoothTwoForm.flat (mextDerivₗ 𝓘(ℝ, E) 1
      ((ofComplexManifold E M).covectorComplexStructure
        (mextDerivₗ 𝓘(ℝ, E) 0 (SmoothForm.ofFunction ψ)))) x).IsInvertible) :
    a x * mvfderiv 𝓘(ℝ, E) φ x (dCLiouvilleField ψ x) =
      a x * (mextDerivₗ 𝓘(ℝ, E) 1 ((ofComplexManifold E M).covectorComplexStructure
        (mextDerivₗ 𝓘(ℝ, E) 0 (SmoothForm.ofFunction φ)))).val x
          ![dCLiouvilleField ψ x, (ofComplexManifold E M).toEndomorphism x (dCLiouvilleField ψ x)] +
      b x * (mvfderiv 𝓘(ℝ, E) φ x (dCLiouvilleField ψ x) ^ 2 +
        mvfderiv 𝓘(ℝ, E) φ x
          ((ofComplexManifold E M).toEndomorphism x (dCLiouvilleField ψ x)) ^ 2) := by
  -- The wedge is read in degree `0 + 1 + 1`, which is `2` by definition.
  have hcast (u w : TangentSpace 𝓘(ℝ, E) x) :
      ![u, w] ∘ Fin.cast (show 0 + 1 + 1 = 1 + 1 by omega) = ![u, w] := rfl
  -- Evaluate `ι_X ω_ψ = λ_ψ` on `J X`, with `ω_ψ = a ω_φ + b (dφ ∧ λ_φ)` and `λ_ψ = a λ_φ`.
  have key := apply_dCLiouvilleField_of_isInvertible ψ hx
    ((ofComplexManifold E M).toEndomorphism x (dCLiouvilleField ψ x))
  rw [mextDerivₗ_covectorComplexStructure_mextDerivₗ_ofFunction_comp_of_hasDerivAt hψ ha hb hg hg',
    covectorComplexStructure_mextDerivₗ_ofFunction_comp_of_hasDerivAt (g' := a) hψ
      fun y ↦ ha y ▸ hg y] at key
  simp only [Submodule.coe_add, Pi.add_apply, ContinuousAlternatingMap.add_apply,
    SmoothForm.coe_funSMulₗ, ContinuousAlternatingMap.smul_apply, smul_eq_mul,
    SmoothForm.extDerivWedgeₗ_apply, hcast, RoughForm.wedge_apply_one_one,
    mextDeriv_ofFunction_apply, covectorComplexStructure_apply_vec, mextDerivₗ_zero_apply,
    SmoothForm.ofFunction_apply_zero, SmoothAlmostComplexStructure.apply_apply, map_neg,
    ← mvfderiv_apply_eq_mfderiv_apply] at key
  linear_combination -key

variable [FiniteDimensional ℂ E]

/-- Where `ω_φ` is nondegenerate, the Liouville field of `φ` is the vector field that Tau Ceti's
contraction equivalence `TauCeti.SmoothTwoForm.IsNondegenerate.interiorEquiv` assigns to
`λ_φ`. -/
theorem dCLiouvilleField_eq_interiorEquiv_symm (φ : C^∞⟮𝓘(ℝ, E), M; ℝ⟯)
    (hω : SmoothTwoForm.IsNondegenerate (mextDerivₗ 𝓘(ℝ, E) 1
      ((ofComplexManifold E M).covectorComplexStructure
        (mextDerivₗ 𝓘(ℝ, E) 0 (SmoothForm.ofFunction φ))))) :
    dCLiouvilleField φ = ⇑(hω.interiorEquiv.symm ((ofComplexManifold E M).covectorComplexStructure
      (mextDerivₗ 𝓘(ℝ, E) 0 (SmoothForm.ofFunction φ)))) :=
  funext fun x ↦ by
    rw [dCLiouvilleField_def, SmoothTwoForm.IsNondegenerate.interiorEquiv_symm_apply]

/-- Where `ω_φ` is nondegenerate, the Liouville field `X` of `φ` satisfies `ι_X ω_φ = λ_φ`. -/
theorem interior_dCLiouvilleField (φ : C^∞⟮𝓘(ℝ, E), M; ℝ⟯)
    (hω : SmoothTwoForm.IsNondegenerate (mextDerivₗ 𝓘(ℝ, E) 1
      ((ofComplexManifold E M).covectorComplexStructure
        (mextDerivₗ 𝓘(ℝ, E) 0 (SmoothForm.ofFunction φ))))) :
    RoughForm.interior (dCLiouvilleField φ) (mextDerivₗ 𝓘(ℝ, E) 1
        ((ofComplexManifold E M).covectorComplexStructure
          (mextDerivₗ 𝓘(ℝ, E) 0 (SmoothForm.ofFunction φ)))).val =
      ((ofComplexManifold E M).covectorComplexStructure
        (mextDerivₗ 𝓘(ℝ, E) 0 (SmoothForm.ofFunction φ))).val := by
  rw [dCLiouvilleField_eq_interiorEquiv_symm φ hω,
    SmoothTwoForm.IsNondegenerate.interior_interiorEquiv_symm]

/-- Where `ω_φ` is nondegenerate, the Liouville field of `φ` is smooth. -/
theorem contMDiff_dCLiouvilleField (φ : C^∞⟮𝓘(ℝ, E), M; ℝ⟯)
    (hω : SmoothTwoForm.IsNondegenerate (mextDerivₗ 𝓘(ℝ, E) 1
      ((ofComplexManifold E M).covectorComplexStructure
        (mextDerivₗ 𝓘(ℝ, E) 0 (SmoothForm.ofFunction φ))))) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞ (T% (dCLiouvilleField φ)) := by
  rw [dCLiouvilleField_eq_interiorEquiv_symm φ hω]
  exact ContMDiffSection.contMDiff _

variable {φ : C^∞⟮𝓘(ℝ, E), M; ℝ⟯}

/-- **The Liouville field of `φ` is a Liouville field** where `ω_φ` is nondegenerate:
`L_X ω_φ = ω_φ`. -/
theorem isLiouvilleVectorField_dCLiouvilleField
    (hω : SmoothTwoForm.IsNondegenerate (mextDerivₗ 𝓘(ℝ, E) 1
      ((ofComplexManifold E M).covectorComplexStructure
        (mextDerivₗ 𝓘(ℝ, E) 0 (SmoothForm.ofFunction φ))))) :
    IsLiouvilleVectorField (mextDerivₗ 𝓘(ℝ, E) 1 ((ofComplexManifold E M).covectorComplexStructure
      (mextDerivₗ 𝓘(ℝ, E) 0 (SmoothForm.ofFunction φ)))).val (dCLiouvilleField φ) := by
  have hσ : SmoothTwoForm.IsSymplectic (mextDerivₗ 𝓘(ℝ, E) 1
      ((ofComplexManifold E M).covectorComplexStructure
        (mextDerivₗ 𝓘(ℝ, E) 0 (SmoothForm.ofFunction φ)))) :=
    ⟨SmoothForm.isClosed_mextDerivₗ _, hω⟩
  rw [isLiouvilleVectorField_iff, dCLiouvilleField_eq_interiorEquiv_symm φ hω,
    hσ.mlieDerivForm_interiorEquiv_symm, mextDerivₗ_apply]

/-- **The Liouville field of a strictly plurisubharmonic function is a gradient.** If `φ` is
strictly plurisubharmonic at every point, the Liouville field of `φ` is the gradient of `φ` for
the Kähler metric `g(u, w) = ω_φ(u, J w)` of the compatible pair `(ω_φ, J)`. -/
theorem dCLiouvilleField_eq_mgradient (hφ : ∀ x, IsManifoldStrictlyPlurisubharmonicAt E φ x) :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) :=
      ⟨(isKahler_mextDerivₗ_covectorComplexStructure hφ).compatible.metric.toRiemannianMetric⟩
    dCLiouvilleField φ = mgradient 𝓘(ℝ, E) φ := by
  have hK := isKahler_mextDerivₗ_covectorComplexStructure hφ
  let : RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) :=
    ⟨hK.compatible.metric.toRiemannianMetric⟩
  funext x
  refine eq_mgradient_iff.2 fun v ↦ ?_
  -- `g(X, v) = ω_φ(X, J v) = λ_φ(J v) = -dφ(J J v) = dφ(v)`
  rw [hK.compatible.inner_eq_eval₂, SmoothBundleForm.eval₂_apply,
    apply_dCLiouvilleField_of_isInvertible φ (hK.isSymplectic.isNondegenerate.isInvertible_flat x),
    covectorComplexStructure_apply_vec, SmoothAlmostComplexStructure.apply_apply,
    mextDerivₗ_zero_apply, SmoothForm.ofFunction_apply_zero, map_neg, _root_.neg_neg]

/-- **The Liouville field of a strictly plurisubharmonic function is gradient-like** for the
function. -/
theorem isGradientLike_dCLiouvilleField (hφ : ∀ x, IsManifoldStrictlyPlurisubharmonicAt E φ x) :
    IsGradientLike φ (dCLiouvilleField φ) := by
  rw [dCLiouvilleField_eq_mgradient hφ]
  exact isGradientLike_mgradient _ _

/-- **The Liouville field of `exp ∘ φ` moves `φ` at a bounded rate.** If `φ` is strictly
plurisubharmonic at every point and `ψ = exp ∘ φ`, then
`0 ≤ dφ(X) ≤ 1` for the Liouville field `X` of `ψ`. -/
theorem mvfderiv_dCLiouvilleField_exp_comp_mem_Icc {ψ : C^∞⟮𝓘(ℝ, E), M; ℝ⟯}
    (hφ : ∀ x, IsManifoldStrictlyPlurisubharmonicAt E φ x) (hψ : ⇑ψ = Real.exp ∘ φ)
    (x : M) : mvfderiv 𝓘(ℝ, E) φ x (dCLiouvilleField ψ x) ∈ Set.Icc 0 1 := by
  have hψφ : ∀ y, IsManifoldStrictlyPlurisubharmonicAt E ψ y := fun y ↦
    hψ ▸ (hφ y).exp_comp (φ.contMDiff.contMDiffAt.of_le (by simp))
  have hω := (isKahler_mextDerivₗ_covectorComplexStructure hψφ).isSymplectic.isNondegenerate
  have hψx (y : M) : ψ y = Real.exp (φ y) := congrFun hψ y
  have key := mul_mvfderiv_dCLiouvilleField_comp (a := ψ) (b := ψ) hψx hψx hψx
    (fun _ ↦ Real.hasDerivAt_exp _) (fun _ ↦ Real.hasDerivAt_exp _) (hω.isInvertible_flat x)
  set X := dCLiouvilleField ψ x
  have hpos : 0 < ψ x := hψx x ▸ Real.exp_pos _
  -- `ω_φ(X, J X) ≥ 0`, since `J` tames `ω_φ`.
  have hωX : 0 ≤ (mextDerivₗ 𝓘(ℝ, E) 1 ((ofComplexManifold E M).covectorComplexStructure
      (mextDerivₗ 𝓘(ℝ, E) 0 (SmoothForm.ofFunction φ)))).val x
        ![X, (ofComplexManifold E M).toEndomorphism x X] := by
    have hK := isKahler_mextDerivₗ_covectorComplexStructure hφ
    simpa only [SmoothTwoForm.IsNondegenerate.symplecticFormAt_apply,
      SmoothAlmostComplexStructure.almostComplexStructureAt_apply, SmoothBundleForm.eval₂_apply]
      using SymplecticForm.Tames.symplecticForm_apply_apply_self_nonneg
        (hK.isNondegenerate.tames_iff.1 hK.compatible.tames x) X
  -- `dφ(X) = ω_φ(X, J X) + dφ(X)² + dφ(J X)²`
  have e := mul_left_cancel₀ hpos.ne' (key.trans (mul_add _ _ _).symm)
  constructor <;>
    nlinarith [sq_nonneg (mvfderiv 𝓘(ℝ, E) φ x ((ofComplexManifold E M).toEndomorphism x X))]

/-- **The Liouville field of `exp ∘ φ` is complete** for a Stein function `φ` on a Hausdorff
complex manifold: `φ` is proper, and changes at a rate in `[0, 1]` along the field. -/
theorem isCompleteVectorField_dCLiouvilleField_exp_comp [T2Space M] {φ : M → ℝ}
    {ψ : C^∞⟮𝓘(ℝ, E), M; ℝ⟯} (hφ : IsSteinFunction E φ) (hψ : ⇑ψ = Real.exp ∘ φ) :
    IsCompleteVectorField (dCLiouvilleField ψ) := by
  have hω := (isKahler_mextDerivₗ_covectorComplexStructure fun y ↦
    hψ ▸ (hφ.isStrictlyPlurisubharmonic y).exp_comp
      (hφ.contMDiff.contMDiffAt.of_le (by simp))).isSymplectic.isNondegenerate
  refine isCompleteVectorField_of_isProperMap_of_abs_mvfderiv_le
    ((contMDiff_dCLiouvilleField ψ hω).of_le (by simp)) hφ.isProperMap
    (hφ.contMDiff.mdifferentiable (by simp)) (C := 1) fun x ↦ ?_
  obtain ⟨h0, h1⟩ : mvfderiv 𝓘(ℝ, E) φ x (dCLiouvilleField ψ x) ∈ Set.Icc 0 1 :=
    mvfderiv_dCLiouvilleField_exp_comp_mem_Icc (φ := ⟨φ, hφ.contMDiff⟩)
      hφ.isStrictlyPlurisubharmonic hψ x
  exact abs_le.2 ⟨by linarith, h1⟩

/-- **A convex reparametrization makes the Liouville field of a Stein function complete.** For a
Stein function `φ` on a Hausdorff complex manifold there is a smooth `h : ℝ → ℝ` with `h' > 0`
and `h'' ≥ 0` such that the Liouville field of the Stein function `h ∘ φ`
(`SymplecticGeometry.IsSteinFunction.comp`) is complete; `h = exp` works. -/
theorem IsSteinFunction.exists_comp_isCompleteVectorField [T2Space M] {φ : M → ℝ}
    (hφ : IsSteinFunction E φ) :
    ∃ h : ℝ → ℝ, ContDiff ℝ ∞ h ∧ (∀ t, 0 < deriv h t) ∧ (∀ t, 0 ≤ iteratedDeriv 2 h t) ∧
      ∃ ψ : C^∞⟮𝓘(ℝ, E), M; ℝ⟯, ⇑ψ = h ∘ φ ∧ IsCompleteVectorField (dCLiouvilleField ψ) :=
  ⟨Real.exp, Real.contDiff_exp,
    fun t ↦ by simp [Real.exp_pos], fun t ↦ by simp [(Real.exp_pos t).le],
    ⟨Real.exp ∘ φ, Real.contDiff_exp.contMDiff.comp hφ.contMDiff⟩, rfl,
    isCompleteVectorField_dCLiouvilleField_exp_comp hφ rfl⟩

end SymplecticGeometry

end
