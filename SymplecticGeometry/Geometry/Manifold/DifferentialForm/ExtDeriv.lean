/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.ExtDeriv
public import TauCeti.Geometry.Manifold.DifferentialForm.Smooth
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Basic
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.DifferentialForm.Opens.ModelSpace
import SymplecticGeometry.Geometry.Manifold.MFDeriv.Opens

/-!
# The exterior derivative of functions, and in a chart

Facts about the exterior derivative `df` of the `0`-form of a function `f` that Tau Ceti does
not state, and the coordinate formula for the exterior derivative of a form.

At a point where `f` and `g` are differentiable, `d(f + g) = df + dg` and `d(f - g) = df - dg`
(`TauCeti.mextDeriv_ofFunction_add_apply`, `TauCeti.mextDeriv_ofFunction_sub_apply`). So for
differentiable functions `d(f - g) = df - dg` (`TauCeti.mextDeriv_ofFunction_sub`), as Tau
Ceti's `TauCeti.mextDeriv_ofFunction_add` says for sums; the pointwise proofs are those of
`TauCeti.mextDeriv_ofFunction_add`, at one point. Negating a function negates its
exterior derivative (`TauCeti.mextDeriv_ofFunction_neg`, `TauCeti.mextDeriv_ofFunction_fun_neg`),
by Tau Ceti's `TauCeti.mextDeriv_neg` and `TauCeti.RoughForm.ofFunction_neg`
(`DifferentialForm/Basic.lean`). As for Mathlib's
`fderiv_fun_neg` and `fderiv_neg`, the form for `fun x ↦ -f x` is a simp lemma and the form for
`-f` is not.

For forms of any degree, `d(φ - η) = dφ - dη` at a point where the coordinate expressions of `φ`
and `η` in the chart there are differentiable (`TauCeti.mextDeriv_sub`): Tau Ceti's
`TauCeti.mextDerivWithin_sub` on the whole space, as Tau Ceti's `TauCeti.mextDeriv_add` follows
from `TauCeti.mextDerivWithin_add`.

On a real normed space `E`, regarded as a manifold with the model `𝓘(ℝ, E)`, `df` at `x` takes
on a single vector `v 0` the value of the Fréchet derivative, `fderiv ℝ f x (v 0)`
(`TauCeti.mextDeriv_ofFunction_modelSpace_apply`). It is Tau Ceti's
`TauCeti.mextDeriv_ofFunction_apply` together with `TauCeti.mvfderiv_eq_fderiv_apply`, stated
for every `v : Fin 1 → E` rather than for `![v]`.

In the chart at `x`, `dφ` at `x` on `V₀, …, Vₖ` is the alternating sum of the derivatives of the
coordinate expression of `φ` in the directions `Vₚ`, evaluated on the other vectors
(`TauCeti.mextDeriv_apply_eq_sum_fderivWithin`): Tau Ceti's `TauCeti.mextDeriv_def` followed by
Mathlib's `extDerivWithin_apply`.

On an open subset `U` of a normed space `E`, with the model `𝓘(ℝ, E)`, the exterior derivative of
a form `ω` differentiable at `b`, at `b` on `v₀, …, vₖ ∈ E`, is the alternating sum of the
derivatives at `b`, in the directions `vᵢ`, of the functions `b' ↦ ω b' (v without vᵢ)` on `U`
(`TauCeti.mextDeriv_opens_apply`). It is Tau Ceti's `TauCeti.mextDeriv_opens_eq_extDeriv`,
applied to the extension of `ω` by zero to `E`, followed by Mathlib's `extDeriv_apply`. Its
hypothesis holds at every point of `U` when `ω` is of class `Cⁿ` with `n ≠ 0`
(`TauCeti.IsSmoothForm.mdifferentiableAt_opens`), by Tau Ceti's
`TauCeti.IsSmoothForm.exists_contDiffOn_opens` and Mathlib's `ContDiffOn.differentiableOn`.

## Main results

* `TauCeti.mextDeriv_ofFunction_add_apply`, `TauCeti.mextDeriv_ofFunction_sub_apply`:
  `d(f + g) = df + dg` and `d(f - g) = df - dg` at a point where `f` and `g` are differentiable.
* `TauCeti.mextDeriv_ofFunction_sub`: `d(f - g) = df - dg` for differentiable functions.
* `TauCeti.mextDeriv_ofFunction_neg`, `TauCeti.mextDeriv_ofFunction_fun_neg`: `d(-f) = -df`.
* `TauCeti.mextDeriv_sub`: `d(φ - η) = dφ - dη` at a point where both forms are differentiable
  in the chart.
* `TauCeti.mextDeriv_ofFunction_modelSpace_apply`: `df(x)(v) = fderiv ℝ f x (v 0)` on a normed
  space.
* `TauCeti.mextDeriv_apply_eq_sum_fderivWithin`: the coordinate formula for `dφ` in the chart at
  `x`.
* `TauCeti.IsSmoothForm.mdifferentiableAt_opens`: a `Cⁿ` form, `n ≠ 0`, on an open subset of a
  normed space is differentiable at every point.
* `TauCeti.mextDeriv_opens_apply`: the formula for `dω` on an open subset of a normed space.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 11 (the differential of a function).
-/

public section

open scoped Manifold

namespace TauCeti

section Manifold

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H}
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- At a point where two functions are differentiable, the exterior derivative of the `0`-form
of their sum is the sum of their exterior derivatives. -/
theorem mextDeriv_ofFunction_add_apply {f g : M → F} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, F) f x) (hg : MDifferentiableAt I 𝓘(ℝ, F) g x) :
    mextDeriv (RoughForm.ofFunction I (f + g)) x =
      mextDeriv (RoughForm.ofFunction I f) x + mextDeriv (RoughForm.ofFunction I g) x := by
  ext v
  simp [mextDeriv_ofFunction, mvfderiv_add hf hg]

/-- At a point where two functions are differentiable, the exterior derivative of the `0`-form
of their difference is the difference of their exterior derivatives. -/
theorem mextDeriv_ofFunction_sub_apply {f g : M → F} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, F) f x) (hg : MDifferentiableAt I 𝓘(ℝ, F) g x) :
    mextDeriv (RoughForm.ofFunction I (f - g)) x =
      mextDeriv (RoughForm.ofFunction I f) x - mextDeriv (RoughForm.ofFunction I g) x := by
  ext v
  simp [mextDeriv_ofFunction, mvfderiv_sub hf hg]

/-- The exterior derivative of the `0`-form of a difference of differentiable functions is the
difference of their exterior derivatives. -/
theorem mextDeriv_ofFunction_sub {f g : M → F} (hf : MDifferentiable I 𝓘(ℝ, F) f)
    (hg : MDifferentiable I 𝓘(ℝ, F) g) :
    mextDeriv (RoughForm.ofFunction I (f - g)) =
      mextDeriv (RoughForm.ofFunction I f) - mextDeriv (RoughForm.ofFunction I g) :=
  funext fun x ↦ mextDeriv_ofFunction_sub_apply (hf x) (hg x)

/-- The exterior derivative of the `0`-form of `-f` is minus that of `f`. -/
theorem mextDeriv_ofFunction_neg (f : M → F) :
    mextDeriv (RoughForm.ofFunction I (-f)) = -mextDeriv (RoughForm.ofFunction I f) := by
  rw [RoughForm.ofFunction_neg, mextDeriv_neg]

/-- The exterior derivative of the `0`-form of `fun x ↦ -f x` is minus that of `f`. -/
@[simp]
theorem mextDeriv_ofFunction_fun_neg (f : M → F) :
    mextDeriv (RoughForm.ofFunction I fun x ↦ -f x) = -mextDeriv (RoughForm.ofFunction I f) :=
  mextDeriv_ofFunction_neg f

/-- The exterior derivative is subtractive on forms whose coordinate expressions in the chart at
the point are differentiable within `range I` there. -/
theorem mextDeriv_sub {k : ℕ} {φ η : RoughForm I M F k} {x : M}
    (hφ : DifferentiableWithinAt ℝ (φ.inChartAt x) (Set.range I) (extChartAt I x x))
    (hη : DifferentiableWithinAt ℝ (η.inChartAt x) (Set.range I) (extChartAt I x x)) :
    mextDeriv (φ - η) x = mextDeriv φ x - mextDeriv η x := by
  simp only [← mextDerivWithin_univ]
  exact mextDerivWithin_sub (uniqueMDiffWithinAt_univ I) (by simpa using hφ) (by simpa using hη)

/-- **The exterior derivative in a chart.** If the coordinate expression of `φ` in the chart at
`x` is differentiable within the model range at the chart image of `x`, then `dφ` at `x` on
`V₀, …, Vₖ` is the alternating sum, over `p`, of the derivatives in the direction `Vₚ` of the
coordinate expression of `φ` evaluated on the other vectors. -/
theorem mextDeriv_apply_eq_sum_fderivWithin {k : ℕ} {φ : RoughForm I M F k} {x : M}
    (hφ : DifferentiableWithinAt ℝ (φ.inChartAt x) (Set.range I) (extChartAt I x x))
    (V : Fin (k + 1) → E) :
    mextDeriv φ x V = ∑ p, (-1) ^ p.val •
      fderivWithin ℝ (fun z ↦ φ.inChartAt x z (p.removeNth V)) (Set.range I)
        (extChartAt I x x) (V p) := by
  rw [mextDeriv_def]
  exact extDerivWithin_apply hφ
    (I.uniqueDiffOn _ (extChartAt_target_subset_range x (mem_extChartAt_target x))) V

end Manifold

section NormedSpace

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- On a normed space `E`, the exterior derivative of the `0`-form of `f : E → F` at `x` takes
on `v : Fin 1 → E` the value `fderiv ℝ f x (v 0)`. -/
theorem mextDeriv_ofFunction_modelSpace_apply (f : E → F) (x : E)
    (v : Fin 1 → TangentSpace 𝓘(ℝ, E) x) :
    mextDeriv (RoughForm.ofFunction 𝓘(ℝ, E) f) x v = fderiv ℝ f x (v 0) := by
  rw [mextDeriv_ofFunction, ContinuousAlternatingMap.ofSubsingleton_apply_apply,
    mvfderiv_eq_fderiv_apply]

/-- On an open subset `U` of a normed space `E`, with the model `𝓘(ℝ, E)`, a form of class
`Cⁿ` with `n ≠ 0`, read as a map from `U` to `E [⋀^Fin k]→L[ℝ] F`, is differentiable at every
point of `U`. -/
theorem IsSmoothForm.mdifferentiableAt_opens {U : TopologicalSpace.Opens E} {k : ℕ}
    {n : WithTop ℕ∞} {ω : RoughForm 𝓘(ℝ, E) U F k} (hω : IsSmoothForm 𝓘(ℝ, E) n ω)
    (hn : n ≠ 0) (b : U) :
    MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)
      (fun b' : U ↦ show E [⋀^Fin k]→L[ℝ] F from ω b') b := by
  obtain ⟨ω₀, h₀, hω₀⟩ := hω.exists_contDiffOn_opens
  rw [show (fun b' : U ↦ show E [⋀^Fin k]→L[ℝ] F from ω b') = ω₀ ∘ Subtype.val from
    funext hω₀, Manifold.mdifferentiableAt_comp_subtype_val_iff,
    mdifferentiableAt_iff_differentiableAt]
  exact (h₀.differentiableOn hn).differentiableAt (U.isOpen.mem_nhds b.property)

/-- **The exterior derivative on an open subset of a normed space.** Let `U` be an open subset of
`E`, with the model `𝓘(ℝ, E)`, and `ω` a form of degree `k` on `U` that is differentiable at
`b ∈ U`. On `v₀, …, vₖ ∈ E`, `dω` at `b` is the alternating sum over `i` of the derivatives at
`b`, in the direction `vᵢ`, of `b' ↦ ω b' (Fin.removeNth i v)`. -/
theorem mextDeriv_opens_apply {U : TopologicalSpace.Opens E} {k : ℕ}
    {ω : RoughForm 𝓘(ℝ, E) U F k} {b : U}
    (hω : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)
      (fun b' : U ↦ show E [⋀^Fin k]→L[ℝ] F from ω b') b)
    (v : Fin (k + 1) → E) :
    mextDeriv ω b v = ∑ i, (-1) ^ i.val •
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) (fun b' : U ↦ ω b' (i.removeNth v)) b (v i) := by
  set ω₀ : E → E [⋀^Fin k]→L[ℝ] F :=
    Function.extend Subtype.val (fun b' : U ↦ show E [⋀^Fin k]→L[ℝ] F from ω b') 0
  have hω₀ (b' : U) : ω b' = ω₀ b' := (Subtype.val_injective.extend_apply _ _ b').symm
  have hd : DifferentiableAt ℝ ω₀ b := by
    rw [show (fun b' : U ↦ show E [⋀^Fin k]→L[ℝ] F from ω b') = ω₀ ∘ Subtype.val from
      funext hω₀] at hω
    exact mdifferentiableAt_iff_differentiableAt.mp
      (Manifold.mdifferentiableAt_comp_subtype_val_iff.mp hω)
  refine (congrArg (fun φ : E [⋀^Fin (k + 1)]→L[ℝ] F ↦ φ v)
    (mextDeriv_opens_eq_extDeriv hω₀ b)).trans ?_
  rw [extDeriv_apply hd]
  refine Finset.sum_congr rfl fun i _ ↦ congrArg _ ?_
  have h : (fun b' : U ↦ ω b' (i.removeNth v)) = (fun e ↦ ω₀ e (i.removeNth v)) ∘ Subtype.val :=
    funext fun b' ↦ congrArg (fun φ : E [⋀^Fin k]→L[ℝ] F ↦ φ (i.removeNth v)) (hω₀ b')
  rw [h]
  exact (mfderiv_modelSpace_comp_subtypeVal_apply (v i)).symm

end NormedSpace

end TauCeti

end
