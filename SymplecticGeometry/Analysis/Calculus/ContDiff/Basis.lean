/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Normed.Operator.Bilinear
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompLinear

/-!
# Derivatives of a map into a finite-dimensional space through its coordinates

For a basis `b` of a finite-dimensional normed space `F` over a complete nontrivially normed field,
and a map `f : E → F`:

* `Module.Basis.contDiffOn_repr`: the coordinates `y ↦ b.repr (f y) j` of `f` are `C^n` on a set
  where `f` is.
* `Module.Basis.norm_iteratedFDeriv_le_sum`: at a point where `f` is `Cⁿ`, the norm of its `n`-th
  derivative is at most `∑ j, ‖b j‖ * ‖iteratedFDeriv 𝕜 n (fun y ↦ b.repr (f y) j) x‖`.

The second is a converse of Mathlib's `ContinuousLinearMap.norm_iteratedFDeriv_comp_left`, applied
to the coordinate functionals. It is Tau Ceti's `TauCeti.norm_iteratedFDeriv_sum_comp_left_le`
for the maps `c ↦ c • b j`, applied to `f = fun y ↦ ∑ j, b.repr (f y) j • b j`.
-/

public section

namespace Module.Basis

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [FiniteDimensional 𝕜 F] {ι : Type*}

/-- The coordinates in a basis `b` of a map `f` that is `C^n` on a set `s` are `C^n` on `s`. -/
theorem contDiffOn_repr (b : Basis ι 𝕜 F) {f : E → F} {s : Set E} {n : WithTop ℕ∞}
    (hf : ContDiffOn 𝕜 n f s) (j : ι) : ContDiffOn 𝕜 n (fun y ↦ b.repr (f y) j) s :=
  (LinearMap.toContinuousLinearMap (b.coord j)).contDiff.comp_contDiffOn hf

variable [Fintype ι]

/-- The `n`-th derivative of a function `f` with values in a finite-dimensional space, at a point
where `f` is `Cⁿ`, has norm at most the sum over a basis `b` of `‖b j‖` times the norm of the
`n`-th derivative of the `j`-th coordinate `y ↦ b.repr (f y) j`. -/
theorem norm_iteratedFDeriv_le_sum (b : Basis ι 𝕜 F) {f : E → F} {x : E} {n : ℕ}
    (hf : ContDiffAt 𝕜 n f x) :
    ‖iteratedFDeriv 𝕜 n f x‖ ≤
      ∑ j, ‖b j‖ * ‖iteratedFDeriv 𝕜 n (fun y ↦ b.repr (f y) j) x‖ := by
  have hc (j : ι) : ContDiffAt 𝕜 n (fun y ↦ b.repr (f y) j) x :=
    (LinearMap.toContinuousLinearMap (b.coord j)).contDiff.contDiffAt.comp x hf
  simpa only [ContinuousLinearMap.toSpanSingleton_apply, ContinuousLinearMap.norm_toSpanSingleton,
    b.sum_repr] using TauCeti.norm_iteratedFDeriv_sum_comp_left_le Finset.univ
      (fun j ↦ ContinuousLinearMap.toSpanSingleton 𝕜 (b j)) fun j _ ↦ hc j

end Module.Basis
