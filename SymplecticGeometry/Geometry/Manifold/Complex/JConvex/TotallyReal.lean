/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Complex.LeviForm
public import SymplecticGeometry.LinearAlgebra.TotallyReal.Basic
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure

/-!
# Plurisubharmonic functions near totally real submanifolds

Let `M` be a complex manifold modelled on `E`, seen as a real manifold, with the complex structure
`J = ofComplexManifold E M`, multiplication by `i` on each tangent space. This file gives a
criterion for strict plurisubharmonicity in terms of the real critical Hessian
`Hess f = TauCeti.criticalHessian 𝓘(ℝ, E) f x`, adapted to functions such as squared distances
to a totally real submanifold, whose Hessian degenerates along the submanifold.

* `SymplecticGeometry.isManifoldStrictlyPlurisubharmonicAt_of_criticalHessian_pos`: if
  `Hess f(v, v) > 0` for every `v` outside a real subspace `L` that is totally real for `J`
  (Tau Ceti's `TauCeti.IsTotallyReal`), then `f` is strictly plurisubharmonic at `x`. By Tau
  Ceti's `isManifoldStrictlyPlurisubharmonicAt_iff_criticalHessian`, one has to show
  `Hess f(v, v) + Hess f(i v, i v) > 0` for `v ≠ 0`, which is
  `TauCeti.IsTotallyReal.add_pos_of_forall_notMem_pos` for `J`.
* `SymplecticGeometry.setOf_isManifoldStrictlyPlurisubharmonicAt_mem_nhdsSet_range`: for a map
  `ι : N → M` with totally real tangent images, and `f` real `C²` along `ι(N)` with Hessian
  positive at each point `ι y` off the tangent image of `ι` at `y`, the function `f` is strictly
  plurisubharmonic on a neighbourhood of `ι(N)`. This combines the criterion with
  `TauCeti.IsManifoldStrictlyPlurisubharmonicAt.eventually`.

A nonnegative function that vanishes along `ι(N)` has a critical point at each point of `ι(N)`,
where its Hessian does not depend on the chart; the statements here do not need this, since
Tau Ceti's criterion holds at every point for the Hessian in the preferred chart.

## References

* [K. Cieliebak, Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  Chapter 2.
-/

public section

open Set Filter Topology
open scoped Manifold ContDiff TauCeti.ComplexManifold

namespace SymplecticGeometry

open TauCeti TauCeti.SmoothAlmostComplexStructure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
  {f : M → ℝ} {x : M}

/-- **Strict plurisubharmonicity from a Hessian degenerate along a totally real subspace.** Let
`L` be a real subspace of the tangent space at `x` that is totally real for the complex structure
of `M`. If the critical Hessian of `f` at `x` satisfies `Hess f(v, v) > 0` for every `v ∉ L`,
then `f` is strictly plurisubharmonic at `x`. -/
theorem isManifoldStrictlyPlurisubharmonicAt_of_criticalHessian_pos
    {L : Submodule ℝ (TangentSpace 𝓘(ℝ, E) x)}
    (hL : IsTotallyReal ((ofComplexManifold E M).toEndomorphism x).toLinearMap L)
    (hpos : ∀ v ∉ L, 0 < criticalHessian 𝓘(ℝ, E) f x v v) :
    IsManifoldStrictlyPlurisubharmonicAt E f x := by
  rw [isManifoldStrictlyPlurisubharmonicAt_iff_criticalHessian]
  have hJv (v : E) : ((ofComplexManifold E M).toEndomorphism x).toLinearMap v = Complex.I • v :=
    -- `toLinearMap` and `toEndomorphism` only coerce `ofComplexManifold E M x`.
    ofComplexManifold_apply x v
  have hJ : Function.Injective ((ofComplexManifold E M).toEndomorphism x).toLinearMap :=
    fun v w h ↦ smul_right_injective E Complex.I_ne_zero <| (hJv v).symm.trans (h.trans (hJv w))
  intro v hv
  have h := hL.add_pos_of_forall_notMem_pos hJ hpos hv
  rw [← hJv v]
  exact h

variable {F H' N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ F H'} [TopologicalSpace N] [ChartedSpace H' N]

/-- **Strict plurisubharmonicity near a totally real submanifold.** Let `ι : N → M` have totally
real tangent images for the complex structure of `M`, and let `f` be real `C²` at each point
`ι y`, with critical Hessian `Hess f(v, v) > 0` at `ι y` for every `v` outside the tangent image
of `ι` at `y`. Then `f` is strictly plurisubharmonic at every point of a neighbourhood of the
image of `ι`. -/
theorem setOf_isManifoldStrictlyPlurisubharmonicAt_mem_nhdsSet_range [FiniteDimensional ℂ E]
    {ι : N → M} (hf : ∀ y, ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 f (ι y))
    (hι : ∀ y,
      IsTotallyReal ((ofComplexManifold E M).toEndomorphism (ι y)).toLinearMap
        (LinearMap.range (mfderiv I' 𝓘(ℝ, E) ι y).toLinearMap))
    (hpos : ∀ y, ∀ v ∉ LinearMap.range (mfderiv I' 𝓘(ℝ, E) ι y).toLinearMap,
      0 < criticalHessian 𝓘(ℝ, E) f (ι y) v v) :
    {x | IsManifoldStrictlyPlurisubharmonicAt E f x} ∈ 𝓝ˢ (range ι) := by
  rw [mem_nhdsSet_iff_forall]
  rintro _ ⟨y, rfl⟩
  exact ((isManifoldStrictlyPlurisubharmonicAt_of_criticalHessian_pos (hι y) (hpos y)).eventually
    (hf y))

end SymplecticGeometry

end
