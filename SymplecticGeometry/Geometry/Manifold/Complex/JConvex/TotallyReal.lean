/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Complex.Plurisubharmonic
public import TauCeti.LinearAlgebra.TotallyReal.Basic

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
  `Hess f(v, v) + Hess f(i v, i v) > 0` for `v ≠ 0`; at most one of `v` and `i v` lies in `L`,
  and `Hess f` is nonnegative on `L` too, as a limit of its values off `L`.
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
  set B := criticalHessian 𝓘(ℝ, E) f x
  -- No nonzero `v` has both `v` and `i v` in `L`.
  have hI (v : E) (hv : v ∈ L) (hIv : Complex.I • v ∈ L) : v = 0 := by
    have hmap : Complex.I • v ∈
        L.map ((ofComplexManifold E M).toEndomorphism x).toLinearMap :=
      ⟨v, hv, ofComplexManifold_apply x v⟩
    have h0 : (Complex.I • v : E) = 0 := Submodule.disjoint_def.1 hL.disjoint _ hIv hmap
    exact (smul_eq_zero.1 h0).resolve_left Complex.I_ne_zero
  -- If some `w` lies off `L`, then `Hess f` is nonnegative everywhere: on `L` as the limit of
  -- its values at `u + t • w`, `t ≠ 0`.
  have hnonneg (w : E) (hw : w ∉ L) (u : E) : 0 ≤ B u u := by
    by_cases hu : u ∈ L
    · have hg : Continuous fun t : ℝ ↦ u + t • w := by fun_prop
      have hcont : Continuous fun t : ℝ ↦ B (u + t • w) (u + t • w) :=
        (B.continuous.comp hg).clm_apply hg
      have hlim : Tendsto (fun t : ℝ ↦ B (u + t • w) (u + t • w)) (𝓝[≠] 0) (𝓝 (B u u)) := by
        simpa using hcont.continuousAt (x := 0) |>.tendsto.mono_left nhdsWithin_le_nhds
      refine ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun t ht ↦ (hpos _ ?_).le)
      intro h
      have htw : t • w ∈ L := (L.add_mem_iff_right hu).1 h
      exact hw ((L.smul_mem_iff ht).1 htw)
    · exact (hpos u hu).le
  intro v hv
  by_cases h₁ : v ∈ L
  · have h₂ : Complex.I • v ∉ L := fun h ↦ hv (hI v h₁ h)
    exact add_pos_of_nonneg_of_pos (hnonneg _ h₂ v) (hpos _ h₂)
  · exact add_pos_of_pos_of_nonneg (hpos v h₁) (hnonneg v h₁ _)

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
