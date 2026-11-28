/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.LocalFrame
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-!
# Differentiability of the ratio of two sections of a line bundle

Let `L` be a bundle with model fibre a field `𝕜'`, smooth over a smaller field `𝕜` (such as a
complex line bundle seen as a real vector bundle), and let `e` be a trivialization of `L` in its
atlas that is linear over `𝕜'`. For two sections `σ` and `τ` of `L`, Tau Ceti's
`Bundle.Trivialization.coordRatio` gives at each point `p` the scalar `e.coordRatio (σ p) (τ p)`,
the quotient of the coordinates of `τ p` and `σ p` in `e`. This file shows that this function is
differentiable over `𝕜` at every point of `e.baseSet` at which `σ` and `τ` are differentiable and
`σ` does not vanish: near such a point it is the quotient of the coordinate functions of `τ` and
`σ`, which are differentiable.

The proof follows the differentiability step of Tau Ceti's
`TauCeti.IsRealCauchyRiemannOperator.exists_mdifferentiableOn_eq_smul`.

## Main results

* `Bundle.Trivialization.mdifferentiableAt_coordRatio`: the ratio of two differentiable sections,
  read in a trivialization, is differentiable where the denominator does not vanish.
-/

public section

open Bundle Filter Set
open scoped Manifold Topology

namespace Bundle.Trivialization

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {L : B → Type*} [TopologicalSpace (TotalSpace 𝕜' L)] [∀ x, TopologicalSpace (L x)]
  [∀ x, AddCommMonoid (L x)] [∀ x, Module 𝕜 (L x)] [∀ x, Module 𝕜' (L x)] [FiberBundle 𝕜' L]
  [VectorBundle 𝕜 𝕜' L] [ContMDiffVectorBundle 1 𝕜' L IB]
  (e : Trivialization 𝕜' (π 𝕜' L)) [e.IsLinear 𝕜'] [MemTrivializationAtlas e]

/-- Let `e` be a trivialization of a bundle `L` with model fibre `𝕜'`, linear over `𝕜'`, and
let `σ` and `τ` be sections of `L` that are differentiable over `𝕜` at a point `x` of
`e.baseSet`, with `σ x ≠ 0`. Then the ratio `p ↦ e.coordRatio (σ p) (τ p)` of `τ` to `σ`, read
in `e`, is differentiable over `𝕜` at `x`. -/
theorem mdifferentiableAt_coordRatio {σ τ : Π x, L x} {x : B} (hx : x ∈ e.baseSet)
    (hσ : MDifferentiableAt IB (IB.prod 𝓘(𝕜, 𝕜')) (fun p ↦ TotalSpace.mk' 𝕜' p (σ p)) x)
    (hτ : MDifferentiableAt IB (IB.prod 𝓘(𝕜, 𝕜')) (fun p ↦ TotalSpace.mk' 𝕜' p (τ p)) x)
    (hσx : σ x ≠ 0) :
    MDifferentiableAt IB 𝓘(𝕜, 𝕜') (fun p ↦ e.coordRatio (σ p) (τ p)) x := by
  have hnum := (e.mdifferentiableAt_section_iff IB τ hx).1 hτ
  have hden := (e.mdifferentiableAt_section_iff IB σ hx).1 hσ
  -- The coordinate of `σ x` does not vanish, since `e` is injective on the fibre at `x`.
  have hden0 : (e ⟨x, σ x⟩).2 ≠ 0 := by
    have h := (map_ne_zero_iff _ (e.continuousLinearEquivAt 𝕜' x hx).injective).2 hσx
    rwa [continuousLinearEquivAt_apply] at h
  refine (hnum.div hden hden0).congr_of_eventuallyEq ?_
  filter_upwards [e.open_baseSet.mem_nhds hx] with p hp
  rw [coordRatio_def, e.continuousLinearMapAt_apply_of_mem (R := 𝕜') hp,
    e.continuousLinearMapAt_apply_of_mem (R := 𝕜') hp, Pi.div_apply]

end Bundle.Trivialization

end
