/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.LocalFrame
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import SymplecticGeometry.Geometry.Manifold.Algebra.Inv
import SymplecticGeometry.Geometry.Manifold.Algebra.Structures
import TauCeti.Topology.VectorBundle.Trivialization

/-!
# Differentiability of the ratio of two sections of a line bundle

Let `L` be a bundle with model fibre a field `𝕜'`, smooth over a smaller field `𝕜` (such as a
complex line bundle seen as a real vector bundle), and let `e` be a trivialization of `L` in its
atlas that is linear over `𝕜'`. For two sections `σ` and `τ` of `L`, Tau Ceti's
`Bundle.Trivialization.coordRatio` gives at each point `p` the scalar `e.coordRatio (σ p) (τ p)`,
over `e.baseSet` the quotient of the coordinates of `τ p` and `σ p` in `e`, as
`Bundle.Trivialization.coordRatio_eq_div_of_mem` states. This file shows that this function is
differentiable over `𝕜`, or `C^n` over `𝕜`, at every point of `e.baseSet` at which `σ` and `τ`
are and `σ` does not vanish: near such a point it is the quotient of the coordinate functions of
`τ` and `σ`. The `C^n` case divides with Mathlib's `ContMDiffAt.div₀`, using that multiplication
and inversion in `𝕜'` are `C^n` over `𝕜` (the instances of
`SymplecticGeometry.Geometry.Manifold.Algebra.Structures` and
`SymplecticGeometry.Geometry.Manifold.Algebra.Inv`).

The proofs follow the differentiability step of Tau Ceti's
`TauCeti.IsRealCauchyRiemannOperator.exists_mdifferentiableOn_eq_smul`.

## Main results

* `Bundle.Trivialization.coordRatio_eq_div_of_mem`: over the base set of `e`, the ratio is the
  quotient of the coordinates of the two vectors in `e`.
* `Bundle.Trivialization.mdifferentiableAt_coordRatio`: the ratio of two differentiable sections,
  read in a trivialization, is differentiable where the denominator does not vanish.
* `Bundle.Trivialization.contMDiffAt_coordRatio`: the same for `C^n` sections.
-/

public section

open Bundle Filter Set
open scoped Manifold Topology ContDiff

namespace Bundle.Trivialization

section Div

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {B : Type*} [TopologicalSpace B]
  {L : B → Type*} [TopologicalSpace (TotalSpace 𝕜 L)] [∀ x, TopologicalSpace (L x)]
  [∀ x, AddCommMonoid (L x)] [∀ x, Module 𝕜 (L x)] [FiberBundle 𝕜 L]
  (e : Trivialization 𝕜 (π 𝕜 L)) [e.IsLinear 𝕜]

/-- Over the base set of a trivialization `e` of a bundle with model fibre `𝕜`, the ratio of
`w` to `v` read in `e` is the quotient of the coordinates of `w` and `v` in `e`. -/
theorem coordRatio_eq_div_of_mem {x : B} (hx : x ∈ e.baseSet) (v w : L x) :
    e.coordRatio v w = (e ⟨x, w⟩).2 / (e ⟨x, v⟩).2 := by
  rw [coordRatio_def, e.continuousLinearMapAt_apply_of_mem (R := 𝕜) hx,
    e.continuousLinearMapAt_apply_of_mem (R := 𝕜) hx]

end Div

section Differentiable

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
  have hden0 : (e ⟨x, σ x⟩).2 ≠ 0 := (e.snd_apply_ne_zero_iff 𝕜' hx).2 hσx
  refine (hnum.div hden hden0).congr_of_eventuallyEq ?_
  filter_upwards [e.open_baseSet.mem_nhds hx] with p hp
  rw [e.coordRatio_eq_div_of_mem hp, Pi.div_apply]

end Differentiable

section ContMDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B] {n : ℕ∞ω}
  {L : B → Type*} [TopologicalSpace (TotalSpace 𝕜' L)] [∀ x, TopologicalSpace (L x)]
  [∀ x, AddCommMonoid (L x)] [∀ x, Module 𝕜 (L x)] [∀ x, Module 𝕜' (L x)] [FiberBundle 𝕜' L]
  [VectorBundle 𝕜 𝕜' L] [ContMDiffVectorBundle n 𝕜' L IB]
  (e : Trivialization 𝕜' (π 𝕜' L)) [e.IsLinear 𝕜'] [MemTrivializationAtlas e]

/-- Let `e` be a trivialization of a bundle `L` with model fibre `𝕜'`, linear over `𝕜'`, and
let `σ` and `τ` be sections of `L` that are `C^n` over `𝕜` at a point `x` of `e.baseSet`, with
`σ x ≠ 0`. Then the ratio `p ↦ e.coordRatio (σ p) (τ p)` of `τ` to `σ`, read in `e`, is `C^n`
over `𝕜` at `x`. -/
theorem contMDiffAt_coordRatio {σ τ : Π x, L x} {x : B} (hx : x ∈ e.baseSet)
    (hσ : ContMDiffAt IB (IB.prod 𝓘(𝕜, 𝕜')) n (fun p ↦ TotalSpace.mk' 𝕜' p (σ p)) x)
    (hτ : ContMDiffAt IB (IB.prod 𝓘(𝕜, 𝕜')) n (fun p ↦ TotalSpace.mk' 𝕜' p (τ p)) x)
    (hσx : σ x ≠ 0) :
    ContMDiffAt IB 𝓘(𝕜, 𝕜') n (fun p ↦ e.coordRatio (σ p) (τ p)) x := by
  have hnum := (e.contMDiffAt_section_iff hx).1 hτ
  have hden := (e.contMDiffAt_section_iff hx).1 hσ
  have hden0 : (e ⟨x, σ x⟩).2 ≠ 0 := (e.snd_apply_ne_zero_iff 𝕜' hx).2 hσx
  refine (hnum.div₀ hden hden0).congr_of_eventuallyEq ?_
  filter_upwards [e.open_baseSet.mem_nhds hx] with p hp
  rw [e.coordRatio_eq_div_of_mem hp, Pi.div_apply]

end ContMDiff

end Bundle.Trivialization

end
