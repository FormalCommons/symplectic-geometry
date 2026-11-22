/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.AlmostComplex
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm

/-!
# Almost complex structures determined by a metric and a two-form: the first consequences

This file is a part of Tau Ceti's `TauCeti/Geometry/Symplectic/Manifold/AlmostComplex/Metric.lean`,
copied from Tau Ceti's main branch at commit `d0858c89d3e451f57c1e07ffb04c0b8eaafe6d9f`
(Tau Ceti pull request #1707), which made these two lemmas public. The pinned version of Tau Ceti
has them only as private lemmas of the root namespace `TauCeti`. For a Riemannian metric on `TM`
with `g(u, v) = σ(u, J v)`:

* `TauCeti.SmoothAlmostComplexStructure.inner_apply_apply_of_inner_eq`: `J` is orthogonal;
* `TauCeti.SmoothAlmostComplexStructure.inner_apply_left_of_inner_eq`: `g(J u, w) = σ(u, w)`.

They are used by `SymplecticGeometry/Geometry/Symplectic/Manifold/AlmostComplex/Metric.lean` and
`SymplecticGeometry/Geometry/Symplectic/Manifold/AlmostComplex/LeviCivita.lean`.

Changes from Tau Ceti's text:
* the module docstring is this one;
* the imports and the opened namespaces are only those the two lemmas need, and the variable
  `K` and the section of Tau Ceti's file that comes before the lemmas are left out.

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford (2017).
* S. K. Donaldson and P. B. Kronheimer, *The Geometry of Four-Manifolds*, Oxford (1990).
-/

public section

noncomputable section

open Bundle
open scoped ContDiff Manifold RealInnerProductSpace

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-! ### Almost complex structures with `g(u, v) = σ(u, J v)` -/

variable {σ : SmoothTwoForm I M} {J : SmoothAlmostComplexStructure I M}

namespace SmoothAlmostComplexStructure

omit [FiniteDimensional ℝ E] in
/-- A smooth almost complex structure with `g(u, v) = σ(u, J v)` is orthogonal. -/
theorem inner_apply_apply_of_inner_eq
    (hJ : ∀ x u v, ⟪u, v⟫ = σ.eval₂ x u (J x v)) (x : M) (u v : TangentSpace I x) :
    ⟪J x u, J x v⟫ = ⟪u, v⟫ := by
  rw [hJ, SmoothAlmostComplexStructure.apply_apply, SmoothBundleForm.eval₂_neg_right,
    ← SmoothBundleForm.eval₂_swap, ← hJ, real_inner_comm]

omit [FiniteDimensional ℝ E] in
/-- A smooth almost complex structure with `g(u, v) = σ(u, J v)` represents `σ` through the
metric: `g(J u, w) = σ(u, w)`. -/
theorem inner_apply_left_of_inner_eq
    (hJ : ∀ x u v, ⟪u, v⟫ = σ.eval₂ x u (J x v)) (x : M) (u w : TangentSpace I x) :
    ⟪J x u, w⟫ = σ.eval₂ x u w := by
  rw [← inner_apply_apply_of_inner_eq hJ x (J x u) w, SmoothAlmostComplexStructure.apply_apply,
    inner_neg_left, hJ x u (J x w), SmoothAlmostComplexStructure.apply_apply,
    SmoothBundleForm.eval₂_neg_right, _root_.neg_neg]

end SmoothAlmostComplexStructure

end TauCeti
