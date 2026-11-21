/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Hom

/-!
# Sections of hom bundles given by bundle isomorphisms

For a family `Φ : ∀ x, V₁ x ≃L[𝕜] V₂ x` of fibrewise linear equivalences whose map of total
spaces is `Cⁿ`, and a finite-dimensional model fibre of `V₁`, the fibrewise inverses
`x ↦ (Φ x).symm` form a `Cⁿ` section of the hom bundle from `V₂` to `V₁`
(`SymplecticGeometry.contMDiff_hom_bundle_symm`). It is the middle step of Tau Ceti's
`TauCeti.contMDiff_bundle_symm`, and its proof follows that one: Tau Ceti's
`TauCeti.contMDiff_hom_bundle_iff` turns `Φ` into a section of the hom bundle, and
`ContMDiff.clm_bundle_inverse` inverts it.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.6
-/

public section

open _root_.Bundle
open scoped Manifold

namespace SymplecticGeometry

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {EB HB B : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  {F₁ F₂ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {V₁ V₂ : B → Type*}
  [∀ x, AddCommGroup (V₁ x)] [∀ x, Module 𝕜 (V₁ x)] [∀ x, TopologicalSpace (V₁ x)]
  [∀ x, IsTopologicalAddGroup (V₁ x)] [∀ x, ContinuousSMul 𝕜 (V₁ x)]
  [TopologicalSpace (TotalSpace F₁ V₁)] [FiberBundle F₁ V₁] [VectorBundle 𝕜 F₁ V₁]
  [∀ x, AddCommGroup (V₂ x)] [∀ x, Module 𝕜 (V₂ x)] [∀ x, TopologicalSpace (V₂ x)]
  [∀ x, IsTopologicalAddGroup (V₂ x)] [∀ x, ContinuousSMul 𝕜 (V₂ x)]
  [TopologicalSpace (TotalSpace F₂ V₂)] [FiberBundle F₂ V₂] [VectorBundle 𝕜 F₂ V₂]
  {n : WithTop ℕ∞}

/-- For a fibrewise linear equivalence `Φ` between vector bundles whose map of total spaces is
`Cⁿ`, with a finite-dimensional model fibre of the source, the fibrewise inverses `(Φ x)⁻¹`
form a `Cⁿ` section of the hom bundle from `V₂` to `V₁`. -/
theorem contMDiff_hom_bundle_symm (Φ : ∀ x, V₁ x ≃L[𝕜] V₂ x)
    (hΦ : ContMDiff (IB.prod 𝓘(𝕜, F₁)) (IB.prod 𝓘(𝕜, F₂)) n
      (fun p : TotalSpace F₁ V₁ ↦ TotalSpace.mk' F₂ p.proj (Φ p.proj p.snd))) :
    ContMDiff IB (IB.prod 𝓘(𝕜, F₂ →L[𝕜] F₁)) n
      (fun x ↦ TotalSpace.mk' (F₂ →L[𝕜] F₁) (E := fun x ↦ V₂ x →L[𝕜] V₁ x) x
        ((Φ x).symm : V₂ x →L[𝕜] V₁ x)) := by
  have : CompleteSpace F₁ := FiniteDimensional.completeSpace 𝕜 F₁
  have h := (TauCeti.contMDiff_hom_bundle_iff (IB := IB) (n := n)
    (fun x ↦ ((Φ x : V₁ x →L[𝕜] V₂ x)))).2 hΦ
  have hi := h.clm_bundle_inverse fun x ↦ ContinuousLinearMap.isInvertible_equiv
  simpa only [ContinuousLinearMap.inverse_equiv] using hi

end SymplecticGeometry

end
