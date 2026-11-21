/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.ContinuousAlternatingMap
public import TauCeti.Geometry.Manifold.VectorBundle.Pullback
public import SymplecticGeometry.Topology.VectorBundle.Pullback

/-!
# Sections of the alternating bundle of a pull-back

Let `V` be a vector bundle over `B` and `f : X → B` a `C^n` map. A family
`A x : V (f x) [⋀^ι]→L[𝕜] G` of alternating maps with values in a fixed normed space `G` can be
read in two ways: as a section of the bundle of alternating maps from `f *ᵖ V` to the trivial
bundle `Bundle.Trivial X G` over `X`, or as a map from `X` into the total space of the bundle of
alternating maps from `V` to `Bundle.Trivial B G`, lying over `f`. This file shows that the two
are `C^n` together (`Bundle.Pullback.contMDiff_continuousAlternatingMap_section_iff`), the
analogue for alternating maps of Tau Ceti's `Bundle.Pullback.contMDiff_hom_section_iff`. The
proof follows Tau Ceti's: near a point, Mathlib's `contMDiffAt_continuousAlternatingMap_bundle`
reduces both sides to coordinate expressions, which agree on a neighbourhood by
`ContinuousAlternatingMap.inCoordinates_pullback_trivial_of_mem`
(`SymplecticGeometry.Topology.VectorBundle.Pullback`).

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.6
* D. Husemoller, *Fibre Bundles*, 3rd ed., Graduate Texts in Mathematics 20, Springer, 1994,
  Chapter 2 (induced bundles).
-/

public section

open Bundle
open scoped Manifold

variable {𝕜 B X F G K ι EB HB EX HX : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  [NormedAddCommGroup EX] [NormedSpace 𝕜 EX] [TopologicalSpace HX]
  {IX : ModelWithCorners 𝕜 EX HX} [TopologicalSpace X] [ChartedSpace HX X]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {V : B → Type*}
  [∀ b, AddCommGroup (V b)] [∀ b, Module 𝕜 (V b)] [∀ b, TopologicalSpace (V b)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle 𝕜 F V]
  [FunLike K X B] [ContinuousMapClass K X B] {n : WithTop ℕ∞}

namespace Bundle.Pullback

/-- A family `A x` of alternating maps from `V (f x)` to `G`, along a `C^n` map `f`, is a `C^n`
section of the bundle of alternating maps from `f *ᵖ V` to the trivial bundle with fibre `G`
exactly when `x ↦ ⟨f x, A x⟩` is `C^n` into the bundle of alternating maps from `V` to the
trivial bundle with fibre `G`. No rank or smooth-bundle assumption is needed. -/
theorem contMDiff_continuousAlternatingMap_section_iff [Fintype ι] (f : K)
    (hf : ContMDiff IX IB n f) (A : ∀ x, V (f x) [⋀^ι]→L[𝕜] G) :
    ContMDiff IX (IX.prod 𝓘(𝕜, F [⋀^ι]→L[𝕜] G)) n
        (fun x ↦ TotalSpace.mk' (F [⋀^ι]→L[𝕜] G)
          (E := fun x ↦ ((f : X → B) *ᵖ V) x [⋀^ι]→L[𝕜] Bundle.Trivial X G x) x (A x)) ↔
      ContMDiff IX (IB.prod 𝓘(𝕜, F [⋀^ι]→L[𝕜] G)) n
        (fun x ↦ TotalSpace.mk' (F [⋀^ι]→L[𝕜] G)
          (E := fun b ↦ V b [⋀^ι]→L[𝕜] Bundle.Trivial B G b) (f x) (A x)) := by
  have heq (x : X) :
      (fun y ↦ ContinuousAlternatingMap.inCoordinates F G (E₁ := (f : X → B) *ᵖ V)
        (E₂ := Bundle.Trivial X G) x y x y (A y)) =ᶠ[nhds x]
      (fun y ↦ ContinuousAlternatingMap.inCoordinates F G (E₁ := V)
        (E₂ := Bundle.Trivial B G) (f x) (f y) (f x) (f y) (A y)) := by
    filter_upwards [hf.continuous.continuousAt.preimage_mem_nhds
      ((trivializationAt F V (f x)).open_baseSet.mem_nhds
        (FiberBundle.mem_baseSet_trivializationAt F V (f x)))] with y hy
    exact ContinuousAlternatingMap.inCoordinates_pullback_trivial_of_mem f x y (A y) hy
  constructor
  · intro h x
    have hx := (contMDiffAt_continuousAlternatingMap_bundle _).mp (h x)
    rw [contMDiffAt_continuousAlternatingMap_bundle]
    exact ⟨hf x, hx.2.congr_of_eventuallyEq (heq x).symm⟩
  · intro h x
    have hx := (contMDiffAt_continuousAlternatingMap_bundle _).mp (h x)
    rw [contMDiffAt_continuousAlternatingMap_bundle]
    exact ⟨contMDiffAt_id, hx.2.congr_of_eventuallyEq (heq x)⟩

end Bundle.Pullback

end
