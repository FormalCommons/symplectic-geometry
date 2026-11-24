/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Basic
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic
import TauCeti.Geometry.Manifold.SmoothEmbedding.LeftInverse
import TauCeti.Geometry.Manifold.VectorBundle.Submersion

/-!
# The zero section of a vector bundle as a smooth embedding

For a smooth vector bundle `V` with finite-dimensional model fibre `F` over a manifold `B`
without boundary, with finite-dimensional model, the zero section `B → TotalSpace F V` is a smooth
embedding: the bundle projection is a smooth left inverse of it. This file bundles it as
`SymplecticGeometry.Bundle.zeroSectionEmbedding`, so that results about submanifolds, such as the
neighbourhood theorems, apply to it, and shows that its image is closed. It also reads the zero
section in the preferred charts of the total space.

The file has the path of Tau Ceti's `Geometry/Manifold/VectorBundle/ZeroSection.lean`, which
splits the tangent spaces along the zero section. The zero section as an embedding is the
library's own definition, in `SymplecticGeometry.Bundle`. Of the lemmas about Mathlib's notions
alone, `isClosed_range_zeroSection` is in Tau Ceti's namespace `TauCeti.Bundle`, and
`extChartAt_symm_apply_zero_of_mem_baseSet`, about the charts of the total space, in Mathlib's
namespace `Bundle`.

## Main definitions

* `SymplecticGeometry.Bundle.zeroSectionEmbedding`: the zero section, as a smooth embedding.

## Main results

* `SymplecticGeometry.Bundle.coe_zeroSectionEmbedding`: its underlying map is `zeroSection F V`.
* `TauCeti.Bundle.isClosed_range_zeroSection`: the image of the zero section is closed when the
  total space is Hausdorff.
* `Bundle.extChartAt_symm_apply_zero_of_mem_baseSet`: the inverse of the preferred chart of the
  total space sends `(y, 0)` to the zero vector over the base point with coordinate `y`.
-/

public section

noncomputable section

open Bundle Set
open scoped Manifold ContDiff

variable {B : Type*} [TopologicalSpace B]

namespace TauCeti.Bundle

/-- The image of the zero section of a vector bundle with Hausdorff total space is closed: the
zero section has the projection as a continuous left inverse. -/
theorem isClosed_range_zeroSection (𝕜 : Type*) [NontriviallyNormedField 𝕜] (F : Type*)
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] (V : B → Type*) [∀ b, AddCommMonoid (V b)]
    [∀ b, Module 𝕜 (V b)] [∀ b, TopologicalSpace (V b)] [TopologicalSpace (TotalSpace F V)]
    [FiberBundle F V] [VectorBundle 𝕜 F V] [T2Space (TotalSpace F V)] :
    IsClosed (range (zeroSection F V)) :=
  Function.LeftInverse.isClosed_range (zeroSection_proj F V) (FiberBundle.continuous_proj F V)
    (Trivialization.continuous_zeroSection 𝕜)

end TauCeti.Bundle

namespace SymplecticGeometry.Bundle

open TauCeti

variable {𝕜 EB HB : Type*} [RCLike 𝕜]
  [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] [FiniteDimensional 𝕜 EB]
  [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB} [IB.Boundaryless]
  [ChartedSpace HB B] [IsManifold IB ∞ B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {V : B → Type*} [∀ b, AddCommMonoid (V b)] [∀ b, Module 𝕜 (V b)]
  [∀ b, TopologicalSpace (V b)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V] [ContMDiffVectorBundle ∞ F V IB]

variable (IB F V) in
/-- The zero section of a smooth vector bundle with finite-dimensional model fibre over a
manifold without boundary with finite-dimensional model, as a smooth embedding of the base into
the total space. -/
def zeroSectionEmbedding : SmoothEmbedding IB (IB.prod 𝓘(𝕜, F)) ∞ B (TotalSpace F V) :=
  SmoothEmbedding.ofIsSmoothEmbedding (zeroSection F V)
    ((contMDiff_zeroSection 𝕜 V).isSmoothEmbedding_of_leftInverse (by simp)
      (contMDiff_proj V) (zeroSection_proj F V))

variable (IB F V) in
/-- The underlying map of `zeroSectionEmbedding` is the zero section. -/
@[simp]
theorem coe_zeroSectionEmbedding : ⇑(zeroSectionEmbedding IB F V) = zeroSection F V :=
  SmoothEmbedding.coe_ofIsSmoothEmbedding _ _

end SymplecticGeometry.Bundle

namespace Bundle

variable {𝕜 F EB HB : Type*} [NontriviallyNormedField 𝕜] {V : B → Type*}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [∀ x, AddCommMonoid (V x)] [∀ x, Module 𝕜 (V x)]
  [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [ChartedSpace HB B] [FiberBundle F V] [VectorBundle 𝕜 F V]

/-- The inverse of the preferred chart at `p` sends `(y, 0)`, with `y` over the base set of the
trivialization at `p.proj`, to the zero vector over `(extChartAt IB p.proj).symm y`. -/
theorem extChartAt_symm_apply_zero_of_mem_baseSet (p : TotalSpace F V) {y : EB}
    (hy : (extChartAt IB p.proj).symm y ∈ (trivializationAt F V p.proj).baseSet) :
    (extChartAt (IB.prod 𝓘(𝕜, F)) p).symm (y, 0) =
      zeroSection F V ((extChartAt IB p.proj).symm y) := by
  rw [extChartAt_symm_apply_of_mem_baseSet p hy, ← Trivialization.symmₗ_apply (R := 𝕜) _ hy,
    map_zero, zeroSection]

end Bundle

end
