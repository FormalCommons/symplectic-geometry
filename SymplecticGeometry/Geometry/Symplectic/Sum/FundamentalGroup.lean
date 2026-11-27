/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.FundamentalGroup.GluedAlong
public import SymplecticGeometry.Geometry.Symplectic.Sum.ComplTube
public import SymplecticGeometry.Geometry.Symplectic.Sum.RationalEllipticSurface.Remodel
import SymplecticGeometry.AlgebraicTopology.FundamentalGroup.BasepointChange

/-!
# The fundamental group of a fibre sum with a simply connected piece

Let `f₁` and `f₂` be product neighbourhoods of radius `ε` of embeddings `ι₁ : Q → M₁` and
`ι₂ : Q → M₂` of a compact, path connected manifold `Q` into connected Hausdorff manifolds, and
let `0 ≤ δ < ε`. The fibre sum `FiberSum f₁ f₂ hδ hδε` glues the complements of the two closed
tubes along their collars. It is path connected (`FiberSum.instPathConnectedSpace`).

When the complement of `ι₂ (Q)` in `M₂` is simply connected, so is the complement of the closed
tube in `M₂` (`ProductNeighborhood.simplyConnectedSpace_complTube`), and van Kampen for the glued
space (`GluedAlong.fundamentalGroupMulEquiv`) identifies `π₁` of the sum with `π₁` of the
complement of the tube in `M₁` modulo the normal closure of the image of the collar. Filling the
tube back in (`ProductNeighborhood.complTubeQuotientMulEquiv`) identifies that quotient with
`π₁(M₁)` modulo the image of the range of `f₁`, and the change of base point along the radial path
from `ι₁ q` (`ProductNeighborhood.basepointChangeSubgroup_collarRadialPath`) with
`π₁(M₁, ι₁ q) ⧸ ⟨⟨ι₁_* π₁(Q, q)⟩⟩`. The composite is `FiberSum.fundamentalGroupMulEquiv`; on
loops of the complement of the tube in `M₁` it is the map induced by the inclusion into the sum
(`FiberSum.fundamentalGroupMulEquiv_mk`).

For `M₂` the rational elliptic surface `E(1)` on the model of a four-manifold `X`
(`rationalEllipticSurface.OnModel e`), its form rescaled to the area of the standard torus `T`, and
`ι₂` its framed fibre torus, the complement of the fibre is simply connected, and this gives
`fibreSum_fundamentalGroupMulEquiv`: `π₁` of the sum of `X` with `E(1)` along a framed symplectic
embedding `ι` of `T` is `π₁(X, ι t) ⧸ ⟨⟨ι_* π₁(T, t)⟩⟩`.

## Main results

* `SymplecticGeometry.FiberSum.instPathConnectedSpace`: the fibre sum is path connected.
* `SymplecticGeometry.FiberSum.fundamentalGroupMulEquiv` and
  `SymplecticGeometry.FiberSum.fundamentalGroupMulEquiv_mk`: the fundamental group of a fibre sum
  whose second piece has simply connected fibre complement, and its value on loops of the
  complement of the tube in `M₁`.
* `SymplecticGeometry.fibreSum_fundamentalGroupMulEquiv` and
  `SymplecticGeometry.fibreSum_fundamentalGroupMulEquiv_mk`: the case of the sum with the rational
  elliptic surface.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  Exercise 7.2.6.
* [R. E. Gompf, *A new construction of symplectic manifolds*][Gompf1995].
-/

public section

noncomputable section

open Module Set TauCeti
open scoped ContDiff Manifold TauCeti.ComplexManifold

namespace SymplecticGeometry

variable {EQ HQ E H : Type*}
  [NormedAddCommGroup EQ] [NormedSpace ℝ EQ] [FiniteDimensional ℝ EQ] [TopologicalSpace HQ]
  {J : ModelWithCorners ℝ EQ HQ} {Q : Type*} [TopologicalSpace Q] [ChartedSpace HQ Q]
  [IsManifold J ∞ Q]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}

namespace FiberSum

universe u

variable {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace H M₁] [IsManifold I ∞ M₁]
  [TopologicalSpace M₂] [ChartedSpace H M₂] [IsManifold I ∞ M₂]
  {σ₁ : SmoothTwoForm I M₁} {hσ₁ : σ₁.IsNondegenerate} {ι₁ : SmoothEmbedding J I ∞ Q M₁}
  {hι₁ : hσ₁.HasSymplecticTangentImages J ι₁} {hP₁ : finrank ℝ ℂ = finrank ℝ E - finrank ℝ EQ}
  {Φ₁ : SymplecticFraming hι₁ hP₁}
  {σ₂ : SmoothTwoForm I M₂} {hσ₂ : σ₂.IsNondegenerate} {ι₂ : SmoothEmbedding J I ∞ Q M₂}
  {hι₂ : hσ₂.HasSymplecticTangentImages J ι₂} {hP₂ : finrank ℝ ℂ = finrank ℝ E - finrank ℝ EQ}
  {Φ₂ : SymplecticFraming hι₂ hP₂}
  [CompactSpace Q] [T2Space M₁] [T2Space M₂] [PathConnectedSpace Q] [ConnectedSpace M₁]
  [ConnectedSpace M₂] {ε δ : ℝ}
  (f₁ : ProductNeighborhood Φ₁ ε) (f₂ : ProductNeighborhood Φ₂ ε) (hδ : 0 ≤ δ) (hδε : δ < ε)

/-- The fibre sum of two connected manifolds along a path connected `Q` is path connected. -/
instance instPathConnectedSpace : PathConnectedSpace (FiberSum f₁ f₂ hδ hδε) :=
  have := isPathConnected_iff_pathConnectedSpace.1 (f₁.isPathConnected_complTube hδ hδε)
  have := isPathConnected_iff_pathConnectedSpace.1 (f₂.isPathConnected_complTube hδ hδε)
  GluedAlong.pathConnectedSpace _ (f₁.isPathConnected_collar hδ hδε).nonempty

variable [SimplyConnectedSpace ↥(range ι₂)ᶜ]

/-- `FiberSum.fundamentalGroupMulEquiv` before the change of base point: at a point `x` of the
collar, `π₁(M₁, x)` modulo the image of the range of `f₁` is `π₁` of the fibre sum at `inl x`.
It is the inverse of `ProductNeighborhood.complTubeQuotientMulEquiv` followed by van Kampen for
the glued space, `GluedAlong.fundamentalGroupMulEquiv`. It takes a point of the collar rather
than `x` and a proof of `x ∈ collar`, so that the base points of the groups it composes agree up
to reducible unfolding, as instance search needs. -/
private def fundamentalGroupMulEquivCollar (x : f₁.collar hδε) :
    FundamentalGroup M₁ (x : f₁.complTube hδε) ⧸
        f₁.tubeSubgroup (x : f₁.complTube hδε) (f₁.mem_collar_iff_coe_mem_range.1 x.property) ≃*
      FundamentalGroup (FiberSum f₁ f₂ hδ hδε) (GluedAlong.inlContinuousMap _ x) :=
  have := f₂.simplyConnectedSpace_complTube hδ hδε
  have := isPathConnected_iff_pathConnectedSpace.1 (f₁.isPathConnected_complTube hδ hδε)
  (f₁.complTubeQuotientMulEquiv hδ hδε x x.property).symm.trans <|
    (QuotientGroup.quotientMulEquivOfEq (G := FundamentalGroup (f₁.complTube hδε) x)
      (M := f₁.collarSubgroup hδε x x.property)
      (N := Subgroup.normalClosure (range (FundamentalGroup.map (X := f₁.collar hδε)
        (ContinuousMap.subtypeVal (f₁.collar hδε : Set (f₁.complTube hδε))) x)))
      (f₁.collarSubgroup_def hδε x x.property)).trans <|
    GluedAlong.fundamentalGroupMulEquiv _ (f₁.isPathConnected_collar hδ hδε) x

private theorem fundamentalGroupMulEquivCollar_mk (x : f₁.collar hδε)
    (γ : FundamentalGroup (f₁.complTube hδε) x) :
    fundamentalGroupMulEquivCollar f₁ f₂ hδ hδε x (QuotientGroup.mk
        (FundamentalGroup.map (ContinuousMap.subtypeVal (f₁.complTube hδε : Set M₁)) _ γ)) =
      FundamentalGroup.map (GluedAlong.inlContinuousMap _) _ γ := by
  have := f₂.simplyConnectedSpace_complTube hδ hδε
  have := isPathConnected_iff_pathConnectedSpace.1 (f₁.isPathConnected_complTube hδ hδε)
  rw [fundamentalGroupMulEquivCollar, MulEquiv.trans_apply,
    (MulEquiv.symm_apply_eq _).2 (f₁.complTubeQuotientMulEquiv_mk hδ hδε _ _ γ).symm,
    MulEquiv.trans_apply]
  exact (congrArg _ (QuotientGroup.quotientMulEquivOfEq_mk _ γ)).trans
    (GluedAlong.fundamentalGroupMulEquiv_mk _ _ x γ)

/-- **The fundamental group of a fibre sum with a simply connected fibre complement.** If the
complement of `ι₂ (Q)` in `M₂` is simply connected, then for a point `p = (q, z)` of
`Q × A(δ, ε)` the fundamental group of the fibre sum at the collar point `f₁ (q, z)` is
`π₁(M₁, ι₁ q)` modulo the normal closure of the image of `ι₁_* : π₁(Q, q) → π₁(M₁, ι₁ q)`. -/
def fundamentalGroupMulEquiv (p : Q × annulus ℂ δ ε) :
    FundamentalGroup M₁ (ι₁ p.1) ⧸
        Subgroup.normalClosure (range (FundamentalGroup.map ι₁.toContinuousMap p.1)) ≃*
      FundamentalGroup (FiberSum f₁ f₂ hδ hδε)
        (GluedAlong.inlContinuousMap _ (f₁.collarMap hδε p)) :=
  (QuotientGroup.congr _ _
      (FundamentalGroup.fundamentalGroupMulEquivOfPath (f₁.collarRadialPath hδε p))
      ((FundamentalGroup.basepointChangeSubgroup_eq_map _ _).symm.trans
        (f₁.basepointChangeSubgroup_collarRadialPath hδε p))).trans
    (fundamentalGroupMulEquivCollar f₁ f₂ hδ hδε ⟨_, f₁.collarMap_mem_collar hδε p⟩)

/-- On the class of a loop `γ` of the complement of the tube in `M₁` at the collar point
`f₁ (q, z)`, carried into `M₁` and moved to `ι₁ q` along the radial path, the isomorphism
`FiberSum.fundamentalGroupMulEquiv` gives the class of `γ` in the fibre sum. -/
theorem fundamentalGroupMulEquiv_mk (p : Q × annulus ℂ δ ε)
    (γ : FundamentalGroup (f₁.complTube hδε) (f₁.collarMap hδε p)) :
    fundamentalGroupMulEquiv f₁ f₂ hδ hδε p (QuotientGroup.mk
        ((FundamentalGroup.fundamentalGroupMulEquivOfPath (f₁.collarRadialPath hδε p)).symm
          (FundamentalGroup.map (ContinuousMap.subtypeVal (f₁.complTube hδε : Set M₁)) _ γ))) =
      FundamentalGroup.map (GluedAlong.inlContinuousMap _) _ γ := by
  -- `fundamentalGroupMulEquiv` sends the class of `g` to `fundamentalGroupMulEquivCollar` of the
  -- class of `g` moved along the radial path, by its definition and `QuotientGroup.congr_mk`
  exact (congrArg (fundamentalGroupMulEquivCollar f₁ f₂ hδ hδε _) (congrArg QuotientGroup.mk
    (MulEquiv.apply_symm_apply _ _))).trans
      (fundamentalGroupMulEquivCollar_mk f₁ f₂ hδ hδε ⟨_, f₁.collarMap_mem_collar hδε p⟩ γ)

end FiberSum

section RationalEllipticSurface

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  (e : (Fin 2 → ℂ) ≃L[ℝ] V) (p : Unit ⊕ Unit → ℝ) [∀ i, Fact (0 < p i)]
  {X : Type} [TopologicalSpace X] [ChartedSpace V X] [IsManifold 𝓘(ℝ, V) ∞ X] [T2Space X]
  [ConnectedSpace X] {σ : SmoothTwoForm 𝓘(ℝ, V) X} {hσ : σ.IsNondegenerate}
  {ι : SmoothEmbedding (ModelWithCorners.pi fun _ : Unit ⊕ Unit ↦ 𝓘(ℝ)) 𝓘(ℝ, V) ∞
    (∀ i, AddCircle (p i)) X}
  {hι : hσ.HasSymplecticTangentImages (ModelWithCorners.pi fun _ : Unit ⊕ Unit ↦ 𝓘(ℝ)) ι}
  {hP : finrank ℝ ℂ = finrank ℝ V - finrank ℝ (Unit ⊕ Unit → ℝ)} {Φ : SymplecticFraming hι hP}
  {ε δ : ℝ} (f₁ : ProductNeighborhood Φ ε)
  (f₂ : ProductNeighborhood (rationalEllipticSurface.OnModel.torusFraming e p) ε)
  (hδ : 0 ≤ δ) (hδε : δ < ε)

/-- **The fundamental group of the fibre sum with the rational elliptic surface.** Let `X : Type`
be a connected Hausdorff manifold modelled on the four-dimensional real space `V`, with a
nondegenerate two-form `σ`, such as a symplectic form, and `ι` an embedding with symplectic
tangent images of the standard torus `T = ∀ i, AddCircle (p i)`, of any area `p inl * p inr`,
with a symplectic framing.
Sum `X` along `ι` with the rational elliptic surface `E(1)`, its form rescaled to that area and
its fibre torus identified with `T` (`rationalEllipticSurface.OnModel.torusFraming`), by any
product neighbourhoods of radius `ε` and any `0 ≤ δ < ε`. The sum is path connected
(`FiberSum.instPathConnectedSpace`), and for a point `w = (t, z)` of `T × A(δ, ε)` its
fundamental group at the collar point `f₁ (t, z)` is `π₁(X, ι t)` modulo the normal closure of
`ι_* π₁(T, t)`. The statement does not ask that `ι` pull `σ` back to the form of `T`: that is
needed only for the symplectic form of the sum (`FiberSum.symplecticForm`). It takes `X` in
`Type`, the universe of `E(1)`, since the two pieces of a fibre sum share a universe.

Milestone: *Fundamental group after summing with the rational elliptic surface*. -/
def fibreSum_fundamentalGroupMulEquiv (w : (∀ i, AddCircle (p i)) × annulus ℂ δ ε) :
    FundamentalGroup X (ι w.1) ⧸
        Subgroup.normalClosure (range (FundamentalGroup.map ι.toContinuousMap w.1)) ≃*
      FundamentalGroup (FiberSum f₁ f₂ hδ hδε)
        (GluedAlong.inlContinuousMap _ (f₁.collarMap hδε w)) :=
  FiberSum.fundamentalGroupMulEquiv f₁ f₂ hδ hδε w

/-- On the class of a loop `γ` of the complement of the tube in `X`, carried into `X` and moved to
`ι t` along the radial path to `f₁ (t, z)`, for `w = (t, z)`, `fibreSum_fundamentalGroupMulEquiv`
gives the class of `γ` in the fibre sum with the rational elliptic surface. -/
theorem fibreSum_fundamentalGroupMulEquiv_mk (w : (∀ i, AddCircle (p i)) × annulus ℂ δ ε)
    (γ : FundamentalGroup (f₁.complTube hδε) (f₁.collarMap hδε w)) :
    fibreSum_fundamentalGroupMulEquiv e p f₁ f₂ hδ hδε w (QuotientGroup.mk
        ((FundamentalGroup.fundamentalGroupMulEquivOfPath (f₁.collarRadialPath hδε w)).symm
          (FundamentalGroup.map (ContinuousMap.subtypeVal (f₁.complTube hδε : Set X)) _ γ))) =
      FundamentalGroup.map (GluedAlong.inlContinuousMap _) _ γ :=
  FiberSum.fundamentalGroupMulEquiv_mk f₁ f₂ hδ hδε w γ

end RationalEllipticSurface

end SymplecticGeometry

end
