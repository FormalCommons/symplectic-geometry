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

For `M₂` the rational elliptic surface `E(1)` on the model and in the universe of a four-manifold
`X` (`rationalEllipticSurface.OnModel e`), its form rescaled to the area of the standard torus
`T`, and `ι₂` its framed fibre torus, the complement of the fibre is simply connected, and this
gives `fibreSum_fundamentalGroupMulEquiv`: `π₁` of the sum of `X` with `E(1)` along a framed
symplectic embedding `ι` of `T` is `π₁(X, ι t) ⧸ ⟨⟨ι_* π₁(T, t)⟩⟩`.

An embedding `ι : Q' → M₁` that misses the closed tube is carried into the sum by `inl`
(`FiberSum.inlEmbedding`). The embedding and the one carried into the sum both factor
through the complement of the tube, so `FiberSum.fundamentalGroupMulEquiv_mk` shows that the
isomorphism, after the quotient map, sends the normal closure of `ι_* π₁(Q', q')` to the normal
closure of the image of the carried embedding
(`FiberSum.map_normalClosure_basepointChangeSubgroup_range_map`). Both are moved to the base
points of the isomorphism along paths, and since normal closures of moved subgroups do not depend
on the path (`FundamentalGroup.normalClosure_basepointChangeSubgroup_eq`), the paths are
arbitrary. This is what lets one sum again along a second embedding after a first sum.

## Main results

* `SymplecticGeometry.FiberSum.instPathConnectedSpace`: the fibre sum is path connected.
* `SymplecticGeometry.FiberSum.fundamentalGroupMulEquiv` and
  `SymplecticGeometry.FiberSum.fundamentalGroupMulEquiv_mk`: the fundamental group of a fibre sum
  whose second piece has simply connected fibre complement, and its value on loops of the
  complement of the tube in `M₁`.
* `SymplecticGeometry.fibreSum_fundamentalGroupMulEquiv` and
  `SymplecticGeometry.fibreSum_fundamentalGroupMulEquiv_mk`: the case of the sum with the rational
  elliptic surface.
* `SymplecticGeometry.FiberSum.map_normalClosure_basepointChangeSubgroup_range_map` and
  `SymplecticGeometry.fibreSum_map_normalClosure_basepointChangeSubgroup_range_map`: the
  isomorphisms carry the normal closure of the image of an embedding that misses the tube onto
  that of the embedding carried to the sum.

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


section Embedding

variable {EQ' HQ' : Type*} [NormedAddCommGroup EQ'] [NormedSpace ℝ EQ'] [TopologicalSpace HQ']
  {J' : ModelWithCorners ℝ EQ' HQ'} {Q' : Type*} [TopologicalSpace Q'] [ChartedSpace HQ' Q']
  (ι : SmoothEmbedding J' I ∞ Q' M₁) (hι : ∀ q, ι q ∈ f₁.complTube hδε)

/-- **Fundamental groups of embeddings carried to the fibre sum.** Let `ι : Q' → M₁` be an
embedding that misses the closed tube, and `inlEmbedding f₂ hδ ι hι` the embedding it gives into
the fibre sum. Move the image of `ι_* π₁(Q', q')` to `ι₁ q` along any path `γ`, and that of the
carried embedding to the collar point `f₁ (q, z)` along any path `η`, for `p = (q, z)`. Then
`FiberSum.fundamentalGroupMulEquiv`, after the quotient map, carries the normal closure of the
first onto the normal closure of the second. -/
theorem map_normalClosure_basepointChangeSubgroup_range_map (p : Q × annulus ℂ δ ε) (q' : Q')
    (γ : Path (ι q') (ι₁ p.1))
    (η : Path (inlEmbedding f₂ hδ ι hι q')
      (GluedAlong.inlContinuousMap _ (f₁.collarMap hδε p))) :
    (Subgroup.normalClosure (FundamentalGroup.basepointChangeSubgroup γ
        (FundamentalGroup.map ι.toContinuousMap q').range :
          Set (FundamentalGroup M₁ (ι₁ p.1)))).map
        ((fundamentalGroupMulEquiv f₁ f₂ hδ hδε p).toMonoidHom.comp (QuotientGroup.mk' _)) =
      Subgroup.normalClosure (FundamentalGroup.basepointChangeSubgroup η
        (FundamentalGroup.map (inlEmbedding f₂ hδ ι hι).toContinuousMap q').range) := by
  have := isPathConnected_iff_pathConnectedSpace.1 (f₁.isPathConnected_complTube hδ hδε)
  -- both embeddings factor through the restriction of `ι` to the complement of the
  -- tube
  have hv : ι.toContinuousMap =
      (ContinuousMap.subtypeVal (f₁.complTube hδε : Set M₁)).comp
        (ι.codRestrict (f₁.complTube hδε) hι).toContinuousMap :=
    ContinuousMap.ext fun q ↦ (ι.val_codRestrict_apply _ hι q).symm
  have hu : (inlEmbedding f₂ hδ ι hι).toContinuousMap =
      (GluedAlong.inlContinuousMap (fiberSumGluing f₁ f₂ hδ hδε).toHomeomorph).comp
        (ι.codRestrict (f₁.complTube hδε) hι).toContinuousMap :=
    ContinuousMap.ext fun q ↦ congrFun (coe_inlEmbedding ι hι) q
  -- `L`: the image on `π₁` of that restriction, moved to the collar point in the complement
  obtain ⟨L, hL⟩ : ∃ L, L = FundamentalGroup.basepointChangeSubgroup
      (PathConnectedSpace.somePath _ (f₁.collarMap hδε p))
      (FundamentalGroup.map (ι.codRestrict (f₁.complTube hδε) hι).toContinuousMap q').range :=
    ⟨_, rfl⟩
  -- on the side of `M₁`, `γ` is moved on to the collar point along the radial path
  have hR : Subgroup.normalClosure (FundamentalGroup.basepointChangeSubgroup
      (γ.trans (f₁.collarRadialPath hδε p)) (FundamentalGroup.map ι.toContinuousMap q').range :
        Set (FundamentalGroup M₁ (f₁.collarMap hδε p : M₁))) =
      Subgroup.normalClosure (SetLike.coe (L.map (FundamentalGroup.map
        (ContinuousMap.subtypeVal (f₁.complTube hδε : Set M₁)) (f₁.collarMap hδε p)))) := by
    rw [hL]
    exact FundamentalGroup.normalClosure_basepointChangeSubgroup_range_eq_of_eq_comp _ _ hv _ _
  -- on loops of the complement of the tube, the isomorphism is induced by `inl`
  have hΨ : (((fundamentalGroupMulEquiv f₁ f₂ hδ hδε p).toMonoidHom.comp
      (QuotientGroup.mk' _)).comp (FundamentalGroup.fundamentalGroupMulEquivOfPath
        (f₁.collarRadialPath hδε p)).symm.toMonoidHom).comp
          (FundamentalGroup.map (ContinuousMap.subtypeVal (f₁.complTube hδε : Set M₁))
            (f₁.collarMap hδε p)) =
      FundamentalGroup.map (GluedAlong.inlContinuousMap _) (f₁.collarMap hδε p) :=
    MonoidHom.ext (fundamentalGroupMulEquiv_mk f₁ f₂ hδ hδε p)
  have hsurj : Function.Surjective (((fundamentalGroupMulEquiv f₁ f₂ hδ hδε p).toMonoidHom.comp
      (QuotientGroup.mk' _)).comp (FundamentalGroup.fundamentalGroupMulEquivOfPath
        (f₁.collarRadialPath hδε p)).symm.toMonoidHom) :=
    (fundamentalGroupMulEquiv f₁ f₂ hδ hδε p).surjective.comp
      ((QuotientGroup.mk'_surjective _).comp (MulEquiv.surjective _))
  rw [FundamentalGroup.normalClosure_basepointChangeSubgroup_range_eq_of_eq_comp _ _ hu η
      (PathConnectedSpace.somePath _ (f₁.collarMap hδε p)), ← hL,
    FundamentalGroup.normalClosure_basepointChangeSubgroup_eq γ
      ((γ.trans (f₁.collarRadialPath hδε p)).trans (f₁.collarRadialPath hδε p).symm),
    FundamentalGroup.basepointChangeSubgroup_trans,
    FundamentalGroup.basepointChangeSubgroup_eq_map,
    FundamentalGroup.fundamentalGroupMulEquivOfPath_symm, Subgroup.coe_map,
    ← Subgroup.map_normalClosure _ _ (MulEquiv.surjective _), Subgroup.map_map, hR]
  refine (Subgroup.map_normalClosure _ _ hsurj).trans ?_
  rw [← hΨ]
  exact congrArg Subgroup.normalClosure ((Subgroup.coe_map _ _).symm.trans
    (congrArg SetLike.coe (Subgroup.map_map _ _ _)))

end Embedding

end FiberSum

section RationalEllipticSurface

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  (e : (Fin 2 → ℂ) ≃L[ℝ] V) (p : Unit ⊕ Unit → ℝ) [∀ i, Fact (0 < p i)]
  {X : Type*} [TopologicalSpace X] [ChartedSpace V X] [IsManifold 𝓘(ℝ, V) ∞ X] [T2Space X]
  [ConnectedSpace X] {σ : SmoothTwoForm 𝓘(ℝ, V) X} {hσ : σ.IsNondegenerate}
  {ι : SmoothEmbedding (ModelWithCorners.pi fun _ : Unit ⊕ Unit ↦ 𝓘(ℝ)) 𝓘(ℝ, V) ∞
    (∀ i, AddCircle (p i)) X}
  {hι : hσ.HasSymplecticTangentImages (ModelWithCorners.pi fun _ : Unit ⊕ Unit ↦ 𝓘(ℝ)) ι}
  {hP : finrank ℝ ℂ = finrank ℝ V - finrank ℝ (Unit ⊕ Unit → ℝ)} {Φ : SymplecticFraming hι hP}
  {ε δ : ℝ} (f₁ : ProductNeighborhood Φ ε)
  (f₂ : ProductNeighborhood (rationalEllipticSurface.OnModel.torusFraming e p) ε)
  (hδ : 0 ≤ δ) (hδε : δ < ε)

/-- **The fundamental group of the fibre sum with the rational elliptic surface.** Let `X`
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
needed only for the symplectic form of the sum (`FiberSum.symplecticForm`). `X` may lie in any
universe: `E(1)` is lifted to it (`rationalEllipticSurface.OnModel`).

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

/-- The analogue of `FiberSum.map_normalClosure_basepointChangeSubgroup_range_map` for the sum
with the rational elliptic surface: for an embedding `ι' : Q' → X` that misses the closed tube,
`fibreSum_fundamentalGroupMulEquiv`, after the quotient map, carries the normal closure of
`ι'_* π₁(Q', q')` moved to `ι t` along any path `γ` onto the normal closure of the image of the
embedding carried to the sum, moved to the collar point `f₁ (t, z)` along any path `η`, for
`w = (t, z)`. -/
theorem fibreSum_map_normalClosure_basepointChangeSubgroup_range_map {EQ' HQ' : Type*}
    [NormedAddCommGroup EQ'] [NormedSpace ℝ EQ'] [TopologicalSpace HQ']
    {J' : ModelWithCorners ℝ EQ' HQ'} {Q' : Type*} [TopologicalSpace Q'] [ChartedSpace HQ' Q']
    (ι' : SmoothEmbedding J' 𝓘(ℝ, V) ∞ Q' X) (hι' : ∀ q, ι' q ∈ f₁.complTube hδε)
    (w : (∀ i, AddCircle (p i)) × annulus ℂ δ ε) (q' : Q') (γ : Path (ι' q') (ι w.1))
    (η : Path (FiberSum.inlEmbedding f₂ hδ ι' hι' q')
      (GluedAlong.inlContinuousMap _ (f₁.collarMap hδε w))) :
    (Subgroup.normalClosure (FundamentalGroup.basepointChangeSubgroup γ
        (FundamentalGroup.map ι'.toContinuousMap q').range :
          Set (FundamentalGroup X (ι w.1)))).map
        ((fibreSum_fundamentalGroupMulEquiv e p f₁ f₂ hδ hδε w).toMonoidHom.comp
          (QuotientGroup.mk' _)) =
      Subgroup.normalClosure (FundamentalGroup.basepointChangeSubgroup η
        (FundamentalGroup.map (FiberSum.inlEmbedding f₂ hδ ι' hι').toContinuousMap q').range) :=
  FiberSum.map_normalClosure_basepointChangeSubgroup_range_map f₁ f₂ hδ hδε ι' hι' w q' γ η

end RationalEllipticSurface

end SymplecticGeometry

end
