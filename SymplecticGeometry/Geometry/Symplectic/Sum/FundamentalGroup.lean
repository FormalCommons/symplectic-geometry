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
import SymplecticGeometry.GroupTheory.Subgroup.NormalClosure

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

A continuous map `φ : W → M₁ ∖ tube` into the complement of the closed tube gives a map `k` into
`M₁` and a map `k'` into the sum through `inl`. By `FiberSum.fundamentalGroupMulEquiv_mk`, the
isomorphism, after the quotient map, sends the normal closure of `k_* π₁(W, x)` to that of
`k'_* π₁(W, x)` (`FiberSum.map_normalClosure_basepointChangeSubgroup_range_map_of_eq_comp`).
Both are moved to the base points of the isomorphism along paths, and since normal closures of
moved subgroups do not depend on the path
(`FundamentalGroup.normalClosure_basepointChangeSubgroup_eq`), the paths are arbitrary. An
embedding `ι : Q' → M₁` that misses the closed tube is such a map, and `k'` is then the embedding
carried into the sum by `inl` (`FiberSum.inlEmbedding`,
`FiberSum.map_normalClosure_basepointChangeSubgroup_range_map`). This is what lets one sum again
along a second embedding after a first sum.

Summing in this way once along each of finitely many pairwise disjoint framed symplectic tori
`ι k` in a compact, connected, symplectic four-manifold `X` gives
`exists_fundamentalGroup_mulEquiv_quotient_tori`: a compact, connected, symplectic `Y` with
`π₁(Y)` isomorphic to `π₁(X, x)` modulo the normal closure of all the `(ι k)_* π₁(T, t)`, moved to
`x` along paths. The proof is an induction on the finite index type
(`Finite.induction_empty_option`). For `Option κ`, a product neighbourhood of `ι none` is taken
inside the complement of the other tori (`ProductNeighborhood.exists_range_subset`), so that they
miss its tube and are carried into the sum with their forms and framings
(`FiberSum.inlEmbedding`, `FiberSum.inlEmbeddingFraming`); the sum is compact
(`FiberSum.instCompactSpace`), and the induction hypothesis applies to it. The two quotients match
because the isomorphism of `fibreSum_fundamentalGroupMulEquiv`, after the quotient map, carries
the normal closure of each remaining torus in `X` onto that of the torus carried into the sum
(`fibreSum_map_normalClosure_basepointChangeSubgroup_range_map`), and by the third isomorphism
theorem, `QuotientGroup.quotientQuotientEquivQuotient`.

## Main results

* `SymplecticGeometry.FiberSum.instPathConnectedSpace`: the fibre sum is path connected.
* `SymplecticGeometry.FiberSum.fundamentalGroupMulEquiv` and
  `SymplecticGeometry.FiberSum.fundamentalGroupMulEquiv_mk`: the fundamental group of a fibre sum
  whose second piece has simply connected fibre complement, and its value on loops of the
  complement of the tube in `M₁`.
* `SymplecticGeometry.fibreSum_fundamentalGroupMulEquiv` and
  `SymplecticGeometry.fibreSum_fundamentalGroupMulEquiv_mk`: the case of the sum with the rational
  elliptic surface.
* `SymplecticGeometry.FiberSum.map_normalClosure_basepointChangeSubgroup_range_map_of_eq_comp`
  and `SymplecticGeometry.fibreSum_map_normalClosure_basepointChangeSubgroup_range_map_of_eq_comp`:
  the isomorphisms carry the normal closure of the image on `π₁` of a map into the complement of
  the tube, taken in `M₁`, onto that of the same map taken in the sum.
* `SymplecticGeometry.FiberSum.map_normalClosure_basepointChangeSubgroup_range_map` and
  `SymplecticGeometry.fibreSum_map_normalClosure_basepointChangeSubgroup_range_map`: the case of
  an embedding that misses the tube and the embedding carried to the sum.
* `SymplecticGeometry.exists_fundamentalGroup_mulEquiv_quotient_tori`: the sum with a copy of the
  rational elliptic surface along each of finitely many disjoint framed symplectic tori.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  Theorem 7.2.8 and Exercise 7.2.6.
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

/-- **Fundamental groups of maps carried to the fibre sum.** Let `φ : W → M₁ ∖ tube` be a
continuous map into the complement of the closed tube, `k : W → M₁` the map it gives into `M₁`
and `k' : W → FiberSum f₁ f₂ hδ hδε` the map it gives into the fibre sum through `inl`. Move the
image of `k_* π₁(W, x)` to `ι₁ q` along any path `γ`, and that of `k'_* π₁(W, x)` to the collar
point `f₁ (q, z)` along any path `η`, for `p = (q, z)`. Then `FiberSum.fundamentalGroupMulEquiv`,
after the quotient map, carries the normal closure of the first onto the normal closure of the
second. -/
theorem map_normalClosure_basepointChangeSubgroup_range_map_of_eq_comp {W : Type*}
    [TopologicalSpace W] (φ : C(W, f₁.complTube hδε)) {k : C(W, M₁)}
    {k' : C(W, FiberSum f₁ f₂ hδ hδε)}
    (hk : k = (ContinuousMap.subtypeVal (f₁.complTube hδε : Set M₁)).comp φ)
    (hk' : k' = (GluedAlong.inlContinuousMap (fiberSumGluing f₁ f₂ hδ hδε).toHomeomorph).comp φ)
    (p : Q × annulus ℂ δ ε) (x : W) (γ : Path (k x) (ι₁ p.1))
    (η : Path (k' x) (GluedAlong.inlContinuousMap _ (f₁.collarMap hδε p))) :
    (Subgroup.normalClosure (FundamentalGroup.basepointChangeSubgroup γ
        (FundamentalGroup.map k x).range : Set (FundamentalGroup M₁ (ι₁ p.1)))).map
        ((fundamentalGroupMulEquiv f₁ f₂ hδ hδε p).toMonoidHom.comp (QuotientGroup.mk' _)) =
      Subgroup.normalClosure (FundamentalGroup.basepointChangeSubgroup η
        (FundamentalGroup.map k' x).range) := by
  have := isPathConnected_iff_pathConnectedSpace.1 (f₁.isPathConnected_complTube hδ hδε)
  -- `L`: the image of `φ` on `π₁`, moved to the collar point in the complement
  obtain ⟨L, hL⟩ : ∃ L, L = FundamentalGroup.basepointChangeSubgroup
      (PathConnectedSpace.somePath _ (f₁.collarMap hδε p)) (FundamentalGroup.map φ x).range :=
    ⟨_, rfl⟩
  -- on the side of `M₁`, `γ` is moved on to the collar point along the radial path
  have hR : Subgroup.normalClosure (FundamentalGroup.basepointChangeSubgroup
      (γ.trans (f₁.collarRadialPath hδε p)) (FundamentalGroup.map k x).range :
        Set (FundamentalGroup M₁ (f₁.collarMap hδε p : M₁))) =
      Subgroup.normalClosure (SetLike.coe (L.map (FundamentalGroup.map
        (ContinuousMap.subtypeVal (f₁.complTube hδε : Set M₁)) (f₁.collarMap hδε p)))) := by
    rw [hL]
    exact FundamentalGroup.normalClosure_basepointChangeSubgroup_range_eq_of_eq_comp _ _ hk _ _
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
  rw [FundamentalGroup.normalClosure_basepointChangeSubgroup_range_eq_of_eq_comp _ _ hk' η
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
        (FundamentalGroup.map (inlEmbedding f₂ hδ ι hι).toContinuousMap q').range) :=
  -- both embeddings factor through the restriction of `ι` to the complement of the tube
  map_normalClosure_basepointChangeSubgroup_range_map_of_eq_comp f₁ f₂ hδ hδε
    (ι.codRestrict (f₁.complTube hδε) hι).toContinuousMap (k := ι.toContinuousMap)
    (k' := (inlEmbedding f₂ hδ ι hι).toContinuousMap)
    (ContinuousMap.ext fun q ↦ (ι.val_codRestrict_apply _ hι q).symm)
    (ContinuousMap.ext fun q ↦ congrFun (coe_inlEmbedding ι hι) q) p q' γ η

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

/-- The analogue of `FiberSum.map_normalClosure_basepointChangeSubgroup_range_map_of_eq_comp` for
the sum with the rational elliptic surface: for a continuous map `φ : W → X ∖ tube`, with `k` and
`k'` the maps it gives into `X` and into the sum, `fibreSum_fundamentalGroupMulEquiv`, after the
quotient map, carries the normal closure of `k_* π₁(W, x)` moved to `ι t` along any path `γ` onto
the normal closure of `k'_* π₁(W, x)` moved to the collar point `f₁ (t, z)` along any path `η`,
for `w = (t, z)`. -/
theorem fibreSum_map_normalClosure_basepointChangeSubgroup_range_map_of_eq_comp {W : Type*}
    [TopologicalSpace W] (φ : C(W, f₁.complTube hδε)) {k : C(W, X)}
    {k' : C(W, FiberSum f₁ f₂ hδ hδε)}
    (hk : k = (ContinuousMap.subtypeVal (f₁.complTube hδε : Set X)).comp φ)
    (hk' : k' = (GluedAlong.inlContinuousMap _).comp φ)
    (w : (∀ i, AddCircle (p i)) × annulus ℂ δ ε) (x : W) (γ : Path (k x) (ι w.1))
    (η : Path (k' x) (GluedAlong.inlContinuousMap _ (f₁.collarMap hδε w))) :
    (Subgroup.normalClosure (FundamentalGroup.basepointChangeSubgroup γ
        (FundamentalGroup.map k x).range : Set (FundamentalGroup X (ι w.1)))).map
        ((fibreSum_fundamentalGroupMulEquiv e p f₁ f₂ hδ hδε w).toMonoidHom.comp
          (QuotientGroup.mk' _)) =
      Subgroup.normalClosure (FundamentalGroup.basepointChangeSubgroup η
        (FundamentalGroup.map k' x).range) :=
  FiberSum.map_normalClosure_basepointChangeSubgroup_range_map_of_eq_comp f₁ f₂ hδ hδε φ hk hk'
    w x γ η

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

section Tori

/-! ### Sums along finitely many disjoint tori -/

universe u w

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  (e : (Fin 2 → ℂ) ≃L[ℝ] V) (p : Unit ⊕ Unit → ℝ) [∀ i, Fact (0 < p i)]

open FundamentalGroup in
/-- The step of the induction in `exists_fundamentalGroup_mulEquiv_quotient_tori`, on fundamental
groups. Sum `X` with the rational elliptic surface along the torus `ι none`, by product
neighbourhoods `f₁` and `f₂`, such that the other tori `ι (some k)` miss the closed tube. If a
group `G` is `π₁` of the sum, at the collar point over `ι none t`, modulo the normal closure of the
images of the carried tori, then `G` is `π₁(X, x)` modulo the normal closure of the images of all
the `ι k`. -/
private theorem nonempty_mulEquiv_quotient_of_fiberSum {κ : Type w} {X : Type u}
    [TopologicalSpace X] [ChartedSpace V X] [IsManifold 𝓘(ℝ, V) ∞ X] [T2Space X]
    [ConnectedSpace X] {σ : SmoothTwoForm 𝓘(ℝ, V) X} {hσ : σ.IsNondegenerate}
    (ι : Option κ → SmoothEmbedding (ModelWithCorners.pi fun _ : Unit ⊕ Unit ↦ 𝓘(ℝ)) 𝓘(ℝ, V) ∞
      (∀ i, AddCircle (p i)) X)
    {hι : hσ.HasSymplecticTangentImages (ModelWithCorners.pi fun _ : Unit ⊕ Unit ↦ 𝓘(ℝ))
      (ι none)}
    {hP : finrank ℝ ℂ = finrank ℝ V - finrank ℝ (Unit ⊕ Unit → ℝ)}
    {Φ : SymplecticFraming hι hP} {ε δ : ℝ} (f₁ : ProductNeighborhood Φ ε)
    (f₂ : ProductNeighborhood (rationalEllipticSurface.OnModel.torusFraming.{_, u} e p) ε)
    (hδ : 0 ≤ δ) (hδε : δ < ε) (hmem : ∀ k q, ι (some k) q ∈ f₁.complTube hδε)
    (t : ∀ i, AddCircle (p i)) (z₀ : annulus ℂ δ ε) (x : X) (ψ : ∀ k, Path (ι k t) x)
    {G : Type*} [Group G]
    (θ : G ≃* FundamentalGroup (FiberSum f₁ f₂ hδ hδε)
        (GluedAlong.inlContinuousMap _ (f₁.collarMap hδε (t, z₀))) ⧸
      Subgroup.normalClosure (⋃ k, (basepointChangeSubgroup (PathConnectedSpace.somePath _
        (GluedAlong.inlContinuousMap _ (f₁.collarMap hδε (t, z₀))))
        (map (FiberSum.inlEmbedding f₂ hδ (ι (some k)) (hmem k)).toContinuousMap t).range :
          Set (FundamentalGroup (FiberSum f₁ f₂ hδ hδε)
            (GluedAlong.inlContinuousMap _ (f₁.collarMap hδε (t, z₀))))))) :
    Nonempty (G ≃* FundamentalGroup X x ⧸ Subgroup.normalClosure
      (⋃ k, (basepointChangeSubgroup (ψ k) (map (ι k).toContinuousMap t).range :
        Set (FundamentalGroup X x)))) := by
  -- `φ`: the quotient map at `ι none t` followed by the isomorphism onto `π₁` of the sum
  let Ψ := fibreSum_fundamentalGroupMulEquiv e p f₁ f₂ hδ hδε (t, z₀)
  let φ := Ψ.toMonoidHom.comp (QuotientGroup.mk' _)
  let c := GluedAlong.inlContinuousMap (fiberSumGluing f₁ f₂ hδ hδε).toHomeomorph
    (f₁.collarMap hδε (t, z₀))
  -- the subgroup `K₀` at `ι none t` that corresponds to the one at `x`
  let ρ := ψ none
  let R : ∀ k, Subgroup (FundamentalGroup X (ι k t)) := fun k ↦
    (FundamentalGroup.map (ι k).toContinuousMap t).range
  let χ : ∀ k, Path (ι k t) (ι none t) := fun k ↦ (ψ k).trans ρ.symm
  let K₀ := Subgroup.normalClosure (⋃ k, (basepointChangeSubgroup (χ k) (R k) :
    Set (FundamentalGroup X (ι none t))))
  have hA : K₀.map (fundamentalGroupMulEquivOfPath ρ).toMonoidHom = Subgroup.normalClosure
      (⋃ k, (basepointChangeSubgroup (ψ k) (R k) : Set (FundamentalGroup X x))) := by
    rw [Subgroup.map_normalClosure _ _ (MulEquiv.surjective _), image_iUnion]
    refine Subgroup.normalClosure_iUnion_congr fun k ↦ ?_
    rw [← Subgroup.coe_map, ← basepointChangeSubgroup_eq_map, ← basepointChangeSubgroup_trans]
    exact normalClosure_basepointChangeSubgroup_eq _ _ _
  have hN₀ : Subgroup.normalClosure (basepointChangeSubgroup (χ none) (R none) :
      Set (FundamentalGroup X (ι none t))) =
        Subgroup.normalClosure (range (map (ι none).toContinuousMap t)) := by
    rw [normalClosure_basepointChangeSubgroup_eq (χ none) (Path.refl _),
      basepointChangeSubgroup_eq_map, fundamentalGroupMulEquivOfPath_refl]
    simp [R]
  have hφN₀ : (Subgroup.normalClosure (range (map (ι none).toContinuousMap t))).map φ = ⊥ :=
    (Subgroup.map_eq_bot_iff _).2 fun g hg ↦ by
      simpa [φ] using hg
  have hNK : Subgroup.normalClosure (range (map (ι none).toContinuousMap t)) ≤ K₀ :=
    hN₀ ▸ Subgroup.normalClosure_mono (subset_iUnion (fun k ↦
      (basepointChangeSubgroup (χ k) (R k) : Set (FundamentalGroup X (ι none t)))) none)
  have hφs : Function.Surjective φ := Ψ.surjective.comp (QuotientGroup.mk'_surjective _)
  let L := Subgroup.normalClosure (⋃ k, (basepointChangeSubgroup (PathConnectedSpace.somePath _ c)
    (map (FiberSum.inlEmbedding f₂ hδ (ι (some k)) (hmem k)).toContinuousMap t).range :
      Set (FundamentalGroup _ c)))
  -- `φ` carries `K₀` onto the subgroup of the sum that the induction hypothesis kills
  have hC : K₀.map φ = L := by
    rw [Subgroup.map_normalClosure _ _ hφs, iUnion_option, image_union,
      Subgroup.normalClosure_union, ← Subgroup.map_normalClosure _ _ hφs, hN₀, hφN₀, bot_sup_eq,
      image_iUnion]
    refine Subgroup.normalClosure_iUnion_congr fun k ↦ ?_
    rw [← Subgroup.map_normalClosure _ _ hφs]
    exact fibreSum_map_normalClosure_basepointChangeSubgroup_range_map e p f₁ f₂ hδ hδε
      (ι (some k)) (hmem k) (t, z₀) t (χ (some k)) _
  exact ⟨θ.trans ((QuotientGroup.congr _ L Ψ (by rw [Subgroup.map_map]; exact hC)).symm.trans
    ((QuotientGroup.quotientQuotientEquivQuotient _ K₀ hNK).trans
    (QuotientGroup.congr K₀ (Subgroup.normalClosure
      (⋃ k, (basepointChangeSubgroup (ψ k) (R k) : Set (FundamentalGroup X x))))
      (fundamentalGroupMulEquivOfPath ρ) hA)))⟩

/-- The conclusion of `exists_fundamentalGroup_mulEquiv_quotient_tori` for the tori indexed by
`κ`, for every compact symplectic `X` on the model `V` in `Type u`; its proof is an induction on
`κ`. -/
private def SumsAlongTori (κ : Type w) : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [ChartedSpace V X] [IsManifold 𝓘(ℝ, V) ∞ X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] {σ : SmoothTwoForm 𝓘(ℝ, V) X} (hσ : σ.IsSymplectic)
    (ι : κ → SmoothEmbedding (ModelWithCorners.pi fun _ : Unit ⊕ Unit ↦ 𝓘(ℝ)) 𝓘(ℝ, V) ∞
      (∀ i, AddCircle (p i)) X)
    (hι : ∀ k, hσ.isNondegenerate.HasSymplecticTangentImages
      (ModelWithCorners.pi fun _ : Unit ⊕ Unit ↦ 𝓘(ℝ)) (ι k)),
    (∀ k, SmoothForm.mpullback (ι k) (ι k).contMDiff σ = torusSymplecticForm p) →
    ∀ {hP : finrank ℝ ℂ = finrank ℝ V - finrank ℝ (Unit ⊕ Unit → ℝ)},
    (∀ k, SymplecticFraming (hι k) hP) →
    (Pairwise fun k l ↦ Disjoint (range (ι k)) (range (ι l))) →
    ∃ (Y : Type u) (_ : TopologicalSpace Y) (_ : ChartedSpace V Y)
      (_ : IsManifold 𝓘(ℝ, V) ∞ Y), T2Space Y ∧ CompactSpace Y ∧ ConnectedSpace Y ∧
      (∃ τ : SmoothTwoForm 𝓘(ℝ, V) Y, τ.IsSymplectic) ∧
      ∀ (t : ∀ i, AddCircle (p i)) (x : X) (y : Y) (ψ : ∀ k, Path (ι k t) x),
        Nonempty (FundamentalGroup Y y ≃* FundamentalGroup X x ⧸ Subgroup.normalClosure
          (⋃ k, (FundamentalGroup.basepointChangeSubgroup (ψ k)
            (FundamentalGroup.map (ι k).toContinuousMap t).range :
              Set (FundamentalGroup X x))))

private theorem sumsAlongTori_of_equiv {α β : Type w} (eqv : α ≃ β)
    (h : SumsAlongTori.{u} p α (V := V)) : SumsAlongTori.{u} p β (V := V) := by
  unfold SumsAlongTori at *
  intro X _ _ _ _ _ _ σ hσ ι hι hισ hP Φ hdisj
  obtain ⟨Y, _, _, _, h₁, h₂, h₃, h₄, hY⟩ := h X hσ (ι ∘ eqv) (fun k ↦ hι (eqv k))
    (fun k ↦ hισ (eqv k)) (fun k ↦ Φ (eqv k)) (hdisj.comp_of_injective eqv.injective)
  refine ⟨Y, _, _, _, h₁, h₂, h₃, h₄, fun t x y ψ ↦ ?_⟩
  obtain ⟨φ⟩ := hY t x y (fun k ↦ ψ (eqv k))
  refine ⟨φ.trans (QuotientGroup.quotientMulEquivOfEq (congrArg Subgroup.normalClosure ?_))⟩
  exact eqv.iSup_comp (g := fun k ↦ (FundamentalGroup.basepointChangeSubgroup (ψ k)
    (FundamentalGroup.map (ι k).toContinuousMap t).range : Set (FundamentalGroup X x)))

private theorem sumsAlongTori_empty : SumsAlongTori.{u} p PEmpty.{w + 1} (V := V) := by
  unfold SumsAlongTori at *
  intro X _ _ _ _ _ _ σ hσ ι _ _ _ _ _
  have := ChartedSpace.locallyPathConnectedSpace V X
  have : PathConnectedSpace X := pathConnectedSpace_iff_connectedSpace.2 inferInstance
  refine ⟨X, _, _, _, inferInstance, inferInstance, inferInstance, ⟨σ, hσ⟩, fun t x y ψ ↦ ?_⟩
  refine ⟨(FundamentalGroup.fundamentalGroupMulEquivOfPath (PathConnectedSpace.somePath y x)).trans
    ((QuotientGroup.quotientBot).symm.trans (QuotientGroup.quotientMulEquivOfEq ?_))⟩
  simp

include e in
open FundamentalGroup in
private theorem sumsAlongTori_option {κ : Type w} [Finite κ] (h : SumsAlongTori.{u} p κ (V := V)) :
    SumsAlongTori.{u} p (Option κ) (V := V) := by
  unfold SumsAlongTori at *
  intro X _ _ _ _ _ _ σ hσ ι hι hισ hP Φ hdisj
  have := ChartedSpace.locallyPathConnectedSpace V X
  have : PathConnectedSpace X := pathConnectedSpace_iff_connectedSpace.2 inferInstance
  -- product neighbourhoods of `ι none` inside the complement `U` of the other tori, and of the
  -- fibre torus of the rational elliptic surface, of one radius `ε`
  let U : Set X := (⋃ k, range (ι (some k)))ᶜ
  have hU : IsOpen U := (isClosed_iUnion_of_finite fun k ↦
    (isCompact_range (ι (some k)).contMDiff.continuous).isClosed).isOpen_compl
  have hιU : range (ι none) ⊆ U := fun x hx ↦ by
    simp only [U, mem_compl_iff, mem_iUnion, not_exists]
    exact fun k hk ↦ (hdisj (Option.some_ne_none k).symm).ne_of_mem hx hk rfl
  obtain ⟨ε₁, hε₁, hf₁⟩ := ProductNeighborhood.exists_range_subset hσ (Φ none) hU hιU
  obtain ⟨ε₂, hε₂, hf₂⟩ := ProductNeighborhood.exists
    (rationalEllipticSurface.OnModel.isSymplectic_symplecticForm.{_, u} e p)
    (rationalEllipticSurface.OnModel.torusFraming.{_, u} e p)
  let ε := min ε₁ ε₂
  have hε : 0 < ε := lt_min hε₁ hε₂
  obtain ⟨f₁, hf₁U⟩ := hf₁ ε (min_le_left _ _)
  obtain ⟨f₂⟩ := hf₂ ε (min_le_right _ _)
  have hδ : (0 : ℝ) ≤ ε / 2 := by positivity
  have hδε : ε / 2 < ε := half_lt_self hε
  have hσ₁₂ : SmoothForm.mpullback (ι none) (ι none).contMDiff σ =
      SmoothForm.mpullback _ (rationalEllipticSurface.OnModel.torusEmbedding.{_, u} e p).contMDiff
        (rationalEllipticSurface.OnModel.symplecticForm e p) :=
    (hισ none).trans
      (rationalEllipticSurface.OnModel.mpullback_torusEmbedding_symplecticForm e p).symm
  -- the sum `Y₁` of `X` with `E(1)` along `ι none`, and the other tori carried into it
  have hω := FiberSum.isSymplectic_symplecticForm (f₁ := f₁) (f₂ := f₂) (hδ := hδ)
    (hδε := hδε) hσ₁₂ hσ (rationalEllipticSurface.OnModel.isSymplectic_symplecticForm e p)
  have hmem (k : κ) (q : ∀ i, AddCircle (p i)) : ι (some k) q ∈ f₁.complTube hδε :=
    f₁.mem_complTube.2 fun hq ↦
      hf₁U (image_subset_range _ _ hq) (mem_iUnion.2 ⟨k, mem_range_self q⟩)
  let ι' := fun k ↦ FiberSum.inlEmbedding f₂ hδ (ι (some k)) (hmem k)
  have hι' (k : κ) : hω.isNondegenerate.HasSymplecticTangentImages
      (ModelWithCorners.pi fun _ : Unit ⊕ Unit ↦ 𝓘(ℝ)) (ι' k) :=
    (FiberSum.hasSymplecticTangentImages_inlEmbedding_iff (ι (some k)) (hmem k)
      hω.isNondegenerate).2 (hι (some k))
  have hισ' (k : κ) : SmoothForm.mpullback (ι' k) (ι' k).contMDiff
      (FiberSum.symplecticForm f₁ f₂ hδ hδε hσ₁₂) = torusSymplecticForm p :=
    (FiberSum.mpullback_inlEmbedding_symplecticForm (ι (some k)) (hmem k) hσ₁₂).trans
      (hισ (some k))
  have hdisj' : Pairwise fun k l ↦ Disjoint (range (ι' k)) (range (ι' l)) := fun k l hkl ↦ by
    refine disjoint_left.2 ?_
    rintro _ ⟨a, rfl⟩ ⟨b, hb⟩
    simp only [ι', FiberSum.inlEmbedding_apply] at hb
    exact disjoint_left.1 (hdisj ((Option.some_injective _).ne hkl)) ⟨a, rfl⟩
      ⟨b, congrArg Subtype.val ((GluedAlong.isOpenEmbedding_inl _).injective hb)⟩
  obtain ⟨Y, _, _, _, h₁, h₂, h₃, hτ, hY⟩ := h (FiberSum f₁ f₂ hδ hδε) hω ι' hι' hισ'
    (fun k ↦ FiberSum.inlEmbeddingFraming hω.isNondegenerate (Φ (some k))) hdisj'
  refine ⟨Y, _, _, _, h₁, h₂, h₃, hτ, fun t x y ψ ↦ ?_⟩
  -- the base point of the sum, on the collar over `ι none t`
  let z₀ : annulus ℂ (ε / 2) ε := ⟨((3 * ε / 4 : ℝ) : ℂ), mem_annulus.2 (by
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]; constructor <;> linarith)⟩
  obtain ⟨θ⟩ := hY t (GluedAlong.inlContinuousMap _ (f₁.collarMap hδε (t, z₀))) y
    fun k ↦ PathConnectedSpace.somePath _ _
  exact nonempty_mulEquiv_quotient_of_fiberSum e p ι f₁ f₂ hδ hδε hmem t z₀ x ψ θ

include e in
/-- **Summing with the rational elliptic surface along finitely many disjoint tori.** Let `X` be
a compact, connected, Hausdorff manifold modelled on a real space `V` isomorphic to `ℂ²`, with a
symplectic form `σ`, and let `ι k`, for `k` in a finite type `κ`, be pairwise disjoint embeddings
of the standard torus `T = ∀ i, AddCircle (p i)` with symplectic tangent images, which pull `σ`
back to `TauCeti.torusSymplecticForm p`, with symplectic framings. Then there is a compact,
connected, Hausdorff manifold `Y` on the same model and in the same universe as `X`, with a
symplectic form, such that for all points `x` of `X` and `y` of `Y`, a point `t` of `T` and paths
`ψ k` from `ι k t` to `x`, `π₁(Y, y)` is isomorphic to `π₁(X, x)` modulo the normal closure of the
images of the `(ι k)_* π₁(T, t)`, each moved to `x` along `ψ k`.

`Y` is the sum of `X` with a separate copy of the rational elliptic surface along each `ι k`
(`fibreSum_fundamentalGroupMulEquiv`). -/
theorem exists_fundamentalGroup_mulEquiv_quotient_tori (κ : Type w) [Finite κ]
    {X : Type u} [TopologicalSpace X] [ChartedSpace V X] [IsManifold 𝓘(ℝ, V) ∞ X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] {σ : SmoothTwoForm 𝓘(ℝ, V) X} (hσ : σ.IsSymplectic)
    (ι : κ → SmoothEmbedding (ModelWithCorners.pi fun _ : Unit ⊕ Unit ↦ 𝓘(ℝ)) 𝓘(ℝ, V) ∞
      (∀ i, AddCircle (p i)) X)
    (hι : ∀ k, hσ.isNondegenerate.HasSymplecticTangentImages
      (ModelWithCorners.pi fun _ : Unit ⊕ Unit ↦ 𝓘(ℝ)) (ι k))
    (hισ : ∀ k, SmoothForm.mpullback (ι k) (ι k).contMDiff σ = torusSymplecticForm p)
    {hP : finrank ℝ ℂ = finrank ℝ V - finrank ℝ (Unit ⊕ Unit → ℝ)}
    (Φ : ∀ k, SymplecticFraming (hι k) hP)
    (hdisj : Pairwise fun k l ↦ Disjoint (range (ι k)) (range (ι l))) :
    ∃ (Y : Type u) (_ : TopologicalSpace Y) (_ : ChartedSpace V Y)
      (_ : IsManifold 𝓘(ℝ, V) ∞ Y), T2Space Y ∧ CompactSpace Y ∧ ConnectedSpace Y ∧
      (∃ τ : SmoothTwoForm 𝓘(ℝ, V) Y, τ.IsSymplectic) ∧
      ∀ (t : ∀ i, AddCircle (p i)) (x : X) (y : Y) (ψ : ∀ k, Path (ι k t) x),
        Nonempty (FundamentalGroup Y y ≃* FundamentalGroup X x ⧸ Subgroup.normalClosure
          (⋃ k, (FundamentalGroup.basepointChangeSubgroup (ψ k)
            (FundamentalGroup.map (ι k).toContinuousMap t).range :
              Set (FundamentalGroup X x)))) :=
  Finite.induction_empty_option (P := SumsAlongTori.{u} p (V := V))
    (fun eqv h ↦ sumsAlongTori_of_equiv p eqv h) (sumsAlongTori_empty p)
    (fun h ↦ sumsAlongTori_option e p h) κ X hσ ι hι hισ Φ hdisj

end Tori

end SymplecticGeometry

end
