/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Boundary.Collar.Double.Height
public import SymplecticGeometry.Geometry.Manifold.Boundary.Collar.Double.Orientation
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.ChernNumber.Axioms
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.ChernNumber.Splitting
public import TauCeti.Geometry.Manifold.Instances.SymplecticGroup
public import SymplecticGeometry.Geometry.Manifold.Boundary.Collar.Double.Topology
import SymplecticGeometry.Geometry.Manifold.IsManifold.InteriorBoundary
import SymplecticGeometry.Geometry.Manifold.VectorBundle.Symplectic.Clutching
import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.Orientation.Smooth

/-!
# The clutched bundle over the double of a surface

Let `S` be a compact connected surface with nonempty boundary, modelled on the half-plane, `o` an
orientation of its interior and `c` a smooth collar of `∂S`. The double `c.Double` of `S` along
`c` (`Boundary/Collar/Double/Basic.lean`) is a closed connected surface, oriented by
`Double.orientation c o`, for which the first copy of the interior of `S` preserves orientation
from `o`. Its height function `Double.height c` splits it into the two copies of `S`:
`{height ≤ 0}` is the first copy, and the level set `{height = 0}` is `∂S`.

For a map `Ψ : ∂S → Sp(2k)`, smooth as a map into `Matrix.symplecticGroup κ ℝ`, this file glues
the trivial bundles with fibre `ℝ²ᵏ` over `U₁ = inl(int S) ∪ band` and `U₂ = inr(int S) ∪ band`
along `Ψ ∘ bandProj` on `U₁ ∩ U₂ = band`, where the band is the image of `(-1, 1) × ∂S` and
`bandProj` its projection onto `∂S` (`symplecticClutchingCore` of
`Symplectic/Clutching.lean`). The first Chern number of this bundle is the boundary Maslov index
of `Ψ` on `S`.

The proof applies the splitting formula `symplecticChernNumber_eq_boundaryMaslovIndex` to the
height function, with the two frames of the charts, which are symplectic over `U₁ ⊇ {height ≤ 0}`
and `U₂ ⊇ {height ≥ 0}` and differ by `Ψ ∘ bandProj`. This gives the boundary Maslov index of
`Ψ ∘ bandProj` on `{height ≤ 0}`, which is the boundary Maslov index of `Ψ` on `S` by the
invariance of boundary Maslov indices under homeomorphisms
(`boundaryMaslovIndex_comp_homeomorph`), along the homeomorphism `Double.homeomorphSublevel`
of `S` with `{height ≤ 0}`. There the orientations agree: the homological orientation of the
double pulls back along the first copy of the interior to that of `o`
(`TauCeti.Manifold.Orientation.comap_toHomologicalOrientation`).

## Main definitions

* `TauCeti.SmoothCollar.Double.sublevelBoundaryBandProj`: `bandProj` on the boundary of
  `{height ≤ 0}`.
* `SymplecticGeometry.ClosedConnectedOrientedSurface.double c o hS`: the double with the
  orientation `Double.orientation c o`, as a closed connected oriented surface.
* `SymplecticGeometry.Bundle.SymplecticSurfaceBundle.doubleClutching c o hS Ψ hΨ`: the
  symplectic bundle over the double clutched by `Ψ`, of complex rank `Fintype.card κ` and fibre
  `StdSpace κ` (`doubleClutching_n`, `doubleClutching_F`), with the frames of its two charts
  `doubleClutchingFrame`.

## Main results

* `TauCeti.Manifold.Orientation.boundaryMaslovIndex_eq_sublevelBoundaryMaslovIndex_height`: the
  boundary Maslov index of `Ψ` on `S` is that of `Ψ ∘ bandProj` on `{height ≤ 0}`.
* `SymplecticGeometry.Bundle.SymplecticSurfaceBundle.isSymplecticFrameOn_doubleClutchingFrame_true`,
  `isSymplecticFrameOn_doubleClutchingFrame_false`, `doubleClutchingFrame_false_apply`: the
  frames are symplectic over `U₁` and `U₂`, and differ by `Ψ ∘ bandProj`.
* `SymplecticGeometry.Bundle.SymplecticSurfaceBundle.symplecticChernNumber_doubleClutching`: the
  first Chern number of the clutched bundle is the boundary Maslov index of `Ψ`.

## Implementation notes

Tau Ceti's smooth structure on `Matrix.symplecticGroup κ ℝ` is stated for the topology
`Matrix.linftyOpTopologicalSpace` on matrices, which is not reducibly the default one, while
`C(∂S, GLSymplectic κ ℝ)` and the boundary Maslov index use the default topology. So the
smoothness hypothesis on `Ψ` sets the topology of the operator norm by `letI`, and only the
private construction of the bundle core makes it a local instance, with `Ψ` as a bare function.

The double as a closed surface is a `def`, not an `abbrev`: instance search then finds the
instances of a bundle over it as projections of the bundle. The instances of the fibres of
`doubleClutching` are those of the bundle core over `c.Double`, given explicitly.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.7
  (bundles over a surface clutched along a curve, and the first Chern number through a splitting).
* M. W. Hirsch, *Differential Topology*, Springer GTM 33, 1976, Chapter 8, §2 (gluing manifolds
  along boundaries by collars).
-/

public section

noncomputable section

open Set Function Topology Manifold TauCeti TauCeti.GLSymplectic SymplecticGeometry
open scoped Manifold ContDiff

namespace TauCeti.SmoothCollar.Double

variable {n : ℕ} {W : Type*} [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
  [IsManifold (𝓡∂ (n + 1)) ∞ W] (c : SmoothCollar n ∞ W)

/-! ### The projection of the band on the level set -/

variable [T2Space W] [CompactSpace ((𝓡∂ (n + 1)).boundary W)] [Nonempty ((𝓡∂ (n + 1)).boundary W)]

/-- The projection `bandProj` of the band onto `∂W`, on the boundary `{height = 0}` of the
sublevel set `{height ≤ 0}` of the double. -/
def sublevelBoundaryBandProj :
    C(sublevelBoundary (contMDiff_height c).continuous, (𝓡∂ (n + 1)).boundary W) where
  toFun z := bandProj c ((z : height c ⁻¹' Iic 0) : c.Double)
  continuous_toFun := (contMDiffOn_bandProj c).continuousOn.comp_continuous
    (continuous_subtypeVal.comp continuous_subtypeVal) fun z ↦
      image_mono (prod_mono (by simp) subset_rfl)
        ((preimage_height_zero c).subset (mem_sublevelBoundary_iff_eq_zero.1 z.property))

@[simp]
theorem sublevelBoundaryBandProj_apply (z : sublevelBoundary (contMDiff_height c).continuous) :
    sublevelBoundaryBandProj c z = bandProj c ((z : height c ⁻¹' Iic 0) : c.Double) :=
  (rfl)

end TauCeti.SmoothCollar.Double

/-! ### The boundary Maslov index on the first copy -/

namespace TauCeti.Manifold.Orientation

open SmoothCollar.Double

variable {S : Type} [TopologicalSpace S] [ChartedSpace (EuclideanHalfSpace 2) S]
  [IsManifold (𝓡∂ 2) ∞ S] [T2Space S] [CompactSpace S] [Nonempty ((𝓡∂ 2).boundary S)]
  (o : Manifold.Orientation (𝓡 2) ((𝓡∂ 2).interior S) (Fin 2))
  (c : SmoothCollar 1 ∞ S) {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- **The boundary Maslov index on the first copy of the double.** Let `S` be a compact surface
with nonempty boundary, `o` an orientation of its interior and `c` a smooth collar of `∂S`. For
every `Ψ : ∂S → Sp(2k)`, the boundary Maslov index of `Ψ` on `S` for `o` is the boundary Maslov
index of `Ψ ∘ bandProj` on the sublevel set `{height ≤ 0}` of the double of `S`, oriented by
`Double.orientation c o`. -/
theorem boundaryMaslovIndex_eq_sublevelBoundaryMaslovIndex_height
    (Ψ : C((𝓡∂ 2).boundary S, GLSymplectic κ ℝ)) :
    o.boundaryMaslovIndex Ψ =
      HomologicalOrientation.sublevelBoundaryMaslovIndex
        ((orientation c o).toHomologicalOrientation finrank_euclideanSpace_fin)
        finrank_euclideanSpace_fin (contMDiff_height c) (isRegularValue_height_zero c)
        (Ψ.comp (sublevelBoundaryBandProj c)) := by
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 := finrank_euclideanSpace_fin
  -- The first copy of the interior of `S` is the open set `{height < 0}`, and pulling the
  -- orientation of the double back along it gives `o`.
  let U : TopologicalSpace.Opens c.Double :=
    ⟨height c ⁻¹' Iio 0, isOpen_Iio.preimage (contMDiff_height c).continuous⟩
  let φ : (𝓡∂ 2).interior S ≃ₜ U :=
    (isOpenEmbedding_inlInterior c).isEmbedding.toHomeomorph.trans
      (Homeomorph.setCongr (preimage_height_Iio c).symm)
  have hφ (p : (𝓡∂ 2).interior S) :
      (φ p : c.Double) = inlInterior c p :=
    rfl
  have ho : (((orientation c o).toHomologicalOrientation hn).comap U.isOpenEmbedding').comap
      φ.isOpenEmbedding = o.toHomologicalOrientation hn :=
    (HomologicalOrientation.comap_comap_of_comp_eq _ U.isOpenEmbedding' φ.isOpenEmbedding
      (isOpenEmbedding_inlInterior c) (funext hφ)).trans
      (comap_toHomologicalOrientation hn (isOpenEmbedding_inlInterior c)
        (isOrientationPreservingAt_inlInterior c o))
  -- The homeomorphism of `S` with `{height ≤ 0}` maps `∂S` to the level set `{height = 0}`.
  let g : C(↥(range (Subtype.val : (𝓡∂ 2).interior S → S))ᶜ,
      sublevelBoundary (contMDiff_height c).continuous) :=
    ⟨fun z ↦ ⟨homeomorphSublevel c z, mem_sublevelBoundary_iff_eq_zero.2 <| by
        rw [coe_homeomorphSublevel, height_inl_eq_zero_iff]
        exact (𝓡∂ 2).compl_range_subtypeVal_interior.subset z.property⟩,
      ((homeomorphSublevel c).continuous.comp continuous_subtypeVal).subtype_mk _⟩
  -- On `∂S`, reading `Ψ` through `bandProj` gives `Ψ` back.
  have hΨ : Ψ.comp (.inclusion (𝓡∂ 2).compl_range_subtypeVal_interior.subset) =
      (Ψ.comp (sublevelBoundaryBandProj c)).comp g := by
    ext1 z
    simp only [ContinuousMap.comp_apply, sublevelBoundaryBandProj_apply]
    have hz : ((g z : height c ⁻¹' Iic 0) : c.Double) =
        bandMap c
          (0, ContinuousMap.inclusion (𝓡∂ 2).compl_range_subtypeVal_interior.subset z) :=
      (coe_homeomorphSublevel c _).trans (bandMap_zero c (ContinuousMap.inclusion _ z)).symm
    rw [hz, bandProj_bandMap c (by norm_num)]
  have := compactSpace_preimage_Iic (contMDiff_height c).continuous
  rw [boundaryMaslovIndex_def, ← ho, HomologicalOrientation.sublevelBoundaryMaslovIndex_def, hΨ]
  exact HomologicalOrientation.boundaryMaslovIndex_comp_homeomorph _ _ _ _ _ _ _ _
    (homeomorphSublevel c) φ
    (funext fun p ↦ Subtype.ext ((coe_homeomorphSublevel c _).trans (inlInterior_apply c p).symm))
    g (fun _ ↦ rfl) _

end TauCeti.Manifold.Orientation

/-! ### The double as a closed oriented surface, and the clutched bundle -/

namespace SymplecticGeometry

open SmoothCollar.Double Matrix
open scoped Matrix.Norms.Operator

variable {S : Type} [TopologicalSpace S] [ChartedSpace (EuclideanHalfSpace 2) S]
  [IsManifold (𝓡∂ 2) ∞ S] [T2Space S] [CompactSpace S] [ConnectedSpace S]
  (c : SmoothCollar 1 ∞ S)
  (o : Manifold.Orientation (𝓡 2) ((𝓡∂ 2).interior S) (Fin 2))
  (hS : ((𝓡∂ 2).boundary S).Nonempty)

/-- **The double of a surface as a closed connected oriented surface.** For a compact connected
surface `S` with nonempty boundary, an orientation `o` of its interior and a smooth collar `c` of
`∂S`: the double `c.Double`, oriented by `Double.orientation c o`. -/
@[expose]
def ClosedConnectedOrientedSurface.double : ClosedConnectedOrientedSurface :=
  haveI := hS.to_subtype
  { carrier := c.Double
    o := orientation c o }

/-- The orientation of the double is `Double.orientation c o`. -/
@[simp]
theorem ClosedConnectedOrientedSurface.double_o :
    (ClosedConnectedOrientedSurface.double c o hS).o = orientation c o :=
  (rfl)

namespace Bundle.SymplecticSurfaceBundle

variable {κ : Type} [Fintype κ] [DecidableEq κ]

section Core

attribute [local instance] Matrix.linftyOpTopologicalSpace

variable (Ψ : (𝓡∂ 2).boundary S → GLSymplectic κ ℝ)

/-- The clutching map `Ψ ∘ bandProj`, with values in the symplectic group. -/
private def clutchingMap (z : c.Double) : symplecticGroup κ ℝ :=
  haveI := hS.to_subtype
  (symplecticGroupContinuousMulEquiv κ ℝ).symm (Ψ (bandProj c z))

omit [IsManifold (𝓡∂ 2) ∞ S] [T2Space S] [CompactSpace S] [ConnectedSpace S] in
private theorem coe_clutchingMap (z : c.Double) :
    (clutchingMap c hS Ψ z : Matrix (κ ⊕ κ) (κ ⊕ κ) ℝ) =
      ((Ψ (haveI := hS.to_subtype; bandProj c z) : GL (κ ⊕ κ) ℝ) :
        Matrix (κ ⊕ κ) (κ ⊕ κ) ℝ) :=
  coe_symplecticGroupContinuousMulEquiv_symm κ ℝ _

omit [T2Space S] [CompactSpace S] [ConnectedSpace S] in
private theorem contMDiffOn_clutchingMap
    (hΨ : ContMDiff (𝓡 1) 𝓘(ℝ, Lie.SymplecticGroupModel κ ℝ) ∞
      fun x ↦ (symplecticGroupContinuousMulEquiv κ ℝ).symm (Ψ x)) :
    ContMDiffOn (𝓡 2) 𝓘(ℝ, Lie.SymplecticGroupModel κ ℝ) ∞ (clutchingMap c hS Ψ)
      ((range (inlInterior c) ∪ bandMap c '' (Ioo (-1) 1 ×ˢ univ)) ∩
        (range (inrInterior c) ∪ bandMap c '' (Ioo (-1) 1 ×ˢ univ))) :=
  haveI := hS.to_subtype
  hΨ.comp_contMDiffOn ((contMDiffOn_bandProj c).mono
    (range_inlInterior_union_bandMap_image_inter_range_inrInterior_union_bandMap_image c).subset)

/-- The vector bundle core clutched by `Ψ ∘ bandProj`. -/
private abbrev clutchingCore
    (hΨ : ContMDiff (𝓡 1) 𝓘(ℝ, Lie.SymplecticGroupModel κ ℝ) ∞
      fun x ↦ (symplecticGroupContinuousMulEquiv κ ℝ).symm (Ψ x)) :
    VectorBundleCore ℝ c.Double (StdSpace κ) Bool :=
  symplecticClutchingCore (IM := 𝓡 2) _ _ (clutchingMap c hS Ψ)
    (isOpen_range_inlInterior_union_bandMap_image c)
    (isOpen_range_inrInterior_union_bandMap_image c)
    (range_inlInterior_union_bandMap_image_union_range_inrInterior_union_bandMap_image c)
    (contMDiffOn_clutchingMap c hS Ψ hΨ)

end Core

/-- **The bundle over the double clutched by `Ψ`.** Let `S` be a compact connected surface with
nonempty boundary, `o` an orientation of its interior, `c` a smooth collar of `∂S`, and
`Ψ : ∂S → Sp(2k)` smooth as a map into `Matrix.symplecticGroup κ ℝ`. This is the symplectic
bundle over the double of `S` with fibre `ℝ²ᵏ` and two charts, over the first copy of the
interior of `S` with the band, and over the second copy with the band, whose coordinate change
from the second chart to the first is `Ψ ∘ bandProj`; the form is the standard one in either
chart. -/
def doubleClutching (Ψ : C((𝓡∂ 2).boundary S, GLSymplectic κ ℝ))
    (hΨ : letI := Matrix.linftyOpTopologicalSpace (κ ⊕ κ) (κ ⊕ κ) ℝ
      ContMDiff (𝓡 1) 𝓘(ℝ, Lie.SymplecticGroupModel κ ℝ) ∞
        fun x ↦ (symplecticGroupContinuousMulEquiv κ ℝ).symm (Ψ x)) :
    SymplecticSurfaceBundle (ClosedConnectedOrientedSurface.double c o hS) where
  n := Fintype.card κ
  F := StdSpace κ
  finrank_eq := by simp [two_mul]
  V := (clutchingCore c hS Ψ hΨ).Fiber
  -- Instance search does not see the base `c.Double` of the bundle core through the carrier of
  -- the bundled double, so the instances of the core are given here.
  addCommGroup (z : c.Double) :=
    (inferInstance : AddCommGroup ((clutchingCore c hS Ψ hΨ).Fiber z))
  module (z : c.Double) := (inferInstance : Module ℝ ((clutchingCore c hS Ψ hΨ).Fiber z))
  topologicalSpaceFiber (z : c.Double) :=
    (inferInstance : TopologicalSpace ((clutchingCore c hS Ψ hΨ).Fiber z))
  isTopologicalAddGroup (z : c.Double) :=
    (inferInstance : IsTopologicalAddGroup ((clutchingCore c hS Ψ hΨ).Fiber z))
  continuousSMul (z : c.Double) :=
    (inferInstance : ContinuousSMul ℝ ((clutchingCore c hS Ψ hΨ).Fiber z))
  topologicalSpaceTotalSpace := (inferInstance :
    TopologicalSpace (_root_.Bundle.TotalSpace (StdSpace κ) (clutchingCore c hS Ψ hΨ).Fiber))
  fiberBundle := (inferInstance : FiberBundle (StdSpace κ) (clutchingCore c hS Ψ hΨ).Fiber)
  vectorBundle :=
    (inferInstance : VectorBundle ℝ (StdSpace κ) (clutchingCore c hS Ψ hΨ).Fiber)
  contMDiffVectorBundle :=
    (inferInstance : ContMDiffVectorBundle ∞ (StdSpace κ) (clutchingCore c hS Ψ hΨ).Fiber (𝓡 2))
  form := symplecticClutchingForm _ _ (clutchingMap c hS Ψ)
    (isOpen_range_inlInterior_union_bandMap_image c)
    (isOpen_range_inrInterior_union_bandMap_image c)
    (range_inlInterior_union_bandMap_image_union_range_inrInterior_union_bandMap_image c)
    (contMDiffOn_clutchingMap c hS Ψ hΨ) ⊤
  isNondegenerate := isNondegenerate_symplecticClutchingForm _ _ _ _ _ _ _ _

variable (Ψ : C((𝓡∂ 2).boundary S, GLSymplectic κ ℝ))
  (hΨ : letI := Matrix.linftyOpTopologicalSpace (κ ⊕ κ) (κ ⊕ κ) ℝ
    ContMDiff (𝓡 1) 𝓘(ℝ, Lie.SymplecticGroupModel κ ℝ) ∞
      fun x ↦ (symplecticGroupContinuousMulEquiv κ ℝ).symm (Ψ x))

/-- The clutched bundle has complex rank `Fintype.card κ`. -/
@[simp]
theorem doubleClutching_n : (doubleClutching c o hS Ψ hΨ).n = Fintype.card κ :=
  (rfl)

/-- The model fibre of the clutched bundle is `StdSpace κ`. -/
theorem doubleClutching_F : (doubleClutching c o hS Ψ hΨ).F = StdSpace κ :=
  (rfl)

/-- **The frames of the charts of the clutched bundle.** The frame `true` is a symplectic frame
over the first copy of the interior of `S` and the band
(`isSymplecticFrameOn_doubleClutchingFrame_true`), the frame `false` over the second copy and the
band (`isSymplecticFrameOn_doubleClutchingFrame_false`), and they differ by `Ψ ∘ bandProj`
(`doubleClutchingFrame_false_apply`). -/
def doubleClutchingFrame (b : Bool) (z : ClosedConnectedOrientedSurface.double c o hS) :
    StdSpace κ ≃L[ℝ] (doubleClutching c o hS Ψ hΨ).V z :=
  symplecticClutchingFrame _ _ (clutchingMap c hS Ψ)
    (isOpen_range_inlInterior_union_bandMap_image c)
    (isOpen_range_inrInterior_union_bandMap_image c)
    (range_inlInterior_union_bandMap_image_union_range_inrInterior_union_bandMap_image c)
    (contMDiffOn_clutchingMap c hS Ψ hΨ) b z

/-- The frame `true` of the clutched bundle is a symplectic frame over the first copy of the
interior of `S` and the band. -/
theorem isSymplecticFrameOn_doubleClutchingFrame_true :
    (doubleClutching c o hS Ψ hΨ).form.IsSymplecticFrameOn (stdForm κ)
      (range (inlInterior c) ∪ bandMap c '' (Ioo (-1) 1 ×ˢ univ))
      (doubleClutchingFrame c o hS Ψ hΨ true) :=
  (isSymplecticFrameOn_symplecticClutchingFrame _ _ _ _ _ _ _ ⊤ true).mono
    (baseSet_twoChartCore_true _ _ _ _ _ _ _ _).symm.subset

/-- The frame `false` of the clutched bundle is a symplectic frame over the second copy of the
interior of `S` and the band. -/
theorem isSymplecticFrameOn_doubleClutchingFrame_false :
    (doubleClutching c o hS Ψ hΨ).form.IsSymplecticFrameOn (stdForm κ)
      (range (inrInterior c) ∪ bandMap c '' (Ioo (-1) 1 ×ˢ univ))
      (doubleClutchingFrame c o hS Ψ hΨ false) :=
  (isSymplecticFrameOn_symplecticClutchingFrame _ _ _ _ _ _ _ ⊤ false).mono
    (baseSet_twoChartCore_false _ _ _ _ _ _ _ _).symm.subset

/-- **The two frames of the clutched bundle differ by `Ψ ∘ bandProj`**: at every point `z` of the
double, the frame `false` at `v` is the frame `true` at `Ψ (bandProj c z) v`. -/
theorem doubleClutchingFrame_false_apply (z : ClosedConnectedOrientedSurface.double c o hS)
    (v : StdSpace κ) :
    doubleClutchingFrame c o hS Ψ hΨ false z v =
      doubleClutchingFrame c o hS Ψ hΨ true z
        (toEuclideanLin ((Ψ (haveI := hS.to_subtype; bandProj c z) : GL (κ ⊕ κ) ℝ) :
          Matrix (κ ⊕ κ) (κ ⊕ κ) ℝ) v) := by
  have := hS.to_subtype
  -- `z` is a point of the bundled double, so the matrix is rewritten apart from the frames.
  have hT : toEuclideanCLM (𝕜 := ℝ) (clutchingMap c hS Ψ z : Matrix (κ ⊕ κ) (κ ⊕ κ) ℝ) v =
      toEuclideanLin ((Ψ (bandProj c z) : GL (κ ⊕ κ) ℝ) : Matrix (κ ⊕ κ) (κ ⊕ κ) ℝ) v := by
    rw [toEuclideanCLM_apply]
    exact congrArg (fun A ↦ toEuclideanLin A v) (coe_clutchingMap c hS Ψ z)
  exact (symplecticClutchingFrame_false_apply _ _ (clutchingMap c hS Ψ)
    (isOpen_range_inlInterior_union_bandMap_image c)
    (isOpen_range_inrInterior_union_bandMap_image c)
    (range_inlInterior_union_bandMap_image_union_range_inrInterior_union_bandMap_image c)
    (contMDiffOn_clutchingMap c hS Ψ hΨ) z v).trans
    (congrArg _ hT)

/-- **The first Chern number of the clutched bundle.** Let `S` be a compact connected surface
with nonempty boundary, `o` an orientation of its interior, `c` a smooth collar of `∂S`, and
`Ψ : ∂S → Sp(2k)` smooth. The first Chern number of the bundle over the double of `S` clutched
by `Ψ` is the boundary Maslov index of `Ψ` on `S` for `o`. -/
theorem symplecticChernNumber_doubleClutching :
    (doubleClutching c o hS Ψ hΨ).symplecticChernNumber = o.boundaryMaslovIndex Ψ := by
  have := hS.to_subtype
  have h₁ := isSymplecticFrameOn_doubleClutchingFrame_true c o hS Ψ hΨ
  have h₂ := isSymplecticFrameOn_doubleClutchingFrame_false c o hS Ψ hΨ
  have : Fact (Module.finrank ℝ (StdSpace κ) =
      2 * Module.finrank ℂ (Fin (doubleClutching c o hS Ψ hΨ).n → ℂ)) :=
    (doubleClutching c o hS Ψ hΨ).fact_finrank_eq
  rw [o.boundaryMaslovIndex_eq_sublevelBoundaryMaslovIndex_height c, symplecticChernNumber_def]
  -- The splitting formula along the height function, with the frames of the two charts.
  exact Bundle.symplecticChernNumber_eq_boundaryMaslovIndex
    (Fin (doubleClutching c o hS Ψ hΨ).n → ℂ) (M := ClosedConnectedOrientedSurface.double c o hS)
    (σ := (doubleClutching c o hS Ψ hΨ).form) _
    finrank_euclideanSpace_fin (contMDiff_height c) (isRegularValue_height_zero c)
    (Φ₁ := fun x ↦ doubleClutchingFrame c o hS Ψ hΨ true x.val)
    (h₁.contMDiffOn.continuousOn.comp_continuous (continuous_subtypeVal.prodMap continuous_id)
      fun q ↦ ⟨preimage_height_Iic_subset_range_inlInterior_union_bandMap_image c
        q.1.property, mem_univ _⟩)
    (fun x ↦ h₁.map_bilinFormAt x.val
      (preimage_height_Iic_subset_range_inlInterior_union_bandMap_image c x.property))
    (Φ₂ := fun x ↦ doubleClutchingFrame c o hS Ψ hΨ false x.val)
    (h₂.contMDiffOn.continuousOn.comp_continuous (continuous_subtypeVal.prodMap continuous_id)
      fun q ↦ ⟨preimage_height_Ici_subset_range_inrInterior_union_bandMap_image c
        q.1.property, mem_univ _⟩)
    (fun x ↦ h₂.map_bilinFormAt x.val
      (preimage_height_Ici_subset_range_inrInterior_union_bandMap_image c x.property)) _
    fun z v ↦ doubleClutchingFrame_false_apply c o hS Ψ hΨ _ v

end Bundle.SymplecticSurfaceBundle

end SymplecticGeometry

end
