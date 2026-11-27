/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import SymplecticGeometry.Geometry.Symplectic.Sum.Fibre
import Mathlib.Analysis.Convex.Contractible
import SymplecticGeometry.AlgebraicTopology.FundamentalGroup.Prod.Basic
import SymplecticGeometry.AlgebraicTopology.FundamentalGroup.VanKampen
import SymplecticGeometry.Topology.Connected.Clopen
import SymplecticGeometry.Topology.Homotopy.Annulus
import TauCeti.AlgebraicTopology.FundamentalGroup.BasepointChange
import TauCeti.AlgebraicTopology.FundamentalGroup.Basic
import TauCeti.AlgebraicTopology.FundamentalGroup.HomotopyEquiv
import TauCeti.AlgebraicTopology.FundamentalGroup.Homeomorph
import TauCeti.AlgebraicTopology.FundamentalGroup.VanKampen.Basic
import TauCeti.Geometry.Manifold.Topology

/-!
# The complement of the closed tube of a product neighbourhood

Let `f : Q × B²(ε) → M` be a product neighbourhood of an embedding `ι` of a compact, path
connected manifold `Q` into a connected Hausdorff manifold `M`, and let `0 ≤ δ < ε`. This file
shows that the complement `ProductNeighborhood.complTube` of the closed tube `f (Q × B̄²(δ))` is
path connected, and that its inclusion into the complement of `ι (Q) = f (Q × {0})` induces a
bijection of fundamental groups. So the complement of the tube is simply connected when the
complement of `ι (Q)` is.

Both are proved with the open sets `f (Q × A(a, ε))`, the images of the products of `Q` with the
open annuli `a < |z| < ε`. The complement of the tube and the range of `f` cover `M` and meet in
the collar `f (Q × A(δ, ε))`, which is path connected; so the complement of the tube is path
connected, as `M` is connected (`IsPreconnected.of_isOpen_of_union_eq_univ`). For the
fundamental groups, the complement of the tube and `f (Q × A(0, ε))` cover the complement of
`ι (Q)`, again with the collar as overlap, and van Kampen
(`TauCeti.isPushout_fundamentalGroup_union`) applies: the inclusion of the collar into
`f (Q × A(0, ε))` is, through `f`, the product of `Q` with the inclusion of an annulus into the
punctured disc, a homotopy equivalence (`SymplecticGeometry.annulusHomotopyEquiv`). The leg of a
pushout opposite an isomorphism is an isomorphism. The argument follows the proof of
`Topology.IsOpenEmbedding.isPathConnected_compl_image` in
`AlgebraicTopology/FundamentalGroup/Prod/ComplDisc.lean` for path connectedness.

The same cover of `M` by the complement of the tube and the range of `f` describes `π₁(M)` from
the complement of the tube. Through `f`, the inclusion of the collar into the range of `f` is the
product of `Q` with the inclusion of an annulus into a disc, which is surjective on fundamental
groups as the disc is simply connected (`FundamentalGroup.map_id_prodMap_surjective`). Van Kampen
with a surjective leg (`FundamentalGroup.map_subtypeVal_surjective_of_map_inclusion_surjective`
and `FundamentalGroup.ker_map_subtypeVal_eq_normalClosure_image`) then shows that the inclusion of
the complement of the tube into `M` is onto on fundamental groups, with kernel inside the normal
closure of the image of the collar's group; and the image of `π₁(range f)` in `π₁(M)` is that of
the collar's group. Dividing by these normal closures gives an isomorphism of quotients. The
transport along `f` follows the proof of `FundamentalGroup.map_subtypeVal_compl_image_surjective`
in `AlgebraicTopology/FundamentalGroup/Prod/ComplDisc.lean`.

## Main results

* `SymplecticGeometry.ProductNeighborhood.isPathConnected_complTube`: the complement of the
  closed tube is path connected.
* `SymplecticGeometry.ProductNeighborhood.complTube_subset_compl_range`: it lies in the
  complement of `ι (Q)`.
* `SymplecticGeometry.ProductNeighborhood.map_inclusion_complTube_bijective`: the inclusion into
  the complement of `ι (Q)` induces a bijection of fundamental groups at every point.
* `SymplecticGeometry.ProductNeighborhood.simplyConnectedSpace_complTube`: the complement of the
  closed tube is simply connected if the complement of `ι (Q)` is.
* `SymplecticGeometry.ProductNeighborhood.map_subtypeVal_complTube_surjective`: the inclusion of
  the complement of the closed tube into `M` induces a surjection of fundamental groups at the
  points of the collar.
* `SymplecticGeometry.ProductNeighborhood.ker_mk_comp_map_subtypeVal_complTube`: modulo the
  normal closure `tubeSubgroup` of the image of `π₁(range f)`, its kernel is the normal closure
  `collarSubgroup` of the image of the collar's fundamental group.
* `SymplecticGeometry.ProductNeighborhood.complTubeQuotientMulEquiv`: the resulting isomorphism
  of quotients, with its value `complTubeQuotientMulEquiv_mk` on classes of loops.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Cambridge University Press, 2002, Theorem 1.20.
* [R. E. Gompf, *A new construction of symplectic manifolds*][Gompf1995]
-/

public section

open Module Set Topology TauCeti
open scoped ContDiff Manifold

namespace SymplecticGeometry.ProductNeighborhood

variable {EQ HQ E H : Type*}
  [NormedAddCommGroup EQ] [NormedSpace ℝ EQ] [FiniteDimensional ℝ EQ] [TopologicalSpace HQ]
  {J : ModelWithCorners ℝ EQ HQ} {Q : Type*} [TopologicalSpace Q] [ChartedSpace HQ Q]
  [IsManifold J ∞ Q]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {σ : SmoothTwoForm I M} {hσ : σ.IsNondegenerate} {ι : SmoothEmbedding J I ∞ Q M}
  {hι : hσ.HasSymplecticTangentImages J ι} {hP : finrank ℝ ℂ = finrank ℝ E - finrank ℝ EQ}
  {Φ : SymplecticFraming hι hP} {ε δ : ℝ} (f : ProductNeighborhood Φ ε)

variable [CompactSpace Q] [T2Space M]

/-- A point `f p` of the range of a product neighbourhood lies outside the closed tube of radius
`δ` exactly when `δ < |p.2|`. -/
theorem apply_mem_complTube_iff (hδε : δ < ε) {p : prodBall Q ε} :
    f p ∈ f.complTube hδε ↔ δ < ‖(p : Q × ℂ).2‖ := by
  rw [mem_complTube, not_iff_comm, not_lt]
  refine ⟨fun h ↦ ⟨p, h, rfl⟩, ?_⟩
  rintro ⟨p', hp', hpp'⟩
  rwa [← f.isOpenEmbedding.injective hpp']

/-- The complement of the closed tube meets the range of a product neighbourhood in the collar
`f (Q × A(δ, ε))`. -/
theorem complTube_inter_range (hδε : δ < ε) :
    (f.complTube hδε : Set M) ∩ range f =
      range (f ∘ annulusToProdBall : Q × annulus ℂ δ ε → M) := by
  ext x
  refine ⟨?_, ?_⟩
  · rintro ⟨hx, p, rfl⟩
    exact f.apply_mem_range_comp_annulusToProdBall_iff.2 ((f.apply_mem_complTube_iff hδε).1 hx)
  · rintro ⟨p, rfl⟩
    exact ⟨f.apply_annulusToProdBall_mem_complTube hδε p, mem_range_self _⟩

/-- For `0 ≤ δ`, the complement of the closed tube meets `f (Q × A(0, ε))` in the collar
`f (Q × A(δ, ε))`. -/
theorem complTube_inter_range_comp_annulusToProdBall_zero (hδ : 0 ≤ δ) (hδε : δ < ε) :
    (f.complTube hδε : Set M) ∩ range (f ∘ annulusToProdBall : Q × annulus ℂ 0 ε → M) =
      range (f ∘ annulusToProdBall : Q × annulus ℂ δ ε → M) := by
  rw [← f.complTube_inter_range hδε]
  refine subset_antisymm (inter_subset_inter_right _ (range_comp_subset_range _ _)) ?_
  rintro x ⟨hx, p, rfl⟩
  exact ⟨hx, f.apply_mem_range_comp_annulusToProdBall_iff.2
    (hδ.trans_lt ((f.apply_mem_complTube_iff hδε).1 hx))⟩

/-- For `0 ≤ δ`, the complement of `ι (Q)` is the union of the complement of the closed tube and
of `f (Q × A(0, ε))`. -/
theorem compl_range_eq_complTube_union (hδ : 0 ≤ δ) (hδε : δ < ε) :
    (range ι)ᶜ =
      (f.complTube hδε : Set M) ∪ range (f ∘ annulusToProdBall : Q × annulus ℂ 0 ε → M) := by
  ext x
  by_cases hx : x ∈ range f
  · obtain ⟨p, rfl⟩ := hx
    rw [mem_compl_iff, mem_union, SetLike.mem_coe, f.apply_mem_range_embedding_iff,
      f.apply_mem_complTube_iff, f.apply_mem_range_comp_annulusToProdBall_iff, norm_pos_iff]
    exact ⟨fun h ↦ .inr h, fun h ↦ h.elim (fun h' ↦ norm_pos_iff.1 (hδ.trans_lt h')) id⟩
  · refine iff_of_true (fun ⟨q, hq⟩ ↦ hx ?_) (.inl (f.mem_complTube.2 fun ⟨p, _, hp⟩ ↦ hx ⟨p, hp⟩))
    have hq0 : (q, (0 : ℂ)) ∈ prodBall Q ε := mem_prodBall.2 (by simpa using hδ.trans_lt hδε)
    exact ⟨_, (f.apply_mk_zero q hq0).trans hq⟩

/-- For `0 ≤ δ`, the complement of the closed tube lies in the complement of `ι (Q)`. -/
theorem complTube_subset_compl_range (hδ : 0 ≤ δ) (hδε : δ < ε) :
    (f.complTube hδε : Set M) ⊆ (range ι)ᶜ :=
  (f.compl_range_eq_complTube_union hδ hδε).symm ▸ subset_union_left

/-- The complement of the closed tube and the range of a product neighbourhood cover `M`. -/
theorem complTube_union_range (hδε : δ < ε) : (f.complTube hδε : Set M) ∪ range f = univ := by
  rw [← compl_subset_iff_union]
  intro x hx
  rw [mem_compl_iff, SetLike.mem_coe, mem_complTube, not_not] at hx
  obtain ⟨p, -, rfl⟩ := hx
  exact mem_range_self p

/-- The interiors of the complement of the closed tube and of the range of a product neighbourhood
cover `M`. -/
theorem interior_complTube_union_interior_range (hδε : δ < ε) :
    interior (f.complTube hδε : Set M) ∪ interior (range f) = univ := by
  rw [(f.complTube hδε).isOpen.interior_eq, f.isOpen_range.interior_eq, f.complTube_union_range hδε]

variable [PathConnectedSpace Q]

/-- The complement in a connected manifold of the closed tube `f (Q × B̄²(δ))`, `0 ≤ δ < ε`, of a
product neighbourhood of a path connected `Q` is path connected. -/
theorem isPathConnected_complTube [ConnectedSpace M] (hδ : 0 ≤ δ) (hδε : δ < ε) :
    IsPathConnected (f.complTube hδε : Set M) := by
  have hAB := f.complTube_inter_range hδε ▸ f.isPathConnected_range_comp_annulusToProdBall hδ hδε
  have : LocallyPathConnectedSpace M := I.locallyPathConnectedSpace_of_chartedSpace M
  refine ((f.complTube hδε).isOpen.isConnected_iff_isPathConnected).1
    ⟨hAB.nonempty.mono inter_subset_left, hAB.isConnected.isPreconnected.of_isOpen_of_union_eq_univ
      hAB.nonempty (f.complTube hδε).isOpen f.isOpen_range (f.complTube_union_range hδε)⟩

omit [PathConnectedSpace Q] in
/-- The inclusion of the collar `f (Q × A(δ, ε))`, as the intersection of the complement of the
tube with `f (Q × A(0, ε))`, into `f (Q × A(0, ε))` induces a bijection of fundamental groups:
through `f` it is the product of `Q` with a homotopy equivalence of annuli. -/
private theorem map_inclusion_collar_bijective (hδ : 0 ≤ δ) (hδε : δ < ε)
    (x : ↥((f.complTube hδε : Set M) ∩
      range (f ∘ annulusToProdBall : Q × annulus ℂ 0 ε → M))) :
    Function.Bijective (FundamentalGroup.map (ContinuousMap.inclusion inter_subset_right) x) := by
  let e₀ := (f.isOpenEmbedding_comp_annulusToProdBall 0).isEmbedding.toHomeomorph
  let e := (f.isOpenEmbedding_comp_annulusToProdBall δ).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (f.complTube_inter_range_comp_annulusToProdBall_zero hδ hδε).symm)
  let H := e.symm.toHomotopyEquiv.trans
    (((ContinuousMap.HomotopyEquiv.refl Q).prodCongr
      (annulusHomotopyEquiv le_rfl hδ hδε)).trans e₀.toHomotopyEquiv)
  have hH : H.toFun = ContinuousMap.inclusion inter_subset_right := by
    ext y
    obtain ⟨w, rfl⟩ := e.surjective y
    simp only [H, ContinuousMap.HomotopyEquiv.trans_apply, Homeomorph.coe_toHomotopyEquiv,
      Homeomorph.symm_apply_apply]
    have hP : ((ContinuousMap.HomotopyEquiv.refl Q).prodCongr
        (annulusHomotopyEquiv (E := ℂ) le_rfl hδ hδε)).toFun =
        (ContinuousMap.id Q).prodMap (annulusHomotopyEquiv (E := ℂ) le_rfl hδ hδε).toFun := rfl
    rw [hP, annulusHomotopyEquiv_toFun]
    simp only [e₀, e, Homeomorph.trans_apply]
    -- `Homeomorph.setCongr` and `IsEmbedding.toHomeomorph` do not move the point in `M`
    change f (annulusToProdBall _) = f (annulusToProdBall w)
    exact congrArg f (Subtype.ext (by simpa using ContinuousMap.inclusion_apply_coe _ w.2))
  rw [← hH]
  exact H.fundamentalGroup_map_bijective x

variable [ConnectedSpace M]

/-- **The complement of the closed tube has the fundamental group of the complement of the core.**
For a product neighbourhood `f` of an embedding `ι` of a compact, path connected `Q` into a
connected Hausdorff manifold `M`, and `0 ≤ δ < ε`, the inclusion of the complement of the closed
tube `f (Q × B̄²(δ))` into the complement of `ι (Q)` induces a bijection of fundamental groups at
every point. -/
theorem map_inclusion_complTube_bijective (hδ : 0 ≤ δ) (hδε : δ < ε) (x : f.complTube hδε) :
    Function.Bijective (FundamentalGroup.map
      (ContinuousMap.inclusion (f.complTube_subset_compl_range hδ hδε)) x) := by
  have hAB := f.complTube_inter_range_comp_annulusToProdBall_zero hδ hδε
  have hABc := hAB ▸ f.isPathConnected_range_comp_annulusToProdBall hδ hδε
  obtain ⟨y, hy⟩ := hABc.nonempty
  have hP := TauCeti.isPushout_fundamentalGroup_union (f.compl_range_eq_complTube_union hδ hδε)
    (f.complTube hδε).isOpen (f.isOpenEmbedding_comp_annulusToProdBall 0).isOpen_range
    (f.isPathConnected_complTube hδ hδε)
    (f.isPathConnected_range_comp_annulusToProdBall le_rfl (hδ.trans_lt hδε)) hABc y hy.1 hy.2
  have : CategoryTheory.IsIso (GrpCat.ofHom (FundamentalGroup.map
      (ContinuousMap.inclusion inter_subset_right) (⟨y, hy⟩ : ↥((f.complTube hδε : Set M) ∩
        range (f ∘ annulusToProdBall : Q × annulus ℂ 0 ε → M))))) :=
    (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).2
      (f.map_inclusion_collar_bijective hδ hδε ⟨y, hy⟩)
  have hy' := (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).1 hP.isIso_inl_of_isIso
  have : PathConnectedSpace (f.complTube hδε : Set M) :=
    isPathConnected_iff_pathConnectedSpace.1 (f.isPathConnected_complTube hδ hδε)
  exact FundamentalGroup.map_bijective_of_path _ (PathConnectedSpace.somePath _ x) hy'

/-- For a product neighbourhood `f` of an embedding `ι` of a compact, path connected `Q` into a
connected Hausdorff manifold `M`, and `0 ≤ δ < ε`, the complement of the closed tube
`f (Q × B̄²(δ))` is simply connected if the complement of `ι (Q)` is. -/
theorem simplyConnectedSpace_complTube [SimplyConnectedSpace ↥(range ι)ᶜ] (hδ : 0 ≤ δ)
    (hδε : δ < ε) : SimplyConnectedSpace (f.complTube hδε) := by
  have : PathConnectedSpace (f.complTube hδε : Set M) :=
    isPathConnected_iff_pathConnectedSpace.1 (f.isPathConnected_complTube hδ hδε)
  let x : (f.complTube hδε : Set M) := Classical.arbitrary _
  have := (f.map_inclusion_complTube_bijective hδ hδε x).1.subsingleton
  exact TauCeti.simplyConnectedSpace_of_subsingleton_fundamentalGroup x

/-! ### The fundamental group of `M` modulo the range of the tube -/

omit [PathConnectedSpace Q] [ConnectedSpace M] in
/-- A point of the complement of the closed tube lies in the collar exactly when it lies in the
range of the product neighbourhood. -/
theorem mem_collar_iff_coe_mem_range {hδε : δ < ε} {x : f.complTube hδε} :
    x ∈ f.collar hδε ↔ (x : M) ∈ range f := by
  rw [mem_collar_iff]
  refine ⟨fun ⟨p, hp⟩ ↦ ⟨annulusToProdBall p, (f.coe_collarMap hδε p).symm.trans
    (congrArg Subtype.val hp)⟩, fun hx ↦ ?_⟩
  obtain ⟨p, hp⟩ : (x : M) ∈ range (f ∘ annulusToProdBall : Q × annulus ℂ δ ε → M) :=
    f.complTube_inter_range hδε ▸ ⟨x.property, hx⟩
  exact ⟨p, Subtype.ext ((f.coe_collarMap hδε p).trans hp)⟩

omit [PathConnectedSpace Q] [ConnectedSpace M] in
/-- The inclusion of the collar `f (Q × A(δ, ε))`, as the intersection of the complement of the
tube with the range of `f`, into the range of `f` induces a surjection of fundamental groups:
through `f` it is the product of `Q` with the inclusion of an annulus into a disc. -/
theorem map_inclusion_inter_range_surjective (hδε : δ < ε)
    (y : ↥((f.complTube hδε : Set M) ∩ range f)) :
    Function.Surjective (FundamentalGroup.map (ContinuousMap.inclusion inter_subset_right) y) := by
  obtain ⟨p, hp⟩ : (y : M) ∈ range (f ∘ annulusToProdBall : Q × annulus ℂ δ ε → M) :=
    f.complTube_inter_range hδε ▸ y.property
  have hsub : (annulus ℂ δ ε : Set ℂ) ⊆ Metric.ball 0 ε := fun z hz ↦
    mem_ball_zero_iff.2 (mem_annulus.1 hz).2
  let F := (ContinuousMap.id Q).prodMap (ContinuousMap.inclusion hsub)
  let eB : Q × Metric.ball (0 : ℂ) ε ≃ₜ prodBall Q ε :=
    { toFun := fun w ↦ ⟨(w.1, w.2), mem_prodBall.2 (mem_ball_zero_iff.1 w.2.property)⟩
      invFun := fun w ↦ ((w : Q × ℂ).1,
        ⟨(w : Q × ℂ).2, mem_ball_zero_iff.2 (mem_prodBall.1 w.property)⟩)
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  let e : Q × Metric.ball (0 : ℂ) ε ≃ₜ range f :=
    eB.trans f.isOpenEmbedding.isEmbedding.toHomeomorph
  let e' : Q × annulus ℂ δ ε ≃ₜ ↥((f.complTube hδε : Set M) ∩ range f) :=
    (f.isOpenEmbedding_comp_annulusToProdBall δ).isEmbedding.toHomeomorph.trans
      (Homeomorph.setCongr (f.complTube_inter_range hδε).symm)
  -- `e'` and `e ∘ F` are `f` on points, so their basepoint equations are `hp`
  let φ' := FundamentalGroup.homeomorphMulEquivOfEq e' (Subtype.ext hp : e' p = y)
  let φ := FundamentalGroup.homeomorphMulEquivOfEq e
    (Subtype.ext ((congrArg f (Subtype.ext (coe_annulusToProdBall p).symm)).trans hp) :
      e (F p) = ContinuousMap.inclusion inter_subset_right y)
  have : ContractibleSpace (Metric.ball (0 : ℂ) ε) :=
    (convex_ball 0 ε).contractibleSpace ⟨_, (F p).2.property⟩
  intro t
  obtain ⟨γ, hγ⟩ := FundamentalGroup.map_id_prodMap_surjective _ p.1 p.2 (φ.symm t)
  refine ⟨φ' γ, ?_⟩
  have hsq : FundamentalGroup.map (ContinuousMap.inclusion inter_subset_right) y (φ' γ) =
      φ (FundamentalGroup.map F p γ) := by
    simp only [φ, φ', FundamentalGroup.homeomorphMulEquivOfEq_apply,
      ← FundamentalGroup.mapOfEq_rfl]
    -- both composites are `(q, z) ↦ f (q, z)` on points; the `show` states the coercions to
    -- `M` through the definitions of `e` and `e'`
    have hcomp : (ContinuousMap.inclusion
        (inter_subset_right : (f.complTube hδε : Set M) ∩ range f ⊆ range f)).comp
          (e' : C(Q × annulus ℂ δ ε, _)) =
        (e : C(Q × Metric.ball (0 : ℂ) ε, range f)).comp F :=
      ContinuousMap.ext fun w ↦ Subtype.ext
      (show f (annulusToProdBall w) = f (eB (F w)) from
        congrArg f (Subtype.ext (coe_annulusToProdBall w)))
    exact FundamentalGroup.mapOfEq_mapOfEq_eq_mapOfEq_mapOfEq hcomp _ _ _ _ γ
  rw [hsq, hγ, MulEquiv.apply_symm_apply]

omit [PathConnectedSpace Q] [ConnectedSpace M] in
/-- The fundamental group of the collar and that of the intersection of the complement of the tube
with the range of `f` have the same image in the fundamental group of the complement of the
tube. -/
private theorem range_map_subtypeVal_collar (hδε : δ < ε) (x : f.complTube hδε)
    (hx : x ∈ f.collar hδε) :
    Set.range (FundamentalGroup.map
      (ContinuousMap.subtypeVal (f.collar hδε : Set (f.complTube hδε))) ⟨x, hx⟩) =
    Set.range (FundamentalGroup.map (ContinuousMap.inclusion inter_subset_left)
      (⟨x, x.property, f.mem_collar_iff_coe_mem_range.1 hx⟩ :
        ↥((f.complTube hδε : Set M) ∩ range f))) := by
  let h : C(f.collar hδε, ↥((f.complTube hδε : Set M) ∩ range f)) :=
    ⟨fun z ↦ ⟨z.val, z.val.property, f.mem_collar_iff_coe_mem_range.1 z.property⟩, by fun_prop⟩
  let g : C(↥((f.complTube hδε : Set M) ∩ range f), f.collar hδε) :=
    ⟨fun z ↦ ⟨⟨z.val, z.property.1⟩, f.mem_collar_iff_coe_mem_range.2 z.property.2⟩,
      by fun_prop⟩
  -- the subspace inclusions factor through `h` and `g`, which do not move points of `M`
  refine Subset.antisymm (fun _ ⟨γ, hγ⟩ ↦ ⟨FundamentalGroup.map h ⟨x, hx⟩ γ, ?_⟩)
    (fun _ ⟨γ, hγ⟩ ↦ ⟨FundamentalGroup.map g _ γ, ?_⟩)
  · exact (DFunLike.congr_fun (FundamentalGroup.map_comp
      (ContinuousMap.inclusion inter_subset_left) h ⟨x, hx⟩) γ).symm.trans hγ
  · exact (DFunLike.congr_fun (FundamentalGroup.map_comp
      (ContinuousMap.subtypeVal _) g _) γ).symm.trans hγ

/-- For a product neighbourhood `f` of an embedding of a compact, path connected `Q` into a
connected Hausdorff manifold `M`, and `0 ≤ δ < ε`, the inclusion of the complement of the closed
tube `f (Q × B̄²(δ))` into `M` induces a surjection of fundamental groups at every point of the
collar. -/
theorem map_subtypeVal_complTube_surjective (hδ : 0 ≤ δ) (hδε : δ < ε) (x : f.complTube hδε)
    (hx : x ∈ f.collar hδε) :
    Function.Surjective
      (FundamentalGroup.map (ContinuousMap.subtypeVal (f.complTube hδε : Set M)) x) :=
  FundamentalGroup.map_subtypeVal_surjective_of_map_inclusion_surjective
    (f.interior_complTube_union_interior_range hδε)
    (f.isPathConnected_complTube hδ hδε) (f.isPathConnected_range (hδ.trans_lt hδε))
    (f.complTube_inter_range hδε ▸ f.isPathConnected_range_comp_annulusToProdBall hδ hδε)
    x.property (f.mem_collar_iff_coe_mem_range.1 hx) (f.map_inclusion_inter_range_surjective hδε _)

omit [PathConnectedSpace Q] [ConnectedSpace M] [CompactSpace Q] [T2Space M] in
/-- The normal closure in `π₁(M, x)` of the image of the fundamental group of the range of `f`,
for a point `x` of that range. -/
noncomputable def tubeSubgroup (x : M) (hx : x ∈ range f) : Subgroup (FundamentalGroup M x) :=
  Subgroup.normalClosure
    (Set.range (FundamentalGroup.map (ContinuousMap.subtypeVal (range f)) ⟨x, hx⟩))

omit [PathConnectedSpace Q] [ConnectedSpace M] [CompactSpace Q] [T2Space M] in
theorem tubeSubgroup_def (x : M) (hx : x ∈ range f) :
    f.tubeSubgroup x hx = Subgroup.normalClosure
      (Set.range (FundamentalGroup.map (ContinuousMap.subtypeVal (range f)) ⟨x, hx⟩)) :=
  (rfl)

omit [PathConnectedSpace Q] [ConnectedSpace M] [CompactSpace Q] [T2Space M] in
instance tubeSubgroup_normal (x : M) (hx : x ∈ range f) : (f.tubeSubgroup x hx).Normal :=
  Subgroup.normalClosure_normal

omit [PathConnectedSpace Q] [ConnectedSpace M] in
/-- The normal closure in the fundamental group of the complement of the closed tube, at a point
`x` of the collar, of the image of the fundamental group of the collar. -/
noncomputable def collarSubgroup (hδε : δ < ε) (x : f.complTube hδε) (hx : x ∈ f.collar hδε) :
    Subgroup (FundamentalGroup (f.complTube hδε) x) :=
  Subgroup.normalClosure (Set.range
    (FundamentalGroup.map (ContinuousMap.subtypeVal (f.collar hδε : Set (f.complTube hδε)))
      ⟨x, hx⟩))

omit [PathConnectedSpace Q] [ConnectedSpace M] in
theorem collarSubgroup_def (hδε : δ < ε) (x : f.complTube hδε) (hx : x ∈ f.collar hδε) :
    f.collarSubgroup hδε x hx = Subgroup.normalClosure (Set.range
      (FundamentalGroup.map (ContinuousMap.subtypeVal (f.collar hδε : Set (f.complTube hδε)))
        ⟨x, hx⟩)) :=
  (rfl)

omit [PathConnectedSpace Q] [ConnectedSpace M] in
instance collarSubgroup_normal (hδε : δ < ε) (x : f.complTube hδε) (hx : x ∈ f.collar hδε) :
    (f.collarSubgroup hδε x hx).Normal :=
  Subgroup.normalClosure_normal

/-- **The fundamental group of `M` modulo the tube, surjectivity.** For a product neighbourhood
`f` of an embedding of a compact, path connected `Q` into a connected Hausdorff manifold `M`,
`0 ≤ δ < ε` and a point `x` of the collar, the map from the fundamental group of the complement
of the closed tube `f (Q × B̄²(δ))` to `π₁(M, x) ⧸ f.tubeSubgroup x _` is surjective. -/
theorem mk_comp_map_subtypeVal_complTube_surjective (hδ : 0 ≤ δ) (hδε : δ < ε)
    (x : f.complTube hδε) (hx : x ∈ f.collar hδε) :
    Function.Surjective
      ((QuotientGroup.mk' (f.tubeSubgroup x (f.mem_collar_iff_coe_mem_range.1 hx))).comp
        (FundamentalGroup.map (ContinuousMap.subtypeVal (f.complTube hδε : Set M)) x)) :=
  (QuotientGroup.mk'_surjective _).comp (f.map_subtypeVal_complTube_surjective hδ hδε x hx)

/-- **The fundamental group of `M` modulo the tube, the kernel.** For a product neighbourhood `f`
of an embedding of a compact, path connected `Q` into a connected Hausdorff manifold `M`,
`0 ≤ δ < ε` and a point `x` of the collar, the kernel of the map from the fundamental group of
the complement of the closed tube `f (Q × B̄²(δ))` to `π₁(M, x) ⧸ f.tubeSubgroup x _` is the
normal closure `f.collarSubgroup hδε x hx` of the image of the fundamental group of the
collar. -/
theorem ker_mk_comp_map_subtypeVal_complTube (hδ : 0 ≤ δ) (hδε : δ < ε)
    (x : f.complTube hδε) (hx : x ∈ f.collar hδε) :
    ((QuotientGroup.mk' (f.tubeSubgroup x (f.mem_collar_iff_coe_mem_range.1 hx))).comp
      (FundamentalGroup.map (ContinuousMap.subtypeVal (f.complTube hδε : Set M)) x)).ker =
    f.collarSubgroup hδε x hx := by
  have hxB := f.mem_collar_iff_coe_mem_range.1 hx
  set y : ↥((f.complTube hδε : Set M) ∩ range f) := ⟨x, x.property, hxB⟩
  set φ : FundamentalGroup (f.complTube hδε) x →* FundamentalGroup M x :=
    FundamentalGroup.map (ContinuousMap.subtypeVal (f.complTube hδε : Set M)) x
  set legA : FundamentalGroup _ y →* FundamentalGroup (f.complTube hδε) x :=
    FundamentalGroup.map (ContinuousMap.inclusion inter_subset_left) y
  set legB : FundamentalGroup _ y →* FundamentalGroup (range f) ⟨x, hxB⟩ :=
    FundamentalGroup.map (ContinuousMap.inclusion inter_subset_right) y
  set ψ : FundamentalGroup (range f) ⟨x, hxB⟩ →* FundamentalGroup M x :=
    FundamentalGroup.map (ContinuousMap.subtypeVal (range f)) ⟨x, hxB⟩
  have hsurj := f.map_inclusion_inter_range_surjective hδε y
  have hφs : Function.Surjective φ := f.map_subtypeVal_complTube_surjective hδ hδε x hx
  have hφ : φ.ker = Subgroup.normalClosure (legA '' legB.ker) :=
    FundamentalGroup.ker_map_subtypeVal_eq_normalClosure_image
      (f.interior_complTube_union_interior_range hδε)
      (f.isPathConnected_complTube hδ hδε) (f.isPathConnected_range (hδ.trans_lt hδε))
      (f.complTube_inter_range hδε ▸ f.isPathConnected_range_comp_annulusToProdBall hδ hδε)
      x.property hxB hsurj (Subgroup.normalClosure_eq_self _).symm
  have hsq : ∀ γ, φ (legA γ) = ψ (legB γ) := fun γ ↦
    -- both composites are induced by the inclusion of the intersection into `M`
    (DFunLike.congr_fun (FundamentalGroup.map_comp
      (ContinuousMap.subtypeVal (f.complTube hδε : Set M))
      (ContinuousMap.inclusion inter_subset_left) y) γ).symm.trans
    (DFunLike.congr_fun (FundamentalGroup.map_comp (ContinuousMap.subtypeVal (range f))
      (ContinuousMap.inclusion inter_subset_right) y) γ)
  have hψ : Set.range ψ = φ '' Set.range legA :=
    (hsurj.range_comp ψ).symm.trans
      ((congrArg Set.range (funext fun γ ↦ (hsq γ).symm)).trans (Set.range_comp _ _))
  have hN : f.tubeSubgroup x hxB = (Subgroup.normalClosure (Set.range legA)).map φ := by
    rw [Subgroup.map_normalClosure _ φ hφs, ← hψ]
    exact f.tubeSubgroup_def x hxB
  have hK : Subgroup.normalClosure (Set.range legA) ⊔ φ.ker =
      Subgroup.normalClosure (Set.range legA) := by
    rw [sup_eq_left, hφ]
    exact Subgroup.normalClosure_mono (image_subset_range _ _)
  rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', hN, Subgroup.comap_map_eq, hK,
    collarSubgroup_def]
  exact congrArg _ (f.range_map_subtypeVal_collar hδε x hx).symm

/-- **The fundamental group of `M` modulo the tube.** For a product neighbourhood `f` of an
embedding of a compact, path connected `Q` into a connected Hausdorff manifold `M`, `0 ≤ δ < ε`
and a point `x` of the collar, the isomorphism, induced by the inclusion, between the fundamental
group of the complement of the closed tube `f (Q × B̄²(δ))` modulo the normal closure of the image
of the fundamental group of the collar, and `π₁(M, x)` modulo the normal closure of the image of
the fundamental group of the range of `f`. -/
noncomputable def complTubeQuotientMulEquiv (hδ : 0 ≤ δ) (hδε : δ < ε) (x : f.complTube hδε)
    (hx : x ∈ f.collar hδε) :
    FundamentalGroup (f.complTube hδε) x ⧸ f.collarSubgroup hδε x hx ≃*
      FundamentalGroup M x ⧸ f.tubeSubgroup x (f.mem_collar_iff_coe_mem_range.1 hx) :=
  (QuotientGroup.quotientMulEquivOfEq
    (f.ker_mk_comp_map_subtypeVal_complTube hδ hδε x hx).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _
      (f.mk_comp_map_subtypeVal_complTube_surjective hδ hδε x hx))

/-- The isomorphism `complTubeQuotientMulEquiv` sends the class of a loop in the complement of the
closed tube to the class of the same loop in `M`. -/
@[simp]
theorem complTubeQuotientMulEquiv_mk (hδ : 0 ≤ δ) (hδε : δ < ε) (x : f.complTube hδε)
    (hx : x ∈ f.collar hδε) (γ : FundamentalGroup (f.complTube hδε) x) :
    f.complTubeQuotientMulEquiv hδ hδε x hx γ =
      QuotientGroup.mk (s := f.tubeSubgroup x (f.mem_collar_iff_coe_mem_range.1 hx))
        (FundamentalGroup.map (ContinuousMap.subtypeVal (f.complTube hδε : Set M)) x γ :
          FundamentalGroup M x) :=
  (rfl)

end SymplecticGeometry.ProductNeighborhood

end
