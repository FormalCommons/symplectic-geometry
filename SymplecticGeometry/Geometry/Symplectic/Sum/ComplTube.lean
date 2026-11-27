/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import SymplecticGeometry.Geometry.Symplectic.Sum.Fibre
public import TauCeti.AlgebraicTopology.FundamentalGroup.BasepointChange
import Mathlib.Analysis.Convex.Contractible
import SymplecticGeometry.AlgebraicTopology.FundamentalGroup.BasepointChange
import SymplecticGeometry.AlgebraicTopology.FundamentalGroup.Homeomorph
import SymplecticGeometry.AlgebraicTopology.FundamentalGroup.Prod.Basic
import SymplecticGeometry.AlgebraicTopology.FundamentalGroup.VanKampen
import SymplecticGeometry.Topology.Connected.Clopen
import SymplecticGeometry.Topology.Homotopy.Annulus
import TauCeti.AlgebraicTopology.FundamentalGroup.Basic
import TauCeti.AlgebraicTopology.FundamentalGroup.HomotopyEquiv
import TauCeti.Geometry.Manifold.Topology
import TauCeti.Topology.Homeomorph.SetCongr
import TauCeti.Topology.Homotopy.Path

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
connected, as `M` is connected (`IsPathConnected.of_isOpen_of_union_eq_univ`). For the
fundamental groups, the complement of the tube and `f (Q × A(0, ε))` cover the complement of
`ι (Q)`, again with the collar as overlap, and van Kampen with a bijective leg
(`FundamentalGroup.map_inclusion_bijective_of_map_inclusion_bijective`) applies: the inclusion of
the collar into `f (Q × A(0, ε))` is, through `f`, the product of `Q` with the inclusion of an
annulus into the punctured disc, a homotopy equivalence
(`SymplecticGeometry.annulusHomotopyEquiv`).

The same cover of `M` by the complement of the tube and the range of `f` describes `π₁(M)` from
the complement of the tube. Through `f`, the inclusion of the collar into the range of `f` is the
product of `Q` with the inclusion of an annulus into a disc, which is surjective on fundamental
groups as the disc is simply connected (`FundamentalGroup.map_id_prodMap_surjective`). Van Kampen
with a surjective leg (`FundamentalGroup.map_subtypeVal_surjective_of_map_inclusion_surjective`
and `FundamentalGroup.ker_map_subtypeVal_eq_normalClosure_image`) then shows that the inclusion of
the complement of the tube into `M` is onto on fundamental groups, with kernel inside the normal
closure of the image of the collar's group; and the image of `π₁(range f)` in `π₁(M)` is that of
the collar's group. Dividing by these normal closures gives an isomorphism of quotients. The
surjectivity is moved along `f` by `FundamentalGroup.map_surjective_iff_of_homeomorph`.

At a point `f (q, z)` of the collar, the normal closure `tubeSubgroup` is that of the image of
`ι_* : π₁(Q, q) → π₁(M, ι q)`, moved along the radial path
`ProductNeighborhood.radialPath`, `t ↦ f (q, t • z)`. The change of base point commutes with the
map induced by the inclusion of the range of `f`, which contains the path
(`FundamentalGroup.basepointChangeSubgroup_map_range`), and `q ↦ f (q, 0)` is onto on
fundamental groups, as through `f` it is the inclusion of the slice `Q × {0}` into the product
of `Q` with a simply connected disc (`FundamentalGroup.map_prodMk_const_surjective`).

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
* `SymplecticGeometry.ProductNeighborhood.range_map_subtypeVal_eq_range_map_embedding`: the
  fundamental groups of the range of `f` and of `Q` have the same image in `π₁(M, ι q)`.
* `SymplecticGeometry.ProductNeighborhood.basepointChangeSubgroup_radialPath`: the change of base
  point along the radial path carries the normal closure of the image of `ι_*` onto
  `tubeSubgroup`.
* `SymplecticGeometry.ProductNeighborhood.collarRadialPath`: the radial path from `ι q` to a
  point `f (q, z)` of the collar, and `basepointChangeSubgroup_collarRadialPath`, the same
  change of base point along it.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Cambridge University Press, 2002, §1.1 (change of base point), Proposition 1.12 and
  Theorem 1.20.
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
  exact hAB.of_isOpen_of_union_eq_univ (f.complTube hδε).isOpen f.isOpen_range
    (f.complTube_union_range hδε)

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
    simp only [e₀, e, Homeomorph.trans_apply, Homeomorph.setCongr_apply,
      IsEmbedding.toHomeomorph_apply_coe, Function.comp_apply]
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
  exact FundamentalGroup.map_inclusion_bijective_of_map_inclusion_bijective
    (f.compl_range_eq_complTube_union hδ hδε) (f.complTube hδε).isOpen
    (f.isOpenEmbedding_comp_annulusToProdBall 0).isOpen_range (f.isPathConnected_complTube hδ hδε)
    (f.isPathConnected_range_comp_annulusToProdBall le_rfl (hδ.trans_lt hδε)) hABc hy.1 hy.2
    (f.map_inclusion_collar_bijective hδ hδε ⟨y, hy⟩) x

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
  have : ContractibleSpace (Metric.ball (0 : ℂ) ε) :=
    (convex_ball 0 ε).contractibleSpace ⟨_, hsub p.2.property⟩
  let e' : Q × annulus ℂ δ ε ≃ₜ ↥((f.complTube hδε : Set M) ∩ range f) :=
    (f.isOpenEmbedding_comp_annulusToProdBall δ).isEmbedding.toHomeomorph.trans
      (Homeomorph.setCongr (f.complTube_inter_range hδε).symm)
  have hsq : ∀ w, ContinuousMap.inclusion inter_subset_right (e' w) =
      f.rangeHomeomorph ((ContinuousMap.id Q).prodMap (ContinuousMap.inclusion hsub) w) := by
    intro w
    ext
    simp only [e', Homeomorph.trans_apply, Homeomorph.setCongr_apply, coe_rangeHomeomorph_apply]
    exact congrArg f (Subtype.ext (by
      simpa [coe_annulusToProdBall] using (ContinuousMap.inclusion_apply_coe hsub w.2).symm))
  exact (FundamentalGroup.map_surjective_iff_of_homeomorph hsq (Subtype.ext hp)).2
    (FundamentalGroup.map_id_prodMap_surjective _ p.1 p.2)

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

/-! ### The radial change of base point from the collar to the core -/

omit [PathConnectedSpace Q] [ConnectedSpace M] [CompactSpace Q] [T2Space M] in
/-- The fundamental group of the range of a product neighbourhood `f` and that of `Q` have the
same image in `π₁(M, ι q)`: the map `Q → range f`, `q ↦ ι q = f (q, 0)`, is onto on fundamental
groups, since through `f` it is the inclusion of the slice `Q × {0}` into `Q × B²(ε)` and the
disc is simply connected. -/
theorem range_map_subtypeVal_eq_range_map_embedding (q : Q) (h : ι q ∈ range f) :
    Set.range (FundamentalGroup.map (ContinuousMap.subtypeVal (range f)) ⟨ι q, h⟩) =
      Set.range (FundamentalGroup.map ι.toContinuousMap q) := by
  have hε : 0 < ε := by
    obtain ⟨p, -⟩ := h
    exact (norm_nonneg _).trans_lt (mem_prodBall.1 p.property)
  have : ContractibleSpace (Metric.ball (0 : ℂ) ε) :=
    (convex_ball 0 ε).contractibleSpace ⟨0, Metric.mem_ball_self hε⟩
  let r : C(Q, range f) :=
    ⟨fun q' ↦ ⟨ι q', f.range_embedding_subset_range hε ⟨q', rfl⟩⟩, by fun_prop⟩
  let s : C(Q, Q × Metric.ball (0 : ℂ) ε) :=
    (ContinuousMap.id Q).prodMk (.const Q ⟨0, Metric.mem_ball_self hε⟩)
  -- `f.rangeHomeomorph ∘ s` is `q ↦ f (q, 0)`, which is `r` only by `apply_mk_zero`
  have hr : ∀ g : C(Q, range f), (f.rangeHomeomorph : C(_, range f)).comp s = g →
      Function.Surjective (FundamentalGroup.map g q) := by
    rintro _ rfl
    rw [FundamentalGroup.map_comp]
    exact (f.rangeHomeomorph.toHomotopyEquiv.fundamentalGroup_map_bijective _).2.comp
      (FundamentalGroup.map_prodMk_const_surjective q _)
  rw [← (hr r (ContinuousMap.ext fun q' ↦ Subtype.ext ((f.coe_rangeHomeomorph_apply _).trans
    (f.apply_mk_zero q' _)))).range_comp]
  -- `subtypeVal ∘ r` is `ι` as a continuous map, by the definition of `r`
  exact congrArg Set.range
    (funext fun x ↦ (DFunLike.congr_fun (FundamentalGroup.map_comp _ r q) x).symm)

omit [PathConnectedSpace Q] [ConnectedSpace M] [CompactSpace Q] [T2Space M] in
/-- **Radial change of base point to the core.** For a product neighbourhood
`f` of an embedding `ι : Q → M` and a point `p = (q, z)` of `Q × B²(ε)`, the change of base point
along the radial path from `ι q` to `f p` carries the normal closure of the image of
`ι_* : π₁(Q, q) → π₁(M, ι q)` onto the normal closure `f.tubeSubgroup (f p) _` of the image of the
fundamental group of the range of `f`. -/
theorem basepointChangeSubgroup_radialPath (p : prodBall Q ε) :
    FundamentalGroup.basepointChangeSubgroup (f.radialPath p) (Subgroup.normalClosure
      (Set.range (FundamentalGroup.map ι.toContinuousMap (p : Q × ℂ).1))) =
    f.tubeSubgroup (f p) (mem_range_self p) := by
  have h : ι (p : Q × ℂ).1 ∈ range f := by
    rw [← (f.radialPath p).source, radialPath_apply]
    exact mem_range_self _
  -- the radial path, as a path in the range of `f`
  let γ : Path (⟨ι (p : Q × ℂ).1, h⟩ : range f) ⟨f p, mem_range_self p⟩ :=
    (f.radialPath p).codRestrict fun _ ↦ by simp
  have hγ : γ.map (ContinuousMap.subtypeVal (range f)).continuous = f.radialPath p :=
    Path.map_codRestrict _ _
  -- the base points `subtypeVal ⟨x, _⟩` of the induced maps are `x` only up to unfolding the
  -- coercion, which `rw` does not do, so the subgroups are related by terms rather than `rw`
  have key : FundamentalGroup.basepointChangeSubgroup (f.radialPath p)
      (FundamentalGroup.map (ContinuousMap.subtypeVal (range f)) ⟨_, h⟩).range =
      (FundamentalGroup.map (ContinuousMap.subtypeVal (range f)) ⟨f p, mem_range_self p⟩).range :=
    hγ ▸ FundamentalGroup.basepointChangeSubgroup_map_range _ γ
  replace key := (FundamentalGroup.basepointChangeSubgroup_eq_map (f.radialPath p) _).symm.trans key
  rw [FundamentalGroup.basepointChangeSubgroup_eq_map, Subgroup.map_normalClosure _ _
    (FundamentalGroup.fundamentalGroupMulEquivOfPath _).surjective, tubeSubgroup_def,
    ← f.range_map_subtypeVal_eq_range_map_embedding _ h]
  exact congrArg _ (((Subgroup.coe_map _ _).symm.trans (congrArg SetLike.coe key)).trans
    (MonoidHom.coe_range _))

omit [PathConnectedSpace Q] [ConnectedSpace M] in
/-- The radial path `t ↦ f (q, t • z)` from `ι q` to the collar point `f (q, z)`, for a point
`p = (q, z)` of `Q × A(δ, ε)`: `ProductNeighborhood.radialPath` with its end points written
through `p`. -/
noncomputable def collarRadialPath (hδε : δ < ε) (p : Q × annulus ℂ δ ε) :
    Path (ι p.1) (f.collarMap hδε p : M) :=
  (f.radialPath (annulusToProdBall p)).cast (by rw [coe_annulusToProdBall])
    (f.coe_collarMap hδε p)

omit [PathConnectedSpace Q] [ConnectedSpace M] in
@[simp]
theorem collarRadialPath_apply (hδε : δ < ε) (p : Q × annulus ℂ δ ε) (t : unitInterval) :
    f.collarRadialPath hδε p t = f.radialPath (annulusToProdBall p) t :=
  (rfl)

omit [PathConnectedSpace Q] [ConnectedSpace M] in
/-- The change of base point along the radial path from `ι q` to the collar point `f (q, z)`
carries the normal closure of the image of `ι_* : π₁(Q, q) → π₁(M, ι q)` onto
`f.tubeSubgroup`. -/
theorem basepointChangeSubgroup_collarRadialPath (hδε : δ < ε) (p : Q × annulus ℂ δ ε) :
    FundamentalGroup.basepointChangeSubgroup (f.collarRadialPath hδε p)
        (Subgroup.normalClosure (Set.range (FundamentalGroup.map ι.toContinuousMap p.1))) =
      f.tubeSubgroup (f.collarMap hδε p)
        (f.mem_collar_iff_coe_mem_range.1 (f.collarMap_mem_collar hδε p)) := by
  -- the end points of the radial path are those of `collarRadialPath` only propositionally
  have key : ∀ (pb : prodBall Q ε) (a : Q) (ha : a = (pb : Q × ℂ).1) (y : M) (hy : y = f pb),
      FundamentalGroup.basepointChangeSubgroup ((f.radialPath pb).cast (congrArg ι ha) hy)
          (Subgroup.normalClosure (Set.range (FundamentalGroup.map ι.toContinuousMap a))) =
        f.tubeSubgroup y (hy ▸ mem_range_self pb) := by
    rintro pb a rfl y rfl
    exact f.basepointChangeSubgroup_radialPath pb
  exact key _ _ (by rw [coe_annulusToProdBall]) _ (f.coe_collarMap hδε p)

end SymplecticGeometry.ProductNeighborhood

end
