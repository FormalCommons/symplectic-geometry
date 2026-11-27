/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import SymplecticGeometry.Geometry.Symplectic.Sum.Fibre
import Mathlib.Algebra.Category.Grp.EpiMono
import SymplecticGeometry.Topology.Connected.Clopen
import SymplecticGeometry.Topology.Homotopy.Annulus
import TauCeti.AlgebraicTopology.FundamentalGroup.BasepointChange
import TauCeti.AlgebraicTopology.FundamentalGroup.Basic
import TauCeti.AlgebraicTopology.FundamentalGroup.HomotopyEquiv
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

## Main results

* `SymplecticGeometry.ProductNeighborhood.isPathConnected_complTube`: the complement of the
  closed tube is path connected.
* `SymplecticGeometry.ProductNeighborhood.complTube_subset_compl_range`: it lies in the
  complement of `ι (Q)`.
* `SymplecticGeometry.ProductNeighborhood.map_inclusion_complTube_bijective`: the inclusion into
  the complement of `ι (Q)` induces a bijection of fundamental groups at every point.
* `SymplecticGeometry.ProductNeighborhood.simplyConnectedSpace_complTube`: the complement of the
  closed tube is simply connected if the complement of `ι (Q)` is.

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


/-- A product neighbourhood restricted to the product of `Q` with the annulus `a < |z| < ε` is an
open embedding. -/
theorem isOpenEmbedding_comp_annulusToProdBall (a : ℝ) :
    IsOpenEmbedding (f ∘ annulusToProdBall : Q × annulus ℂ a ε → M) := by
  have h : IsLocalDiffeomorph (J.prod 𝓘(ℝ, ℂ)) I ∞ (f ∘ annulusToProdBall :
      Q × annulus ℂ a ε → M) := fun p ↦
    (isLocalDiffeomorph_annulusToProdBall p).comp (hg := f.isLocalDiffeomorph _)
  exact .of_continuous_injective_isOpenMap h.contMDiff.continuous
    (f.isOpenEmbedding.injective.comp annulusToProdBall_injective) h.isOpenMap

/-- The range of a product neighbourhood on `Q × A(a, ε)` is path connected, for path connected
`Q` and `0 ≤ a < ε`. -/
theorem isPathConnected_range_comp_annulusToProdBall [PathConnectedSpace Q] {a : ℝ} (ha : 0 ≤ a)
    (haε : a < ε) :
    IsPathConnected (range (f ∘ annulusToProdBall : Q × annulus ℂ a ε → M)) := by
  have : PathConnectedSpace (annulus ℂ a ε) := isPathConnected_iff_pathConnectedSpace.1
    (isPathConnected_annulus (by simp [Complex.rank_real_complex]) ha haε)
  exact isPathConnected_range (f.isOpenEmbedding_comp_annulusToProdBall a).continuous

/-- A point `f p` lies on `ι (Q)` exactly when the disc coordinate of `p` vanishes. -/
theorem apply_mem_range_iff {p : prodBall Q ε} : f p ∈ range ι ↔ (p : Q × ℂ).2 = 0 := by
  refine ⟨?_, fun h ↦ ⟨(p : Q × ℂ).1, ?_⟩⟩
  · rintro ⟨q, hq⟩
    have hq0 : (q, (0 : ℂ)) ∈ prodBall Q ε := mem_prodBall.2 (by
      simpa using (norm_nonneg _).trans_lt (mem_prodBall.1 p.property))
    rw [← f.apply_mk_zero q hq0] at hq
    rw [← f.isOpenEmbedding.injective hq]
  · have hp : p = ⟨((p : Q × ℂ).1, 0), h ▸ p.property⟩ := Subtype.ext (Prod.ext rfl h)
    rw [hp, f.apply_mk_zero]

/-- A point `f p` lies in `f (Q × A(a, ε))` exactly when `a < |p.2|`. -/
theorem apply_mem_range_comp_annulusToProdBall_iff {a : ℝ} {p : prodBall Q ε} :
    f p ∈ range (f ∘ annulusToProdBall : Q × annulus ℂ a ε → M) ↔ a < ‖(p : Q × ℂ).2‖ := by
  refine ⟨?_, fun h ↦ ⟨_, congrArg f (annulusToProdBall_mk p
    (mem_annulus.2 ⟨h, mem_prodBall.1 p.property⟩))⟩⟩
  rintro ⟨w, hw⟩
  rw [← f.isOpenEmbedding.injective hw]
  simpa using (mem_annulus.1 w.2.property).1

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
    rw [mem_compl_iff, mem_union, SetLike.mem_coe, f.apply_mem_range_iff,
      f.apply_mem_complTube_iff, f.apply_mem_range_comp_annulusToProdBall_iff, norm_pos_iff]
    exact ⟨fun h ↦ .inr h, fun h ↦ h.elim (fun h' ↦ norm_pos_iff.1 (hδ.trans_lt h')) id⟩
  · refine iff_of_true (fun ⟨q, hq⟩ ↦ hx ?_) (.inl (f.mem_complTube.2 fun ⟨p, _, hp⟩ ↦ hx ⟨p, hp⟩))
    have hq0 : (q, (0 : ℂ)) ∈ prodBall Q ε := mem_prodBall.2 (by simpa using hδ.trans_lt hδε)
    exact ⟨_, (f.apply_mk_zero q hq0).trans hq⟩

/-- For `0 ≤ δ`, the complement of the closed tube lies in the complement of `ι (Q)`. -/
theorem complTube_subset_compl_range (hδ : 0 ≤ δ) (hδε : δ < ε) :
    (f.complTube hδε : Set M) ⊆ (range ι)ᶜ :=
  (f.compl_range_eq_complTube_union hδ hδε).symm ▸ subset_union_left

variable [PathConnectedSpace Q]

/-- The complement in a connected manifold of the closed tube `f (Q × B̄²(δ))`, `0 ≤ δ < ε`, of a
product neighbourhood of a path connected `Q` is path connected. -/
theorem isPathConnected_complTube [ConnectedSpace M] (hδ : 0 ≤ δ) (hδε : δ < ε) :
    IsPathConnected (f.complTube hδε : Set M) := by
  have hAB := f.complTube_inter_range hδε ▸ f.isPathConnected_range_comp_annulusToProdBall hδ hδε
  have : LocallyPathConnectedSpace M := I.locallyPathConnectedSpace_of_chartedSpace M
  refine ((f.complTube hδε).isOpen.isConnected_iff_isPathConnected).1
    ⟨hAB.nonempty.mono inter_subset_left, hAB.isConnected.isPreconnected.of_isOpen_of_union_eq_univ
      hAB.nonempty (f.complTube hδε).isOpen f.isOpen_range ?_⟩
  rw [← compl_subset_iff_union]
  intro x hx
  rw [mem_compl_iff, SetLike.mem_coe, mem_complTube, not_not] at hx
  obtain ⟨p, -, rfl⟩ := hx
  exact mem_range_self p

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

end SymplecticGeometry.ProductNeighborhood

end
