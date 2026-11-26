/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Connected
public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Homogeneity
import SymplecticGeometry.Geometry.Manifold.NullSet
import TauCeti.Geometry.Manifold.SmoothEmbedding.Diffeomorph

/-!
# Proper rays from a closed discrete set

This file builds rays, smooth embeddings `ℝ → M` that go to infinity, through the points of a
closed discrete set of a manifold of dimension at least two. Each ray is grown arc by arc.

## Main results

* `exists_mem_sdiff_union_iUnion_image_notMem`: a target for the arc. If an open set `W` is not
  contained in a closed set `L`, some point of `W` outside `L` misses a discrete set and
  countably many arcs of differentiable curves, since these form a null set
  (`dense_compl_union_iUnion_range`).
* `exists_diffeomorph_grow_arc`: one arc of growth. Let `W` be a preconnected open set of `M`,
  `s` a closed discrete set and finitely many disjoint arcs with free ends, closed in `W \ s`,
  among them the part `γ '' J` of a smooth embedding `γ` that ends at `γ T`. Some diffeomorphism
  `Ψ` of `M`, the identity outside a compact subset of the open set `U` left from `W` by removing
  `s` and the arcs, makes `Ψ ∘ γ` agree with `γ` up to `T`, run through `U` just after `T`, and
  reach a prescribed point of `U`.
* `LeavesForGood γ K D`: along the parameters `D`, once the curve `γ` is outside `K` it stays
  outside. This is the invariant that the rays keep for every compact set of the exhaustion as
  they grow. It holds when `γ` maps `D` into `K` or outside `K`, survives extension by a piece
  outside `K` (`LeavesForGood.extend_Icc`, `LeavesForGood.extend_Iic`) and by an earlier piece
  inside `K` (`LeavesForGood.union_of_mapsTo_left`), and, for `D` an
  interval ending at `T` on which `γ` is continuous, makes the points of `γ '' D` in the
  component of `Kᶜ` through `γ T` the image of an order-connected set that contains `T` once it
  is nonempty (`LeavesForGood.image_inter_connectedComponentIn`), the form that
  `exists_diffeomorph_grow_arc` takes.

The set `U` is preconnected by `isPreconnected_sdiff_union_iUnion_image_of_one_lt_rank`, and
`Ψ` is the final map of a diffeotopy given by Tau Ceti's homogeneity lemma
`TauCeti.exists_diffeotopy_final_apply_eq_of_isPreconnected`, which moves a point of `γ` just
after `T` to the prescribed point. Since `Ψ` fixes the arcs, the part of `γ` already built does
not move.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Theorem 7.3.1, for the construction of the rays.
* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia
  (1965), §4, for the homogeneity lemma.
-/

public section

open Function Set Topology Manifold
open scoped ContDiff

namespace SymplecticGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [I.Boundaryless] [T2Space M] [IsManifold I ∞ M] in
/-- **A target off the arcs, outside a closed set.** Let `M` be a manifold whose model space has
rank greater than one, `W ⊆ M` open, `s` discrete and `f i : ℝ → M`, for `i` in a countable type,
differentiable curves. If `W` is not contained in a closed set `L`, for instance a compact set
when `closure W` is not compact, then some point of `W` outside `L` lies neither on `s` nor on
any of the arcs `f i '' J i`. -/
theorem exists_mem_sdiff_union_iUnion_image_notMem [IsManifold I 1 M]
    (hE : 1 < Module.rank ℝ E) {ι : Type*} [Countable ι] {W s L : Set M} (hW : IsOpen W)
    (hL : IsClosed L) (hWL : ¬ W ⊆ L) (hs : IsDiscrete s) {f : ι → ℝ → M}
    (hf : ∀ i, MDifferentiable 𝓘(ℝ) I (f i)) (J : ι → Set ℝ) :
    ∃ y ∈ W \ (s ∪ ⋃ i, f i '' J i), y ∉ L := by
  rw [← Module.finrank_eq_rank] at hE
  obtain ⟨y, ⟨hyW, hyL⟩, hy⟩ := (dense_compl_union_iUnion_range (by exact_mod_cast hE) hs hf)
    |>.inter_open_nonempty (W \ L) (hW.sdiff hL) (not_subset.1 hWL)
  refine ⟨y, ⟨hyW, fun h ↦ hy ?_⟩, hyL⟩
  exact union_subset_union_right s (iUnion_mono fun i ↦ image_subset_range _ _) h

/-- **Growing a ray by one arc.** Let `M` be a finite-dimensional Hausdorff boundaryless smooth
manifold whose model space has rank greater than one, `W ⊆ M` open and preconnected and `s`
closed and discrete. For `i` in a finite type let `f i : ℝ → M` be a smooth embedding and
`J i ⊆ ℝ` order-connected with a greatest or a least element, such that the arcs `f i '' J i` lie
in `W \ s`, are pairwise disjoint and are closed in `W \ s`; write
`U := W \ (s ∪ ⋃ i, f i '' J i)`. Let `γ := f i₀`, where `T` is the greatest element of `J i₀`,
and suppose that every point of `γ '' Iic T` in `W` lies on one of the arcs. Then for every
`y ∈ U` there are a diffeomorphism `Ψ` of `M`, the identity outside a
compact subset `K` of `U`, and `δ > 0` such that `Ψ ∘ γ` is a smooth embedding that agrees with
`γ` on `Iic T`, sends `T + δ` to `y`, and maps `Ioc T (T + δ)` into `U`. -/
theorem exists_diffeomorph_grow_arc {ι : Type*} [Finite ι] (hE : 1 < Module.rank ℝ E)
    {W s : Set M} (hW : IsOpen W) (hWc : IsPreconnected W) (hs : IsClosed s)
    (hd : IsDiscrete s) {f : ι → ℝ → M} (hf : ∀ i, IsSmoothEmbedding 𝓘(ℝ) I ∞ (f i))
    {J : ι → Set ℝ} (hJ : ∀ i, (J i).OrdConnected)
    (hb : ∀ i, ∃ b, IsGreatest (J i) b ∨ IsLeast (J i) b) (hJW : ∀ i, f i '' J i ⊆ W \ s)
    (hdisj : Pairwise (Disjoint on fun i ↦ f i '' J i))
    (hcl : ∀ i, closure (f i '' J i) ∩ (W \ s) ⊆ f i '' J i)
    {γ : ℝ → M} {i₀ : ι} (hγ : f i₀ = γ) {T : ℝ} (hT : IsGreatest (J i₀) T)
    (hγW : γ '' Iic T ∩ W ⊆ ⋃ i, f i '' J i) {y : M}
    (hy : y ∈ W \ (s ∪ ⋃ i, f i '' J i)) :
    ∃ (Ψ : M ≃ₘ^∞⟮I, I⟯ M) (K : Set M), IsCompact K ∧ K ⊆ W \ (s ∪ ⋃ i, f i '' J i) ∧
      EqOn Ψ id Kᶜ ∧ ∃ δ > 0, IsSmoothEmbedding 𝓘(ℝ) I ∞ (Ψ ∘ γ) ∧
        EqOn (Ψ ∘ γ) γ (Iic T) ∧ Ψ (γ (T + δ)) = y ∧
        Ψ ∘ γ '' Ioc T (T + δ) ⊆ W \ (s ∪ ⋃ i, f i '' J i) := by
  -- `U` is open, since the arcs are closed in `W \ s`.
  have hUo : IsOpen (W \ (s ∪ ⋃ i, f i '' J i)) := by
    rw [← sdiff_sdiff]
    exact (hW.sdiff hs).sdiff_iUnion_of_closure_inter_subset hcl
  set U := W \ (s ∪ ⋃ i, f i '' J i)
  subst hγ
  have hUc : IsPreconnected U :=
    isPreconnected_sdiff_union_iUnion_image_of_one_lt_rank hE hW hWc hs hd hf hJ hb hJW hdisj hcl
  -- Near `γ T`, the points of `W` off `s` miss the closures of the other arcs.
  set V := (W \ s) \ ⋃ i ∈ {i | i ≠ i₀}, closure (f i '' J i)
  have hTV : f i₀ T ∈ V := by
    have hT' := hJW i₀ (mem_image_of_mem _ hT.1)
    refine ⟨hT', fun h ↦ ?_⟩
    obtain ⟨i, hi, hTi⟩ := mem_iUnion₂.1 h
    exact disjoint_left.1 (hdisj hi) (hcl i ⟨hTi, hT'⟩) (mem_image_of_mem _ hT.1)
  have hVo : IsOpen V := (hW.sdiff hs).sdiff
    ((toFinite _).isClosed_biUnion fun _ _ ↦ isClosed_closure)
  have hTV' : f i₀ ⁻¹' V ∈ 𝓝 T :=
    (hf i₀).isEmbedding.continuous.continuousAt.preimage_mem_nhds (hVo.mem_nhds hTV)
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.1 hTV'
  -- The part of `γ` just after `T` lies in `U`.
  have hγU : f i₀ '' Ioc T (T + ε / 2) ⊆ U := by
    rintro _ ⟨t, ⟨htT, htε⟩, rfl⟩
    have htV : f i₀ t ∈ V := hεV (by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith)
    refine ⟨htV.1.1, fun h ↦ h.elim htV.1.2 fun h ↦ ?_⟩
    obtain ⟨i, u, hu, hut⟩ := mem_iUnion.1 h
    by_cases hi : i = i₀
    · subst hi
      exact (hT.2 hu).not_gt (((hf i).isEmbedding.injective hut) ▸ htT)
    · exact htV.2 (mem_iUnion₂.2 ⟨i, hi, subset_closure ⟨u, hu, hut⟩⟩)
  have hδU : f i₀ (T + ε / 2) ∈ U := hγU ⟨T + ε / 2, ⟨by linarith, le_rfl⟩, rfl⟩
  obtain ⟨Φ, K, hK, hKU, hΦK, hΦ⟩ :=
    TauCeti.exists_diffeotopy_final_apply_eq_of_isPreconnected (I := I) (n := ∞) (m := ⊤) le_top
      (by simp) hUo hUc hδU hy
  have hΨK : EqOn Φ.final id Kᶜ := fun z hz ↦ by simpa using hΦK 1 hz
  refine ⟨Φ.final, K, hK, hKU, hΨK, ε / 2, half_pos hε,
    TauCeti.isSmoothEmbedding_diffeomorph_comp (hf i₀) Φ.final, fun t ht ↦ hΨK fun htK ↦ ?_,
    hΦ, ?_⟩
  · obtain ⟨i, hi⟩ := mem_iUnion.1 (hγW ⟨mem_image_of_mem _ ht, (hKU htK).1⟩)
    exact (hKU htK).2 (.inr (mem_iUnion.2 ⟨i, hi⟩))
  · rw [image_comp]
    exact ((Φ.mapsTo_final_of_eqOn_compl hKU hΦK).mono_left hγU).image_subset


section LeavesForGood

variable {X : Type*} {γ γ' : ℝ → X} {K : Set X} {D D' : Set ℝ} {a s T T' : ℝ}

/-- A curve `γ : ℝ → X` *leaves `K` for good* along a set of parameters `D` if, along `D`, once
`γ` is outside `K` it stays outside `K`: for `s ≤ t` in `D` with `γ s ∉ K`, also `γ t ∉ K`.
Equivalently, the parameters of `D` sent outside `K` form an upper set of `D`; for an
order-connected `D` with greatest element `T`, they form an order-connected set that contains `T`
unless it is empty (`leavesForGood_iff_ordConnected`). -/
def LeavesForGood (γ : ℝ → X) (K : Set X) (D : Set ℝ) : Prop :=
  ∀ ⦃s⦄, s ∈ D → ∀ ⦃t⦄, t ∈ D → s ≤ t → γ s ∉ K → γ t ∉ K

theorem leavesForGood_def :
    LeavesForGood γ K D ↔ ∀ ⦃s⦄, s ∈ D → ∀ ⦃t⦄, t ∈ D → s ≤ t → γ s ∉ K → γ t ∉ K :=
  Iff.rfl

theorem leavesForGood_iff_monotoneOn :
    LeavesForGood γ K D ↔ MonotoneOn (fun t ↦ γ t ∉ K) D :=
  Iff.rfl

/-- A curve that maps `D` into `K` leaves `K` for good along `D`. -/
theorem leavesForGood_of_mapsTo (h : MapsTo γ D K) : LeavesForGood γ K D :=
  fun _ hs _ _ _ hsK ↦ (hsK (h hs)).elim

/-- A curve that maps `D` outside `K` leaves `K` for good along `D`. -/
theorem leavesForGood_of_mapsTo_compl (h : MapsTo γ D Kᶜ) : LeavesForGood γ K D :=
  fun _ _ _ ht _ _ ↦ h ht

theorem LeavesForGood.mono (h : LeavesForGood γ K D) (hD : D' ⊆ D) : LeavesForGood γ K D' :=
  fun _ hs _ ht hst ↦ h (hD hs) (hD ht) hst

theorem LeavesForGood.congr (h : LeavesForGood γ K D) (hγ : EqOn γ' γ D) :
    LeavesForGood γ' K D := fun s hs t ht hst ↦ by
  rw [hγ hs, hγ ht]
  exact h hs ht hst

/-- If `γ` leaves `K` for good along `D` and maps outside `K` a set `D'` of parameters that all
come after those of `D`, then `γ` leaves `K` for good along `D ∪ D'`. -/
theorem LeavesForGood.union (h : LeavesForGood γ K D) (h' : MapsTo γ D' Kᶜ)
    (hDD' : ∀ s ∈ D, ∀ t ∈ D', s < t) : LeavesForGood γ K (D ∪ D') := by
  rintro s (hs | hs) t (ht | ht) hst
  · exact h hs ht hst
  · exact fun _ ↦ h' ht
  · exact ((hDD' t ht s hs).not_ge hst).elim
  · exact fun _ ↦ h' ht

/-- If `γ` maps `D` into `K` and leaves `K` for good along a set `D'` of parameters that
all come at or after those of `D`, then `γ` leaves `K` for good along `D ∪ D'`. -/
theorem LeavesForGood.union_of_mapsTo_left (h : LeavesForGood γ K D') (h' : MapsTo γ D K)
    (hDD' : ∀ s ∈ D, ∀ t ∈ D', s ≤ t) : LeavesForGood γ K (D ∪ D') := by
  rintro s (hs | hs) t (ht | ht) hst hsK
  · exact (hsK (h' hs)).elim
  · exact (hsK (h' hs)).elim
  · exact (hsK (h' (le_antisymm hst (hDD' t ht s hs) ▸ ht))).elim
  · exact h hs ht hst hsK

/-- A curve that maps `Iic a` into `K` and leaves `K` for good along `Icc a s` leaves `K` for
good along `Iic s`. -/
theorem LeavesForGood.Iic_of_mapsTo_Iic (h : LeavesForGood γ K (Icc a s))
    (h' : MapsTo γ (Iic a) K) : LeavesForGood γ K (Iic s) :=
  (h.union_of_mapsTo_left h' fun _ hu _ hv ↦ (mem_Iic.1 hu).trans hv.1).mono
    Iic_subset_Iic_union_Icc

/-- Extension of a curve that leaves `K` for good along `Icc a T`: a curve `γ'` that agrees with
`γ` on `Icc a T` and maps `Ioc T T'` outside `K` leaves `K` for good along `Icc a T'`. -/
theorem LeavesForGood.extend_Icc (h : LeavesForGood γ K (Icc a T)) (hγ : EqOn γ' γ (Icc a T))
    (h' : MapsTo γ' (Ioc T T') Kᶜ) : LeavesForGood γ' K (Icc a T') :=
  ((h.congr hγ).union h' fun _ hs _ ht ↦ hs.2.trans_lt ht.1).mono Icc_subset_Icc_union_Ioc

/-- Extension of a curve that leaves `K` for good along `Iic T`: a curve `γ'` that agrees with
`γ` on `Iic T` and maps `Ioc T T'` outside `K` leaves `K` for good along `Iic T'`. -/
theorem LeavesForGood.extend_Iic (h : LeavesForGood γ K (Iic T)) (hγ : EqOn γ' γ (Iic T))
    (h' : MapsTo γ' (Ioc T T') Kᶜ) : LeavesForGood γ' K (Iic T') :=
  ((h.congr hγ).union h' fun _ hs _ ht ↦ (mem_Iic.1 hs).trans_lt ht.1).mono
    Iic_subset_Iic_union_Ioc

/-- A curve that maps `Icc a s` into `K` and `Ioc s T` outside `K` leaves `K` for good along
`Icc a T`. -/
theorem leavesForGood_Icc_of_mapsTo_of_mapsTo_compl (h : MapsTo γ (Icc a s) K)
    (h' : MapsTo γ (Ioc s T) Kᶜ) : LeavesForGood γ K (Icc a T) :=
  (leavesForGood_of_mapsTo h).extend_Icc (fun _ _ ↦ rfl) h'

/-- A curve that maps `Iic s` into `K` and `Ioc s T` outside `K` leaves `K` for good along
`Iic T`. -/
theorem leavesForGood_Iic_of_mapsTo_of_mapsTo_compl (h : MapsTo γ (Iic s) K)
    (h' : MapsTo γ (Ioc s T) Kᶜ) : LeavesForGood γ K (Iic T) :=
  (leavesForGood_of_mapsTo h).extend_Iic (fun _ _ ↦ rfl) h'

/-- If `γ` leaves `K` for good along an order-connected `D`, then the parameters of `D` that
`γ` sends outside `K` form an order-connected set. -/
theorem LeavesForGood.ordConnected_inter_preimage_compl (h : LeavesForGood γ K D)
    (hD : D.OrdConnected) : (D ∩ γ ⁻¹' Kᶜ).OrdConnected :=
  ⟨fun _ hs _ ht _ hu ↦ ⟨hD.out hs.1 ht.1 hu, h hs.1 (hD.out hs.1 ht.1 hu) hu.1 hs.2⟩⟩

/-- Along an order-connected `D` with greatest element `T`, a curve leaves `K` for good if and
only if the parameters of `D` sent outside `K` form an order-connected set that contains `T`
unless it is empty. -/
theorem leavesForGood_iff_ordConnected (hD : D.OrdConnected) (hT : IsGreatest D T) :
    LeavesForGood γ K D ↔
      (D ∩ γ ⁻¹' Kᶜ).OrdConnected ∧ ((D ∩ γ ⁻¹' Kᶜ).Nonempty → T ∈ D ∩ γ ⁻¹' Kᶜ) := by
  refine ⟨fun h ↦ ⟨h.ordConnected_inter_preimage_compl hD,
    fun ⟨s, hs⟩ ↦ ⟨hT.1, h hs.1 hT.1 (hT.2 hs.1) hs.2⟩⟩, fun ⟨h, hT'⟩ s hs t ht hst hsK ↦ ?_⟩
  exact (h.out ⟨hs, hsK⟩ (hT' ⟨s, hs, hsK⟩) ⟨hst, hT.2 ht⟩).2

variable [TopologicalSpace X]

/-- If a curve `γ`, continuous on an order-connected `D` with greatest element `T`, leaves `K`
for good along `D`, then it maps the parameters of `D` that it sends outside `K` into the
connected component of `Kᶜ` that contains `γ T`. -/
theorem LeavesForGood.mapsTo_connectedComponentIn (h : LeavesForGood γ K D)
    (hD : D.OrdConnected) (hT : IsGreatest D T) (hγ : ContinuousOn γ D) :
    MapsTo γ (D ∩ γ ⁻¹' Kᶜ) (connectedComponentIn Kᶜ (γ T)) := by
  intro t ht
  have hI : Icc t T ⊆ D ∩ γ ⁻¹' Kᶜ :=
    (h.ordConnected_inter_preimage_compl hD).out ht ⟨hT.1, h ht.1 hT.1 (hT.2 ht.1) ht.2⟩
  have hc : IsPreconnected (γ '' Icc t T) :=
    isPreconnected_Icc.image γ (hγ.mono (hI.trans inter_subset_left))
  have hTt : T ∈ Icc t T := ⟨hT.2 ht.1, le_rfl⟩
  exact hc.subset_connectedComponentIn (mem_image_of_mem γ hTt)
    (image_subset_iff.2 fun u hu ↦ (hI hu).2) (mem_image_of_mem γ ⟨le_rfl, hT.2 ht.1⟩)

/-- If a curve `γ`, continuous on an order-connected `D` with greatest element `T`, leaves `K`
for good along `D`, then the points of `γ '' D` in the connected component of `Kᶜ` that contains
`γ T` are the images of the parameters of `D` sent outside `K`. -/
theorem LeavesForGood.image_inter_connectedComponentIn (h : LeavesForGood γ K D)
    (hD : D.OrdConnected) (hT : IsGreatest D T) (hγ : ContinuousOn γ D) :
    γ '' D ∩ connectedComponentIn Kᶜ (γ T) = γ '' (D ∩ γ ⁻¹' Kᶜ) := by
  refine subset_antisymm ?_ (subset_inter (image_mono inter_subset_left)
    (h.mapsTo_connectedComponentIn hD hT hγ).image_subset)
  rintro _ ⟨⟨t, ht, rfl⟩, htW⟩
  exact mem_image_of_mem γ ⟨ht, mem_preimage.2 (connectedComponentIn_subset _ _ htW)⟩

end LeavesForGood

end SymplecticGeometry

end
