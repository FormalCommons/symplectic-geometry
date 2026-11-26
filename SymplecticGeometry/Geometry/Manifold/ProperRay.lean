/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Connected
public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Homogeneity
public import SymplecticGeometry.Topology.FilledHull
import SymplecticGeometry.Analysis.Calculus.Deriv.CriticalValue
import SymplecticGeometry.Geometry.Manifold.NullSet
import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.Segment
import SymplecticGeometry.Topology.Closure
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
* `exists_grow_rays`: one arc for each of finitely many rays. Rays whose built parts
  `γ k '' Iic (T k)` are disjoint, miss `s`, are closed off `s` and leave a closed set `K` for
  good, each ending outside `K` in a component of `Kᶜ` with noncompact closure, are all extended
  past a compact set `L`, with new arcs outside `K ∪ s`. The new built parts are again disjoint,
  miss `s`, are closed off `s` and leave `K` for good. The rays grow one at a time: for the ray
  `γ k`, `exists_diffeomorph_grow_arc` runs in the component `W` of `Kᶜ` through its endpoint,
  with the parts in `W` of the rays ending in `W` as the arcs, each of the order-connected form
  that `LeavesForGood.image_inter_connectedComponentIn` gives. A ray ending elsewhere does not
  meet `W` (`LeavesForGood.apply_mem_connectedComponentIn`). The target outside `L` comes from
  `exists_mem_sdiff_union_iUnion_image_notMem`. The diffeomorphism fixes
  every built part, so only `γ k` changes.
* `exists_mem_forall_exists_mem_Ioo_leavesForGood_filledSublevel`: the next level of the
  exhaustion and the cut of the arcs of a stage. For a continuous `h` and countably many curves
  `α k` from the interior of `filledSublevel h d` to its outside, with `h ∘ α k` differentiable,
  some level `c` in a prescribed nonempty open set below `d` is crossed cleanly by every
  `h ∘ α k` (`exists_mem_Ioo_forall_apply_eq_imp_deriv_ne_zero`), and each `α k` can be cut just
  after its first exit from `filledSublevel h c`
  (`exists_image_Icc_subset_filledSublevel_and_disjoint`), or at once if it starts outside, so
  that the cut arc stays in the interior of `filledSublevel h d` and leaves `filledSublevel h c`
  for good (`exists_mem_Ioo_leavesForGood_filledSublevel`).
* `IsRayStage` and `exists_isRayStage_succ`: one stage of the construction. `IsRayStage` records
  the rays built after stage `j`, one for each point already used of a closed discrete set `P`,
  together with a closed discrete set of obstacles that holds the unused points of `P` and the
  backward limit points of the rays. `exists_isRayStage_succ` passes from stage `j` to stage
  `j + 1`. A new ray starts with a short segment through its point
  (`exists_isSmoothEmbedding_real_of_mem_nhds`), chosen so that `h` stays close to its value at
  the point; the next level is taken in a window of levels that these values avoid, so that each
  segment, being connected, lies inside the next filled sublevel set or outside it
  (`subset_filledSublevel_or_disjoint_of_isPreconnected`). The backward limit point of the
  segment joins the obstacles, so that the built part is closed off them. Then every ray grows
  past a filled sublevel set slightly above level `c j + 2` (`exists_grow_rays`), and the next
  level and the cuts come from
  `exists_mem_forall_exists_mem_Ioo_leavesForGood_filledSublevel`. The built parts then lie in
  `filledSublevel h (c' + 1)` for the new level `c'`, which is what the next stage needs.

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

/-- If a curve `γ`, continuous on an order-connected `D` with greatest element `T`, leaves `K`
for good along `D`, and `γ t` lies in the connected component of `Kᶜ` through `x` for some
`t ∈ D`, then so does `γ T`. -/
theorem LeavesForGood.apply_mem_connectedComponentIn (h : LeavesForGood γ K D)
    (hD : D.OrdConnected) (hT : IsGreatest D T) (hγ : ContinuousOn γ D) {x : X} {t : ℝ}
    (ht : t ∈ D) (hx : γ t ∈ connectedComponentIn Kᶜ x) : γ T ∈ connectedComponentIn Kᶜ x := by
  have h := h.mapsTo_connectedComponentIn hD hT hγ
    ⟨ht, mem_preimage.2 (connectedComponentIn_subset _ _ hx)⟩
  rw [connectedComponentIn_eq hx, ← connectedComponentIn_eq h]
  exact mem_connectedComponentIn (connectedComponentIn_nonempty_iff.mp ⟨_, h⟩)

end LeavesForGood

section GrowRays

variable {ι : Type*} {K L s : Set M} {γ : ι → ℝ → M} {T : ι → ℝ}

/-- One step of the growth of a stage of rays: the ray `γ k` gets an arc `g '' Ioc (T k) T'` in
the component of `Kᶜ` through its endpoint, off `s` and off the built parts of all the rays, that
ends outside `L`. -/
private theorem exists_grow_one_ray [Finite ι] (hE : 1 < Module.rank ℝ E) (hK : IsClosed K)
    (hL : IsCompact L) (hs : IsClosed s) (hd : IsDiscrete s)
    (hγ : ∀ j, IsSmoothEmbedding 𝓘(ℝ) I ∞ (γ j))
    (hdisj : Pairwise (Disjoint on fun j ↦ γ j '' Iic (T j)))
    (hγs : ∀ j, Disjoint (γ j '' Iic (T j)) s)
    (hcl : ∀ j, closure (γ j '' Iic (T j)) \ s ⊆ γ j '' Iic (T j))
    (hR : ∀ j, LeavesForGood (γ j) K (Iic (T j))) (hend : ∀ j, γ j (T j) ∉ K)
    (hnc : ∀ j, ¬ IsCompact (closure (connectedComponentIn Kᶜ (γ j (T j))))) (k : ι) :
    ∃ g : ℝ → M, ∃ T' : ℝ, IsSmoothEmbedding 𝓘(ℝ) I ∞ g ∧ T k < T' ∧
      EqOn g (γ k) (Iic (T k)) ∧ g T' ∉ L ∧
      g '' Ioc (T k) T' ⊆ connectedComponentIn Kᶜ (γ k (T k)) \ (s ∪ ⋃ j, γ j '' Iic (T j)) := by
  have : LocallyConnectedSpace H := I.toHomeomorph.locallyConnectedSpace
  have : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace H M
  set W := connectedComponentIn Kᶜ (γ k (T k))
  have hγc : ∀ j, Continuous (γ j) := fun j ↦ (hγ j).isEmbedding.continuous
  -- The arcs are the parts in `W` of the rays that end in `W`.
  let J : {j // γ j (T j) ∈ W} → Set ℝ := fun j ↦ Iic (T j) ∩ γ j ⁻¹' Kᶜ
  have himage (j : {j // γ j (T j) ∈ W}) : γ j '' J j = γ j '' Iic (T j) ∩ W := by
    have h := (hR j).image_inter_connectedComponentIn ordConnected_Iic isGreatest_Iic
      (hγc j).continuousOn
    rw [← connectedComponentIn_eq j.property] at h
    exact h.symm
  have hmem {j : ι} {x : M} (hx : x ∈ γ j '' Iic (T j)) (hxW : x ∈ W) :
      ∃ i : {j // γ j (T j) ∈ W}, x ∈ γ i '' J i := by
    obtain ⟨t, ht, rfl⟩ := hx
    exact ⟨⟨j, (hR j).apply_mem_connectedComponentIn ordConnected_Iic isGreatest_Iic
      (hγc j).continuousOn ht hxW⟩, by
      rw [himage]; exact ⟨mem_image_of_mem _ ht, hxW⟩⟩
  have hWL : ¬ W ⊆ L := fun h ↦ hnc k (hL.closure_of_subset h)
  obtain ⟨y, hyW, hyL⟩ := exists_mem_sdiff_union_iUnion_image_notMem hE
    hK.isOpen_compl.connectedComponentIn hL.isClosed hWL hd
    (f := fun j : {j // γ j (T j) ∈ W} ↦ γ j)
    (fun j ↦ ((hγ j).contMDiff.mdifferentiable (by simp))) J
  have hk : γ k (T k) ∈ W := mem_connectedComponentIn (hend k)
  obtain ⟨Ψ, -, -, -, -, δ, hδ, hΨγ, heq, hΨy, hU⟩ := exists_diffeomorph_grow_arc hE
    hK.isOpen_compl.connectedComponentIn isPreconnected_connectedComponentIn hs hd
    (f := fun j : {j // γ j (T j) ∈ W} ↦ γ j) (fun j ↦ hγ j)
    (fun j ↦ (hR j).ordConnected_inter_preimage_compl ordConnected_Iic)
    (fun j ↦ ⟨T j, .inl ⟨⟨mem_Iic.2 le_rfl,
      mem_preimage.2 (connectedComponentIn_subset _ _ j.property)⟩,
      fun _ ht ↦ ht.1⟩⟩)
    (fun j ↦ by
      rw [himage]
      exact fun x hx ↦ ⟨hx.2, disjoint_left.1 (hγs j) hx.1⟩)
    (fun a b hab ↦ (hdisj (Subtype.coe_injective.ne hab)).mono
      (image_mono inter_subset_left) (image_mono inter_subset_left))
    (fun j ↦ by
      rw [himage]
      exact fun x ⟨hx, hxW, hxs⟩ ↦
        ⟨hcl j ⟨closure_mono inter_subset_left hx, hxs⟩, hxW⟩)
    (γ := γ k) (i₀ := ⟨k, hk⟩) rfl ⟨⟨mem_Iic.2 le_rfl, hend k⟩, fun _ ht ↦ ht.1⟩
    (fun x ⟨hx, hxW⟩ ↦ mem_iUnion.2 (hmem hx hxW)) hyW
  refine ⟨Ψ ∘ γ k, T k + δ, hΨγ, by linarith, heq, by simpa [hΨy] using hyL, fun x hx ↦ ?_⟩
  obtain ⟨hxW, hx⟩ := hU hx
  refine ⟨hxW, fun h ↦ hx (h.imp id fun h ↦ ?_)⟩
  obtain ⟨j, hj⟩ := mem_iUnion.1 h
  exact mem_iUnion.2 (hmem hj hxW)


variable (I K s γ T) in
/-- The hypotheses on a stage of rays kept while its rays grow one after another. -/
private structure GrowRaysInv : Prop where
  emb : ∀ j, IsSmoothEmbedding 𝓘(ℝ) I ∞ (γ j)
  disj : Pairwise (Disjoint on fun j ↦ γ j '' Iic (T j))
  disj_s : ∀ j, Disjoint (γ j '' Iic (T j)) s
  cl : ∀ j, closure (γ j '' Iic (T j)) \ s ⊆ γ j '' Iic (T j)
  leaves : ∀ j, LeavesForGood (γ j) K (Iic (T j))
  notMem : ∀ j, γ j (T j) ∉ K
  not_isCompact : ∀ j, ¬ IsCompact (closure (connectedComponentIn Kᶜ (γ j (T j))))

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] in
/-- Replacing the ray `γ k` by an extension `g` whose new arc lies in the component of `Kᶜ`
through the endpoint of `γ k`, off `s` and off all the built parts, keeps the invariant. -/
private theorem GrowRaysInv.update [DecidableEq ι] (h : GrowRaysInv I K s γ T) {k : ι}
    {g : ℝ → M} {T' : ℝ} (hg : IsSmoothEmbedding 𝓘(ℝ) I ∞ g) (hT : T k < T')
    (heq : EqOn g (γ k) (Iic (T k)))
    (hN : g '' Ioc (T k) T' ⊆ connectedComponentIn Kᶜ (γ k (T k)) \ (s ∪ ⋃ j, γ j '' Iic (T j))) :
    GrowRaysInv I K s (update γ k g) (update T k T') := by
  have hB : g '' Iic T' = γ k '' Iic (T k) ∪ g '' Ioc (T k) T' := by
    rw [← Iic_union_Ioc_eq_Iic hT.le, image_union, heq.image_eq]
  have hNd (j : ι) : Disjoint (g '' Ioc (T k) T') (γ j '' Iic (T j)) :=
    disjoint_left.2 fun x hx hx' ↦ (hN hx).2 (.inr (mem_iUnion.2 ⟨j, hx'⟩))
  have hW : g T' ∈ connectedComponentIn Kᶜ (γ k (T k)) := (hN ⟨T', ⟨hT, le_rfl⟩, rfl⟩).1
  refine ⟨fun j ↦ ?_, fun a b hab ↦ ?_, fun j ↦ ?_, fun j ↦ ?_, fun j ↦ ?_, fun j ↦ ?_,
    fun j ↦ ?_⟩
  · rcases eq_or_ne j k with rfl | hj
    · simpa using hg
    · simpa [hj] using h.emb j
  · simp only [onFun]
    rcases eq_or_ne a k with rfl | ha
    · rw [update_self, update_self, update_of_ne hab.symm, update_of_ne hab.symm, hB]
      exact disjoint_union_left.2 ⟨h.disj hab, hNd b⟩
    rcases eq_or_ne b k with rfl | hb
    · rw [update_self, update_self, update_of_ne hab, update_of_ne hab, hB]
      exact disjoint_union_right.2 ⟨h.disj hab, (hNd a).symm⟩
    simpa [ha, hb] using h.disj hab
  · rcases eq_or_ne j k with rfl | hj
    · rw [update_self, update_self, hB]
      exact disjoint_union_left.2 ⟨h.disj_s j,
        disjoint_left.2 fun x hx hxs ↦ (hN hx).2 (.inl hxs)⟩
    · simpa [hj] using h.disj_s j
  · rcases eq_or_ne j k with rfl | hj
    · rw [update_self, update_self]
      have hc : closure (g '' Ioc (T j) T') ⊆ g '' Iic T' :=
        (closure_minimal (image_mono Ioc_subset_Icc_self)
          (isCompact_Icc.image hg.contMDiff.continuous).isClosed).trans
          (image_mono fun t ht ↦ mem_Iic.2 ht.2)
      rintro x ⟨hx, hxs⟩
      rw [hB, closure_union] at hx
      exact hx.elim (fun hx ↦ hB ▸ subset_union_left (h.cl j ⟨hx, hxs⟩)) fun hx ↦ hc hx
    · simpa [hj] using h.cl j
  · rcases eq_or_ne j k with rfl | hj
    · rw [update_self, update_self]
      exact (h.leaves j).extend_Iic heq fun x hx ↦
        connectedComponentIn_subset _ _ (hN ⟨x, hx, rfl⟩).1
    · simpa [hj] using h.leaves j
  · rcases eq_or_ne j k with rfl | hj
    · simpa using connectedComponentIn_subset _ _ hW
    · simpa [hj] using h.notMem j
  · rcases eq_or_ne j k with rfl | hj
    · simpa [← connectedComponentIn_eq hW] using h.not_isCompact j
    · simpa [hj] using h.not_isCompact j

/-- **Growing every ray of a stage by one arc.** Let `M` be a finite-dimensional Hausdorff
boundaryless smooth manifold whose model space has rank greater than one, `K ⊆ M` closed,
`L ⊆ M` compact and `s ⊆ M` closed and discrete. For `k` in a finite type let `γ k : ℝ → M` be a
smooth embedding with built part `γ k '' Iic (T k)`, such that the built parts are pairwise
disjoint, miss `s` and are closed off `s`, each ray leaves `K` for good along `Iic (T k)`, and its
endpoint `γ k (T k)` lies outside `K` in a component of `Kᶜ` with noncompact closure. Then there are
smooth embeddings `γ' k` and parameters `T' k > T k` with `γ' k = γ k` on `Iic (T k)`, new arcs
`γ' k '' Ioc (T k) (T' k)` outside `K ∪ s`, new built parts `γ' k '' Iic (T' k)` that are
pairwise disjoint, miss `s` and are closed off `s`, along which each `γ' k` leaves `K` for good,
and endpoints `γ' k (T' k)` outside `L`. -/
theorem exists_grow_rays [Finite ι] (hE : 1 < Module.rank ℝ E) (hK : IsClosed K)
    (hL : IsCompact L) (hs : IsClosed s) (hd : IsDiscrete s)
    (hγ : ∀ k, IsSmoothEmbedding 𝓘(ℝ) I ∞ (γ k))
    (hdisj : Pairwise (Disjoint on fun k ↦ γ k '' Iic (T k)))
    (hγs : ∀ k, Disjoint (γ k '' Iic (T k)) s)
    (hcl : ∀ k, closure (γ k '' Iic (T k)) \ s ⊆ γ k '' Iic (T k))
    (hR : ∀ k, LeavesForGood (γ k) K (Iic (T k))) (hend : ∀ k, γ k (T k) ∉ K)
    (hnc : ∀ k, ¬ IsCompact (closure (connectedComponentIn Kᶜ (γ k (T k))))) :
    ∃ (γ' : ι → ℝ → M) (T' : ι → ℝ), (∀ k, IsSmoothEmbedding 𝓘(ℝ) I ∞ (γ' k)) ∧
      (∀ k, T k < T' k) ∧ (∀ k, EqOn (γ' k) (γ k) (Iic (T k))) ∧
      (∀ k, γ' k '' Ioc (T k) (T' k) ⊆ (K ∪ s)ᶜ) ∧
      Pairwise (Disjoint on fun k ↦ γ' k '' Iic (T' k)) ∧
      (∀ k, Disjoint (γ' k '' Iic (T' k)) s) ∧
      (∀ k, closure (γ' k '' Iic (T' k)) \ s ⊆ γ' k '' Iic (T' k)) ∧
      (∀ k, LeavesForGood (γ' k) K (Iic (T' k))) ∧ ∀ k, γ' k (T' k) ∉ L := by
  classical
  have := Fintype.ofFinite ι
  -- Grow the rays of a finite set `S` of indices, one after another.
  suffices ∀ S : Finset ι, ∃ (γ' : ι → ℝ → M) (T' : ι → ℝ), GrowRaysInv I K s γ' T' ∧ ∀ k,
      (k ∈ S → T k < T' k ∧ EqOn (γ' k) (γ k) (Iic (T k)) ∧
        γ' k '' Ioc (T k) (T' k) ⊆ (K ∪ s)ᶜ ∧ γ' k (T' k) ∉ L) ∧
      (k ∉ S → γ' k = γ k ∧ T' k = T k) by
    obtain ⟨γ', T', h, h'⟩ := this Finset.univ
    exact ⟨γ', T', h.emb, fun k ↦ ((h' k).1 (Finset.mem_univ k)).1,
      fun k ↦ ((h' k).1 (Finset.mem_univ k)).2.1, fun k ↦ ((h' k).1 (Finset.mem_univ k)).2.2.1,
      h.disj, h.disj_s, h.cl, h.leaves, fun k ↦ ((h' k).1 (Finset.mem_univ k)).2.2.2⟩
  intro S
  induction S using Finset.induction_on with
  | empty =>
    exact ⟨γ, T, ⟨hγ, hdisj, hγs, hcl, hR, hend, hnc⟩, fun k ↦
      ⟨fun hk ↦ absurd hk (Finset.notMem_empty k), fun _ ↦ ⟨rfl, rfl⟩⟩⟩
  | insert k S hk ih =>
    obtain ⟨γ', T', h, h'⟩ := ih
    obtain ⟨hγk, hTk⟩ := (h' k).2 hk
    obtain ⟨g, T'', hg, hT, heq, hgL, hN⟩ := exists_grow_one_ray hE hK hL hs hd h.emb h.disj
      h.disj_s h.cl h.leaves h.notMem h.not_isCompact k
    refine ⟨update γ' k g, update T' k T'', h.update hg hT heq hN, fun j ↦ ?_⟩
    rcases eq_or_ne j k with rfl | hj
    · rw [hTk] at hT
      rw [hγk, hTk] at heq
      rw [hTk] at hN
      refine ⟨fun _ ↦ ?_, fun hj ↦ absurd (Finset.mem_insert_self j S) hj⟩
      simp only [update_self]
      refine ⟨hT, heq, fun x hx hxKs ↦ ?_, hgL⟩
      obtain ⟨hxW, hx⟩ := hN hx
      exact hxKs.elim (connectedComponentIn_subset _ _ hxW) fun hxs ↦ hx (.inl hxs)
    · simpa [hj] using h' j

end GrowRays

section CutArcs

variable {X : Type*} [TopologicalSpace X] [R0Space X] [LocallyConnectedSpace X] {h : X → ℝ}

/-- **Cutting a curve just after its first exit.** Let `h : X → ℝ` be continuous, `c < d`, and
`α : ℝ → X` a continuous curve with `α a` in the interior of `filledSublevel h d` and `α b`
outside it, where `a < b`, whose crossings of the level `c` in `[a, b)` are isolated from the
right. Then for some `s ∈ (a, b)` the arc `α '' [a, s]` lies in the interior of
`filledSublevel h d`, its end `α s` lies outside `filledSublevel h c`, and `α` leaves
`filledSublevel h c` for good along `[a, s]`. -/
theorem exists_mem_Ioo_leavesForGood_filledSublevel (hh : Continuous h) {α : ℝ → X}
    (hα : Continuous α) {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (ha : α a ∈ interior (filledSublevel h d)) (hb : α b ∉ filledSublevel h d)
    (hzero : ∀ t ∈ Ico a b, h (α t) = c → ∀ᶠ u in 𝓝[>] t, h (α u) ≠ c) :
    ∃ s ∈ Ioo a b, α '' Icc a s ⊆ interior (filledSublevel h d) ∧
      α s ∉ filledSublevel h c ∧ LeavesForGood α (filledSublevel h c) (Icc a s) := by
  have hcF : filledSublevel h c ⊆ interior (filledSublevel h d) :=
    filledSublevel_subset_interior hh hcd
  by_cases hac : α a ∈ filledSublevel h c
  · -- The curve starts in `filledSublevel h c`: cut it just after its first exit.
    obtain ⟨s, ⟨has, hsb⟩, hIcc, ε₀, hε₀, hdisj⟩ :=
      exists_image_Icc_subset_filledSublevel_and_disjoint hh hα hab hac
        (fun hb' ↦ hb (filledSublevel_mono hcd.le hb')) hzero
    have hs : α ⁻¹' interior (filledSublevel h d) ∩ Iio b ∩ Iic (s + ε₀) ∈ 𝓝[≥] s :=
      Filter.inter_mem (Filter.inter_mem (nhdsWithin_le_nhds (hα.continuousAt.preimage_mem_nhds
        (isOpen_interior.mem_nhds (hcF (hIcc (mem_image_of_mem α ⟨has, le_rfl⟩))))))
        (nhdsWithin_le_nhds (Iio_mem_nhds hsb)))
        (nhdsWithin_le_nhds (Iic_mem_nhds (by linarith)))
    obtain ⟨u, hu, hsub⟩ := mem_nhdsGE_iff_exists_Icc_subset.1 hs
    have hIoc : Ioc s u ⊆ Ioc s (s + ε₀) := fun t ht ↦ ⟨ht.1, (hsub (Ioc_subset_Icc_self ht)).2⟩
    have hout : MapsTo α (Ioc s u) (filledSublevel h c)ᶜ := fun t ht ↦
      disjoint_left.1 hdisj (mem_image_of_mem α (hIoc ht))
    refine ⟨u, ⟨has.trans_lt hu, (hsub ⟨le_of_lt hu, le_rfl⟩).1.2⟩, ?_,
      hout ⟨hu, le_rfl⟩, leavesForGood_Icc_of_mapsTo_of_mapsTo_compl (mapsTo_iff_image_subset.2
        hIcc) hout⟩
    rintro _ ⟨t, ⟨hat, htu⟩, rfl⟩
    rcases le_or_gt t s with hts | hst
    · exact hcF (hIcc (mem_image_of_mem α ⟨hat, hts⟩))
    · exact (hsub ⟨hst.le, htu⟩).1.1
  · -- The curve starts outside `filledSublevel h c`: cut it at once.
    have hs : α ⁻¹' ((filledSublevel h c)ᶜ ∩ interior (filledSublevel h d)) ∩ Iio b ∈ 𝓝[≥] a :=
      Filter.inter_mem (nhdsWithin_le_nhds (hα.continuousAt.preimage_mem_nhds
        (((isClosed_filledSublevel hh).isOpen_compl.inter isOpen_interior).mem_nhds ⟨hac, ha⟩)))
        (nhdsWithin_le_nhds (Iio_mem_nhds hab))
    obtain ⟨u, hu, hsub⟩ := mem_nhdsGE_iff_exists_Icc_subset.1 hs
    have hout : MapsTo α (Icc a u) (filledSublevel h c)ᶜ := fun t ht ↦ (hsub ht).1.1
    refine ⟨u, ⟨hu, (hsub ⟨le_of_lt hu, le_rfl⟩).2⟩, ?_, hout ⟨le_of_lt hu, le_rfl⟩,
      leavesForGood_of_mapsTo_compl hout⟩
    rintro _ ⟨t, ht, rfl⟩
    exact (hsub ht).1.2

/-- **Choosing the next level and cutting the arcs.** Let `h : X → ℝ` be continuous, `d` a level
and `O` a nonempty open set of levels below `d`, for instance `(c₀ + 1, c₀ + 2)` with `d = c₀ + 2`,
less finitely many closed intervals. For countably many continuous curves `α k : ℝ → X` such that
each `h ∘ α k` is differentiable, with `a k < b k`, `α k (a k)` in the interior of
`filledSublevel h d` and `α k (b k)` outside it, there are a level `c ∈ O` and, for each `k`, a
parameter `s ∈ (a k, b k)` such that `α k '' [a k, s]` lies in the interior of
`filledSublevel h d`, `α k s` lies outside `filledSublevel h c`, and `α k` leaves
`filledSublevel h c` for good along `[a k, s]`. -/
theorem exists_mem_forall_exists_mem_Ioo_leavesForGood_filledSublevel (hh : Continuous h)
    {ι : Type*} [Countable ι] {α : ι → ℝ → X} (hα : ∀ k, Continuous (α k))
    (hdiff : ∀ k, Differentiable ℝ (h ∘ α k)) {a b : ι → ℝ} (hab : ∀ k, a k < b k) {d : ℝ}
    (ha : ∀ k, α k (a k) ∈ interior (filledSublevel h d))
    (hb : ∀ k, α k (b k) ∉ filledSublevel h d) {O : Set ℝ} (hO : IsOpen O) (hOn : O.Nonempty)
    (hOd : O ⊆ Iio d) :
    ∃ c ∈ O, ∀ k, ∃ s ∈ Ioo (a k) (b k), α k '' Icc (a k) s ⊆ interior (filledSublevel h d) ∧
      α k s ∉ filledSublevel h c ∧ LeavesForGood (α k) (filledSublevel h c) (Icc (a k) s) := by
  obtain ⟨x, hx⟩ := hOn
  obtain ⟨l, u, hxlu, hluO⟩ := (mem_nhds_iff_exists_Ioo_subset.1 (hO.mem_nhds hx))
  obtain ⟨c, hc, hreg⟩ :=
    exists_mem_Ioo_forall_apply_eq_imp_deriv_ne_zero (fun k ↦ h ∘ α k) (hxlu.1.trans hxlu.2)
  refine ⟨c, hluO hc, fun k ↦ exists_mem_Ioo_leavesForGood_filledSublevel hh (hα k) (hab k)
    (hOd (hluO hc)) (ha k) (hb k) fun t _ htc ↦ ?_⟩
  exact nhdsWithin_mono t (fun _ hu ↦ ne_of_gt hu) ((hreg k t htc (hdiff k t)).2)

end CutArcs

section Stage

variable (I) in
/-- The invariants of the construction of rays from the points of `P` after stage `j`, with
levels `c 0, …, c j`: the rays `γ p`, for `p` in the finite set `S ⊆ P` of points already used,
start at `p`, have pairwise disjoint built parts `γ p '' Iic (T p)` that miss the closed discrete
set `s` of obstacles, contain the unused points of `P`, and whose closures add only points of
`s` outside `P`. Every ray leaves each `filledSublevel h (c i)` for good, ends outside
`filledSublevel h (c j)` and is built inside `filledSublevel h (c j + 1)`; every point of `P` in
`filledSublevel h (c j)` is used. -/
structure IsRayStage (h : M → ℝ) (P s : Set M) (c : ℕ → ℝ) (j : ℕ) (S : Finset M)
    (γ : M → ℝ → M) (T : M → ℝ) : Prop where
  le_level : ∀ i ≤ j, c i ≤ c j
  isClosed : IsClosed s
  isDiscrete : IsDiscrete s
  subset_P : ↑S ⊆ P
  inter_subset : P ∩ filledSublevel h (c j) ⊆ S
  sdiff_subset : P \ S ⊆ s
  emb : ∀ p ∈ S, IsSmoothEmbedding 𝓘(ℝ) I ∞ (γ p)
  apply_zero : ∀ p ∈ S, γ p 0 = p
  nonneg : ∀ p ∈ S, 0 ≤ T p
  disj : (S : Set M).PairwiseDisjoint fun p ↦ γ p '' Iic (T p)
  disj_s : ∀ p ∈ S, Disjoint (γ p '' Iic (T p)) s
  closure_subset : ∀ p ∈ S, closure (γ p '' Iic (T p)) ⊆ γ p '' Iic (T p) ∪ (s \ P)
  leaves : ∀ p ∈ S, ∀ i ≤ j, LeavesForGood (γ p) (filledSublevel h (c i)) (Iic (T p))
  notMem : ∀ p ∈ S, γ p (T p) ∉ filledSublevel h (c j)
  subset : ∀ p ∈ S, γ p '' Iic (T p) ⊆ filledSublevel h (c j + 1)

/-- Short smooth segments through the points of a finite set `N`, each inside a prescribed
neighbourhood of its point, with pairwise disjoint closures. -/
private theorem exists_segments [Nontrivial E] (N : Finset M) {G : M → Set M}
    (hG : ∀ p ∈ N, G p ∈ 𝓝 p) :
    ∃ (σ : M → ℝ → M) (q : M → M), (∀ p ∈ N, IsSmoothEmbedding 𝓘(ℝ) I ∞ (σ p) ∧ σ p 0 = p ∧
      closure (range (σ p)) ⊆ G p ∧ q p ∈ closure (range (σ p)) ∧ q p ∉ range (σ p) ∧
      ∀ T, closure (σ p '' Iic T) = insert (q p) (σ p '' Iic T)) ∧
      (N : Set M).PairwiseDisjoint fun p ↦ closure (range (σ p)) := by
  classical
  obtain ⟨U, hU, hUd⟩ := N.finite_toSet.t2_separation
  have hGU (p : M) (hp : p ∈ N) : G p ∩ U p ∈ 𝓝 p :=
    Filter.inter_mem (hG p hp) ((hU p).2.mem_nhds (hU p).1)
  choose! σ q hσ hσ0 hσV hσq hqσ hσcl using fun p (hp : p ∈ N) ↦
    exists_isSmoothEmbedding_real_of_mem_nhds (I := I) (hGU p hp)
  refine ⟨σ, q, fun p hp ↦ ⟨hσ p hp, hσ0 p hp, (hσV p hp).trans inter_subset_left,
    mem_closure_of_tendsto (hσq p hp) (Filter.Eventually.of_forall mem_range_self), hqσ p hp,
    hσcl p hp⟩, fun a ha b hb hab ↦ ?_⟩
  exact (hUd ha hb hab).mono ((hσV a ha).trans inter_subset_right)
    ((hσV b hb).trans inter_subset_right)

/-- **One stage of the construction of rays.** Let `M` be a finite-dimensional Hausdorff
boundaryless smooth manifold whose model space has rank greater than one, `h : M → ℝ` a `C¹`
function whose filled sublevel sets are compact, and `P` closed and discrete. From the rays of
stage `j` (`IsRayStage`), with levels `c 0, …, c j`, this builds stage `j + 1`: a level
`c' ∈ (c j + 1, c j + 2)` and rays for the levels `update c (j + 1) c'`, with obstacles `s'`
that contain the old obstacles off `P`. Every old ray is extended past its cut parameter by a
piece outside `filledSublevel h (c j)`, a new ray starts at every unused point of `P` in
`filledSublevel h (c j + 2)`, and the built part of a new ray lies outside
`filledSublevel h (c j)`. -/
theorem exists_isRayStage_succ (hE : 1 < Module.rank ℝ E) {h : M → ℝ}
    (hh : ContMDiff I 𝓘(ℝ) 1 h) (hF : ∀ c, IsCompact (filledSublevel h c))
    {P s : Set M} (hP : IsClosed P) (hPd : IsDiscrete P) {c : ℕ → ℝ} {j : ℕ} {S : Finset M}
    {γ : M → ℝ → M} {T : M → ℝ} (hst : IsRayStage I h P s c j S γ T) :
    ∃ c' ∈ Ioo (c j + 1) (c j + 2), ∃ (s' : Set M) (S' : Finset M) (γ' : M → ℝ → M)
      (T' : M → ℝ), IsRayStage I h P s' (update c (j + 1) c') (j + 1) S' γ' T' ∧ S ⊆ S' ∧
      s \ P ⊆ s' ∧ (∀ p ∈ S, T p < T' p ∧ EqOn (γ' p) (γ p) (Iic (T p)) ∧
        γ' p '' Ioc (T p) (T' p) ⊆ (filledSublevel h (c j))ᶜ) ∧
      ∀ p ∈ S', p ∉ S → γ' p '' Iic (T' p) ⊆ (filledSublevel h (c j))ᶜ := by
  classical
  have : Nontrivial E := rank_pos_iff_nontrivial.1 (zero_lt_one.trans hE)
  have hhc : Continuous h := hh.continuous
  have : LocallyConnectedSpace H := I.toHomeomorph.locallyConnectedSpace
  have : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace H M
  set K := filledSublevel h (c j)
  have hKc : IsClosed K := isClosed_filledSublevel hhc
  have hsub_s : ∀ t ⊆ s, IsClosed t := fun t ht ↦
    isClosed_of_subset_discrete_closed ht hst.isDiscrete hst.isClosed
  -- The new points: the unused points of `P` in `filledSublevel h (c j + 2)`.
  have hNfin : ((P ∩ filledSublevel h (c j + 2)) \ (S : Set M)).Finite :=
    (((hF _).inter_left hP).finite (hPd.mono inter_subset_left)).subset sdiff_subset
  set N := hNfin.toFinset
  have hN (p : M) (hp : p ∈ N) : p ∈ P ∧ p ∈ filledSublevel h (c j + 2) ∧ p ∉ S := by
    have h1 := hNfin.mem_toFinset.1 hp; exact ⟨h1.1.1, h1.1.2, h1.2⟩
  have hNK (p : M) (hp : p ∈ N) : p ∉ K := fun hpK ↦
    (hN p hp).2.2 (hst.inter_subset ⟨(hN p hp).1, hpK⟩)
  have hNs (p : M) (hp : p ∈ N) : p ∈ s := hst.sdiff_subset ⟨(hN p hp).1, (hN p hp).2.2⟩
  -- A candidate level `cs`, away from the values of `h` at the new points.
  have hfinv : (h '' (N : Set M)).Finite := N.finite_toSet.image h
  obtain ⟨cs, hcs⟩ : (Ioo (c j + 1) (c j + 2) \ h '' (N : Set M)).Nonempty :=
    ((Ioo_infinite (by linarith)).sdiff hfinv).nonempty
  obtain ⟨r, hr, hrΩ⟩ := Metric.isOpen_iff.1 (isOpen_Ioo.sdiff hfinv.isClosed) cs hcs
  set r' := min r (cs - (c j + 1))
  have hr'r : r' ≤ r := min_le_left _ _
  have hr'c : r' ≤ cs - (c j + 1) := min_le_right _ _
  have hr' : 0 < r' := lt_min hr (by linarith [hcs.1.1])
  have hcs2 : cs < c j + 2 := hcs.1.2
  set d := c j + 2 + r' / 2
  have hd_def : d = c j + 2 + r' / 2 := rfl
  have hO (c' : ℝ) (hc' : c' ∈ Metric.ball cs (r' / 2)) :
      c' ∈ Ioo (c j + 1) (c j + 2) ∧ d ≤ c' + 1 ∧ ∀ p ∈ N, r' / 2 < |h p - c'| := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hc'
    obtain ⟨hc1, hc2⟩ := hc'
    have hball : c' ∈ Metric.ball cs r := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith
    refine ⟨(hrΩ hball).1, show c j + 2 + r' / 2 ≤ c' + 1 by linarith, fun p hp ↦ ?_⟩
    have h0 : r ≤ |h p - cs| := not_lt.1 fun hlt ↦
      (hrΩ (show h p ∈ Metric.ball cs r by rwa [Metric.mem_ball, Real.dist_eq])).2 ⟨p, hp, rfl⟩
    have h1 : |h p - cs| ≤ |h p - c'| + |c' - cs| := abs_sub_le (h p) c' cs
    have h2 : |c' - cs| < r' / 2 := abs_lt.2 ⟨by linarith, by linarith⟩
    linarith
  -- The closures of the old built parts.
  set C := ⋃ p ∈ S, closure (γ p '' Iic (T p))
  have hC : IsClosed C := isClosed_biUnion_finset fun _ _ ↦ isClosed_closure
  have hbC (p : M) (hp : p ∈ S) : γ p '' Iic (T p) ⊆ C := fun x hx ↦
    mem_iUnion₂.2 ⟨p, hp, subset_closure hx⟩
  have hNC (p : M) (hp : p ∈ N) : p ∉ C := by
    intro hpC
    obtain ⟨k, hk, hpk⟩ := mem_iUnion₂.1 hpC
    rcases hst.closure_subset k hk hpk with h1 | h1
    · exact disjoint_left.1 (hst.disj_s k hk) h1 (hNs p hp)
    · exact h1.2 (hN p hp).1
  have hPC (x : M) (hx : x ∈ P) (hxC : x ∉ C) (hxs : x ∉ s) : False := by
    by_cases hxS : x ∈ S
    · exact hxC (hbC x hxS ⟨0, mem_Iic.2 (hst.nonneg x hxS), hst.apply_zero x hxS⟩)
    · exact hxs (hst.sdiff_subset ⟨hx, hxS⟩)
  -- The neighbourhoods in which the new segments are taken.
  set G : M → Set M := fun p ↦ Kᶜ ∩ Cᶜ ∩ (s \ {p})ᶜ ∩ h ⁻¹' Metric.ball (h p) (r' / 2) ∩
    interior (filledSublevel h d)
  have hG (p : M) (hp : p ∈ N) : G p ∈ 𝓝 p := by
    refine IsOpen.mem_nhds ?_ ⟨⟨⟨⟨hNK p hp, hNC p hp⟩, fun h1 ↦ h1.2 rfl⟩,
      (Metric.mem_ball_self (half_pos hr') : h p ∈ _)⟩,
      filledSublevel_subset_interior hhc (show c j + 2 < c j + 2 + r' / 2 by linarith)
        (hN p hp).2.1⟩
    exact ((((hKc.isOpen_compl.inter hC.isOpen_compl).inter
      (hsub_s _ sdiff_subset).isOpen_compl).inter (Metric.isOpen_ball.preimage hhc))).inter
      isOpen_interior
  obtain ⟨σ, q, hσ, hσd⟩ := exists_segments (I := I) N hG
  have hqG (p : M) (hp : p ∈ N) : q p ∈ G p := (hσ p hp).2.2.1 (hσ p hp).2.2.2.1
  have hqs (p : M) (hp : p ∈ N) : q p ∉ s := fun hqs ↦ (hqG p hp).1.1.2
    ⟨hqs, fun hqp ↦ (hσ p hp).2.2.2.2.1 ⟨0, (hσ p hp).2.1.trans hqp.symm⟩⟩
  have hqP (p : M) (hp : p ∈ N) : q p ∉ P := fun hqP ↦
    hPC (q p) hqP (hqG p hp).1.1.1.2 (hqs p hp)
  -- The rays before the growth: the old ones and the new segments.
  set S1 := S ∪ N
  set s1 := (s \ N) ∪ q '' N
  set γ1 : M → ℝ → M := fun p ↦ if p ∈ S then γ p else σ p
  set T1 : M → ℝ := fun p ↦ if p ∈ S then T p else 0
  have hold (p : M) (hp : p ∈ S) : γ1 p = γ p ∧ T1 p = T p := by simp [γ1, T1, hp]
  have hnew (p : M) (hp : p ∈ N) : γ1 p = σ p ∧ T1 p = 0 := by
    simp [γ1, T1, (hN p hp).2.2]
  have hcases (k : S1) : k.val ∈ S ∨ k.val ∈ N := Finset.mem_union.1 k.property
  have hsN : s \ P ⊆ s1 := fun x hx ↦ .inl ⟨hx.1, fun hxN ↦ hx.2 (hN x hxN).1⟩
  have hnewG (p : M) (hp : p ∈ N) : γ1 p '' Iic (T1 p) ⊆ G p := by
    rw [(hnew p hp).1]
    exact (image_subset_range _ _).trans (subset_closure.trans (hσ p hp).2.2.1)
  have hs1 : IsClosed s1 := (hsub_s _ sdiff_subset).union (N.finite_toSet.image q).isClosed
  have hd1 : IsDiscrete s1 := (hst.isDiscrete.mono sdiff_subset).union
    (N.finite_toSet.image q).isDiscrete (hsub_s _ sdiff_subset) (N.finite_toSet.image q).isClosed
  have hγ1 (k : S1) : IsSmoothEmbedding 𝓘(ℝ) I ∞ (γ1 k) := by
    rcases hcases k with hk | hk
    · rw [(hold _ hk).1]; exact hst.emb _ hk
    · rw [(hnew _ hk).1]; exact (hσ _ hk).1
  have hdisj1 : Pairwise (Disjoint on fun k : S1 ↦ γ1 k '' Iic (T1 k)) := by
    have hon (a b : S1) (ha : a.val ∈ S) (hb : b.val ∈ N) :
        Disjoint (γ1 a '' Iic (T1 a)) (γ1 b '' Iic (T1 b)) :=
      disjoint_left.2 fun x hxa hxb ↦ (hnewG _ hb hxb).1.1.1.2
        (hbC _ ha (by rwa [(hold _ ha).1, (hold _ ha).2] at hxa))
    intro a b hab
    have hab' : a.val ≠ b.val := Subtype.coe_injective.ne hab
    rcases hcases a with ha | ha <;> rcases hcases b with hb | hb
    · simp only [onFun, (hold _ ha).1, (hold _ ha).2, (hold _ hb).1, (hold _ hb).2]
      exact hst.disj ha hb hab'
    · exact hon a b ha hb
    · exact (hon b a hb ha).symm
    · simp only [onFun, (hnew _ ha).1, (hnew _ ha).2, (hnew _ hb).1, (hnew _ hb).2]
      exact (hσd ha hb hab').mono ((image_subset_range _ _).trans subset_closure)
        ((image_subset_range _ _).trans subset_closure)
  have hdisj_s1 (k : S1) : Disjoint (γ1 k '' Iic (T1 k)) s1 := by
    rcases hcases k with hk | hk
    · rw [(hold _ hk).1, (hold _ hk).2]
      refine disjoint_union_right.2 ⟨(hst.disj_s _ hk).mono_right sdiff_subset, ?_⟩
      refine disjoint_left.2 fun x hx ⟨p, hp, hpx⟩ ↦ (hqG p hp).1.1.1.2 ?_
      rw [hpx]; exact hbC _ hk hx
    · refine disjoint_left.2 fun x hx hxs1 ↦ ?_
      have hxG := hnewG _ hk hx
      rw [(hnew _ hk).1] at hx
      rcases hxs1 with ⟨hxs, hxN⟩ | ⟨p', hp', rfl⟩
      · refine hxG.1.1.2 ⟨hxs, fun hxp ↦ hxN ?_⟩
        rw [mem_singleton_iff.1 hxp]; exact hk
      · by_cases hpp : p' = k.val
        · subst hpp; exact (hσ _ hk).2.2.2.2.1 (image_subset_range _ _ hx)
        · exact disjoint_left.1 (hσd hp' hk hpp) (hσ p' hp').2.2.2.1
            (subset_closure (image_subset_range _ _ hx))
  have hcl1 (k : S1) : closure (γ1 k '' Iic (T1 k)) ⊆ γ1 k '' Iic (T1 k) ∪ (s1 \ P) := by
    rcases hcases k with hk | hk
    · rw [(hold _ hk).1, (hold _ hk).2]
      exact (hst.closure_subset _ hk).trans (union_subset_union_right _ fun x hx ↦
        ⟨hsN hx, hx.2⟩)
    · rw [(hnew _ hk).1, (hnew _ hk).2, (hσ _ hk).2.2.2.2.2 0, insert_eq, union_comm]
      exact union_subset_union_right _ (singleton_subset_iff.2
        ⟨.inr ⟨k, hk, rfl⟩, hqP _ hk⟩)
  have hR1 (k : S1) (i : ℕ) (hi : i ≤ j) :
      LeavesForGood (γ1 k) (filledSublevel h (c i)) (Iic (T1 k)) := by
    rcases hcases k with hk | hk
    · rw [(hold _ hk).1, (hold _ hk).2]; exact hst.leaves _ hk i hi
    · exact leavesForGood_of_mapsTo_compl fun t ht hti ↦ (hnewG _ hk ⟨t, ht, rfl⟩).1.1.1.1
        (filledSublevel_mono (hst.le_level i hi) hti)
  have hend1 (k : S1) : γ1 k (T1 k) ∉ K := by
    rcases hcases k with hk | hk
    · rw [(hold _ hk).1, (hold _ hk).2]; exact hst.notMem _ hk
    · rw [(hnew _ hk).1, (hnew _ hk).2, (hσ _ hk).2.1]; exact hNK _ hk
  -- Grow every ray past `filledSublevel h d`.
  obtain ⟨γ2, T2, hγ2, hT12, heq, hout, hdisj2, hs2, -, -, hL2⟩ :=
    exists_grow_rays (γ := fun k : S1 ↦ γ1 k) (T := fun k : S1 ↦ T1 k) hE hKc (hF d) hs1 hd1
      hγ1 hdisj1 hdisj_s1 (fun k x hx ↦ (hcl1 k hx.1).resolve_right fun h ↦ hx.2 h.1)
      (fun k ↦ hR1 k j le_rfl) hend1
      (fun k ↦ not_isCompact_closure_connectedComponentIn_compl_filledSublevel (hend1 k))
  have hstart (k : S1) : γ2 k (T1 k) = γ1 k (T1 k) := heq k (mem_Iic.2 le_rfl)
  have hdj : c j + 1 < d := by linarith
  have hint (k : S1) : γ1 k (T1 k) ∈ interior (filledSublevel h d) := by
    rcases hcases k with hk | hk
    · rw [(hold _ hk).1, (hold _ hk).2]
      exact filledSublevel_subset_interior hhc hdj
        (hst.subset _ hk ⟨T k, mem_Iic.2 le_rfl, rfl⟩)
    · rw [(hnew _ hk).1, (hnew _ hk).2, (hσ _ hk).2.1]
      exact filledSublevel_subset_interior hhc (by linarith) (hN _ hk).2.1
  -- Choose the next level and cut every arc just after its first exit.
  obtain ⟨c', hc'O, hcut⟩ := exists_mem_forall_exists_mem_Ioo_leavesForGood_filledSublevel hhc
    (α := γ2) (fun k ↦ (hγ2 k).isEmbedding.continuous)
    (fun k ↦ ((hh.comp ((hγ2 k).contMDiff.of_le (by simp))).mdifferentiable
      (by simp)).differentiable) hT12 (d := d) (fun k ↦ hstart k ▸ hint k) hL2
    Metric.isOpen_ball ⟨cs, Metric.mem_ball_self (half_pos hr')⟩ fun x hx ↦ by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hx
      exact mem_Iio.2 (by linarith)
  obtain ⟨hc'I, hdc', hc'N⟩ := hO c' hc'O
  choose u hu hucut hunot hulv using hcut
  have hc'1 : c j + 1 ≤ c' := hc'I.1.le
  have hFd : interior (filledSublevel h d) ⊆ filledSublevel h (c' + 1) :=
    interior_subset.trans (filledSublevel_mono hdc')
  have himg1 (k : S1) : γ2 k '' Iic (T1 k) = γ1 k '' Iic (T1 k) := (heq k).image_eq
  have hsplit (k : S1) : Iic (u k) = Iic (T1 k) ∪ Icc (T1 k) (u k) :=
    (Iic_union_Icc_eq_Iic (hu k).1.le).symm
  have hT1 (k : S1) : 0 ≤ T1 k := by
    rcases hcases k with hk | hk
    · rw [(hold _ hk).2]; exact hst.nonneg _ hk
    · rw [(hnew _ hk).2]
  have hzero (k : S1) : γ2 k 0 = k := by
    rw [heq k (mem_Iic.2 (hT1 k))]
    rcases hcases k with hk | hk
    · rw [(hold _ hk).1]; exact hst.apply_zero _ hk
    · rw [(hnew _ hk).1]; exact (hσ _ hk).2.1
  have hcl2 (k : S1) : closure (γ2 k '' Iic (u k)) ⊆ γ2 k '' Iic (u k) ∪ (s1 \ P) := by
    rw [hsplit, image_union, closure_union, himg1,
      (isCompact_Icc.image (hγ2 k).isEmbedding.continuous).isClosed.closure_eq]
    exact union_subset ((hcl1 k).trans (union_subset_union_left _ subset_union_left))
      (subset_union_right.trans subset_union_left)
  have hlast (k : S1) : LeavesForGood (γ2 k) (filledSublevel h c') (Iic (u k)) := by
    have hseg : MapsTo (γ2 k) (Iic (T1 k)) (filledSublevel h c') ∨
        MapsTo (γ2 k) (Iic (T1 k)) (filledSublevel h c')ᶜ := by
      rcases hcases k with hk | hk
      · refine .inl fun t ht ↦ ?_
        rw [heq k ht]
        rw [(hold _ hk).2] at ht
        rw [(hold _ hk).1]
        exact filledSublevel_mono hc'1 (hst.subset _ hk ⟨t, ht, rfl⟩)
      · have hcon : IsPreconnected (closure (range (σ k))) :=
          (isPreconnected_range (hσ _ hk).1.isEmbedding.continuous).closure
        rcases subset_filledSublevel_or_disjoint_of_isPreconnected hhc (c := c') hcon
            (fun x hx hxc ↦ by
            have hxG := (hσ _ hk).2.2.1 hx
            have h1 := hxG.1.2
            rw [mem_preimage, Metric.mem_ball, Real.dist_eq, hxc] at h1
            have h2 := hc'N _ hk
            rw [abs_sub_comm] at h1
            linarith) with h' | h'
        · refine .inl fun t ht ↦ ?_
          rw [heq k ht, (hnew _ hk).1]
          exact h' (subset_closure (mem_range_self t))
        · refine .inr fun t ht ↦ ?_
          rw [heq k ht, (hnew _ hk).1]
          exact disjoint_left.1 h' (subset_closure (mem_range_self t))
    rcases hseg with h' | h'
    · exact (hulv k).Iic_of_mapsTo_Iic h'
    · refine leavesForGood_of_mapsTo_compl fun t ht ↦ ?_
      rcases le_or_gt t (T1 k) with htT | htT
      · exact h' htT
      · exact hulv k ⟨le_rfl, (hu k).1.le⟩ ⟨htT.le, ht⟩ htT.le (h' (mem_Iic.2 le_rfl))
  have hR2' (k : S1) (i : ℕ) (hi : i ≤ j) :
      LeavesForGood (γ2 k) (filledSublevel h (c i)) (Iic (u k)) :=
    ((hR1 k i hi).extend_Iic (heq k) fun t ht hti ↦ hout k ⟨t, ht, rfl⟩
      (.inl (filledSublevel_mono (hst.le_level i hi) hti))).mono (Iic_subset_Iic.2 (hu k).2.le)
  have hsub2 (k : S1) : γ2 k '' Iic (u k) ⊆ filledSublevel h (c' + 1) := by
    rw [hsplit, image_union, himg1]
    refine union_subset ?_ ((hucut k).trans hFd)
    rcases hcases k with hk | hk
    · rw [(hold _ hk).1, (hold _ hk).2]
      exact (hst.subset _ hk).trans (filledSublevel_mono (by linarith))
    · exact (hnewG _ hk).trans (inter_subset_right.trans hFd)
  -- The rays of the next stage.
  set γ' : M → ℝ → M := fun p ↦ if hp : p ∈ S1 then γ2 ⟨p, hp⟩ else γ p
  set T' : M → ℝ := fun p ↦ if hp : p ∈ S1 then u ⟨p, hp⟩ else T p
  have hall (p : M) (hp : p ∈ S1) : γ' p = γ2 ⟨p, hp⟩ ∧ T' p = u ⟨p, hp⟩ :=
    ⟨by simp [γ', hp], by simp [T', hp]⟩
  refine ⟨c', hc'I, s1, S1, γ', T', ⟨fun i hi ↦ ?_, hs1, hd1, ?_, ?_, ?_, fun p hp ↦ ?_,
    fun p hp ↦ ?_, fun p hp ↦ ?_, fun a ha b hb hab ↦ ?_, fun p hp ↦ ?_, fun p hp ↦ ?_,
    fun p hp i hi ↦ ?_, fun p hp ↦ ?_, fun p hp ↦ ?_⟩, Finset.subset_union_left, hsN,
    fun p hp ↦ ?_, fun p hp hpS ↦ ?_⟩
  · rw [update_self]
    rcases Nat.lt_or_ge i (j + 1) with hi' | hi'
    · rw [update_of_ne hi'.ne]
      exact (hst.le_level i (Nat.lt_succ_iff.1 hi')).trans (by linarith)
    · rw [le_antisymm hi hi', update_self]
  · intro x hx
    rcases Finset.mem_union.1 hx with hx | hx
    · exact hst.subset_P hx
    · exact (hN x hx).1
  · rw [update_self]
    rintro x ⟨hxP, hxF⟩
    by_cases hxS : x ∈ S
    · exact Finset.mem_union_left _ hxS
    · exact Finset.mem_union_right _
        (hNfin.mem_toFinset.2 ⟨⟨hxP, filledSublevel_mono hc'I.2.le hxF⟩, hxS⟩)
  · rintro x ⟨hxP, hxS1⟩
    exact .inl ⟨hst.sdiff_subset ⟨hxP, fun h ↦ hxS1 (Finset.mem_union_left _ h)⟩,
      fun h ↦ hxS1 (Finset.mem_union_right _ h)⟩
  · rw [(hall p hp).1]; exact hγ2 _
  · rw [(hall p hp).1]; exact hzero _
  · rw [(hall p hp).2]; exact (hT1 _).trans (hu _).1.le
  · simp only [onFun, (hall a ha).1, (hall a ha).2, (hall b hb).1, (hall b hb).2]
    exact (hdisj2 fun h ↦ hab (congrArg Subtype.val h)).mono
      (image_mono (Iic_subset_Iic.2 (hu _).2.le)) (image_mono (Iic_subset_Iic.2 (hu _).2.le))
  · rw [(hall p hp).1, (hall p hp).2]
    exact (hs2 _).mono_left (image_mono (Iic_subset_Iic.2 (hu _).2.le))
  · rw [(hall p hp).1, (hall p hp).2]; exact hcl2 _
  · rw [(hall p hp).1, (hall p hp).2]
    rcases Nat.lt_or_ge i (j + 1) with hi' | hi'
    · rw [update_of_ne hi'.ne]; exact hR2' _ i (Nat.lt_succ_iff.1 hi')
    · rw [le_antisymm hi hi', update_self]; exact hlast _
  · rw [(hall p hp).1, (hall p hp).2, update_self]; exact hunot _
  · rw [(hall p hp).1, (hall p hp).2, update_self]; exact hsub2 _
  · have hp1 : p ∈ S1 := Finset.mem_union_left _ hp
    rw [(hall p hp1).1, (hall p hp1).2]
    have hT := (hold p hp).2
    refine ⟨hT ▸ (hu ⟨p, hp1⟩).1, fun t ht ↦ ?_, ?_⟩
    · rw [heq ⟨p, hp1⟩ (by rwa [← hT] at ht)]
      exact congrFun (hold p hp).1 t
    · rintro _ ⟨t, ht, rfl⟩ hK
      exact hout ⟨p, hp1⟩ ⟨t, ⟨hT ▸ ht.1, ht.2.trans (hu _).2.le⟩, rfl⟩ (.inl hK)
  · have hpN : p ∈ N := (Finset.mem_union.1 hp).resolve_left hpS
    rw [(hall p hp).1, (hall p hp).2, ← Iic_union_Ioc_eq_Iic (hu ⟨p, hp⟩).1.le, image_union,
      himg1]
    refine union_subset (fun x hx ↦ (hnewG _ hpN hx).1.1.1.1) ?_
    rintro _ ⟨t, ht, rfl⟩ hK
    exact hout ⟨p, hp⟩ ⟨t, ⟨ht.1, ht.2.trans (hu _).2.le⟩, rfl⟩ (.inl hK)

end Stage

end SymplecticGeometry

end
