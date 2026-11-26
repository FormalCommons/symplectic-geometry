/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Connected
public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Homogeneity
public import SymplecticGeometry.Topology.FilledHull
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic
import SymplecticGeometry.Analysis.Calculus.Deriv.CriticalValue
import SymplecticGeometry.Geometry.Manifold.Diffeomorph.Real
import SymplecticGeometry.Geometry.Manifold.NullSet
import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.Segment
import SymplecticGeometry.Order.Interval.Set.Image
import SymplecticGeometry.Topology.Closure
import SymplecticGeometry.Topology.Instances.Real
import TauCeti.Geometry.Manifold.SmoothEmbedding.Diffeomorph
import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.Limit
import TauCeti.Geometry.Manifold.Exhaustion
import SymplecticGeometry.Analysis.SpecificLimits.Basic

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
  backward limit points of the rays; `isRayStage_zero` is the start, with no rays.
  `exists_isRayStage_succ` passes from stage `j` to stage `j + 1`. New rays start with short
  segments through their points (`exists_isSmoothEmbedding_real_pairwiseDisjoint_of_mem_nhds`),
  chosen so that `h` stays close to its value at the point; the next level is taken in a window
  of levels that these values avoid (`Set.Finite.exists_ball_subset_Ioo_forall_lt_abs_sub`), so
  that each segment, being connected, lies inside the next filled sublevel set or outside it
  (`subset_filledSublevel_or_disjoint_of_isPreconnected`); then `LeavesForGood.Iic_of_mapsTo_Iic`
  or `LeavesForGood.Iic_of_mapsTo_compl_Iic` gives the invariant for the new level. The
  backward limit point of a segment joins the obstacles, so that the built part is closed off
  them. Then every ray grows past a filled sublevel set slightly above level `c j + 2`
  (`exists_grow_rays`), since a new point may lie on the frontier of
  `filledSublevel h (c j + 2)`, and the next level and the cuts come from
  `exists_mem_forall_exists_mem_Ioo_leavesForGood_filledSublevel`. The built parts then lie in
  `filledSublevel h (c' + 1)` for the new level `c'`, which is what the next stage needs.
  Last, each ray is reparametrized by an increasing diffeomorphism of `ℝ` that fixes the old
  part and slows the new arc down (`IsRayStage.exists_add_one_le_of_lt`, from
  `Real.exists_diffeomorph_strictMono_eqOn_Iic`),
  which keeps the stage (`IsRayStage.comp_diffeomorph`, by `LeavesForGood.comp_monotone`) and
  makes every old cut parameter grow by at least one. The limit of the rays needs this, since
  cut parameters that only increase may stay bounded.
* `exists_seq_isRayStage`: the stages for all `k`, by iterating `exists_isRayStage_succ` from a
  stage `0`, with one sequence of levels (`IsRayStage.congr_level`).
* `exists_rays`: rays from a closed discrete set `P` avoiding a closed discrete set `Q` disjoint
  from it, on a σ-compact manifold of dimension at least two with no compact component. The
  function `h` is a nonnegative proper smooth function (Tau Ceti's
  `TauCeti.exists_contMDiffMap_isProperMap_nonneg`), whose filled sublevel sets are compact and,
  below level `0`, empty, so that the stages start with no rays and with obstacles `P ∪ Q`. Since
  the levels grow by more than one at each step, their filled sublevel sets form a compact
  exhaustion, and the ray of `p` is the limit of its stages from the first stage that uses `p`
  (`TauCeti.SmoothEmbedding.exists_eqOn_Iic_tendsto_cocompact_of_ge`). A ray meets the set of a
  stage only if that stage already uses its point, which gives local finiteness.

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

/-- Reparametrizing by a monotone map `f : ℝ → ℝ` keeps a curve leaving `K` for good, along the
preimage of the parameters. -/
theorem LeavesForGood.comp_monotone {f : ℝ → ℝ} (h : LeavesForGood γ K D) (hf : Monotone f) :
    LeavesForGood (γ ∘ f) K (f ⁻¹' D) :=
  fun _ hs _ ht hst ↦ h hs ht (hf hst)

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

/-- A curve that maps `Iic a` outside `K` and leaves `K` for good along `Icc a s` maps `Iic s`
outside `K`, so it leaves `K` for good along `Iic s`. -/
theorem LeavesForGood.Iic_of_mapsTo_compl_Iic (h : LeavesForGood γ K (Icc a s))
    (h' : MapsTo γ (Iic a) Kᶜ) : LeavesForGood γ K (Iic s) :=
  leavesForGood_of_mapsTo_compl fun t ht ↦ (le_or_gt t a).elim (fun hta ↦ h' hta) fun hat ↦
    h ⟨le_rfl, hat.le.trans ht⟩ ⟨hat.le, ht⟩ hat.le (h' (mem_Iic.2 le_rfl))

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
levels `c 0, …, c j` that are at most `c j`. The closed discrete set `s` of obstacles contains
the points of `P` outside the finite set `S ⊆ P` of points already used, and every point of `P`
in `filledSublevel h (c j)` is used. For `p ∈ S` the ray `γ p` is a smooth embedding with
`γ p 0 = p` and a cut parameter `T p ≥ 0`; the built parts `γ p '' Iic (T p)` are pairwise
disjoint and miss `s`, and the closure of each adds to it only points of `s` outside `P`. Each
ray leaves every `filledSublevel h (c i)`, `i ≤ j`, for good along `Iic (T p)`, ends outside
`filledSublevel h (c j)` and has its built part in `filledSublevel h (c j + 1)`. -/
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

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] [IsManifold I ∞ M] in
/-- The stage with no rays yet: it holds at level `c 0` when no point of `P` lies in
`filledSublevel h (c 0)` and the closed discrete set of obstacles `s` contains `P`. -/
theorem isRayStage_zero {h : M → ℝ} {P s : Set M} {c : ℕ → ℝ} (hs : IsClosed s)
    (hsd : IsDiscrete s) (hPs : P ⊆ s) (hP : Disjoint P (filledSublevel h (c 0)))
    (γ : M → ℝ → M) (T : M → ℝ) : IsRayStage I h P s c 0 ∅ γ T where
  le_level i hi := by rw [Nat.le_zero.1 hi]
  isClosed := hs
  isDiscrete := hsd
  subset_P := by simp
  inter_subset x hx := (disjoint_left.1 hP hx.1 hx.2).elim
  sdiff_subset := sdiff_subset.trans hPs
  emb := by simp
  apply_zero := by simp
  nonneg := by simp
  disj := by simp
  disj_s := by simp
  closure_subset := by simp
  leaves := by simp
  notMem := by simp
  subset := by simp

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] [IsManifold I ∞ M] in
/-- Reparametrizing the rays of a stage by increasing diffeomorphisms `e p` of `ℝ` that fix `0`
gives a stage, with the cut parameters `T' p` that `e p` sends to the old ones `T p`: the
built parts `γ p '' Iic (T p)` stay the same. -/
theorem IsRayStage.comp_diffeomorph {h : M → ℝ} {P s : Set M} {c : ℕ → ℝ} {j : ℕ}
    {S : Finset M} {γ : M → ℝ → M} {T : M → ℝ} (hst : IsRayStage I h P s c j S γ T)
    (e : M → ℝ ≃ₘ⟮𝓘(ℝ), 𝓘(ℝ)⟯ ℝ) (he : ∀ p ∈ S, StrictMono (e p)) (he₀ : ∀ p ∈ S, e p 0 = 0)
    {T' : M → ℝ} (hT' : ∀ p ∈ S, e p (T' p) = T p) :
    IsRayStage I h P s c j S (fun p ↦ γ p ∘ e p) T' := by
  have himg (p : M) (hp : p ∈ S) : (γ p ∘ e p) '' Iic (T' p) = γ p '' Iic (T p) := by
    rw [image_comp, (he p hp).image_Iic_of_surjective (e p).surjective, hT' p hp]
  refine ⟨hst.le_level, hst.isClosed, hst.isDiscrete, hst.subset_P, hst.inter_subset,
    hst.sdiff_subset, fun p hp ↦ TauCeti.isSmoothEmbedding_comp_diffeomorph (e p) (hst.emb p hp),
    fun p hp ↦ ?_, fun p hp ↦ ?_, fun a ha b hb hab ↦ ?_, fun p hp ↦ ?_, fun p hp ↦ ?_,
    fun p hp i hi ↦ ?_, fun p hp ↦ ?_, fun p hp ↦ ?_⟩
  · rw [comp_apply, he₀ p hp, hst.apply_zero p hp]
  · rw [← (he p hp).le_iff_le, he₀ p hp, hT' p hp]
    exact hst.nonneg p hp
  · simp only [onFun, himg a ha, himg b hb]
    exact hst.disj ha hb hab
  · rw [himg p hp]; exact hst.disj_s p hp
  · rw [himg p hp]; exact hst.closure_subset p hp
  · have hpre : e p ⁻¹' Iic (T p) = Iic (T' p) := by
      ext t; rw [mem_preimage, mem_Iic, mem_Iic, ← hT' p hp, (he p hp).le_iff_le]
    exact hpre ▸ (hst.leaves p hp i hi).comp_monotone (he p hp).monotone
  · rw [comp_apply, hT' p hp]; exact hst.notMem p hp
  · rw [himg p hp]; exact hst.subset p hp

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] [IsManifold I ∞ M] in
/-- Slowing down the rays of a stage: if `0 ≤ T₀ p < T p` for every ray, then reparametrizing
each ray `γ p` on the line gives a stage, with the same levels, points and obstacles, and with
cut parameters `T' p ≥ T₀ p + 1`. The new ray agrees with `γ p` on `Iic (T₀ p)`, and runs
through the arc `γ p '' Ioc (T₀ p) (T p)` along `Ioc (T₀ p) (T' p)`, so that its built part is
that of `γ p`. -/
theorem IsRayStage.exists_add_one_le_of_lt {h : M → ℝ} {P s : Set M} {c : ℕ → ℝ} {j : ℕ}
    {S : Finset M} {γ : M → ℝ → M} {T : M → ℝ} (hst : IsRayStage I h P s c j S γ T)
    {T₀ : M → ℝ} (hT₀ : ∀ p ∈ S, 0 ≤ T₀ p) (hT : ∀ p ∈ S, T₀ p < T p) :
    ∃ (γ' : M → ℝ → M) (T' : M → ℝ), IsRayStage I h P s c j S γ' T' ∧
      ∀ p ∈ S, T₀ p + 1 ≤ T' p ∧ EqOn (γ' p) (γ p) (Iic (T₀ p)) ∧
        γ' p '' Ioc (T₀ p) (T' p) = γ p '' Ioc (T₀ p) (T p) ∧
        γ' p '' Iic (T' p) = γ p '' Iic (T p) := by
  classical
  -- An increasing diffeomorphism `e p` of `ℝ` that fixes `Iic (T₀ p)` and sends `T p + 1`
  -- to `T p`.
  have hφ (p : M) : ∃ e : ℝ ≃ₘ⟮𝓘(ℝ), 𝓘(ℝ)⟯ ℝ, p ∈ S →
      StrictMono e ∧ EqOn e id (Iic (T₀ p)) ∧ e (T p + 1) = T p := by
    by_cases hp : p ∈ S
    · obtain ⟨e, he⟩ := Real.exists_diffeomorph_strictMono_eqOn_Iic (hT p hp)
        (le_add_of_nonneg_right zero_le_one)
      exact ⟨e, fun _ ↦ he⟩
    · exact ⟨Diffeomorph.refl _ _ _, fun h ↦ (hp h).elim⟩
  choose e he using hφ
  refine ⟨fun p ↦ γ p ∘ e p, fun p ↦ T p + 1,
    hst.comp_diffeomorph e (fun p hp ↦ (he p hp).1)
      (fun p hp ↦ (he p hp).2.1 (mem_Iic.2 (hT₀ p hp))) fun p hp ↦ (he p hp).2.2,
    fun p hp ↦ ⟨by linarith [hT p hp], fun t ht ↦ congrArg (γ p) ((he p hp).2.1 ht), ?_, ?_⟩⟩
  · rw [image_comp, (he p hp).1.image_Ioc_of_surjective (e p).surjective,
      (he p hp).2.1 (mem_Iic.2 le_rfl), (he p hp).2.2, id]
  · rw [image_comp, (he p hp).1.image_Iic_of_surjective (e p).surjective, (he p hp).2.2]

/-- The rays of a stage together with short segments at finitely many new points `N`, before
they grow: the old rays are kept, and the ray at a new point `p` is a short segment through `p`
inside the neighbourhood `V p` and outside `filledSublevel h (c j)`. The backward limit points
of the segments join the obstacles, which lose the new points. -/
private theorem exists_seed_of_isRayStage [Nontrivial E] [DecidableEq M] {h : M → ℝ}
    {P s : Set M} {c : ℕ → ℝ} {j : ℕ} {S : Finset M} {γ : M → ℝ → M} {T : M → ℝ}
    (hst : IsRayStage I h P s c j S γ T)
    (hh : Continuous h) {N : Finset M} (hNP : ∀ p ∈ N, p ∈ P ∧ p ∉ S)
    (hNK : ∀ p ∈ N, p ∉ filledSublevel h (c j)) {V : M → Set M} (hV : ∀ p ∈ N, V p ∈ 𝓝 p) :
    ∃ (s₁ : Set M) (γ₁ : M → ℝ → M) (T₁ : M → ℝ), (∀ p ∈ S, γ₁ p = γ p ∧ T₁ p = T p) ∧
      (∀ p ∈ N, γ₁ p '' Iic (T₁ p) ⊆ V p \ filledSublevel h (c j)) ∧
      (∀ p ∈ N, IsPreconnected (γ₁ p '' Iic (T₁ p))) ∧
      IsClosed s₁ ∧ IsDiscrete s₁ ∧ s \ P ⊆ s₁ ∧ P \ ↑(S ∪ N) ⊆ s₁ ∧
      (∀ p ∈ S ∪ N, IsSmoothEmbedding 𝓘(ℝ) I ∞ (γ₁ p)) ∧ (∀ p ∈ S ∪ N, γ₁ p 0 = p) ∧
      (∀ p ∈ S ∪ N, 0 ≤ T₁ p) ∧
      (↑(S ∪ N) : Set M).PairwiseDisjoint (fun p ↦ γ₁ p '' Iic (T₁ p)) ∧
      (∀ p ∈ S ∪ N, Disjoint (γ₁ p '' Iic (T₁ p)) s₁) ∧
      (∀ p ∈ S ∪ N, closure (γ₁ p '' Iic (T₁ p)) ⊆ γ₁ p '' Iic (T₁ p) ∪ (s₁ \ P)) ∧
      (∀ p ∈ S ∪ N, ∀ i ≤ j, LeavesForGood (γ₁ p) (filledSublevel h (c i)) (Iic (T₁ p))) ∧
      ∀ p ∈ S ∪ N, γ₁ p (T₁ p) ∉ filledSublevel h (c j) := by
  have : LocallyConnectedSpace H := I.toHomeomorph.locallyConnectedSpace
  have : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace H M
  set K := filledSublevel h (c j)
  have hsub_s : ∀ t ⊆ s, IsClosed t := fun t ht ↦
    isClosed_of_subset_discrete_closed ht hst.isDiscrete hst.isClosed
  have hNs (p : M) (hp : p ∈ N) : p ∈ s := hst.sdiff_subset ⟨(hNP p hp).1, (hNP p hp).2⟩
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
    · exact h1.2 (hNP p hp).1
  have hPC (x : M) (hx : x ∈ P) (hxC : x ∉ C) (hxs : x ∉ s) : False := by
    by_cases hxS : x ∈ S
    · exact hxC (hbC x hxS ⟨0, mem_Iic.2 (hst.nonneg x hxS), hst.apply_zero x hxS⟩)
    · exact hxs (hst.sdiff_subset ⟨hx, hxS⟩)
  -- The neighbourhoods in which the segments are taken.
  set G : M → Set M := fun p ↦ V p ∩ Kᶜ ∩ Cᶜ ∩ (s \ {p})ᶜ
  have hGV (p : M) : G p ⊆ V p := fun _ hx ↦ hx.1.1.1
  have hGK (p : M) : G p ⊆ Kᶜ := fun _ hx ↦ hx.1.1.2
  have hGC (p : M) : G p ⊆ Cᶜ := fun _ hx ↦ hx.1.2
  have hGs (p : M) : G p ⊆ (s \ {p})ᶜ := fun _ hx ↦ hx.2
  have hG (p : M) (hp : p ∈ N) : G p ∈ 𝓝 p :=
    Filter.inter_mem (Filter.inter_mem (Filter.inter_mem (hV p hp)
      ((isClosed_filledSublevel hh).isOpen_compl.mem_nhds (hNK p hp)))
      (hC.isOpen_compl.mem_nhds (hNC p hp)))
      ((hsub_s _ sdiff_subset).isOpen_compl.mem_nhds fun h1 ↦ h1.2 rfl)
  obtain ⟨σ, q, hσ, hσ0, hσG, hσq, hqσ, hσcl, hσd⟩ :=
    exists_isSmoothEmbedding_real_pairwiseDisjoint_of_mem_nhds (I := I) N hG
  have hqcl (p : M) (hp : p ∈ N) : q p ∈ closure (range (σ p)) :=
    mem_closure_of_tendsto (hσq p hp) (Filter.Eventually.of_forall mem_range_self)
  have hqG (p : M) (hp : p ∈ N) : q p ∈ G p := hσG p hp (hqcl p hp)
  have hqs (p : M) (hp : p ∈ N) : q p ∉ s := fun hqs ↦
    hGs p (hqG p hp) ⟨hqs, fun hqp ↦ hqσ p hp ⟨0, (hσ0 p hp).trans hqp.symm⟩⟩
  have hqP (p : M) (hp : p ∈ N) : q p ∉ P := fun hqP ↦
    hPC (q p) hqP (hGC p (hqG p hp)) (hqs p hp)
  -- The rays: the old ones, and the segments at the new points.
  set γ₁ : M → ℝ → M := fun p ↦ if p ∈ S then γ p else σ p
  set T₁ : M → ℝ := fun p ↦ if p ∈ S then T p else 0
  have hold (p : M) (hp : p ∈ S) : γ₁ p = γ p ∧ T₁ p = T p := by simp [γ₁, T₁, hp]
  have hnew (p : M) (hp : p ∈ N) : γ₁ p = σ p ∧ T₁ p = 0 := by simp [γ₁, T₁, (hNP p hp).2]
  have hnewG (p : M) (hp : p ∈ N) : γ₁ p '' Iic (T₁ p) ⊆ G p := by
    rw [(hnew p hp).1]
    exact (image_subset_range _ _).trans (subset_closure.trans (hσG p hp))
  have hsP : s \ P ⊆ (s \ N) ∪ q '' N := fun x hx ↦ .inl ⟨hx.1, fun hxN ↦ hx.2 (hNP x hxN).1⟩
  refine ⟨(s \ N) ∪ q '' N, γ₁, T₁, hold, fun p hp x hx ↦ ⟨hGV p (hnewG p hp hx),
    hGK p (hnewG p hp hx)⟩, fun p hp ↦ ?_, (hsub_s _ sdiff_subset).union
    (N.finite_toSet.image q).isClosed, (hst.isDiscrete.mono sdiff_subset).union
    (N.finite_toSet.image q).isDiscrete (hsub_s _ sdiff_subset) (N.finite_toSet.image q).isClosed,
    hsP, ?_, fun p hp ↦ ?_, fun p hp ↦ ?_, fun p hp ↦ ?_, fun a ha b hb hab ↦ ?_, fun p hp ↦ ?_,
    fun p hp ↦ ?_, fun p hp i hi ↦ ?_, fun p hp ↦ ?_⟩
  · rw [(hnew p hp).1]
    exact isPreconnected_Iic.image _ (hσ p hp).isEmbedding.continuous.continuousOn
  · rintro x ⟨hxP, hxS1⟩
    exact .inl ⟨hst.sdiff_subset ⟨hxP, fun h ↦ hxS1 (Finset.mem_union_left _ h)⟩,
      fun h ↦ hxS1 (Finset.mem_union_right _ h)⟩
  · rcases Finset.mem_union.1 hp with hp | hp
    · rw [(hold p hp).1]; exact hst.emb p hp
    · rw [(hnew p hp).1]; exact hσ p hp
  · rcases Finset.mem_union.1 hp with hp | hp
    · rw [(hold p hp).1]; exact hst.apply_zero p hp
    · rw [(hnew p hp).1]; exact hσ0 p hp
  · rcases Finset.mem_union.1 hp with hp | hp
    · rw [(hold p hp).2]; exact hst.nonneg p hp
    · rw [(hnew p hp).2]
  · have hon {a b : M} (ha : a ∈ S) (hb : b ∈ N) :
        Disjoint (γ₁ a '' Iic (T₁ a)) (γ₁ b '' Iic (T₁ b)) :=
      disjoint_left.2 fun x hxa hxb ↦ hGC b (hnewG b hb hxb)
        (hbC a ha (by rwa [(hold a ha).1, (hold a ha).2] at hxa))
    rcases Finset.mem_union.1 ha with ha | ha <;> rcases Finset.mem_union.1 hb with hb | hb
    · simp only [onFun, (hold a ha).1, (hold a ha).2, (hold b hb).1, (hold b hb).2]
      exact hst.disj ha hb hab
    · exact hon ha hb
    · exact (hon hb ha).symm
    · simp only [onFun, (hnew a ha).1, (hnew a ha).2, (hnew b hb).1, (hnew b hb).2]
      exact (hσd ha hb hab).mono ((image_subset_range _ _).trans subset_closure)
        ((image_subset_range _ _).trans subset_closure)
  · rcases Finset.mem_union.1 hp with hp | hp
    · rw [(hold p hp).1, (hold p hp).2]
      refine disjoint_union_right.2 ⟨(hst.disj_s p hp).mono_right sdiff_subset, ?_⟩
      refine disjoint_left.2 fun x hx ⟨p', hp', hpx⟩ ↦ hGC p' (hqG p' hp') ?_
      rw [hpx]; exact hbC p hp hx
    · refine disjoint_left.2 fun x hx hxs₁ ↦ ?_
      have hxG := hnewG p hp hx
      rw [(hnew p hp).1] at hx
      rcases hxs₁ with ⟨hxs, hxN⟩ | ⟨p', hp', rfl⟩
      · refine hGs p hxG ⟨hxs, fun hxp ↦ hxN ?_⟩
        rw [mem_singleton_iff.1 hxp]; exact hp
      · by_cases hpp : p' = p
        · subst hpp; exact hqσ p' hp (image_subset_range _ _ hx)
        · exact disjoint_left.1 (hσd hp' hp hpp) (hqcl p' hp')
            (subset_closure (image_subset_range _ _ hx))
  · rcases Finset.mem_union.1 hp with hp | hp
    · rw [(hold p hp).1, (hold p hp).2]
      exact (hst.closure_subset p hp).trans (union_subset_union_right _ fun x hx ↦
        ⟨hsP hx, hx.2⟩)
    · rw [(hnew p hp).1, (hnew p hp).2, hσcl p hp 0, insert_eq, union_comm]
      exact union_subset_union_right _ (singleton_subset_iff.2 ⟨.inr ⟨p, hp, rfl⟩, hqP p hp⟩)
  · rcases Finset.mem_union.1 hp with hp | hp
    · rw [(hold p hp).1, (hold p hp).2]; exact hst.leaves p hp i hi
    · exact leavesForGood_of_mapsTo_compl fun t ht hti ↦ hGK p (hnewG p hp ⟨t, ht, rfl⟩)
        (filledSublevel_mono (hst.le_level i hi) hti)
  · rcases Finset.mem_union.1 hp with hp | hp
    · rw [(hold p hp).1, (hold p hp).2]; exact hst.notMem p hp
    · rw [(hnew p hp).1, (hnew p hp).2, hσ0 p hp]; exact hNK p hp

/-- Rays indexed by a finite set `S`, as in `exists_grow_rays` for `K = filledSublevel h e`, with
ends in the interior of `filledSublevel h d`, are grown past `filledSublevel h d`, a level `c` is
chosen in the open set `O` of levels below `d`, and each new arc is cut just after its exit from
`filledSublevel h c` (`exists_mem_forall_exists_mem_Ioo_leavesForGood_filledSublevel`). -/
private theorem exists_grow_cut_rays (hE : 1 < Module.rank ℝ E) {h : M → ℝ}
    (hh : ContMDiff I 𝓘(ℝ) 1 h) (hF : ∀ c, IsCompact (filledSublevel h c)) {e d : ℝ}
    {O : Set ℝ} (hO : IsOpen O) (hOn : O.Nonempty) (hOd : O ⊆ Iio d) {s : Set M}
    (hs : IsClosed s) (hsd : IsDiscrete s) {S : Finset M} {γ : M → ℝ → M} {T : M → ℝ}
    (hγ : ∀ p ∈ S, IsSmoothEmbedding 𝓘(ℝ) I ∞ (γ p))
    (hdisj : (S : Set M).PairwiseDisjoint fun p ↦ γ p '' Iic (T p))
    (hγs : ∀ p ∈ S, Disjoint (γ p '' Iic (T p)) s)
    (hcl : ∀ p ∈ S, closure (γ p '' Iic (T p)) \ s ⊆ γ p '' Iic (T p))
    (hR : ∀ p ∈ S, LeavesForGood (γ p) (filledSublevel h e) (Iic (T p)))
    (hend : ∀ p ∈ S, γ p (T p) ∉ filledSublevel h e)
    (hint : ∀ p ∈ S, γ p (T p) ∈ interior (filledSublevel h d)) :
    ∃ c ∈ O, ∃ (γ' : M → ℝ → M) (u : M → ℝ), (∀ p ∈ S, IsSmoothEmbedding 𝓘(ℝ) I ∞ (γ' p)) ∧
      (∀ p ∈ S, T p < u p) ∧ (∀ p ∈ S, EqOn (γ' p) (γ p) (Iic (T p))) ∧
      (∀ p ∈ S, γ' p '' Ioc (T p) (u p) ⊆ (filledSublevel h e ∪ s)ᶜ) ∧
      (∀ p ∈ S, γ' p '' Icc (T p) (u p) ⊆ interior (filledSublevel h d)) ∧
      (∀ p ∈ S, γ' p (u p) ∉ filledSublevel h c) ∧
      (∀ p ∈ S, LeavesForGood (γ' p) (filledSublevel h c) (Icc (T p) (u p))) ∧
      (S : Set M).PairwiseDisjoint (fun p ↦ γ' p '' Iic (u p)) ∧
      ∀ p ∈ S, Disjoint (γ' p '' Iic (u p)) s := by
  classical
  have hhc : Continuous h := hh.continuous
  have : LocallyConnectedSpace H := I.toHomeomorph.locallyConnectedSpace
  have : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace H M
  obtain ⟨γ₂, T₂, hγ₂, hT₂, heq, hout, hdisj₂, hs₂, -, -, hL₂⟩ :=
    exists_grow_rays (γ := fun k : S ↦ γ k) (T := fun k : S ↦ T k) hE
      (isClosed_filledSublevel hhc) (hF d) hs hsd (fun k ↦ hγ k k.property)
      (fun a b hab ↦ hdisj a.property b.property (Subtype.coe_injective.ne hab))
      (fun k ↦ hγs k k.property) (fun k ↦ hcl k k.property) (fun k ↦ hR k k.property)
      (fun k ↦ hend k k.property) fun k ↦
        not_isCompact_closure_connectedComponentIn_compl_filledSublevel (hend k k.property)
  obtain ⟨c, hcO, hcut⟩ := exists_mem_forall_exists_mem_Ioo_leavesForGood_filledSublevel hhc
    (α := γ₂) (fun k ↦ (hγ₂ k).isEmbedding.continuous)
    (fun k ↦ ((hh.comp ((hγ₂ k).contMDiff.of_le (by simp))).mdifferentiable
      (by simp)).differentiable) hT₂ (fun k ↦ heq k (mem_Iic.2 le_rfl) ▸ hint k k.property)
    hL₂
    hO hOn hOd
  choose u hu hucut hunot hulv using hcut
  set γ' : M → ℝ → M := fun p ↦ if hp : p ∈ S then γ₂ ⟨p, hp⟩ else γ p
  set u' : M → ℝ := fun p ↦ if hp : p ∈ S then u ⟨p, hp⟩ else T p
  have hγ' (p : M) (hp : p ∈ S) : γ' p = γ₂ ⟨p, hp⟩ := by simp [γ', hp]
  have hu' (p : M) (hp : p ∈ S) : u' p = u ⟨p, hp⟩ := by simp [u', hp]
  have hIic (p : M) (hp : p ∈ S) : Iic (u' p) ⊆ Iic (T₂ ⟨p, hp⟩) := by
    rw [hu' p hp]; exact Iic_subset_Iic.2 (hu _).2.le
  refine ⟨c, hcO, γ', u', fun p hp ↦ ?_, fun p hp ↦ ?_, fun p hp ↦ ?_, fun p hp ↦ ?_,
    fun p hp ↦ ?_, fun p hp ↦ ?_, fun p hp ↦ ?_, fun a ha b hb hab ↦ ?_, fun p hp ↦ ?_⟩
  · rw [hγ' p hp]; exact hγ₂ _
  · rw [hu' p hp]; exact (hu ⟨p, hp⟩).1
  · rw [hγ' p hp]; exact heq _
  · rw [hγ' p hp, hu' p hp]
    exact (image_mono (Ioc_subset_Ioc_right (hu _).2.le)).trans (hout _)
  · rw [hγ' p hp, hu' p hp]; exact hucut _
  · rw [hγ' p hp, hu' p hp]; exact hunot _
  · rw [hγ' p hp, hu' p hp]; exact hulv _
  · simp only [onFun, hγ' a ha, hγ' b hb]
    exact (hdisj₂ fun h ↦ hab (congrArg Subtype.val h)).mono (image_mono (hIic a ha))
      (image_mono (hIic b hb))
  · rw [hγ' p hp]; exact (hs₂ _).mono_left (image_mono (hIic p hp))

/-- **One stage of the construction of rays.** Let `M` be a finite-dimensional Hausdorff
boundaryless smooth manifold whose model space has rank greater than one, `h : M → ℝ` a `C¹`
function whose filled sublevel sets are compact, and `P` closed and discrete. From the rays of
stage `j` (`IsRayStage`), with levels `c 0, …, c j`, this builds stage `j + 1`: a level
`c' ∈ (c j + 1, c j + 2)` and rays for the levels `update c (j + 1) c'`, with obstacles `s'`
that contain the old obstacles off `P`. Every old ray is extended past its cut parameter `T p`,
to a new cut parameter `T' p ≥ T p + 1`, by a piece outside `filledSublevel h (c j)`; a new ray
starts at every unused point of `P` in `filledSublevel h (c j + 2)`, and the built part of a new
ray lies outside `filledSublevel h (c j)`. -/
theorem exists_isRayStage_succ (hE : 1 < Module.rank ℝ E) {h : M → ℝ}
    (hh : ContMDiff I 𝓘(ℝ) 1 h) (hF : ∀ c, IsCompact (filledSublevel h c))
    {P s : Set M} (hP : IsClosed P) (hPd : IsDiscrete P) {c : ℕ → ℝ} {j : ℕ} {S : Finset M}
    {γ : M → ℝ → M} {T : M → ℝ} (hst : IsRayStage I h P s c j S γ T) :
    ∃ c' ∈ Ioo (c j + 1) (c j + 2), ∃ (s' : Set M) (S' : Finset M) (γ' : M → ℝ → M)
      (T' : M → ℝ), IsRayStage I h P s' (update c (j + 1) c') (j + 1) S' γ' T' ∧ S ⊆ S' ∧
      s \ P ⊆ s' ∧ P ∩ filledSublevel h (c j + 2) ⊆ S' ∧
      (∀ p ∈ S, T p + 1 ≤ T' p ∧ EqOn (γ' p) (γ p) (Iic (T p)) ∧
        γ' p '' Ioc (T p) (T' p) ⊆ (filledSublevel h (c j))ᶜ) ∧
      ∀ p ∈ S', p ∉ S → γ' p '' Iic (T' p) ⊆ (filledSublevel h (c j))ᶜ := by
  classical
  have : Nontrivial E := rank_pos_iff_nontrivial.1 (zero_lt_one.trans hE)
  have hhc : Continuous h := hh.continuous
  have : LocallyConnectedSpace H := I.toHomeomorph.locallyConnectedSpace
  have : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace H M
  -- The new points: the unused points of `P` in `filledSublevel h (c j + 2)`.
  have hNfin : ((P ∩ filledSublevel h (c j + 2)) \ (S : Set M)).Finite :=
    (((hF _).inter_left hP).finite (hPd.mono inter_subset_left)).subset sdiff_subset
  set N := hNfin.toFinset
  have hN (p : M) (hp : p ∈ N) : (p ∈ P ∧ p ∈ filledSublevel h (c j + 2)) ∧ p ∉ S :=
    hNfin.mem_toFinset.1 hp
  have hNK (p : M) (hp : p ∈ N) : p ∉ filledSublevel h (c j) := fun hpK ↦
    (hN p hp).2 (hst.inter_subset ⟨(hN p hp).1.1, hpK⟩)
  have hPS : P ∩ filledSublevel h (c j + 2) ⊆ ↑(S ∪ N) := by
    rintro x ⟨hxP, hxF⟩
    by_cases hxS : x ∈ S
    · exact Finset.mem_union_left _ hxS
    · exact Finset.mem_union_right _ (hNfin.mem_toFinset.2 ⟨⟨hxP, hxF⟩, hxS⟩)
  -- A window of levels `Metric.ball cs ρ` kept apart from the values of `h` at the new points.
  obtain ⟨cs, ρ, hρ, hball, hfar⟩ :=
    (N.finite_toSet.image h).exists_ball_subset_Ioo_forall_lt_abs_sub
      (by linarith : c j + 1 < c j + 2)
  obtain ⟨d, hd⟩ : ∃ d, d = c j + 2 + ρ := ⟨_, rfl⟩
  -- The rays before the growth, with segments at the new points on which `h` stays `ρ`-close
  -- to its value at the point.
  obtain ⟨s₁, γ₁, T₁, hold, hnewV, hnewc, hs₁, hsd₁, hsP, hPs₁, hemb₁, hzero₁, hT₁, hdisj₁,
      hdisj_s₁, hcl₁, hR₁, hend₁⟩ := exists_seed_of_isRayStage hst hhc
    (fun p hp ↦ ⟨(hN p hp).1.1, (hN p hp).2⟩)
    hNK (V := fun p ↦ h ⁻¹' Metric.ball (h p) ρ ∩ interior (filledSublevel h d)) fun p hp ↦
      Filter.inter_mem (hhc.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ hρ))
        (isOpen_interior.mem_nhds
          (filledSublevel_subset_interior hhc (by linarith) (hN p hp).1.2))
  have hint (p : M) (hp : p ∈ S ∪ N) : γ₁ p (T₁ p) ∈ interior (filledSublevel h d) := by
    rcases Finset.mem_union.1 hp with hp | hp
    · rw [(hold p hp).1, (hold p hp).2]
      exact filledSublevel_subset_interior hhc (by linarith)
        (hst.subset p hp ⟨T p, mem_Iic.2 le_rfl, rfl⟩)
    · exact (hnewV p hp ⟨T₁ p, mem_Iic.2 le_rfl, rfl⟩).1.2
  -- Grow every ray past `filledSublevel h d`, choose the next level `c'` and cut the arcs.
  obtain ⟨c', hc', γ', u, hemb, hTu, heq, hout, hucut, hunot, hulv, hdisj, hdisj_s⟩ :=
    exists_grow_cut_rays hE hh hF Metric.isOpen_ball ⟨cs, Metric.mem_ball_self hρ⟩
      (fun x hx ↦ mem_Iio.2 (by linarith [(hball hx).2])) hs₁ hsd₁ hemb₁ hdisj₁ hdisj_s₁
      (fun p hp x hx ↦ (hcl₁ p hp hx.1).resolve_right fun h ↦ hx.2 h.1)
      (fun p hp ↦ hR₁ p hp j le_rfl) hend₁ hint
  obtain ⟨hc'1, hc'2⟩ := hball hc'
  have hFd : interior (filledSublevel h d) ⊆ filledSublevel h (c' + 1) :=
    interior_subset.trans (filledSublevel_mono (by linarith))
  have himg (p : M) (hp : p ∈ S ∪ N) : γ' p '' Iic (T₁ p) = γ₁ p '' Iic (T₁ p) :=
    (heq p hp).image_eq
  have hsplit (p : M) (hp : p ∈ S ∪ N) :
      γ' p '' Iic (u p) = γ₁ p '' Iic (T₁ p) ∪ γ' p '' Icc (T₁ p) (u p) := by
    rw [← Iic_union_Icc_eq_Iic (hTu p hp).le, image_union, himg p hp]
  -- Each built part before the growth lies in `filledSublevel h c'` or misses it.
  have hseg (p : M) (hp : p ∈ S ∪ N) : MapsTo (γ' p) (Iic (T₁ p)) (filledSublevel h c') ∨
      MapsTo (γ' p) (Iic (T₁ p)) (filledSublevel h c')ᶜ := by
    rw [mapsTo_iff_image_subset, mapsTo_iff_image_subset, himg p hp,
      subset_compl_iff_disjoint_right]
    rcases Finset.mem_union.1 hp with hp | hp
    · rw [(hold p hp).1, (hold p hp).2]
      exact .inl ((hst.subset p hp).trans (filledSublevel_mono (by linarith)))
    · refine subset_filledSublevel_or_disjoint_of_isPreconnected hhc (hnewc p hp)
        fun x hx hxc ↦ ?_
      have h1 := (hnewV p hp hx).1.1
      rw [mem_preimage, Metric.mem_ball, Real.dist_eq, hxc, abs_sub_comm] at h1
      linarith [hfar c' hc' (h p) (mem_image_of_mem h hp)]
  have hR (p : M) (hp : p ∈ S ∪ N) (i : ℕ) (hi : i ≤ j + 1) :
      LeavesForGood (γ' p) (filledSublevel h (update c (j + 1) c' i)) (Iic (u p)) := by
    rcases Nat.lt_or_ge i (j + 1) with hi' | hi'
    · rw [update_of_ne hi'.ne]
      have hij := Nat.lt_succ_iff.1 hi'
      exact (hR₁ p hp i hij).extend_Iic (heq p hp) fun t ht hti ↦ hout p hp ⟨t, ht, rfl⟩
        (.inl (filledSublevel_mono (hst.le_level i hij) hti))
    · rw [le_antisymm hi hi', update_self]
      exact (hseg p hp).elim (hulv p hp).Iic_of_mapsTo_Iic (hulv p hp).Iic_of_mapsTo_compl_Iic
  have hst' : IsRayStage I h P s₁ (update c (j + 1) c') (j + 1) (S ∪ N) γ' u := by
    refine ⟨fun i hi ↦ ?_, hs₁, hsd₁, fun x hx ↦ ?_, ?_, hPs₁, hemb, fun p hp ↦ ?_,
      fun p hp ↦ (hT₁ p hp).trans (hTu p hp).le, hdisj, hdisj_s, fun p hp ↦ ?_, hR,
      fun p hp ↦ ?_, fun p hp ↦ ?_⟩
    · rw [update_self]
      rcases Nat.lt_or_ge i (j + 1) with hi' | hi'
      · rw [update_of_ne hi'.ne]
        exact (hst.le_level i (Nat.lt_succ_iff.1 hi')).trans (by linarith)
      · rw [le_antisymm hi hi', update_self]
    · rcases Finset.mem_union.1 hx with hx | hx
      · exact hst.subset_P hx
      · exact (hN x hx).1.1
    · rw [update_self]
      exact (inter_subset_inter_right _ (filledSublevel_mono (by linarith))).trans hPS
    · rw [heq p hp (mem_Iic.2 (hT₁ p hp))]; exact hzero₁ p hp
    · rw [hsplit p hp, closure_union,
        (isCompact_Icc.image (hemb p hp).isEmbedding.continuous).isClosed.closure_eq]
      exact union_subset ((hcl₁ p hp).trans (union_subset_union_left _ subset_union_left))
        (subset_union_right.trans subset_union_left)
    · rw [update_self]; exact hunot p hp
    · rw [update_self, hsplit p hp]
      refine union_subset ?_ ((hucut p hp).trans hFd)
      rcases Finset.mem_union.1 hp with hp | hp
      · rw [(hold p hp).1, (hold p hp).2]
        exact (hst.subset p hp).trans (filledSublevel_mono (by linarith))
      · exact fun x hx ↦ hFd (hnewV p hp hx).1.2
  -- Slow the rays down, so that every cut parameter exceeds `T₁ p` by at least one.
  obtain ⟨γ'', T'', hst'', hslow⟩ := hst'.exists_add_one_le_of_lt hT₁ hTu
  refine ⟨c', ⟨by linarith, by linarith⟩, s₁, S ∪ N, γ'', T'', hst'',
    Finset.subset_union_left, hsP, hPS, fun p hp ↦ ?_, fun p hp hpS ↦ ?_⟩
  · have hp₁ := Finset.mem_union_left N hp
    obtain ⟨hT'', heq'', hIoc'', -⟩ := hslow p hp₁
    obtain ⟨hγp, hTp⟩ := hold p hp
    rw [← hγp, ← hTp]
    refine ⟨hT'', heq''.trans (heq p hp₁), ?_⟩
    rw [hIoc'']
    exact fun x hx hxK ↦ hout p hp₁ hx (.inl hxK)
  · have hpN := (Finset.mem_union.1 hp).resolve_left hpS
    rw [(hslow p hp).2.2.2, ← Iic_union_Ioc_eq_Iic (hTu p hp).le, image_union, himg p hp]
    exact union_subset (fun x hx ↦ (hnewV p hpN hx).2) fun x hx hxK ↦ hout p hp hx (.inl hxK)

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] [IsManifold I ∞ M] in
/-- A stage at step `j` depends only on the levels `c 0, …, c j`. -/
theorem IsRayStage.congr_level {h : M → ℝ} {P s : Set M} {c c' : ℕ → ℝ} {j : ℕ}
    {S : Finset M} {γ : M → ℝ → M} {T : M → ℝ} (hst : IsRayStage I h P s c j S γ T)
    (hc : ∀ i ≤ j, c' i = c i) : IsRayStage I h P s c' j S γ T :=
  { hst with
    le_level := fun i hi ↦ by rw [hc i hi, hc j le_rfl]; exact hst.le_level i hi
    inter_subset := by rw [hc j le_rfl]; exact hst.inter_subset
    leaves := fun p hp i hi ↦ by rw [hc i hi]; exact hst.leaves p hp i hi
    notMem := fun p hp ↦ by rw [hc j le_rfl]; exact hst.notMem p hp
    subset := fun p hp ↦ by rw [hc j le_rfl]; exact hst.subset p hp }

end Stage

section Rays

/-- The data of a stage of the construction of rays: the levels, the obstacles, the points
used, the rays and their cut parameters. -/
private structure RayData (M : Type*) where
  c : ℕ → ℝ
  s : Set M
  S : Finset M
  γ : M → ℝ → M
  T : M → ℝ

/-- **The staged construction of rays.** Let `M` be a finite-dimensional Hausdorff boundaryless
smooth manifold whose model space has rank greater than one, `h : M → ℝ` a `C¹` function whose
filled sublevel sets are compact, and `P` closed and discrete. Starting from a stage `0`
(`IsRayStage`) with obstacles `s₀` and level `c₀ 0`, there are levels `c k` with
`c k + 1 < c (k + 1)` and stages `k` for all `k`, with obstacles `s k` and points `S k`, such that
each step is one of `exists_isRayStage_succ`: the points and the obstacles off `P` only increase,
every point of `P` in `filledSublevel h (c k + 2)` is used at step `k + 1`, every old ray is
extended past its cut parameter, which grows by at least one, by an arc outside
`filledSublevel h (c k)`, and a new ray of step `k + 1` lies outside `filledSublevel h (c k)` up
to its cut parameter. -/
theorem exists_seq_isRayStage (hE : 1 < Module.rank ℝ E) {h : M → ℝ}
    (hh : ContMDiff I 𝓘(ℝ) 1 h) (hF : ∀ c, IsCompact (filledSublevel h c))
    {P s₀ : Set M} (hP : IsClosed P) (hPd : IsDiscrete P) {c₀ : ℕ → ℝ} {S₀ : Finset M}
    {γ₀ : M → ℝ → M} {T₀ : M → ℝ} (h₀ : IsRayStage I h P s₀ c₀ 0 S₀ γ₀ T₀) :
    ∃ (c : ℕ → ℝ) (s : ℕ → Set M) (S : ℕ → Finset M) (γ : ℕ → M → ℝ → M) (T : ℕ → M → ℝ),
      c 0 = c₀ 0 ∧ s 0 = s₀ ∧ ∀ k, IsRayStage I h P (s k) c k (S k) (γ k) (T k) ∧
        c k + 1 < c (k + 1) ∧ S k ⊆ S (k + 1) ∧ s k \ P ⊆ s (k + 1) ∧
        P ∩ filledSublevel h (c k + 2) ⊆ S (k + 1) ∧
        (∀ p ∈ S k, T k p + 1 ≤ T (k + 1) p ∧ EqOn (γ (k + 1) p) (γ k p) (Iic (T k p)) ∧
          γ (k + 1) p '' Ioc (T k p) (T (k + 1) p) ⊆ (filledSublevel h (c k))ᶜ) ∧
        ∀ p ∈ S (k + 1), p ∉ S k →
          γ (k + 1) p '' Iic (T (k + 1) p) ⊆ (filledSublevel h (c k))ᶜ := by
  have step (k : ℕ) (d : {d : RayData M // IsRayStage I h P d.s d.c k d.S d.γ d.T}) :
      ∃ d' : {d' : RayData M // IsRayStage I h P d'.s d'.c (k + 1) d'.S d'.γ d'.T},
        (∀ i ≤ k, d'.val.c i = d.val.c i) ∧
        d'.val.c (k + 1) ∈ Ioo (d.val.c k + 1) (d.val.c k + 2) ∧
        d.val.S ⊆ d'.val.S ∧ d.val.s \ P ⊆ d'.val.s ∧
        P ∩ filledSublevel h (d.val.c k + 2) ⊆ d'.val.S ∧
        (∀ p ∈ d.val.S, d.val.T p + 1 ≤ d'.val.T p ∧
          EqOn (d'.val.γ p) (d.val.γ p) (Iic (d.val.T p)) ∧
          d'.val.γ p '' Ioc (d.val.T p) (d'.val.T p) ⊆ (filledSublevel h (d.val.c k))ᶜ) ∧
        ∀ p ∈ d'.val.S, p ∉ d.val.S →
          d'.val.γ p '' Iic (d'.val.T p) ⊆ (filledSublevel h (d.val.c k))ᶜ := by
    obtain ⟨c', hc', s', S', γ', T', hst, hSS, hss, hPS, hold, hnew⟩ :=
      exists_isRayStage_succ hE hh hF hP hPd d.property
    exact ⟨⟨⟨update d.val.c (k + 1) c', s', S', γ', T'⟩, hst⟩,
      fun i hi ↦ update_of_ne (by omega) _ _, by simpa using hc', hSS, hss, hPS, hold, hnew⟩
  choose next hnext using step
  let seq (k : ℕ) : {d : RayData M // IsRayStage I h P d.s d.c k d.S d.γ d.T} :=
    Nat.rec (motive := fun k ↦ {d : RayData M // IsRayStage I h P d.s d.c k d.S d.γ d.T})
      ⟨⟨c₀, s₀, S₀, γ₀, T₀⟩, h₀⟩ next k
  have hseq (k : ℕ) : seq (k + 1) = next k (seq k) := rfl
  let c (i : ℕ) : ℝ := (seq i).val.c i
  have hc (k i : ℕ) (hi : i ≤ k) : (seq k).val.c i = c i := by
    induction k, hi using Nat.le_induction with
    | base => rfl
    | succ k hik ih => rw [hseq, (hnext k (seq k)).1 i hik, ih]
  refine ⟨c, fun k ↦ (seq k).val.s, fun k ↦ (seq k).val.S, fun k ↦ (seq k).val.γ,
    fun k ↦ (seq k).val.T, rfl, rfl, fun k ↦ ?_⟩
  obtain ⟨-, hlev, hSS, hss, hPS, hold, hnew⟩ := hnext k (seq k)
  rw [← hseq] at hlev hSS hss hPS hold hnew
  exact ⟨(seq k).property.congr_level fun i hi ↦ (hc k i hi).symm, hlev.1, hSS, hss, hPS, hold,
    hnew⟩

variable [SigmaCompactSpace M]

/-- On a manifold with no compact connected component there is a `C¹` function whose filled
sublevel sets are compact and empty at level `-1`. -/
private theorem exists_contMDiff_isCompact_filledSublevel
    (hM : ∀ x : M, ¬ IsCompact (connectedComponent x)) :
    ∃ h : M → ℝ, ContMDiff I 𝓘(ℝ) 1 h ∧ (∀ c, IsCompact (filledSublevel h c)) ∧
      filledSublevel h (-1) = ∅ := by
  have : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  have : LocallyConnectedSpace H := I.toHomeomorph.locallyConnectedSpace
  have : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace H M
  obtain ⟨f, hfp, hf0⟩ := TauCeti.exists_contMDiffMap_isProperMap_nonneg (M := M) I
  refine ⟨f, f.contMDiff.of_le (by simp), fun c ↦ isCompact_filledSublevel hM ?_, ?_⟩
  · have : {x | f x ≤ c} = f ⁻¹' Icc 0 c := by ext x; simp [hf0 x]
    rw [this]
    exact hfp.isCompact_preimage isCompact_Icc
  · exact filledSublevel_eq_empty hM fun x ↦ by linarith [hf0 x]

/-- **Rays from a closed discrete set, avoiding another.** Let `M` be a finite-dimensional,
Hausdorff, σ-compact, boundaryless smooth manifold of dimension at least two with no compact
connected component, and `P`, `Q` disjoint closed discrete subsets of `M`. Then there are smooth
embeddings `γ p : ℝ → M`, one for each `p ∈ P`, with `γ p 0 = p` and `γ p t → ∞` as `t → ∞`,
whose ranges are pairwise disjoint and miss `Q`, and such that the sets `γ p '' [-2, ∞)` form a
locally finite family. -/
theorem exists_rays (hE : 2 ≤ Module.finrank ℝ E)
    (hM : ∀ x : M, ¬ IsCompact (connectedComponent x))
    {P Q : Set M} (hP : IsClosed P) [DiscreteTopology P] (hQ : IsClosed Q)
    [DiscreteTopology Q] (hPQ : Disjoint P Q) :
    ∃ γ : P → TauCeti.SmoothEmbedding 𝓘(ℝ) I ∞ ℝ M,
      (∀ p, γ p 0 = p) ∧ (∀ p, Filter.Tendsto (γ p) Filter.atTop (Filter.cocompact M)) ∧
      LocallyFinite (fun p ↦ γ p '' Ici (-2)) ∧
      Pairwise (Disjoint on fun p ↦ range (γ p)) ∧ ∀ p, Disjoint (range (γ p)) Q := by
  have hE' : 1 < Module.rank ℝ E := Module.one_lt_rank_of_one_lt_finrank hE
  have : LocallyConnectedSpace H := I.toHomeomorph.locallyConnectedSpace
  have : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace H M
  obtain ⟨h, hh, hF, hempty⟩ := exists_contMDiff_isCompact_filledSublevel (I := I) hM
  have hPd : IsDiscrete P := isDiscrete_iff_discreteTopology.2 ‹_›
  have hQd : IsDiscrete Q := isDiscrete_iff_discreteTopology.2 ‹_›
  -- The stages, from the stage with no rays at level `-1` and with obstacles `P ∪ Q`.
  have h₀ := isRayStage_zero (I := I) (c := fun _ ↦ -1) (hP.union hQ) (hPd.union hQd hP hQ)
    subset_union_left (by rw [hempty]; exact disjoint_empty P) (fun p _ ↦ p) 0
  obtain ⟨c, s, S, γ, T, -, hs0, hst⟩ := exists_seq_isRayStage hE' hh hF hP hPd h₀
  choose hstage hlev hSS hss hPS hold hnew using hst
  -- The filled sublevel sets at the levels `c k` form a compact exhaustion.
  have hcge := add_natCast_le_of_add_one_le fun k ↦ (hlev k).le
  have hcov (x : M) : ∃ k, x ∈ filledSublevel h (c k) := by
    obtain ⟨k, hk⟩ := exists_nat_ge (h x - c 0)
    exact ⟨k, filledSublevel_mono (by linarith [hcge k])
      (setOfPred_le_subset_filledSublevel (show h x ≤ h x from le_rfl))⟩
  let K : CompactExhaustion M :=
    { toFun k := filledSublevel h (c k)
      isCompact' k := hF _
      subset_interior_succ' k :=
        filledSublevel_subset_interior hh.continuous (by linarith [hlev k])
      iUnion_eq' := eq_univ_of_forall fun x ↦ mem_iUnion.2 (hcov x) }
  have hK (k : ℕ) : K k = filledSublevel h (c k) := rfl
  have hSmono : Monotone S := monotone_nat_of_le_succ hSS
  have hcmono : Monotone c := monotone_nat_of_le_succ fun k ↦ by linarith [hlev k]
  have hQs (k : ℕ) : Q ⊆ s k \ P := by
    induction k with
    | zero => rw [hs0]; exact fun x hx ↦ ⟨subset_union_right hx, disjoint_right.1 hPQ hx⟩
    | succ k ih => exact fun x hx ↦ ⟨hss k (ih hx), disjoint_right.1 hPQ hx⟩
  -- The ray of `p` is the limit of the rays of `p` at the stages from the first that uses `p`,
  -- which exists since every point of `P` lies in some `filledSublevel h (c k)`.
  have hray (p : P) : ∃ δ : TauCeti.SmoothEmbedding 𝓘(ℝ) I ∞ ℝ M,
      (∀ t, ∀ᶠ k in Filter.atTop, (p : M) ∈ S k ∧ t ≤ T k p ∧ δ t = γ k p t) ∧
        Filter.Tendsto δ Filter.atTop (Filter.cocompact M) := by
    obtain ⟨j, hj⟩ := hcov p
    have hpS {k : ℕ} (hk : j + 1 ≤ k) : (p : M) ∈ S k :=
      hSmono hk (hPS j ⟨p.property, filledSublevel_mono (by linarith) hj⟩)
    have harc (k : ℕ) (hk : j + 1 ≤ k) :
        MapsTo (γ (k + 1) p) (Icc (T k p) (T (k + 1) p)) (K k)ᶜ := by
      obtain ⟨hT, heq, harc⟩ := hold k p (hpS hk)
      rw [← Icc_union_Ioc_eq_Icc le_rfl (by linarith [hT]), Icc_self, mapsTo_union, hK]
      refine ⟨fun t ht ↦ ?_, mapsTo_iff_image_subset.2 harc⟩
      rw [mem_singleton_iff.1 ht, heq (mem_Iic.2 le_rfl)]
      exact (hstage k).notMem p (hpS hk)
    -- From stage `j + 1` on, the cut parameters of `p` grow by at least one at each step.
    have hTt : Filter.Tendsto (fun k ↦ T k p) Filter.atTop Filter.atTop :=
      (Filter.tendsto_add_atTop_iff_nat (j + 1)).1 <| tendsto_atTop_of_add_one_le fun k ↦
        Nat.add_right_comm k 1 (j + 1) ▸ (hold (k + (j + 1)) p (hpS (by omega))).1
    obtain ⟨δ, hδ, -, hδt⟩ := TauCeti.SmoothEmbedding.exists_eqOn_Iic_tendsto_cocompact_of_ge
      (fun k hk ↦ (hstage k).emb p (hpS hk)) (fun k hk ↦ by linarith [(hold k p (hpS hk)).1])
      hTt K (fun k hk ↦ (hold k p (hpS hk)).2.1) harc ((hstage (j + 1)).notMem p (hpS le_rfl))
    refine ⟨δ, fun t ↦ ?_, hδt⟩
    filter_upwards [hTt.eventually_ge_atTop t, Filter.eventually_ge_atTop (j + 1)] with k htk hjk
    exact ⟨hpS hjk, htk, hδ k hjk htk⟩
  choose δ hδ hδt using hray
  -- The built part of a ray at any stage misses the filled sublevel sets of the stages before
  -- the one that uses its point.
  have hout (p : M) (i : ℕ) (hpi : p ∉ S i) :
      ∀ k, p ∈ S k → γ k p '' Iic (T k p) ⊆ (filledSublevel h (c i))ᶜ := by
    intro k
    induction k with
    | zero => exact fun hp ↦ (hpi (hSmono (Nat.zero_le i) hp)).elim
    | succ k ih =>
      intro hp
      have hik : i ≤ k := by
        by_contra hik
        exact hpi (hSmono (by omega) hp)
      have hKik : (filledSublevel h (c k))ᶜ ⊆ (filledSublevel h (c i))ᶜ :=
        compl_subset_compl.2 (filledSublevel_mono (hcmono hik))
      by_cases hpk : p ∈ S k
      · obtain ⟨hT, heq, harc⟩ := hold k p hpk
        rw [← Iic_union_Ioc_eq_Iic (by linarith : T k p ≤ T (k + 1) p), image_union,
          heq.image_eq]
        exact union_subset (ih hpk) (harc.trans hKik)
      · exact (hnew k p hp hpk).trans hKik
  refine ⟨δ, fun p ↦ ?_, hδt, ?_, fun p q hpq ↦ ?_, fun p ↦ ?_⟩
  · obtain ⟨k, hkS, -, hk⟩ := (hδ p 0).exists
    rw [hk]
    exact (hstage k).apply_zero p hkS
  · -- A neighbourhood `K i` meets only the rays of the finitely many points of `S i`.
    refine LocallyFinite.subset (f := fun p ↦ range (δ p)) (fun x ↦ ?_)
      fun p ↦ image_subset_range _ _
    obtain ⟨i, hi⟩ := K.exists_mem_nhds x
    refine ⟨K i, hi, ((S i).finite_toSet.preimage Subtype.val_injective.injOn).subset ?_⟩
    rintro p ⟨_, ⟨t, rfl⟩, hti⟩
    by_contra hpi
    obtain ⟨k, hkS, htk, hk⟩ := (hδ p t).exists
    rw [hK, hk] at hti
    exact hout p i hpi k hkS ⟨t, htk, rfl⟩ hti
  · refine disjoint_left.2 ?_
    rintro _ ⟨t, rfl⟩ ⟨t', ht'⟩
    obtain ⟨k, ⟨hp, htk, hk⟩, hq, htk', hk'⟩ := ((hδ p t).and (hδ q t')).exists
    refine disjoint_left.1 ((hstage k).disj hq hp fun h ↦ hpq (Subtype.ext h).symm)
      ⟨t', htk', rfl⟩ ?_
    rw [← hk', ht', hk]
    exact ⟨t, htk, rfl⟩
  · refine disjoint_left.2 ?_
    rintro _ ⟨t, rfl⟩ htQ
    obtain ⟨k, hkS, htk, hk⟩ := (hδ p t).exists
    rw [hk] at htQ
    exact disjoint_left.1 ((hstage k).disj_s p hkS) ⟨t, htk, rfl⟩ (hQs k htQ).1

end Rays

end SymplecticGeometry

end
