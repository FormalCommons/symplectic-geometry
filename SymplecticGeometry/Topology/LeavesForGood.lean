/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Topology.FilledHull

/-!
# Curves that leave a set for good

A curve `γ : ℝ → X` leaves a set `K` for good along a set of parameters `D`
(`SymplecticGeometry.LeavesForGood γ K D`) if, along `D`, it never comes back to `K` once it is
outside: the parameters of `D` that `γ` sends outside `K` form an upper set of `D`.

## Main results

* `LeavesForGood`, with `leavesForGood_def` and `leavesForGood_iff_monotoneOn`: the definition.
* `leavesForGood_of_mapsTo`, `leavesForGood_of_mapsTo_compl`: a curve that maps `D` into `K`, or
  outside `K`, leaves `K` for good along `D`.
* `LeavesForGood.mono`, `LeavesForGood.congr`, `LeavesForGood.comp_monotone`: restriction of
  the parameters, change of the curve off `D`, and monotone reparametrization.
* `LeavesForGood.union`, `LeavesForGood.union_of_mapsTo_left`, `LeavesForGood.extend_Icc`,
  `LeavesForGood.extend_Iic`, `LeavesForGood.Iic_of_mapsTo_Iic`,
  `LeavesForGood.Iic_of_mapsTo_compl_Iic`: extension by a later piece outside `K`, or by an
  earlier piece inside `K`.
* `leavesForGood_iff_ordConnected`: along an order-connected `D` with greatest element `T`, the
  property says that the parameters sent outside `K` form an order-connected set, which contains
  `T` when it is nonempty.
* `LeavesForGood.mapsTo_connectedComponentIn`, `LeavesForGood.image_inter_connectedComponentIn`,
  `LeavesForGood.apply_mem_connectedComponentIn`: for a curve continuous on such a `D`, the part
  outside `K` lies in the component of `Kᶜ` that contains the endpoint `γ T`.
* `exists_mem_Ioo_leavesForGood_filledSublevel`: a curve from the interior of
  `filledSublevel h d` to its outside, whose crossings of a level `c < d` are isolated from the
  right, can be cut just after its first exit from `filledSublevel h c`
  (`exists_image_Icc_subset_filledSublevel_and_disjoint`), or at once if it starts outside, so
  that the cut arc stays in the interior of `filledSublevel h d` and leaves `filledSublevel h c`
  for good.

These are the invariant and the cuts of the construction of proper rays in
`SymplecticGeometry/Geometry/Manifold/ProperRay.lean`, which also chooses the levels at which
the cuts are made.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Theorem 7.3.1, for the construction of the rays.
-/

public section

open Function Set Topology

namespace SymplecticGeometry

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

end CutArcs

end SymplecticGeometry

end
