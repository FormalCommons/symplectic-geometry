/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.IsManifold.InteriorBoundary
public import SymplecticGeometry.Topology.Collar.Compact
public import TauCeti.Geometry.Manifold.Boundary.Collar.Deformation
public import TauCeti.Geometry.Manifold.Boundary.Interior
public import TauCeti.Topology.Homeomorph.Extend

/-!
# Pushing a compact manifold with boundary into its interior

Let `c : N × [0, 1) → M` be a collar of `f : N → M` (`TauCeti.IsCollar`), with `N` compact and
`M` Hausdorff. For a depth `t ∈ [0, 1)`, raising the depth coordinate of every collar point
`c (y, s)` to `max s (τ * t)`, and fixing the points outside the collar, is a homotopy, for
`τ ∈ [0, 1]`, from the identity of `M` to a map `g` that sends `c (y, s)` to `c (y, t)` when
`s < t` and fixes every point outside `TauCeti.collarPart c t = c(N × [0, t))`. So `g` takes its
values outside `c(N × [0, t))`
(`TauCeti.IsCollar.exists_homotopic_push_off_collarPart`).

For a compact Hausdorff charted space `M` over a finite-dimensional real model `I`, the boundary is
closed and so compact, and it has a collar by Brown's theorem
(`TauCeti.isCollared_subtypeVal_boundary_of_compactSpace`, for the half-space model). Taking
`t = 1 / 2` pushes `M` into the compact set `K = M \ c(∂M × [0, 1 / 2))`, which lies in the
interior of `M`, and leaves free the open set `c(∂M × (0, 1 / 2))` of the interior, nonempty
when the boundary is (`TauCeti.IsCollar.exists_homotopy_push`).

## Main results

* `TauCeti.IsCollar.exists_homotopic_push_off_collarPart`: a collar of a compact space in a
  Hausdorff space gives a map homotopic to the identity that raises the depth below `t` to `t`.
* `TauCeti.IsCollar.exists_homotopy_push`: a compact Hausdorff manifold with boundary is pushed,
  by a map homotopic to the identity, into a compact subset of its interior that misses an open
  part of the collar, nonempty when the boundary is.

## References

* M. Brown, *Locally flat imbeddings of topological manifolds*, Annals of Mathematics 75 (1962),
  331–341.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.3, proof of
  Theorem 3.43.
-/

public section

noncomputable section

namespace TauCeti

open Set Topology

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N] {f : N → M}
  {c : N × Ico (0 : ℝ) 1 → M}

namespace IsCollar

/-- The collar coordinates `p` with the depth raised to `max p.2 (τ * t)`. -/
private def raise (t : Ico (0 : ℝ) 1) (τ : unitInterval) (p : N × Ico (0 : ℝ) 1) :
    N × Ico (0 : ℝ) 1 :=
  (p.1, ⟨max p.2 (τ * t), le_max_of_le_left p.2.property.1,
    max_lt p.2.property.2
      ((mul_le_of_le_one_left t.property.1 τ.property.2).trans_lt t.property.2)⟩)

private lemma continuous_raise (t : Ico (0 : ℝ) 1) :
    Continuous fun q : unitInterval × (N × Ico (0 : ℝ) 1) ↦ raise t q.1 q.2 :=
  continuous_snd.fst.prodMk (((continuous_subtypeVal.comp continuous_snd.snd).max
    ((continuous_subtypeVal.comp continuous_fst).mul continuous_const)).subtype_mk _)

omit [TopologicalSpace N] in
/-- Raising a depth that is at least `τ * t` changes nothing. -/
private lemma raise_of_le {t : Ico (0 : ℝ) 1} {τ : unitInterval} {p : N × Ico (0 : ℝ) 1}
    (h : (τ : ℝ) * t ≤ p.2) : raise t τ p = p :=
  Prod.ext rfl (Subtype.ext (max_eq_left h))

variable (hc : IsCollar f c)
include hc

/-- **Pushing along a collar.** Let `c` be a collar of `f : N → M`, with `N` compact and `M`
Hausdorff, and let `t ∈ [0, 1)`. There is a map `g : M → M`, homotopic to the identity, that
sends a collar point `c (y, s)` of depth `s < t` to `c (y, t)` and fixes every point outside the
collar `c(N × [0, t))` of depth less than `t`. In particular `g` takes no value in that collar. -/
theorem exists_homotopic_push_off_collarPart [CompactSpace N] [T2Space M] (t : Ico (0 : ℝ) 1) :
    ∃ g : C(M, M), (ContinuousMap.id M).Homotopic g ∧
      (∀ p : N × Ico (0 : ℝ) 1, (p.2 : ℝ) < t → g (c p) = c (p.1, t)) ∧
      (∀ x ∉ collarPart c t, g x = x) ∧ range g ⊆ (collarPart c t)ᶜ := by
  -- Away from the collar of depth at most `t`, every stage of the push is the identity.
  obtain ⟨F, hFc, hFV⟩ := hc.isOpenEmbedding.exists_continuousMap_extend_id
    (hc.isCompact_image_setOf_le t.property.2).isClosed.isOpen_compl
    (fun x hx h ↦ hx (image_subset_range _ _ h))
    ⟨fun q : unitInterval × (N × Ico (0 : ℝ) 1) ↦ raise t q.1 q.2, continuous_raise t⟩
    fun τ p hp ↦ raise_of_le <| (mul_le_of_le_one_left t.property.1 τ.property.2).trans
      (le_of_not_ge fun h ↦ hp ⟨p, h, rfl⟩)
  let g : C(M, M) := ⟨fun x ↦ F (1, x), F.continuous.comp (continuous_const.prodMk continuous_id)⟩
  have hg : ∀ p : N × Ico (0 : ℝ) 1, (p.2 : ℝ) < t → g (c p) = c (p.1, t) := fun p hp ↦ by
    refine (hFc 1 p).trans (congrArg c (Prod.ext rfl (Subtype.ext ?_)))
    simp [raise, hp.le]
  -- A point outside `collarPart c t` is either off the collar or of depth at least `t`.
  have hF : ∀ τ : unitInterval, ∀ x ∉ collarPart c t, F (τ, x) = x := fun τ x hx ↦ by
    by_cases hxc : x ∈ range c
    · obtain ⟨p, rfl⟩ := hxc
      rw [hFc]
      refine congrArg c (raise_of_le ?_)
      exact (mul_le_of_le_one_left t.property.1 τ.property.2).trans
        (le_of_not_gt fun h ↦ hx (mem_collarPart_iff.2 ⟨p, h, rfl⟩))
    · exact hFV τ x fun ⟨p, _, hp⟩ ↦ hxc ⟨p, hp⟩
  have hg' : ∀ x ∉ collarPart c t, g x = x := hF 1
  have hF0 : ∀ x, F (0, x) = x := fun x ↦ by
    by_cases hxc : x ∈ range c
    · obtain ⟨p, rfl⟩ := hxc
      rw [hFc]
      exact congrArg c (raise_of_le (by simpa using p.2.property.1))
    · exact hFV 0 x fun ⟨p, _, hp⟩ ↦ hxc ⟨p, hp⟩
  refine ⟨g, ⟨{ toContinuousMap := F, map_zero_left := hF0, map_one_left := fun _ ↦ rfl }⟩,
    hg, hg', ?_⟩
  rintro _ ⟨x, rfl⟩ hgx
  by_cases hx : x ∈ collarPart c t
  · obtain ⟨p, hp, rfl⟩ := mem_collarPart_iff.1 hx
    rw [hg p hp, apply_mem_collarPart_iff hc.isOpenEmbedding.injective] at hgx
    exact lt_irrefl _ hgx
  · exact hx (hg' x hx ▸ hgx)

end IsCollar

section Manifold

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [ChartedSpace H M]
  {c : I.boundary M × Ico (0 : ℝ) 1 → M}

/-- **Pushing a compact manifold with boundary into its interior.** Let `M` be a compact Hausdorff
charted space over a finite-dimensional real model `I`, and `c : ∂M × [0, 1) → M` a collar of its
boundary (as given, for the half-space model, by
`TauCeti.isCollared_subtypeVal_boundary_of_compactSpace`). There are a compact subset `K` of the
interior of `M`, an open subset `U` of the interior, inside the collar `c(∂M × [0, 1 / 2))`,
disjoint from `K` and nonempty when the boundary is, and a map `g : M → M` homotopic to the
identity with image in `K`. Here `U = c(∂M × (0, 1 / 2))`, and `g` raises the depth of the
collar points of depth below `1 / 2` to `1 / 2` and fixes all other points. -/
theorem IsCollar.exists_homotopy_push [CompactSpace M] [T2Space M]
    (hc : IsCollar ((↑) : I.boundary M → M) c) :
    ∃ (K U : Set M) (g : C(M, M)), IsCompact K ∧ K ⊆ I.interior M ∧ IsOpen U ∧
      U ⊆ I.interior M ∧ Disjoint U K ∧ ((I.boundary M).Nonempty → U.Nonempty) ∧
      U = c '' {p | (p.2 : ℝ) ∈ Ioo 0 (1 / 2)} ∧ U ⊆ collarPart c (1 / 2) ∧
      range g ⊆ K ∧ (ContinuousMap.id M).Homotopic g ∧
      (∀ p : I.boundary M × Ico (0 : ℝ) 1, (p.2 : ℝ) < 1 / 2 →
        g (c p) = c (p.1, ⟨1 / 2, by norm_num, by norm_num⟩)) ∧
      ∀ x ∉ collarPart c (1 / 2), g x = x := by
  obtain ⟨g, hg, hgc, hgo, hgr⟩ :=
    hc.exists_homotopic_push_off_collarPart ⟨1 / 2, by norm_num, by norm_num⟩
  have hU : c '' {p | (p.2 : ℝ) ∈ Ioo 0 (1 / 2)} ⊆ collarPart c (1 / 2) :=
    fun _ ⟨p, hp, hpx⟩ ↦
      mem_collarPart_iff.2 ⟨p, (show (p.2 : ℝ) ∈ Ioo 0 (1 / 2) from hp).2, hpx⟩
  refine ⟨(collarPart c (1 / 2))ᶜ, c '' {p | (p.2 : ℝ) ∈ Ioo 0 (1 / 2)}, g,
    (hc.isOpen_collarPart _).isClosed_compl.isCompact, ?_, ?_, ?_,
    disjoint_compl_right.mono_left hU, ?_, rfl, hU, hgr, hg, hgc, hgo⟩
  · simpa only [Subtype.range_coe] using
      hc.compl_collarPart_subset_range I.range_subtypeVal_interior (by norm_num : (0 : ℝ) < 1 / 2)
  · exact hc.isOpenEmbedding.isOpenMap _
      (isOpen_Ioo.preimage (continuous_subtypeVal.comp continuous_snd))
  · -- A collar point of positive depth is not `c (x, 0)` for a boundary point `x`.
    rintro _ ⟨p, hp, rfl⟩
    rw [← I.compl_boundary, ← Subtype.range_coe (s := I.boundary M)]
    intro hb
    have h : p.2 = ⟨0, by norm_num⟩ := (hc.preimage_range.subset hb).2
    exact hp.1.ne' (congrArg Subtype.val h)
  · rintro ⟨x, hx⟩
    exact ⟨c (⟨x, hx⟩, ⟨1 / 4, by norm_num, by norm_num⟩), mem_image_of_mem _
      (show (1 / 4 : ℝ) ∈ Ioo 0 (1 / 2) by norm_num)⟩

end Manifold

end TauCeti
