/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Collar.Deformation
public import TauCeti.Geometry.Manifold.Boundary.Collar.Retraction
public import TauCeti.Geometry.Manifold.Boundary.Interior
import SymplecticGeometry.Geometry.Manifold.IsManifold.InteriorBoundary

/-!
# Pushing a compact manifold with boundary into its interior

Let `M` be a compact Hausdorff charted space over a finite-dimensional real model `I`, and
`c : ∂M × [0, 1) → M` a collar of its boundary (Brown's theorem gives one for the half-space
model: `TauCeti.isCollared_subtypeVal_boundary_of_compactSpace`). Tau Ceti's homotopy
equivalence `TauCeti.IsCollar.complHomotopyEquiv` between `M \ ∂M` and `M` has a homotopy inverse
that sends a collar point `c (y, s)` to `c (y, max s (1 / 2 - s))`, of depth at least `1 / 4`, and
fixes the points off the collar. Composed with the inclusion, it is a map `M → M` homotopic to the
identity whose image lies in the compact set `K = M \ c(∂M × [0, 1 / 4))`, which lies in the
interior of `M`. It leaves free the open set `c(∂M × (0, 1 / 4))` of the interior, nonempty when
the boundary is (`TauCeti.IsCollar.exists_homotopy_push`).

## Main results

* `TauCeti.IsCollar.coe_complHomotopyEquiv_symm_notMem_collarPart`: the homotopy inverse of
  `TauCeti.IsCollar.complHomotopyEquiv` misses the collar points of depth less than `1 / 4`.
* `TauCeti.IsCollar.exists_homotopy_push`: a compact Hausdorff manifold with boundary is pushed,
  by a map homotopic to the identity, into a compact subset of its interior that misses a
  nonempty open subset of the interior when the boundary is not empty.

## References

* M. Brown, *Locally flat imbeddings of topological manifolds*, Annals of Mathematics 75 (1962),
  331–341.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.3, proof of
  Theorem 3.43.
-/

public section

namespace TauCeti

open Set Topology

/-- The homotopy inverse of `TauCeti.IsCollar.complHomotopyEquiv` misses the points of depth less
than `1 / 4` in the collar: it sends a collar point of depth `s` to depth `max s (1 / 2 - s)`, and
fixes the points off the collar. -/
theorem IsCollar.coe_complHomotopyEquiv_symm_notMem_collarPart {M N : Type*} [TopologicalSpace M]
    [TopologicalSpace N] {f : N → M} {c : N × Ico (0 : ℝ) 1 → M} (hc : IsCollar f c)
    [CompactSpace N] [T2Space M] (x : M) :
    (hc.complHomotopyEquiv.symm x : M) ∉ collarPart c (1 / 4) := by
  by_cases hxc : x ∈ range c
  · obtain ⟨p, rfl⟩ := hxc
    rw [hc.coe_complHomotopyEquiv_symm_apply,
      apply_mem_collarPart_iff hc.isOpenEmbedding.injective, max_lt_iff]
    intro h
    linarith [h.1, h.2]
  · rw [hc.coe_complHomotopyEquiv_symm_apply_of_notMem_range hxc]
    intro hx
    obtain ⟨p, -, hp⟩ := mem_collarPart_iff.1 hx
    exact hxc ⟨p, hp⟩

variable {M : Type*} [TopologicalSpace M]
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [ChartedSpace H M]
  {c : I.boundary M × Ico (0 : ℝ) 1 → M}

/-- **Pushing a compact manifold with boundary into its interior.** Let `M` be a compact Hausdorff
charted space over a finite-dimensional real model `I`, and `c : ∂M × [0, 1) → M` a collar of its
boundary (as given, for the half-space model, by
`TauCeti.isCollared_subtypeVal_boundary_of_compactSpace`). There are a compact subset `K` of the
interior of `M`, an open subset `U` of the interior, disjoint from `K` and nonempty when the
boundary is, and a map `g : M → M` homotopic to the identity with image in `K`. -/
theorem IsCollar.exists_homotopy_push [CompactSpace M] [T2Space M]
    (hc : IsCollar ((↑) : I.boundary M → M) c) :
    ∃ (K U : Set M) (g : C(M, M)), IsCompact K ∧ K ⊆ I.interior M ∧ IsOpen U ∧
      U ⊆ I.interior M ∧ Disjoint U K ∧ ((I.boundary M).Nonempty → U.Nonempty) ∧
      range g ⊆ K ∧ (ContinuousMap.id M).Homotopic g := by
  let e := hc.complHomotopyEquiv
  have hU : c '' {p | (p.2 : ℝ) ∈ Ioo 0 (1 / 4)} ⊆ collarPart c (1 / 4) :=
    fun _ ⟨p, hp, hpx⟩ ↦
      mem_collarPart_iff.2 ⟨p, (show (p.2 : ℝ) ∈ Ioo 0 (1 / 4) from hp).2, hpx⟩
  refine ⟨(collarPart c (1 / 4))ᶜ, c '' {p | (p.2 : ℝ) ∈ Ioo 0 (1 / 4)},
    e.toFun.comp e.invFun, (hc.isOpen_collarPart _).isClosed_compl.isCompact, ?_, ?_, ?_,
    disjoint_compl_right.mono_left hU, ?_, ?_, e.right_inv.symm⟩
  · simpa only [Subtype.range_coe] using
      hc.compl_collarPart_subset_range I.range_subtypeVal_interior (by norm_num : (0 : ℝ) < 1 / 4)
  · exact hc.isOpenEmbedding.isOpenMap _
      (isOpen_Ioo.preimage (continuous_subtypeVal.comp continuous_snd))
  · -- A collar point of positive depth is not `c (x, 0)` for a boundary point `x`.
    rintro _ ⟨p, hp, rfl⟩
    rw [← I.compl_boundary, ← Subtype.range_coe (s := I.boundary M)]
    intro hb
    have h : p.2 = ⟨0, by norm_num⟩ := (hc.preimage_range.subset hb).2
    exact hp.1.ne' (congrArg Subtype.val h)
  · rintro ⟨x, hx⟩
    exact ⟨c (⟨x, hx⟩, ⟨1 / 8, by norm_num, by norm_num⟩), mem_image_of_mem _
      (show (1 / 8 : ℝ) ∈ Ioo 0 (1 / 4) by norm_num)⟩
  · rintro _ ⟨x, rfl⟩
    -- Tau Ceti states `coe_complHomotopyEquiv` for the coercion of `e`, which is that of `e.toFun`.
    have he : ⇑e.toFun = Subtype.val := hc.coe_complHomotopyEquiv
    simpa only [ContinuousMap.comp_apply, ContinuousMap.HomotopyEquiv.coe_invFun, he,
      mem_compl_iff] using hc.coe_complHomotopyEquiv_symm_notMem_collarPart x

end TauCeti

end
