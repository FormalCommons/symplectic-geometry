/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.GroupAction.CompactLinearization

/-!
# Fixed tangent vectors at fixed points of compact group actions

Let a compact group `G` act smoothly on a manifold `M` without boundary, and let `x` be a fixed
point. If the derivatives at `x` of the maps `g • ·` all fix a nonzero tangent vector `v`, then
`x` is not isolated among the fixed points of `G`.

The proof reads the action in the linearizing chart `e` of Tau Ceti's
`TauCeti.exists_contMDiff_chart_fixedPoints`, in which the fixed points near `x` are the points
sent into the invariant vectors of the tangent representation at `x`
(`TauCeti.mem_invariants_tangentRepresentation_iff_of_mem_fixedPoints`). The points
`e⁻¹ (ε • v)`, for small real `ε ≠ 0`, are then fixed points other than `x` that tend to `x`.

## Main results

* `SymplecticGeometry.frequently_mem_fixedPoints_of_mfderiv_smul_eq_self`: a nonzero tangent
  vector at a fixed point `x` fixed by the derivatives of the action gives fixed points other
  than `x` in every neighbourhood of `x`.

## References

* S. Bochner, *Compact groups of differentiable transformations*, Ann. of Math. (2) 46 (1945),
  372–381.
* J. J. Duistermaat and J. A. C. Kolk, *Lie Groups*, Universitext, Springer, 2000, Section 2.2.
-/

public section

open Filter Topology MulAction TauCeti
open scoped Manifold ContDiff

namespace SymplecticGeometry

variable {E H M EG HG G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [NormedAddCommGroup EG] [NormedSpace ℝ EG] [TopologicalSpace HG]
  {IG : ModelWithCorners ℝ EG HG} [IG.Boundaryless] [TopologicalSpace G] [ChartedSpace HG G]
  [Group G] [IsTopologicalGroup G] [CompactSpace G] [MulAction G M] {n : ℕ∞}
  [IsManifold I n M] [IsManifold IG n G]

variable (IG) in
/-- **A fixed tangent vector at a fixed point gives nearby fixed points.** Let a compact group
`G`, a manifold without boundary, act on a manifold `M` without boundary by a jointly `C^n` map,
`1 ≤ n`, and let `x` be a fixed point. If the derivatives at `x` of all the maps `g • ·` fix a
nonzero tangent vector `v`, then every neighbourhood of `x` contains fixed points other than
`x`. -/
theorem frequently_mem_fixedPoints_of_mfderiv_smul_eq_self [ContMDiffSMul IG I n G M]
    (hn : 1 ≤ n) {x : M} (hx : x ∈ fixedPoints G M) {v : TangentSpace I x} (hv : v ≠ 0)
    (hfix : ∀ g : G, mfderiv I I (fun y : M ↦ g • y) x v = v) :
    ∃ᶠ y in 𝓝[≠] x, y ∈ fixedPoints G M := by
  have hn0 : (n : WithTop ℕ∞) ≠ 0 := by
    exact_mod_cast (lt_of_lt_of_le zero_lt_one hn).ne'
  have hd : ∀ g ∈ stabilizer G x, MDifferentiableAt I I (fun y : M ↦ g • y) x :=
    fun g _ ↦ (ContMDiffSMul.contMDiff_const_smul (I := IG) (n := n) g).mdifferentiableAt hn0
  obtain ⟨e, hxe, hex, -, -, -, -, hfixed⟩ :=
    exists_contMDiff_chart_fixedPoints (I := I) IG hn hx hd
  have hv' : v ∈ (tangentRepresentation hd).toRepresentation.invariants :=
    (mem_invariants_tangentRepresentation_iff_of_mem_fixedPoints hd hx).2 hfix
  have h0 : (0 : E) ∈ e.target := hex ▸ e.map_source hxe
  have hx0 : e.symm 0 = x := hex ▸ e.left_inv hxe
  have hcont : Tendsto (fun ε : ℝ ↦ (ε • v : E)) (𝓝 0) (𝓝 0) :=
    Continuous.tendsto' (f := fun ε : ℝ ↦ (ε • v : E)) (by fun_prop) 0 0 (zero_smul ℝ _)
  have htarget : ∀ᶠ ε : ℝ in 𝓝 0, (ε • v : E) ∈ e.target :=
    hcont (e.open_target.mem_nhds h0)
  have hc : Tendsto (fun ε : ℝ ↦ e.symm (ε • v)) (𝓝[≠] 0) (𝓝[≠] x) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · exact (hx0 ▸ (e.continuousAt_symm h0).tendsto.comp hcont).mono_left nhdsWithin_le_nhds
    · filter_upwards [nhdsWithin_le_nhds htarget, self_mem_nhdsWithin] with ε hε hε0 hεx
      have h := congrArg e hεx
      rw [e.right_inv hε, hex] at h
      exact hε0 ((smul_eq_zero.1 h).resolve_right hv)
  have hmem : ∀ᶠ ε : ℝ in 𝓝[≠] 0, e.symm (ε • v) ∈ fixedPoints G M := by
    filter_upwards [nhdsWithin_le_nhds htarget] with ε hε
    refine (hfixed _ (e.map_target hε)).2 ?_
    rw [e.right_inv hε]
    exact Submodule.smul_mem _ ε hv'
  exact hc.frequently hmem.frequently

end SymplecticGeometry

end
