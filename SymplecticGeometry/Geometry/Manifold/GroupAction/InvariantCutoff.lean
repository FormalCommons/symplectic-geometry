/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Geometry.Manifold.Algebra.SMul
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
import TauCeti.Geometry.Manifold.PartitionOfUnity.Compact
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Topology.Algebra.ConstMulAction
import TauCeti.Topology.Algebra.Support
import SymplecticGeometry.Analysis.Calculus.BumpFunction.Radial
import SymplecticGeometry.Geometry.Manifold.ContMDiff.Indicator
import SymplecticGeometry.Geometry.Manifold.GroupAction.Average

/-!
# Invariant cut-offs

This file builds smooth cut-off functions that are invariant under a group action.

## In a chart that the action preserves radially

Let `Φ` be a smooth partial diffeomorphism from a real inner product space `V` of finite
dimension to a Hausdorff manifold `M`, and let a group `G` act on `M` so that each `g` sends the
image of a point `z` of the source to the image of a point of the source of the same norm.
Then for `0 ≤ a < b` with `closedBall 0 b` in the source there is a smooth `G`-invariant
function `ρ : M → [0, 1]` that is `1` on `Φ '' closedBall 0 a` and has its support in
`Φ '' closedBall 0 b` (`PartialDiffeomorph.exists_smul_invariant_cutoff`). It is a radial
cut-off of `V` (`SymplecticGeometry.exists_contDiff_norm_cutoff`) read through `Φ⁻¹` and extended
by zero off the target of `Φ`; it is invariant because it depends only on the norm.

Such cut-offs are used to glue invariant objects defined near fixed points of an action, as in
the proof of the Duistermaat–Heckman formula.

## Around a compact set, for a compact Lie group

Let a compact Lie group `G` act smoothly on a boundaryless Hausdorff manifold `M` with a
finite-dimensional model. A compact set `K` inside a `G`-invariant open set `U` has a smooth
`G`-invariant cut-off with values in `[0, 1]`, equal to `1` on a `G`-invariant open neighbourhood
of `K` and with compact topological support inside `U`
(`SymplecticGeometry.exists_invariant_contMDiff_eq_one_of_isCompact`). It is the orbit average
(`SymplecticGeometry.orbitAverage`) of a cut-off around the compact saturation `G • K` given by
Tau Ceti's `IsCompact.exists_contMDiff_one_nhds_tsupport_subset`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §5.6
* G. E. Bredon, *Introduction to Compact Transformation Groups*, Academic Press (1972),
  Chapter VI (averaging over a compact group).
-/

public section

open Set Metric
open scoped Manifold ContDiff

namespace PartialDiffeomorph

variable {E H M V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {G : Type*} [Group G] [MulAction G M]

/-- **An invariant cut-off in a chart.** Let `Φ` be a smooth partial diffeomorphism from
`V`, a real inner product space of finite dimension, to a Hausdorff manifold `M`, and let a group
`G` act on `M` so that for every `g` and every `z` in the source of `Φ`, `g • Φ z = Φ z'` for some
`z'` in the source with `‖z'‖ = ‖z‖`. For `0 ≤ a < b` with `closedBall 0 b` in the source of `Φ`,
there is a smooth function `ρ : M → ℝ` with values in `[0, 1]`, invariant under `G`, equal to `1`
on `Φ '' closedBall 0 a`, and whose support lies in `Φ '' closedBall 0 b`. -/
theorem exists_smul_invariant_cutoff (Φ : PartialDiffeomorph 𝓘(ℝ, V) I V M ∞)
    (hΦ : ∀ g : G, ∀ z ∈ Φ.source, ∃ z' ∈ Φ.source, ‖z'‖ = ‖z‖ ∧ Φ z' = g • Φ z)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : closedBall (0 : V) b ⊆ Φ.source) :
    ∃ ρ : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ ρ ∧ (∀ x, ρ x ∈ Icc 0 1) ∧
      (∀ (g : G) x, ρ (g • x) = ρ x) ∧ EqOn ρ 1 (Φ '' closedBall 0 a) ∧
      tsupport ρ ⊆ Φ '' closedBall 0 b := by
  obtain ⟨h, hc, h01, h1, h0⟩ := SymplecticGeometry.exists_contDiff_norm_cutoff V ha hab
  set ρ : M → ℝ := Φ.target.indicator fun x ↦ h ‖Φ.symm x‖ with hρ
  -- The action preserves the target of `Φ` and the norm of the inverse of `Φ`.
  have hmem {g : G} {x : M} (hx : x ∈ Φ.target) :
      g • x ∈ Φ.target ∧ ‖Φ.symm (g • x)‖ = ‖Φ.symm x‖ := by
    obtain ⟨z', hz', hn, hzx⟩ := hΦ g _ (Φ.map_target hx)
    rw [Φ.right_inv hx] at hzx
    rw [← hzx, Φ.symm_toPartialEquiv, Φ.left_inv hz']
    exact ⟨Φ.map_source hz', hn⟩
  -- The radial cut-off of `V` is supported in `closedBall 0 b`.
  have hcb : tsupport (fun z : V ↦ h ‖z‖) ⊆ closedBall 0 b :=
    TauCeti.tsupport_subset_of_forall_notMem_eq_zero
      (fun z hz ↦ h0 _ (by simpa [abs_norm] using hz)) isClosed_closedBall
  have hcK : IsCompact (tsupport fun z : V ↦ h ‖z‖) :=
    (isCompact_closedBall 0 b).of_isClosed_subset (isClosed_tsupport _) hcb
  refine ⟨ρ, Φ.contMDiff_indicator_comp_symm hc.contMDiff hcK (hcb.trans hb), fun x ↦ ?_,
    fun g x ↦ ?_, ?_,
    (Φ.tsupport_indicator_comp_symm_subset hcK (hcb.trans hb)).trans (image_mono hcb)⟩
  · by_cases hxt : x ∈ Φ.target
    · rw [hρ, indicator_of_mem hxt]
      exact h01 _
    · rw [hρ, indicator_of_notMem hxt]
      exact ⟨le_rfl, zero_le_one⟩
  · by_cases hxt : x ∈ Φ.target
    · obtain ⟨hgx, hn⟩ := hmem (g := g) hxt
      rw [hρ, indicator_of_mem hxt, indicator_of_mem hgx, hn]
    · have hgx : g • x ∉ Φ.target := fun hgx ↦ hxt <| by
        simpa using (hmem (g := g⁻¹) hgx).1
      rw [hρ, indicator_of_notMem hxt, indicator_of_notMem hgx]
  · rintro _ ⟨z, hz, rfl⟩
    have hzs : z ∈ Φ.source := hb (closedBall_subset_closedBall hab.le hz)
    rw [hρ, indicator_of_mem (Φ.map_source hzs), Φ.symm_toPartialEquiv, Φ.left_inv hzs,
      Pi.one_apply]
    exact h1 _ (by rw [abs_norm]; exact mem_closedBall_zero_iff.1 hz)

end PartialDiffeomorph

noncomputable section

open Function TauCeti Topology
open scoped Pointwise

namespace SymplecticGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] (J : ModelWithCorners ℝ E' H')
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [ChartedSpace H' G] [IsManifold J ∞ G] [MulAction G M] [ContMDiffSMul J I ∞ G M]

include J in
/-- **A smooth invariant cutoff around a compact set.** For a compact Lie group `G` acting
smoothly, a compact set `K` inside a `G`-invariant open set `U` has a smooth `G`-invariant
function `ρ` with values in `[0, 1]` that is `1` on a `G`-invariant open neighbourhood `W` of
`K`, and whose topological support is compact and contained in `U`. -/
theorem exists_invariant_contMDiff_eq_one_of_isCompact {K U : Set M} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) (hUinv : ∀ (g : G) (x : M), x ∈ U → g • x ∈ U) :
    ∃ (ρ : M → ℝ) (W : Set M), ContMDiff I 𝓘(ℝ) ∞ ρ ∧ (∀ x, ρ x ∈ Icc 0 1) ∧
      (∀ (g : G) (x : M), ρ (g • x) = ρ x) ∧ IsOpen W ∧ K ⊆ W ∧
      (∀ (g : G) (x : M), x ∈ W → g • x ∈ W) ∧ (∀ x ∈ W, ρ x = 1) ∧
      HasCompactSupport ρ ∧ tsupport ρ ⊆ U := by
  have : ContinuousSMul G M := ⟨(contMDiff_smul (I := J) (I' := I) (n := ∞)).continuous⟩
  -- The saturation `G • K` is compact and lies in `U`.
  have hC : IsCompact ((univ : Set G) • K) := isCompact_univ.smul_set hK
  have hCU : (univ : Set G) • K ⊆ U := by
    rintro _ ⟨a, -, y, hy, rfl⟩
    exact hUinv a y (hKU hy)
  obtain ⟨σ, hσ, hσ1, hσc, hσU, hσ01⟩ := hC.exists_contMDiff_one_nhds_tsupport_subset I hU hCU
  -- The open set where `σ = 1` contains `G • K`; `W` is the set of points whose orbit lies in it.
  set V := interior {x | σ x = 1}
  have hCV : (univ : Set G) • K ⊆ V := subset_interior_iff_mem_nhdsSet.2 hσ1
  set W := {x : M | ∀ a : G, a • x ∈ V}
  have hW : IsOpen W := isOpen_setOf_forall_smul_mem isOpen_interior
  have hKW : K ⊆ W := fun y hy a ↦ hCV (smul_mem_smul (mem_univ a) hy)
  have hWinv (g : G) (x : M) (hx : x ∈ W) : g • x ∈ W := fun a ↦ by
    rw [smul_smul]
    exact hx (a * g)
  -- The saturation `D` of `tsupport σ` is compact, invariant, and lies in `U`.
  set D := (univ : Set G) • tsupport σ
  have hD : IsCompact D := isCompact_univ.smul_set hσc
  have hDU : D ⊆ U := by
    rintro _ ⟨a, -, y, hy, rfl⟩
    exact hUinv a y (hσU hy)
  have hDinv (g : G) (x : M) (hx : x ∈ D) : g • x ∈ D := by
    obtain ⟨a, -, y, hy, rfl⟩ := hx
    exact ⟨g * a, mem_univ _, y, hy, mul_smul g a y⟩
  -- `ρ` is the orbit average of `σ`.
  borelize G
  have hρD (x : M) (hx : x ∉ D) : orbitAverage G σ x = 0 :=
    orbitAverage_eq_zero_of_notMem hDinv (fun y hy ↦ image_eq_zero_of_notMem_tsupport
      fun h ↦ hy ⟨1, mem_univ _, y, h, one_smul G y⟩) hx
  refine ⟨orbitAverage G σ, W, hσ.orbitAverage J, orbitAverage_mem_Icc hσ01, orbitAverage_smul σ,
    hW, hKW, hWinv, fun x hx ↦ orbitAverage_eq_of_eqOn hWinv (fun y hy ↦ ?_) hx,
    HasCompactSupport.intro hD hρD,
    (TauCeti.tsupport_subset_of_forall_notMem_eq_zero hρD hD.isClosed).trans hDU⟩
  simpa using interior_subset (hy 1)

end SymplecticGeometry

end

end
