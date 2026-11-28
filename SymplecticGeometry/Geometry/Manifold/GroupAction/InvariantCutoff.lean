/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Geometry.Manifold.Algebra.SMul
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
import TauCeti.Geometry.Manifold.GroupAction.InvariantCutoff
import TauCeti.Topology.Algebra.Support
import SymplecticGeometry.Analysis.Calculus.BumpFunction.Radial
import SymplecticGeometry.Geometry.Manifold.ContMDiff.Indicator
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.Basic
import SymplecticGeometry.Logic.Equiv.PartialEquiv

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
finite-dimensional model. Let `K` be a compact set and `U` an open set that contains `g • x` for
every `g : G` and `x ∈ K`. Then there is a smooth `G`-invariant cut-off with values in `[0, 1]`,
equal to `1` on a `G`-invariant open neighbourhood of `K` and with compact topological support
inside `U` (`IsCompact.exists_invariant_contMDiff_eq_one`). The hypothesis on `U` cannot be
weakened, since such a neighbourhood contains the orbit of every point of `K`. The cut-off is
Tau Ceti's invariant cut-off `IsCompact.exists_contMDiff_one_nhds_tsupport_subset_of_smul_mem`
around the compact saturation `G • K`, and the neighbourhood is the interior of the set where it
equals `1`. Unlike Tau Ceti's statement, this one does not ask `K` to be invariant, only that
`U` contain its saturation `G • K`, and it names an invariant open neighbourhood of `K` on which
the cut-off is `1`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §5.6
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
    rw [← hzx, Φ.left_inv hz']
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
    rw [Pi.one_apply, ← h1 ‖z‖ (by rw [abs_norm]; exact mem_closedBall_zero_iff.1 hz)]
    simpa [hρ] using Φ.toPartialEquiv.indicator_target_comp_symm_apply_self (fun z ↦ h ‖z‖) hzs

end PartialDiffeomorph

open scoped Pointwise

namespace IsCompact

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] (J : ModelWithCorners ℝ E' H')
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [ChartedSpace H' G] [IsManifold J ∞ G] [MulAction G M] [ContMDiffSMul J I ∞ G M]

include J in
omit [I.Boundaryless] in
/-- **A smooth invariant cutoff around a compact set.** For a compact Lie group `G` acting
smoothly, let `K` be a compact set and `U` an open set with `g • x ∈ U` for every `g : G` and
`x ∈ K`. Then there is a smooth `G`-invariant function `ρ` with values in `[0, 1]` that is `1`
on a `G`-invariant open neighbourhood `W` of `K`, and whose topological support is compact and
contained in `U`. -/
theorem exists_invariant_contMDiff_eq_one {K U : Set M} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : ∀ (g : G), ∀ x ∈ K, g • x ∈ U) :
    ∃ (ρ : M → ℝ) (W : Set M), ContMDiff I 𝓘(ℝ) ∞ ρ ∧ (∀ x, ρ x ∈ Icc 0 1) ∧
      (∀ (g : G) (x : M), ρ (g • x) = ρ x) ∧ IsOpen W ∧ K ⊆ W ∧
      (∀ (g : G) (x : M), x ∈ W → g • x ∈ W) ∧ (∀ x ∈ W, ρ x = 1) ∧
      HasCompactSupport ρ ∧ tsupport ρ ⊆ U := by
  have : ContinuousSMul G M := ContMDiffSMul.continuousSMul (I := J) (I' := I) ∞
  -- Tau Ceti's invariant cut-off around the saturation `G • K`, which is compact, invariant and
  -- lies in `U`.
  have hKC : K ⊆ (univ : Set G) • K := fun y hy ↦ ⟨1, mem_univ _, y, hy, one_smul G y⟩
  have hC : IsCompact ((univ : Set G) • K) := isCompact_univ.smul_set hK
  have hCU : (univ : Set G) • K ⊆ U := by
    rintro _ ⟨a, -, y, hy, rfl⟩
    exact hKU a y hy
  have hCinv (g : G) (x : M) (hx : x ∈ (univ : Set G) • K) : g • x ∈ (univ : Set G) • K := by
    obtain ⟨a, -, y, hy, rfl⟩ := hx
    exact ⟨g * a, mem_univ _, y, hy, mul_smul g a y⟩
  obtain ⟨ρ, hρ, hρ1, hρc, hρU, hρ01, hρinv⟩ :=
    hC.exists_contMDiff_one_nhds_tsupport_subset_of_smul_mem I J hU hCU hCinv
  -- `W` is the interior of the level set `ρ = 1`, which is invariant since `ρ` is.
  have hWinv (g : G) (x : M) (hx : x ∈ interior {x | ρ x = 1}) :
      g • x ∈ interior {x | ρ x = 1} := by
    have hsub : g • interior {x | ρ x = 1} ⊆ interior {x | ρ x = 1} := by
      refine interior_maximal ?_ (isOpen_interior.smul g)
      rintro _ ⟨y, hy, rfl⟩
      simpa [hρinv] using interior_subset hy
    exact hsub (smul_mem_smul_set hx)
  exact ⟨ρ, interior {x | ρ x = 1}, hρ, hρ01, hρinv, isOpen_interior,
    hKC.trans (subset_interior_iff_mem_nhdsSet.2 hρ1), hWinv, fun x hx ↦ interior_subset hx,
    hρc, hρU⟩

end IsCompact

end
