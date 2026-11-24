/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Topology.Algebra.Support
import SymplecticGeometry.Analysis.Calculus.BumpFunction.Radial
import SymplecticGeometry.Geometry.Manifold.ContMDiff.Indicator
import SymplecticGeometry.Topology.OpenPartialHomeomorph.Compact

/-!
# Invariant cut-offs in a chart that the action preserves radially

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
    rw [← hzx, Φ.symm_toPartialEquiv, Φ.left_inv hz']
    exact ⟨Φ.map_source hz', hn⟩
  have hK : IsCompact (Φ '' closedBall 0 b) :=
    Φ.toOpenPartialHomeomorph.isCompact_image_of_subset_source (isCompact_closedBall 0 b) hb
  -- Off `Φ '' closedBall 0 b`, `ρ` vanishes.
  have hzero {x : M} (hx : x ∉ Φ '' closedBall 0 b) : ρ x = 0 := by
    by_cases hxt : x ∈ Φ.target
    · rw [hρ, indicator_of_mem hxt, h0]
      rw [abs_norm, ← not_le, ← mem_closedBall_zero_iff]
      exact fun hbx ↦ hx ⟨Φ.symm x, hbx, Φ.right_inv hxt⟩
    · exact indicator_of_notMem hxt _
  refine ⟨ρ, ?_, fun x ↦ ?_, fun g x ↦ ?_, ?_,
    TauCeti.tsupport_subset_of_forall_notMem_eq_zero (fun _ hx ↦ hzero hx) hK.isClosed⟩
  · refine Φ.symm.toOpenPartialHomeomorph.contMDiff_of_contMDiffOn_source_of_contMDiffOn_compl
      (isCompact_closedBall 0 b) (by simpa using hb) ?_ ?_
    · refine (hc.contMDiff.comp_contMDiffOn Φ.symm.contMDiffOn).congr fun x hx ↦ ?_
      exact indicator_of_mem (by simpa using hx) _
    · refine contMDiffOn_const.congr fun x hx ↦ hzero ?_
      simpa using hx
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

end
