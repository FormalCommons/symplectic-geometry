/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import TauCeti.Analysis.Complex.Euclidean.Space
public import SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import SymplecticGeometry.Geometry.Manifold.ContMDiff.Indicator

/-!
# Invariant cut-offs at a fixed point, in the weight chart

The localizing one-form of the Duistermaat–Heckman formula is glued from model forms near the
fixed points and an averaged form elsewhere. This file gives the cut-offs of that gluing.

* `PartialDiffeomorph.exists_smul_invariant_cutoff`: let `Φ` be a smooth partial diffeomorphism
  from `V`, a real inner product space of finite dimension, to a Hausdorff manifold `M`, on
  which a group `G` acts, such that `g • Φ z = Φ z'` for some `z'` of the source with
  `‖z'‖ = ‖z‖`. Then for `0 ≤ a < b` with `closedBall 0 b` in the source, some smooth
  `ρ : M → [0, 1]`, invariant under `G`, equals `1` on `Φ '' closedBall 0 a` and has its
  support in `Φ '' closedBall 0 b`. It is the radial profile
  `smoothTransition ((b² - ‖z‖²) / (b² - a²))` read through `Φ⁻¹`, and extended by zero off the
  target of `Φ`.
* `SymplecticGeometry.exists_smul_invariant_cutoff_weightChart`: the same for a chart that is
  equivariant in the form that `SymplecticGeometry.exists_weightChart` gives, where `g`
  multiplies each complex coordinate by a unit complex number, which preserves the norm.

A form on the chart, pulled back to `M` and multiplied by such a cut-off, is a smooth form on `M`
(`TauCeti.IsSmoothForm.fun_smul_mpullback`), and it is invariant when the form is invariant on
the support of the cut-off (`TauCeti.mpullback_fun_smul_eq_self`).

The radial profile is that of Tau Ceti's private `smoothTransition_radial_cutoff`
(`TauCeti/Analysis/Calculus/BumpFunction/Cutoff.lean`), centred at `0`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §5.6
-/

public section

noncomputable section

open Set Metric
open scoped Manifold ContDiff

/-! ### The cut-off in a chart -/

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
  have hD : 0 < b ^ 2 - a ^ 2 := by nlinarith
  -- The radial profile, as a function of the norm.
  set h : ℝ → ℝ := fun t ↦ Real.smoothTransition ((b ^ 2 - t ^ 2) / (b ^ 2 - a ^ 2))
  have h0 {t : ℝ} (ht : 0 ≤ t) (hbt : t ∉ Icc 0 b) : h t = 0 := by
    refine Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg ?_ hD.le)
    have : b < t := lt_of_not_ge fun h' ↦ hbt ⟨ht, h'⟩
    nlinarith
  have h1 {t : ℝ} (ht : 0 ≤ t) (hat : t ≤ a) : h t = 1 :=
    Real.smoothTransition.one_of_one_le <| by rw [le_div_iff₀ hD]; nlinarith
  have hc : ContDiff ℝ ∞ fun z : V ↦ h ‖z‖ :=
    Real.smoothTransition.contDiff.comp ((contDiff_const.sub (contDiff_norm_sq ℝ)).div_const _)
  set ρ : M → ℝ := Φ.target.indicator fun x ↦ h ‖Φ.symm x‖ with hρ
  -- The action preserves the target of `Φ` and the norm of the inverse of `Φ`.
  have hmem {g : G} {x : M} (hx : x ∈ Φ.target) :
      g • x ∈ Φ.target ∧ ‖Φ.symm (g • x)‖ = ‖Φ.symm x‖ := by
    obtain ⟨z', hz', hn, hzx⟩ := hΦ g _ (Φ.map_target hx)
    rw [Φ.right_inv hx] at hzx
    rw [← hzx, Φ.symm_toPartialEquiv, Φ.left_inv hz']
    exact ⟨Φ.map_source hz', hn⟩
  have hK : IsCompact (Φ '' closedBall 0 b) :=
    (isCompact_closedBall 0 b).image_of_continuousOn
      (Φ.toOpenPartialHomeomorph.continuousOn.mono hb)
  -- Off `Φ '' closedBall 0 b`, `ρ` vanishes.
  have hzero {x : M} (hx : x ∉ Φ '' closedBall 0 b) : ρ x = 0 := by
    by_cases hxt : x ∈ Φ.target
    · rw [hρ, indicator_of_mem hxt]
      refine h0 (norm_nonneg _) fun ⟨_, hbx⟩ ↦ hx ⟨Φ.symm x, ?_, Φ.right_inv hxt⟩
      rwa [mem_closedBall_zero_iff]
    · exact indicator_of_notMem hxt _
  refine ⟨ρ, ?_, fun x ↦ ?_, fun g x ↦ ?_, ?_, ?_⟩
  · refine Φ.symm.toOpenPartialHomeomorph.contMDiff_of_contMDiffOn_source_of_contMDiffOn_compl
      (isCompact_closedBall 0 b) (by simpa using hb) ?_ ?_
    · refine (hc.contMDiff.comp_contMDiffOn Φ.symm.contMDiffOn).congr fun x hx ↦ ?_
      exact indicator_of_mem (by simpa using hx) _
    · refine contMDiffOn_const.congr fun x hx ↦ hzero ?_
      simpa using hx
  · by_cases hxt : x ∈ Φ.target
    · rw [hρ, indicator_of_mem hxt]
      exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
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
    exact h1 (norm_nonneg _) (mem_closedBall_zero_iff.1 hz)
  · exact closure_minimal (fun x hx ↦ by_contra fun h' ↦ hx (hzero h')) hK.isClosed

end PartialDiffeomorph

/-! ### The cut-off in the weight chart -/

namespace SymplecticGeometry

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] {G : Type*} [TopologicalSpace G] [Group G] [MulAction G M]

/-- **An invariant cut-off in the weight chart.** Let `Φ` be a smooth partial diffeomorphism from
`StdSpace (Fin n)` to a Hausdorff manifold `M` with a `G`-action, equivariant as the weight chart
of `SymplecticGeometry.exists_weightChart` is: in the complex coordinates
`z = complexToRealEuclidean (Fin n) u`, `g` sends `Φ z` to `Φ` of `uₖ ↦ χₖ(g) uₖ`, for
characters `χₖ : G → S¹`. For `0 ≤ a < b` with `closedBall 0 b` in the source of `Φ`, there is a
smooth function `ρ : M → ℝ` with values in `[0, 1]`, invariant under `G`, equal to `1` on
`Φ '' closedBall 0 a`, and whose support lies in `Φ '' closedBall 0 b`. -/
theorem exists_smul_invariant_cutoff_weightChart {n : ℕ} (χ : Fin n → G →ₜ* Circle)
    (Φ : PartialDiffeomorph 𝓘(ℝ, StdSpace (Fin n)) I (StdSpace (Fin n)) M ∞)
    (hequiv : ∀ g : G, ∀ u : Fin n → ℂ, TauCeti.complexToRealEuclidean (Fin n) u ∈ Φ.source →
      TauCeti.complexToRealEuclidean (Fin n) (fun k ↦ (χ k g : ℂ) * u k) ∈ Φ.source ∧
        Φ (TauCeti.complexToRealEuclidean (Fin n) fun k ↦ (χ k g : ℂ) * u k) =
          g • Φ (TauCeti.complexToRealEuclidean (Fin n) u))
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : closedBall (0 : StdSpace (Fin n)) b ⊆ Φ.source) :
    ∃ ρ : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ ρ ∧ (∀ x, ρ x ∈ Icc 0 1) ∧
      (∀ (g : G) x, ρ (g • x) = ρ x) ∧ EqOn ρ 1 (Φ '' closedBall 0 a) ∧
      tsupport ρ ⊆ Φ '' closedBall 0 b := by
  refine Φ.exists_smul_invariant_cutoff (fun g z hz ↦ ?_) ha hab hb
  set e := TauCeti.complexToRealEuclidean (Fin n)
  obtain ⟨u, rfl⟩ : ∃ u, e u = z := ⟨e.symm z, e.apply_symm_apply z⟩
  obtain ⟨hs, hΦ⟩ := hequiv g u hz
  refine ⟨_, hs, ?_, hΦ⟩
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sq_complexToRealEuclidean,
    norm_sq_complexToRealEuclidean]
  simp

end SymplecticGeometry

end
