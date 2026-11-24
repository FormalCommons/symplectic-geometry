/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Analysis.Complex.Euclidean.Space
public import SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Basic
import SymplecticGeometry.Geometry.Manifold.GroupAction.InvariantCutoff

/-!
# Invariant cut-offs at a fixed point, in the weight chart

The localizing one-form of the Duistermaat–Heckman formula is glued from model forms near the
fixed points and an averaged form elsewhere. This file gives the cut-offs of that gluing.

* `SymplecticGeometry.exists_smul_invariant_cutoff_weightChart`: let `Φ` be a smooth partial
  diffeomorphism from `StdSpace (Fin n)` to a Hausdorff manifold `M` with a `G`-action, equivariant
  in the form that `SymplecticGeometry.exists_weightChart` gives, where `g` multiplies each
  complex coordinate by a unit complex number. Then for `0 ≤ a < b` with `closedBall 0 b` in the
  source, some smooth `ρ : M → [0, 1]`, invariant under `G`, equals `1` on `Φ '' closedBall 0 a`
  and has its support in `Φ '' closedBall 0 b`. Since the action preserves the norm in the chart,
  this is a case of `PartialDiffeomorph.exists_smul_invariant_cutoff`.

A form on the chart, pulled back to `M` and multiplied by such a cut-off, is a smooth form on `M`
(`TauCeti.IsSmoothForm.fun_smul_mpullback`), and it is invariant when the form is invariant on
the support of the cut-off (`TauCeti.mpullback_fun_smul_eq_self`).

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §5.6
-/

public section

open Set Metric
open scoped Manifold ContDiff

namespace SymplecticGeometry

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] {G : Type*} [Group G] [MulAction G M]

/-- **An invariant cut-off in the weight chart.** Let `Φ` be a smooth partial diffeomorphism from
`StdSpace (Fin n)` to a Hausdorff manifold `M` with a `G`-action, equivariant as the weight chart
of `SymplecticGeometry.exists_weightChart` is: in the complex coordinates
`z = complexToRealEuclidean (Fin n) u`, `g` sends `Φ z` to `Φ` of `uₖ ↦ χₖ(g) uₖ`, for
maps `χₖ : G → S¹`. For `0 ≤ a < b` with `closedBall 0 b` in the source of `Φ`, there is a
smooth function `ρ : M → ℝ` with values in `[0, 1]`, invariant under `G`, equal to `1` on
`Φ '' closedBall 0 a`, and whose support lies in `Φ '' closedBall 0 b`. -/
theorem exists_smul_invariant_cutoff_weightChart {n : ℕ} (χ : Fin n → G → Circle)
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
