/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.Basic
public import TauCeti.Geometry.Manifold.DeRham.HomotopyInvariance
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality

/-!
# Pullbacks of closed forms

A complement to Tau Ceti's `TauCeti/Geometry/Manifold/DeRham/Map.lean`: the membership form of
the fact that a smooth map pulls closed forms back to closed forms,
`TauCeti.SmoothForm.mpullback_mem_closedForms`. It lets a caller state closedness of
`SmoothForm.mpullback f hf φ` directly, without passing through the subtype map
`TauCeti.closedForms.mpullback`. Also the form-level consequence of homotopy invariance,
`TauCeti.SmoothForm.mpullback_sub_mem_exactForms_of_homotopy`: smoothly homotopic maps pull a
closed form back to forms that differ by an exact form.

## References

* [R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §2 (pullback
  commutes with the exterior derivative) and §4 (homotopy invariance).
-/

public section

open scoped ContDiff Manifold

namespace TauCeti.SmoothForm

variable {E H E' H' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'}
  {M M' : Type*}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' 2 M']

/-- The pullback of a closed smooth form along a smooth map is closed. -/
theorem mpullback_mem_closedForms (f : M → M') (hf : ContMDiff I I' ∞ f) {k : ℕ}
    {φ : SmoothForm I' M' ℝ k} (hφ : φ ∈ closedForms I' M' k) :
    SmoothForm.mpullback f hf φ ∈ closedForms I M k := by
  rw [mem_closedForms_iff_mextDerivₗ_eq_zero, SmoothForm.mextDerivₗ_mpullback,
    (mem_closedForms_iff_mextDerivₗ_eq_zero I' φ).mp hφ, map_zero]

/-- **Homotopic maps pull back closed forms to cohomologous forms.** If `F : M × [0, 1] → M'`
is a smooth homotopy from `f` to `g`, then for every closed real form `γ` on `M'` the difference
`f^* γ - g^* γ` is exact. -/
theorem mpullback_sub_mem_exactForms_of_homotopy [IsManifold I ∞ M] {f g : M → M'}
    (hf : ContMDiff I I' ∞ f) (hg : ContMDiff I I' ∞ g) {F : M × Set.Icc (0 : ℝ) 1 → M'}
    (hF : ContMDiff (I.prod (𝓡∂ 1)) I' ∞ F) (h₀ : ∀ x, F (x, 0) = f x)
    (h₁ : ∀ x, F (x, 1) = g x) {k : ℕ} {γ : SmoothForm I' M' ℝ k}
    (hγ : γ ∈ closedForms I' M' k) :
    SmoothForm.mpullback f hf γ - SmoothForm.mpullback g hg γ ∈ exactForms I M k := by
  have h := congrArg (· (deRhamCohomology.mk I' k ⟨γ, hγ⟩))
    (deRhamCohomology.map_eq_of_homotopy hf hg hF h₀ h₁ k)
  simp only [deRhamCohomology.map_mk] at h
  rw [← sub_eq_zero, ← map_sub, deRhamCohomology.mk_eq_zero_iff] at h
  simpa using h

end TauCeti.SmoothForm

end
