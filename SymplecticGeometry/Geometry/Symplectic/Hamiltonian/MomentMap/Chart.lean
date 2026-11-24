/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap
public import TauCeti.Geometry.Symplectic.StandardCompatible
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# A moment map read in a symplectic chart

Let `μ` be a moment map, in Tau Ceti's sign `σ(Z_M, ·) = dμ^Z`, of an infinitesimal action
`Z ↦ Z_M` on a symplectic manifold `(M, σ)`. In a chart of `M` with values in `V × V` that carries
`σ` to the standard symplectic form `ω₀`, the components of `μ` are read as functions on `V × V`,
and their derivatives are given by `ω₀` and the images of the generators under the chart.

## Main results

* `TauCeti.SmoothTwoForm.IsMomentMap.fderiv_comp_symm_apply`: the derivative at `chart y` of
  `μ^Z ∘ chart⁻¹` is `ω₀(dchart_y (Z_M(y)), ·)`.
-/

public section

open scoped ContDiff Manifold

namespace TauCeti.SmoothTwoForm.IsMomentMap

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤] {σ : SmoothTwoForm I' M}
  {a : InfinitesimalAction 𝔤 I' M} {μ : M → Module.Dual ℝ 𝔤}

/-- **The derivative of a moment map in a symplectic chart.** Let `μ` be a moment map of an
infinitesimal action `Z ↦ Z_M` for `σ`, and let `chart` be a partial diffeomorphism of `M` onto
an open subset of `V × V` that carries `σ` at `y` to the standard symplectic form `ω₀`. Then the
derivative at `chart y` of the component `μ^Z` read in the chart is `ω₀(dchart_y (Z_M(y)), ·)`. -/
theorem fderiv_comp_symm_apply (h : σ.IsMomentMap a μ)
    (chart : PartialDiffeomorph I' 𝓘(ℝ, V × V) M (V × V) ∞) {y : M} (hy : y ∈ chart.source)
    (hform : ∀ v w : TangentSpace I' y,
      σ.eval₂ y v w = stdSymplecticForm (mvfderiv I' chart y v) (mvfderiv I' chart y w))
    (Z : 𝔤) (w : V × V) :
    fderiv ℝ (fun z ↦ μ (chart.symm z) Z) (chart y) w =
      stdSymplecticForm (mfderiv I' 𝓘(ℝ, V × V) chart y (a Z y)) w := by
  obtain ⟨z, hz, rfl⟩ : ∃ z ∈ chart.target, chart.symm z = y :=
    ⟨chart y, chart.map_source hy, chart.left_inv hy⟩
  -- Rewriting `chart (chart.symm z) = z` everywhere would leave a vector of the tangent space at
  -- `chart (chart.symm z)` where one at `z` is expected, so only the left side is rewritten.
  conv_lhs => erw [chart.right_inv hz]
  set u := mfderiv 𝓘(ℝ, V × V) I' chart.symm z w
  have h1 := (mvfderiv_eq_fderiv_apply (𝕜 := ℝ) ((fun x ↦ μ x Z) ∘ chart.symm) z w).symm
  have h2 := mvfderiv_apply_eq_mfderiv_apply (𝕜 := ℝ) (I := 𝓘(ℝ, V × V))
    ((fun x ↦ μ x Z) ∘ chart.symm) z w
  have h3 := mfderiv_comp_apply_of_eq z (h.mdifferentiableAt Z _)
    (chart.symm.mdifferentiableAt (by simp) hz) rfl w
  have h4 := mvfderiv_apply_eq_mfderiv_apply (𝕜 := ℝ) (I := I') (fun x ↦ μ x Z) (chart.symm z) u
  have h5 := h.eval₂_apply Z (chart.symm z) u
  have h6 := hform (a Z (chart.symm z)) u
  have h7 : mvfderiv I' chart (chart.symm z) u = w := by
    rw [mvfderiv_apply_eq_mfderiv_apply]
    exact chart.mfderiv_apply_mfderiv_symm_apply (by simp) hz w
  rw [h7, mvfderiv_apply_eq_mfderiv_apply] at h6
  exact h1.trans (h2.trans (h3.trans (h4.symm.trans (h5.symm.trans h6))))

end TauCeti.SmoothTwoForm.IsMomentMap

end
