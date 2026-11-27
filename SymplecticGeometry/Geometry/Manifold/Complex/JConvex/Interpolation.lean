/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import TauCeti.Geometry.Manifold.Morse.Hessian
import SymplecticGeometry.Analysis.Calculus.FDeriv.FirstOrderVanishing
import SymplecticGeometry.Analysis.Calculus.FDeriv.Glaeser
import SymplecticGeometry.Geometry.Manifold.Immersion.InfDist
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic

/-!
# Interpolation along a totally real submanifold

This file is meant to hold the interpolation of two strictly plurisubharmonic functions with the
same 1-jet along a compact part of a totally real submanifold (Proposition 3.26 of
Cieliebak–Eliashberg). For now it contains the Taylor bounds that the proof uses near a point of
the submanifold.

## Main results

* `Manifold.IsSmoothEmbedding.exists_abs_comp_symm_le`: let `ι : N → M` be a `C^n` embedding,
  `n ≥ 2`, of a boundaryless manifold into a manifold modelled on a finite-dimensional real
  normed space `E`, let `ρ : M → ℝ` be `C²` at `ι y`, nonnegative near `ι y`, zero on the image
  of `ι` near `ι y`, with critical Hessian at `ι y` positive off the tangent image of `ι`, and
  let `D : M → ℝ` be `C²` near `ι y`, with `D` and its differential zero at the points `ι y'`
  for `y'` near `y`. Then, in a chart `e` of the `C²` maximal atlas at `ι y`, there is `A` with
  `|D x| ≤ A * ρ x`, `‖fderiv ℝ (D ∘ e.symm) z‖ ≤ A * √(ρ x)`,
  `‖fderiv ℝ (ρ ∘ e.symm) z‖ ≤ A * √(ρ x)` and `‖fderiv ℝ (fderiv ℝ (ρ ∘ e.symm)) z‖ ≤ A`
  for `z` near `e (ι y)` and `x = e.symm z`.

The function `ρ` is the one that
`Manifold.IsSmoothEmbedding.exists_contMDiff_isManifoldStrictlyPlurisubharmonicAt_of_isCompact`
gives near a compact part of a totally real submanifold of a complex manifold, and `D` the
difference of the two functions to be interpolated. Charts of the holomorphic maximal atlas are
in the real one (Tau Ceti's `IsManifold.maximalAtlas_subset_restrictScalars`), so the lemma
applies to them. Neither the complex structure nor total reality enters the proof.

The proof works in the chart, with `Z = e '' (e.source ∩ range ι)`. The squared distance to `Z`
is at most a multiple of `ρ`
(`Manifold.IsImmersionAt.exists_eventually_infDist_sq_le_mul`). Since `D ∘ e.symm` vanishes to
first order on `Z` near `e (ι y)` (here `ι` being an embedding matters: the points of `Z` near
`e (ι y)` are images of points near `y`), it is at most a multiple of the squared distance to
`Z`, and its derivative at most a multiple of the distance
(`IsCompact.exists_eventually_norm_le_mul_infDist_sq_and_norm_fderiv_le_mul_infDist`). The bound
on the derivative of `ρ ∘ e.symm` is Glaeser's inequality
(`IsCompact.exists_eventually_norm_fderiv_le_mul_sqrt`), and that on its second derivative is
continuity at `e (ι y)`. These are the estimates by which Cieliebak–Eliashberg bound the
derivatives of the cutoff and of the difference of the two functions in their proof of
Proposition 3.26; the route through Glaeser's inequality and the distance to the submanifold is
the one this library takes, and we do not claim that it follows their lemmas step by step.

## References

* [K. Cieliebak, Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  Proposition 3.26
* G. Glaeser, *Racine carrée d'une fonction différentiable*, Ann. Inst. Fourier 13 (1963),
  no. 2, 203–210.
-/

public section

open Set Function Filter Metric Manifold Topology TauCeti
open scoped ContDiff Manifold

namespace Manifold.IsSmoothEmbedding

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {n : WithTop ℕ∞} {ι : N → M} {y : N} {ρ D : M → ℝ}

/-- **Taylor bounds near an embedded submanifold.** Let `ι` be a `C^n` embedding, `n ≥ 2`, of a
boundaryless manifold into a manifold modelled on a finite-dimensional real normed space `E`.
Let `ρ` be `C²` at `ι y`, nonnegative near `ι y`, with `ρ ∘ ι` zero near `y` and with critical
Hessian at `ι y` positive on every vector off the tangent image of `ι`. Let `D` be `C²` near
`ι y`, with `D (ι y') = 0` and `mvfderiv 𝓘(ℝ, E) D (ι y') = 0` for `y'` near `y`. Then for every
chart `e` of the `C²` maximal atlas whose source contains `ι y` there is `A` such that for all
`z` near `e (ι y)`, with `x = e.symm z`: `|D x| ≤ A * ρ x`,
`‖fderiv ℝ (D ∘ e.symm) z‖ ≤ A * √(ρ x)`, `‖fderiv ℝ (ρ ∘ e.symm) z‖ ≤ A * √(ρ x)` and
`‖fderiv ℝ (fderiv ℝ (ρ ∘ e.symm)) z‖ ≤ A`. -/
theorem exists_abs_comp_symm_le [I'.Boundaryless] (h : IsSmoothEmbedding I' 𝓘(ℝ, E) n ι)
    (hn : 2 ≤ n) (hρ : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 ρ (ι y)) (hρ0 : ∀ᶠ x in 𝓝 (ι y), 0 ≤ ρ x)
    (hρι : ∀ᶠ y' in 𝓝 y, ρ (ι y') = 0)
    (hpos : ∀ v ∉ LinearMap.range (mfderiv I' 𝓘(ℝ, E) ι y).toLinearMap,
      0 < criticalHessian 𝓘(ℝ, E) ρ (ι y) v v)
    (hD : ∀ᶠ x in 𝓝 (ι y), ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 D x)
    (hDι : ∀ᶠ y' in 𝓝 y, D (ι y') = 0 ∧ mvfderiv 𝓘(ℝ, E) D (ι y') = 0)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 2 M)
    (hy : ι y ∈ e.source) :
    ∃ A, ∀ᶠ z in 𝓝 (e (ι y)),
      |D (e.symm z)| ≤ A * ρ (e.symm z) ∧
      ‖fderiv ℝ (D ∘ e.symm) z‖ ≤ A * √(ρ (e.symm z)) ∧
      ‖fderiv ℝ (ρ ∘ e.symm) z‖ ≤ A * √(ρ (e.symm z)) ∧
      ‖fderiv ℝ (fderiv ℝ (ρ ∘ e.symm)) z‖ ≤ A := by
  have he1 : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 1 M :=
    IsManifold.maximalAtlas_subset_of_le (by norm_num) he
  have hsymm : ∀ f : M → ℝ, f ∘ (e.extend 𝓘(ℝ, E)).symm = f ∘ e.symm := fun f ↦ by
    simp
  have hext : ∀ x, e.extend 𝓘(ℝ, E) x = e x := fun x ↦ by simp
  set z₀ := e (ι y)
  set Z := e '' (e.source ∩ range ι)
  have hz₀ : z₀ ∈ e.target := e.map_source hy
  have hsymm_tendsto : Tendsto e.symm (𝓝 z₀) (𝓝 (ι y)) := by
    have := (e.continuousAt_symm hz₀).tendsto
    rwa [e.left_inv hy] at this
  -- The squared distance to `Z` is at most a multiple of `ρ`.
  obtain ⟨C, hC⟩ := (h.isImmersion.isImmersionAt y).exists_eventually_infDist_sq_le_mul hn hρ
    hρ0 hρι hpos he1 hy
  -- Glaeser's inequality for `ρ ∘ e.symm`.
  have hf : ContDiffAt ℝ 2 (ρ ∘ e.symm) z₀ := by
    have := (contMDiffAt_iff_contDiffAt_comp_extend_symm he hy).1 hρ
    rwa [hsymm, hext] at this
  obtain ⟨A₁, hA₁⟩ := (isCompact_singleton (x := z₀)).exists_eventually_norm_fderiv_le_mul_sqrt
    (by simpa using hf) (by rw [nhdsSet_singleton]; exact hsymm_tendsto.eventually hρ0)
  rw [nhdsSet_singleton] at hA₁
  -- The second derivative of `ρ ∘ e.symm` is continuous at `z₀`, hence bounded near it.
  have hB : ∀ᶠ z in 𝓝 z₀, ‖fderiv ℝ (fderiv ℝ (ρ ∘ e.symm)) z‖ <
      ‖fderiv ℝ (fderiv ℝ (ρ ∘ e.symm)) z₀‖ + 1 :=
    ((hf.fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0)
      (by norm_num)).continuousAt.norm.eventually_lt continuousAt_const (lt_add_one _)
  -- An open set `U ∋ z₀` on which `D ∘ e.symm` is `C²`, and the points of `Z` in `U` that are
  -- images of points where `D` vanishes to first order.
  obtain ⟨O', hO', hO'W⟩ : ∃ O' ∈ 𝓝 (ι y), ι ⁻¹' O' ⊆
      {y' | D (ι y') = 0 ∧ mvfderiv 𝓘(ℝ, E) D (ι y') = 0} := by
    rw [h.isEmbedding.isInducing.nhds_eq_comap] at hDι
    exact hDι
  obtain ⟨O, hOsub, hOo, hyO⟩ := mem_nhds_iff.1 (inter_mem hD hO')
  set U := e.target ∩ e.symm ⁻¹' O
  have hUo : IsOpen U := e.isOpen_inter_preimage_symm hOo
  have hz₀U : z₀ ∈ U := ⟨hz₀, by simpa [z₀, e.left_inv hy] using hyO⟩
  have hgU : ContDiffOn ℝ 2 (D ∘ e.symm) U := fun z hz ↦ by
    have hx := e.map_target hz.1
    have := (contMDiffAt_iff_contDiffAt_comp_extend_symm he hx).1 (hOsub hz.2).1
    rw [hsymm, hext, e.right_inv hz.1] at this
    exact this.contDiffWithinAt
  have hZU : ∀ z ∈ Z ∩ U, ∃ y', e.symm z = ι y' ∧ ι y' ∈ e.source ∧ z = e (ι y') ∧
      D (ι y') = 0 ∧ mvfderiv 𝓘(ℝ, E) D (ι y') = 0 := by
    rintro z ⟨⟨x, ⟨hxs, y', rfl⟩, rfl⟩, -, hzO⟩
    rw [mem_preimage, e.left_inv hxs] at hzO
    exact ⟨y', e.left_inv hxs, hxs, rfl, hO'W (hOsub hzO).2⟩
  obtain ⟨A₂, hA₂⟩ :=
    IsCompact.exists_eventually_norm_le_mul_infDist_sq_and_norm_fderiv_le_mul_infDist
      (K := {z₀}) isCompact_singleton
      (Z := Z) (U := U) (singleton_subset_iff.2 (mem_image_of_mem e ⟨hy, mem_range_self y⟩))
      hUo (singleton_subset_iff.2 hz₀U) hgU
      (fun z hz ↦ by
        obtain ⟨y', hzy, -, -, hD0, -⟩ := hZU z hz
        simp [hzy, hD0])
      (fun z hz ↦ by
        obtain ⟨y', -, hys, rfl, -, hD1⟩ := hZU z hz
        have := (mvfderiv_eq_zero_iff_fderiv_comp_extend_symm_eq_zero he1 hys).1 hD1
        rwa [hsymm, hext] at this)
  rw [nhdsSet_singleton] at hA₂
  -- Combine the bounds.
  set A₂' := max A₂ 0
  set C' := max C 0
  set B := ‖fderiv ℝ (fderiv ℝ (ρ ∘ e.symm)) z₀‖ + 1
  refine ⟨max (A₂' * C') (max (A₂' * √C') (max (max A₁ 0) B)), ?_⟩
  filter_upwards [hC, hA₁, hB, hA₂, hsymm_tendsto.eventually hρ0] with z hCz hA₁z hBz hA₂z hρz
  set d := infDist z Z
  have hd : 0 ≤ d := infDist_nonneg
  have hd2 : d ^ 2 ≤ C' * ρ (e.symm z) :=
    hCz.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hρz)
  have hdsqrt : d ≤ √C' * √(ρ (e.symm z)) := by
    rw [← Real.sqrt_mul (le_max_right _ _), ← Real.sqrt_sq hd]
    exact Real.sqrt_le_sqrt hd2
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc |D (e.symm z)| = ‖(D ∘ e.symm) z‖ := by rw [Real.norm_eq_abs, comp_apply]
      _ ≤ A₂ * d ^ 2 := hA₂z.1
      _ ≤ A₂' * d ^ 2 := by gcongr; exact le_max_left _ _
      _ ≤ A₂' * (C' * ρ (e.symm z)) := by gcongr
      _ = A₂' * C' * ρ (e.symm z) := by ring
      _ ≤ _ := by gcongr; exact le_max_left _ _
  · calc ‖fderiv ℝ (D ∘ e.symm) z‖ ≤ A₂ * d := hA₂z.2
      _ ≤ A₂' * d := by gcongr; exact le_max_left _ _
      _ ≤ A₂' * (√C' * √(ρ (e.symm z))) := by gcongr
      _ = A₂' * √C' * √(ρ (e.symm z)) := by ring
      _ ≤ _ := by gcongr; exact (le_max_left _ _).trans (le_max_right _ _)
  · calc ‖fderiv ℝ (ρ ∘ e.symm) z‖ ≤ A₁ * √(ρ (e.symm z)) := by simpa using hA₁z
      _ ≤ _ := by
        gcongr
        exact (le_max_left _ _).trans ((le_max_left _ _).trans
          ((le_max_right _ _).trans (le_max_right _ _)))
  · exact hBz.le.trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))

end Manifold.IsSmoothEmbedding

end
