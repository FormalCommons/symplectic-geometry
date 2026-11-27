/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import TauCeti.Geometry.Manifold.Complex.LeviForm
public import TauCeti.Geometry.Manifold.Morse.Hessian
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import SymplecticGeometry.Analysis.Calculus.FDeriv.Glaeser
import SymplecticGeometry.Analysis.Complex.Pseudoconvex
import SymplecticGeometry.Geometry.Manifold.Immersion.InfDist
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Geometry.Manifold.Complex.Analytic
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic

/-!
# Interpolation along a totally real submanifold

This file is meant to hold the interpolation of two strictly plurisubharmonic functions with the
same 1-jet along a compact part of a totally real submanifold (Proposition 3.26 of
Cieliebak–Eliashberg). For now it contains the Taylor bounds that the proof uses near a point of
the submanifold, and the uniform local data, on a closed ball of a holomorphic chart, from which
the proof chooses its constants.

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
* `Manifold.IsSmoothEmbedding.exists_closedBall_abs_sub_le_and_le_re_leviForm`: for `M` a
  manifold modelled on a finite-dimensional complex space, `φ` and `ψ` strictly plurisubharmonic
  at `ι y` and with the same 1-jet at the points `ι y'`, and a chart `e` at `ι y` of the
  holomorphic maximal atlas, there is a closed ball about `e (ι y)` in `e.target`, sent by
  `e.symm` into a given neighbourhood of `ι y`, on which the Taylor bounds for `D = ψ - φ` hold
  with one constant `A`, the Levi forms of `φ ∘ e.symm` and `ψ ∘ e.symm` are bounded below by
  `m * ‖v‖ ^ 2` with one `m > 0`, and `‖fderiv ℝ (φ ∘ e.symm)‖ ≥ m` if `ι y` is not a critical
  point of `φ`.

The function `ρ` is the one that
`Manifold.IsSmoothEmbedding.exists_contMDiff_isManifoldStrictlyPlurisubharmonicAt_of_isCompact`
gives near a compact part of a totally real submanifold of a complex manifold, and `D` the
difference of the two functions to be interpolated. Charts of the holomorphic maximal atlas are
in the real `C²` one (Tau Ceti's `IsManifold.maximalAtlas_subset_restrictScalars_of_ne_zero`), so
the lemma applies to them. Neither the complex structure nor total reality enters the proof.

The proof works in the chart, with `Z = e '' (e.source ∩ range ι)`. The squared distance to `Z`
is at most a multiple of `ρ`
(`Manifold.IsImmersionAt.exists_eventually_infDist_sq_le_mul`). Since `ι` is an embedding and `D`
vanishes to first order along it, `|D ∘ e.symm|` is at most a multiple of the squared distance to
`Z`, and its derivative at most a multiple of the distance
(`Topology.IsEmbedding.exists_eventually_abs_comp_symm_le_mul_infDist_sq`). The bound
on the derivative of `ρ ∘ e.symm` is Glaeser's inequality
(`IsCompact.exists_eventually_norm_fderiv_le_mul_sqrt`), and that on its second derivative is
continuity at `e (ι y)`. These are the estimates by which Cieliebak–Eliashberg bound the
derivatives of the cutoff and of the difference of the two functions in their proof of
Proposition 3.26; the route through Glaeser's inequality and the distance to the submanifold is
the one this library takes, and we do not claim that it follows their lemmas step by step.

The uniform local data come from shrinking a ball about `e (ι y)`: the coordinate expressions of
`φ` and `ψ` are strictly plurisubharmonic near `e (ι y)` by
`TauCeti.isManifoldStrictlyPlurisubharmonicAt_iff_of_mem_maximalAtlas` and
`TauCeti.IsStrictlyPlurisubharmonicAt.eventually`, the lower bound `m` on the closed ball is
`IsCompact.exists_pos_mul_sq_norm_le_re_leviForm_of_isStrictlyPlurisubharmonicAt` (in
`SymplecticGeometry.Analysis.Complex.Pseudoconvex`), and the bound on the differential of
`φ ∘ e.symm` is the continuity of that differential at `e (ι y)`
(`TauCeti.mvfderiv_eq_zero_iff_fderiv_comp_extend_symm_eq_zero`).

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
  set z₀ := e (ι y)
  set Z := e '' (e.source ∩ range ι)
  have hsymm_tendsto : Tendsto e.symm (𝓝 z₀) (𝓝 (ι y)) := e.tendsto_symm hy
  -- The squared distance to `Z` is at most a multiple of `ρ`.
  obtain ⟨C, hC⟩ := (h.isImmersion.isImmersionAt y).exists_eventually_infDist_sq_le_mul hn hρ
    hρ0 hρι hpos (IsManifold.maximalAtlas_subset_of_le (by norm_num) he) hy
  -- Glaeser's inequality for `ρ ∘ e.symm`.
  have hf : ContDiffAt ℝ 2 (ρ ∘ e.symm) z₀ := by
    simpa using (contMDiffAt_iff_contDiffAt_comp_extend_symm he hy).1 hρ
  obtain ⟨A₁, hA₁⟩ := (isCompact_singleton (x := z₀)).exists_eventually_norm_fderiv_le_mul_sqrt
    (by simpa using hf) (by rw [nhdsSet_singleton]; exact hsymm_tendsto.eventually hρ0)
  rw [nhdsSet_singleton] at hA₁
  -- The second derivative of `ρ ∘ e.symm` is continuous at `z₀`, hence bounded near it.
  have hB : ∀ᶠ z in 𝓝 z₀, ‖fderiv ℝ (fderiv ℝ (ρ ∘ e.symm)) z‖ <
      ‖fderiv ℝ (fderiv ℝ (ρ ∘ e.symm)) z₀‖ + 1 :=
    -- Naming the codomain lets `ContinuousAt.norm` match the topology of the Tau Ceti lemma.
    (hf.continuousAt_fderiv_fderiv le_rfl).norm (E := E →L[ℝ] E →L[ℝ] ℝ) |>.eventually_lt
      continuousAt_const (lt_add_one _)
  -- `D ∘ e.symm` and its derivative are bounded by the distance to `Z`.
  obtain ⟨A₂, hA₂⟩ := h.isEmbedding.exists_eventually_abs_comp_symm_le_mul_infDist_sq hD hDι he hy
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
  · calc |D (e.symm z)| ≤ A₂ * d ^ 2 := hA₂z.1
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

namespace Manifold.IsSmoothEmbedding

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {n : WithTop ℕ∞} {ι : N → M} {y : N} {ρ φ ψ : M → ℝ} {S : Set M}

/-- **Uniform local data for the interpolation near an embedded submanifold.** Let `ι` and `ρ` be
as in `Manifold.IsSmoothEmbedding.exists_abs_comp_symm_le`, now into a manifold `M` modelled on
a finite-dimensional complex space `E`. Let `φ` and `ψ` be `C²` near `ι y`, strictly
plurisubharmonic at `ι y`, with `φ (ι y') = ψ (ι y')` and
`mvfderiv 𝓘(ℝ, E) φ (ι y') = mvfderiv 𝓘(ℝ, E) ψ (ι y')` for `y'` near `y`, and let `S` be a
neighbourhood of `ι y`. Then for every chart `e` at `ι y` of the holomorphic `C²` maximal atlas
there are `r > 0`, `A` and `m > 0` such that the closed ball of radius `r` about `e (ι y)` lies
in `e.target`, is sent by `e.symm` into `S`, and at each of its points `z`, with `x = e.symm z`:

* `|ψ x - φ x| ≤ A * ρ x`, `‖fderiv ℝ (ψ ∘ e.symm - φ ∘ e.symm) z‖ ≤ A * √(ρ x)`,
  `‖fderiv ℝ (ρ ∘ e.symm) z‖ ≤ A * √(ρ x)` and `‖fderiv ℝ (fderiv ℝ (ρ ∘ e.symm)) z‖ ≤ A`;
* `m * ‖v‖ ^ 2` is at most the real part of the Levi form at `z` of `φ ∘ e.symm`, and of
  `ψ ∘ e.symm`, on every vector `v`;
* if `ι y` is not a critical point of `φ`, then `m ≤ ‖fderiv ℝ (φ ∘ e.symm) z‖`. -/
theorem exists_closedBall_abs_sub_le_and_le_re_leviForm [I'.Boundaryless]
    (h : IsSmoothEmbedding I' 𝓘(ℝ, E) n ι) (hn : 2 ≤ n)
    (hρ : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 ρ (ι y)) (hρ0 : ∀ᶠ x in 𝓝 (ι y), 0 ≤ ρ x)
    (hρι : ∀ᶠ y' in 𝓝 y, ρ (ι y') = 0)
    (hpos : ∀ v ∉ LinearMap.range (mfderiv I' 𝓘(ℝ, E) ι y).toLinearMap,
      0 < criticalHessian 𝓘(ℝ, E) ρ (ι y) v v)
    (hφ : ∀ᶠ x in 𝓝 (ι y), ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 φ x)
    (hψ : ∀ᶠ x in 𝓝 (ι y), ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 ψ x)
    (hφs : IsManifoldStrictlyPlurisubharmonicAt E φ (ι y))
    (hψs : IsManifoldStrictlyPlurisubharmonicAt E ψ (ι y))
    (hφψ : ∀ᶠ y' in 𝓝 y, φ (ι y') = ψ (ι y') ∧
      mvfderiv 𝓘(ℝ, E) φ (ι y') = mvfderiv 𝓘(ℝ, E) ψ (ι y'))
    (hS : S ∈ 𝓝 (ι y)) {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, E) 2 M) (hy : ι y ∈ e.source) :
    ∃ r > 0, closedBall (e (ι y)) r ⊆ e.target ∧ e.symm '' closedBall (e (ι y)) r ⊆ S ∧
      ∃ A, ∃ m > 0, ∀ z ∈ closedBall (e (ι y)) r,
        |ψ (e.symm z) - φ (e.symm z)| ≤ A * ρ (e.symm z) ∧
        ‖fderiv ℝ (ψ ∘ e.symm - φ ∘ e.symm) z‖ ≤ A * √(ρ (e.symm z)) ∧
        ‖fderiv ℝ (ρ ∘ e.symm) z‖ ≤ A * √(ρ (e.symm z)) ∧
        ‖fderiv ℝ (fderiv ℝ (ρ ∘ e.symm)) z‖ ≤ A ∧
        (∀ v, m * ‖v‖ ^ 2 ≤ (leviForm (φ ∘ e.symm) z v v).re) ∧
        (∀ v, m * ‖v‖ ^ 2 ≤ (leviForm (ψ ∘ e.symm) z v v).re) ∧
        (mvfderiv 𝓘(ℝ, E) φ (ι y) ≠ 0 → m ≤ ‖fderiv ℝ (φ ∘ e.symm) z‖) := by
  have := FiniteDimensional.proper ℂ E
  set z₀ := e (ι y)
  have heR : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 2 M :=
    IsManifold.maximalAtlas_subset_restrictScalars_of_ne_zero 2 two_ne_zero he
  have hsymm : Tendsto e.symm (𝓝 z₀) (𝓝 (ι y)) := e.tendsto_symm hy
  have htarget : ∀ᶠ z in 𝓝 z₀, z ∈ e.target := e.open_target.mem_nhds (e.map_source hy)
  -- The Taylor bounds for `D = ψ - φ`, whose 1-jet vanishes along `ι` near `y`.
  have hDι : ∀ᶠ y' in 𝓝 y, (ψ - φ) (ι y') = 0 ∧ mvfderiv 𝓘(ℝ, E) (ψ - φ) (ι y') = 0 := by
    filter_upwards [hφψ, (h.isEmbedding.continuous.tendsto y).eventually (hφ.and hψ)]
      with y' h₁ h₂
    refine ⟨by simp [h₁.1], ?_⟩
    rw [mvfderiv_sub (h₂.2.mdifferentiableAt two_ne_zero) (h₂.1.mdifferentiableAt two_ne_zero),
      h₁.2, sub_self]
  obtain ⟨A, hA⟩ := h.exists_abs_comp_symm_le hn hρ hρ0 hρι hpos
    ((hφ.and hψ).mono fun x hx ↦ ContMDiffAt.sub hx.2 hx.1) hDι heR hy
  -- The coordinate expressions of `φ` and `ψ` are `C²` near `z₀`.
  have hcd {f : M → ℝ} (hf : ∀ᶠ x in 𝓝 (ι y), ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 f x) :
      ∀ᶠ z in 𝓝 z₀, ContDiffAt ℝ 2 (f ∘ e.symm) z := by
    filter_upwards [hsymm.eventually hf, htarget] with z hz hzt
    simpa [e.right_inv hzt] using
      (contMDiffAt_iff_contDiffAt_comp_extend_symm heR (e.map_target hzt)).1 hz
  -- Strict plurisubharmonicity in the chart is an open condition.
  have hsp {f : M → ℝ} (hf : ∀ᶠ x in 𝓝 (ι y), ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 f x)
      (hfs : IsManifoldStrictlyPlurisubharmonicAt E f (ι y)) :
      ∀ᶠ z in 𝓝 z₀, IsStrictlyPlurisubharmonicAt (f ∘ e.symm) z :=
    ((isManifoldStrictlyPlurisubharmonicAt_iff_of_mem_maximalAtlas he hy
      hf.self_of_nhds).1 hfs).eventually (hcd hf).self_of_nhds
  -- Away from a critical point the differential of `φ ∘ e.symm` stays away from zero.
  obtain ⟨d, hd, hdφ⟩ : ∃ d > 0, ∀ᶠ z in 𝓝 z₀,
      mvfderiv 𝓘(ℝ, E) φ (ι y) ≠ 0 → d ≤ ‖fderiv ℝ (φ ∘ e.symm) z‖ := by
    by_cases h0 : mvfderiv 𝓘(ℝ, E) φ (ι y) = 0
    · exact ⟨1, one_pos, Eventually.of_forall fun _ h ↦ absurd h0 h⟩
    have hne : 0 < ‖fderiv ℝ (φ ∘ e.symm) z₀‖ := by
      rw [norm_pos_iff]
      simpa using (mvfderiv_eq_zero_iff_fderiv_comp_extend_symm_eq_zero
        (IsManifold.maximalAtlas_subset_restrictScalars_of_ne_zero 1 two_ne_zero he) hy).not.1 h0
    refine ⟨‖fderiv ℝ (φ ∘ e.symm) z₀‖ / 2, by positivity, ?_⟩
    filter_upwards [continuousAt_const.eventually_lt
      ((hcd hφ).self_of_nhds.continuousAt_fderiv two_ne_zero).norm
      (half_lt_self hne)] with z hz _ using hz.le
  -- Collect the conditions and take a closed ball on which they all hold.
  have hall := htarget.and <| (hsymm.eventually hS).and <| hA.and <| (hcd hφ).and <|
    (hcd hψ).and <| (hsp hφ hφs).and <| (hsp hψ hψs).and hdφ
  obtain ⟨r, hr, hrP⟩ := nhds_basis_closedBall.mem_iff.1 hall
  -- Uniform Levi positivity on the compact closed ball.
  have hreg : ∀ z ∈ closedBall z₀ r,
      (ContDiffAt ℝ 2 (φ ∘ e.symm) z ∧ IsStrictlyPlurisubharmonicAt (φ ∘ e.symm) z) ∧
      (ContDiffAt ℝ 2 (ψ ∘ e.symm) z ∧ IsStrictlyPlurisubharmonicAt (ψ ∘ e.symm) z) := by
    intro z hz
    obtain ⟨-, -, -, h₁, h₂, h₃, h₄, -⟩ := hrP hz
    exact ⟨⟨h₁, h₃⟩, h₂, h₄⟩
  obtain ⟨mφ, hmφ, hLφ⟩ := (isCompact_closedBall z₀ r)
    |>.exists_pos_mul_sq_norm_le_re_leviForm_of_isStrictlyPlurisubharmonicAt
      (fun z hz ↦ (hreg z hz).1.1) fun z hz ↦ (hreg z hz).1.2
  obtain ⟨mψ, hmψ, hLψ⟩ := (isCompact_closedBall z₀ r)
    |>.exists_pos_mul_sq_norm_le_re_leviForm_of_isStrictlyPlurisubharmonicAt
      (fun z hz ↦ (hreg z hz).2.1) fun z hz ↦ (hreg z hz).2.2
  refine ⟨r, hr, fun z hz ↦ (hrP hz).1, ?_, A, min (min mφ mψ) d, by positivity, fun z hz ↦ ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact (hrP hz).2.1
  obtain ⟨-, -, ⟨h₁, h₂, h₃, h₄⟩, -, -, -, -, h₅⟩ := hrP hz
  refine ⟨by simpa using h₁, h₂, h₃, h₄, fun v ↦ ?_, fun v ↦ ?_, fun h0 ↦ ?_⟩
  · exact (mul_le_mul_of_nonneg_right ((min_le_left _ _).trans (min_le_left _ _))
      (by positivity)).trans (hLφ z hz v)
  · exact (mul_le_mul_of_nonneg_right ((min_le_left _ _).trans (min_le_right _ _))
      (by positivity)).trans (hLψ z hz v)
  · exact (min_le_right _ _).trans (h₅ h0)

end Manifold.IsSmoothEmbedding

end
