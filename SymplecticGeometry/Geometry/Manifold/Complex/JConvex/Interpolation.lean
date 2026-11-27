/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import TauCeti.Geometry.Manifold.Complex.LeviForm
public import TauCeti.LinearAlgebra.TotallyReal.Basic
public import TauCeti.Geometry.Manifold.Morse.Hessian
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Analysis.Convex.Segment
import SymplecticGeometry.Analysis.Calculus.FDeriv.CompactBound
import SymplecticGeometry.Analysis.Calculus.FDeriv.Glaeser
import SymplecticGeometry.Analysis.Complex.Pseudoconvex
import SymplecticGeometry.Geometry.Manifold.Immersion.InfDist
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Geometry.Manifold.Complex.Analytic
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import TauCeti.Geometry.Manifold.PartitionOfUnity.Compact
import SymplecticGeometry.Analysis.Complex.LeviForm.LogCutoff
import SymplecticGeometry.Geometry.Manifold.Complex.JConvex.TotallyReal
import SymplecticGeometry.Geometry.Manifold.Riemannian.Surface.LogCutoff.Interpolation

/-!
# Interpolation along a totally real submanifold

This file proves the interpolation of two strictly plurisubharmonic functions with the same 1-jet
along a compact part of a totally real submanifold (Proposition 3.26 of Cieliebak–Eliashberg),
together with the Taylor bounds that the proof uses near a point of the submanifold and the
uniform local data, on a closed ball of a holomorphic chart, from which it chooses its constants.

## Main results

* `Manifold.IsSmoothEmbedding.exists_isManifoldStrictlyPlurisubharmonicAt_interpolate`: for a
  smooth embedding `ι` of a boundaryless manifold into a Hausdorff complex manifold, a compact
  `K` at whose points the tangent images of `ι` are totally real, and `φ`, `ψ` smooth on an open
  `O ⊇ ι '' K`, strictly plurisubharmonic on `ι '' K` and with the same 1-jet along `ι` near `K`,
  there are open `V ⊆ W ⊆ U ∩ O` about `ι '' K`, for any open `U ⊇ ι '' K`, and `θ` smooth on
  `O`, equal to `ψ` on `V` and to `φ` near each point off `W`, strictly plurisubharmonic on `W`,
  between `φ` and `ψ`, and without critical points in `W` if `φ` has none on `ι '' K`.
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

The interpolation is `θ = φ + β (ψ - φ)` with `β = χ (1 - logCutoffProfile ε δ ∘ ρ)`, where `ρ`
is the function of
`Manifold.IsSmoothEmbedding.exists_contMDiff_isManifoldStrictlyPlurisubharmonicAt_of_isCompact`
and `χ` is a cutoff equal to `1` near `ι '' K` and supported in the union `W` of finitely many
of the chart balls given by the uniform local data (Tau Ceti's
`IsCompact.exists_contMDiff_one_nhds_tsupport_subset`, which needs no σ-compactness). In each of
these charts the Levi form of `θ` is bounded below by
`TauCeti.exists_mul_sq_norm_le_re_leviForm_add_logCutoff_mul_sub`, and its differential by
`TauCeti.sub_le_norm_fderiv_add_logCutoff_mul_sub`; both errors are small once `δ = η ^ 2` and
`log (δ / ε) = 1 / η` with `η` small, uniformly over the finitely many charts. This is the
logarithmic cutoff route of the library's design for Proposition 3.26, and we do not claim that
it follows the lemmas of Cieliebak–Eliashberg's proof step by step.

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

namespace Manifold.IsSmoothEmbedding

open TauCeti.SmoothAlmostComplexStructure
open scoped TauCeti.ComplexManifold

/-- The parameters of the logarithmic cutoff, from one small `η`: for `0 < η ≤ 1 / 3`, the
numbers `δ = η ^ 2` and `ε = δ / exp (1 / η)` satisfy `0 < 4ε ≤ δ ≤ 1`, `√δ = η` and
`log (δ / ε) = 1 / η`. -/
private theorem logCutoff_params {η : ℝ} (hη0 : 0 < η) (hη3 : η ≤ 1 / 3) :
    0 < η ^ 2 / Real.exp (1 / η) ∧ 4 * (η ^ 2 / Real.exp (1 / η)) ≤ η ^ 2 ∧ η ^ 2 ≤ 1 ∧
      √(η ^ 2) = η ∧ Real.log (η ^ 2 / (η ^ 2 / Real.exp (1 / η))) = 1 / η := by
  have h4 : 4 ≤ Real.exp (1 / η) := by
    have := Real.add_one_le_exp (1 / η)
    have : 3 ≤ 1 / η := by rw [le_div_iff₀ hη0]; linarith
    linarith
  refine ⟨by positivity, ?_, by nlinarith, Real.sqrt_sq hη0.le, ?_⟩
  · rw [mul_div_assoc', div_le_iff₀ (Real.exp_pos _)]
    nlinarith [sq_nonneg η]
  · rw [div_div_cancel₀ (by positivity), Real.log_exp]

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
  {ι : N → M} {φ ψ : M → ℝ} {K : Set N} {O U : Set M}

/-- **Interpolation along a totally real submanifold.** Let `ι : N → M` be a smooth embedding of
a boundaryless manifold into a Hausdorff complex manifold modelled on a finite-dimensional space
`E`, and `K ⊆ N` a compact set at whose points the tangent images of `ι` are totally real. Let
`φ` and `ψ` be smooth on an open set `O ⊇ ι '' K`, strictly plurisubharmonic at the points of
`ι '' K`, with `φ (ι y) = ψ (ι y)` and `mvfderiv 𝓘(ℝ, E) φ (ι y) = mvfderiv 𝓘(ℝ, E) ψ (ι y)` for
`y` near `K`, and let `U ⊇ ι '' K` be open. Then there are open sets `V ⊆ W` with
`ι '' K ⊆ V` and `W ⊆ U ∩ O`, and a function `θ`, smooth on `O`, such that `θ = ψ` on `V`,
`θ` agrees with `φ` near every point outside `W`, `θ` is strictly plurisubharmonic at every point
of `W`, `θ` lies between `φ` and `ψ` everywhere, and, if `φ` has no critical point on `ι '' K`,
then `θ` has none in `W`. -/
theorem exists_isManifoldStrictlyPlurisubharmonicAt_interpolate [T2Space M] [I'.Boundaryless]
    (h : IsSmoothEmbedding I' 𝓘(ℝ, E) ∞ ι) (hK : IsCompact K)
    (hι : ∀ y ∈ K, IsTotallyReal ((ofComplexManifold E M).toEndomorphism (ι y)).toLinearMap
      (LinearMap.range (mfderiv I' 𝓘(ℝ, E) ι y).toLinearMap))
    (hO : IsOpen O) (hKO : ι '' K ⊆ O)
    (hφ : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞ φ O) (hψ : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞ ψ O)
    (hφs : ∀ x ∈ ι '' K, IsManifoldStrictlyPlurisubharmonicAt E φ x)
    (hψs : ∀ x ∈ ι '' K, IsManifoldStrictlyPlurisubharmonicAt E ψ x)
    (hφψ : ∀ᶠ y in 𝓝ˢ K, φ (ι y) = ψ (ι y) ∧
      mvfderiv 𝓘(ℝ, E) φ (ι y) = mvfderiv 𝓘(ℝ, E) ψ (ι y))
    (hU : IsOpen U) (hKU : ι '' K ⊆ U) :
    ∃ V W : Set M, IsOpen V ∧ IsOpen W ∧ ι '' K ⊆ V ∧ V ⊆ W ∧ W ⊆ U ∩ O ∧
      ∃ θ : M → ℝ, ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞ θ O ∧ EqOn θ ψ V ∧
        (∀ x ∉ W, θ =ᶠ[𝓝 x] φ) ∧ (∀ x ∈ W, IsManifoldStrictlyPlurisubharmonicAt E θ x) ∧
        (∀ x, min (φ x) (ψ x) ≤ θ x ∧ θ x ≤ max (φ x) (ψ x)) ∧
        ((∀ x ∈ ι '' K, mvfderiv 𝓘(ℝ, E) φ x ≠ 0) → ∀ x ∈ W, mvfderiv 𝓘(ℝ, E) θ x ≠ 0) := by
  classical
  have := FiniteDimensional.proper ℂ E
  have : IsManifold 𝓘(ℂ, E) 2 M := IsManifold.of_le (n := ∞) (by simp)
  have hι_cont := h.isEmbedding.continuous
  -- The function `ρ`, a squared distance to the image of `ι` near `ι '' K`.
  obtain ⟨ρ, hρs, hρ0, V₀, hV₀, hKV₀, hρV₀, -, hpos⟩ :=
    h.exists_contMDiff_isManifoldStrictlyPlurisubharmonicAt_of_isCompact (n := ⊤) (by simp) hK hι
  have hρ2 : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) 2 ρ := hρs.of_le (by simp)
  have hC2 {f : M → ℝ} (hf : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞ f O) {x : M} (hx : x ∈ O) :
      ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 f x :=
    (hf.contMDiffAt (hO.mem_nhds hx)).of_le (by simp)
  -- The uniform local data at each point of `K`, in a holomorphic chart.
  have hloc (y : K) :=
    h.exists_closedBall_abs_sub_le_and_le_re_leviForm (n := ∞) (y := (y : N)) (by simp)
    hρ2.contMDiffAt (Eventually.of_forall hρ0)
    (eventually_of_mem (hι_cont.continuousAt.preimage_mem_nhds
      (hV₀.mem_nhds (hKV₀ ⟨y, y.property, rfl⟩))) fun y' hy' ↦ (hρV₀ _ hy').2 ⟨y', rfl⟩)
    (hpos y y.property)
    (eventually_of_mem (hO.mem_nhds (hKO ⟨y, y.property, rfl⟩)) fun _ hx ↦ hC2 hφ hx)
    (eventually_of_mem (hO.mem_nhds (hKO ⟨y, y.property, rfl⟩)) fun _ hx ↦ hC2 hψ hx)
    (hφs _ ⟨y, y.property, rfl⟩) (hψs _ ⟨y, y.property, rfl⟩)
    (hφψ.filter_mono (nhds_le_nhdsSet y.property))
    (((hU.inter hO).inter hV₀).mem_nhds
      ⟨⟨hKU ⟨y, y.property, rfl⟩, hKO ⟨y, y.property, rfl⟩⟩, hKV₀ ⟨y, y.property, rfl⟩⟩)
    (IsManifold.chart_mem_maximalAtlas (ι y)) (mem_chart_source E (ι y))
  choose r hr hrt hrS A m hm hdata using hloc
  set e : K → OpenPartialHomeomorph M E := fun y ↦ chartAt E (ι y)
  have he (y : K) : e y ∈ IsManifold.maximalAtlas 𝓘(ℂ, E) 2 M :=
    IsManifold.chart_mem_maximalAtlas _
  have heR (y : K) : e y ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 2 M :=
    IsManifold.maximalAtlas_subset_restrictScalars_of_ne_zero 2 two_ne_zero (he y)
  -- Finitely many open chart balls cover `ι '' K`; `W` is their union.
  set ball' : K → Set M := fun y ↦ (e y).source ∩ e y ⁻¹' ball (e y (ι y)) (r y)
  have hball'o (y : K) : IsOpen (ball' y) := (e y).isOpen_inter_preimage isOpen_ball
  obtain ⟨t, ht⟩ := (hK.image hι_cont).elim_finite_subcover ball' hball'o (by
    rintro _ ⟨y, hy, rfl⟩
    exact mem_iUnion.2 ⟨⟨y, hy⟩, mem_chart_source E (ι y), mem_ball_self (hr _)⟩)
  set W := ⋃ y ∈ t, ball' y
  have hWo : IsOpen W := isOpen_biUnion fun y _ ↦ hball'o y
  have hmemW {x : M} (hx : x ∈ W) : ∃ y ∈ t, x ∈ (e y).source ∧
      e y x ∈ closedBall (e y (ι y)) (r y) ∧ (e y).symm (e y x) = x := by
    obtain ⟨y, hy, hxs, hxb⟩ := mem_iUnion₂.1 hx
    exact ⟨y, hy, hxs, ball_subset_closedBall hxb, (e y).left_inv hxs⟩
  have hWUO : W ⊆ U ∩ O := by
    intro x hx
    obtain ⟨y, -, -, hz, hzx⟩ := hmemW hx
    have := hrS y ⟨_, hz, rfl⟩
    rw [hzx] at this
    exact this.1
  -- A cutoff `χ`, equal to `1` near `ι '' K` and supported in `W`.
  obtain ⟨χ, hχs, hχ1, -, hχW, hχI⟩ :=
    (hK.image hι_cont).exists_contMDiff_one_nhds_tsupport_subset 𝓘(ℝ, E) hWo ht
  -- Bounds on the first two derivatives of `χ` in the charts.
  have hχ2 : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) 2 χ := hχs.of_le (by simp)
  have hχB (y : K) : ∃ B, ∀ z ∈ closedBall (e y (ι y)) (r y),
      ‖fderiv ℝ (χ ∘ (e y).symm) z‖ ≤ B ∧ ‖fderiv ℝ (fderiv ℝ (χ ∘ (e y).symm)) z‖ ≤ B := by
    refine (isCompact_closedBall _ _).exists_forall_norm_fderiv_le_and_norm_fderiv_fderiv_le
      le_rfl fun z hz ↦ ?_
    have := hχ2.contMDiffAt.contDiffAt_comp_symm_of_mem_maximalAtlas (heR y)
      ((e y).map_target (hrt y hz))
    rwa [(e y).right_inv (hrt y hz)] at this
  choose B hB using hχB
  -- The parameters: `δ = η ^ 2` and `log (δ / ε) = 1 / η`, for `η` small.
  obtain ⟨Kc, hKc⟩ := exists_mul_sq_norm_le_re_leviForm_add_logCutoff_mul_sub
  have hev : ∀ᶠ η in 𝓝 (0 : ℝ), η ≤ 1 / 3 ∧ ∀ y ∈ t,
      Kc * (A y ^ 2 + A y ^ 3 + A y ^ 2 * B y + A y * B y) * (η + η) < m y ∧
      A y * η + (logCutoffConst * A y ^ 2 * η * η + A y * B y * η ^ 2) < m y := by
    refine (eventually_le_nhds (by norm_num)).and ((t.eventually_all).2 fun y _ ↦ ?_)
    refine (ContinuousAt.eventually_lt (by fun_prop) continuousAt_const (by simpa using hm y)).and
      (ContinuousAt.eventually_lt (by fun_prop) continuousAt_const (by simpa using hm y))
  obtain ⟨η, ⟨hη3, hηt⟩, hη0⟩ :=
    ((hev.filter_mono nhdsWithin_le_nhds).and (self_mem_nhdsWithin (s := Ioi 0))).exists
  set δ := η ^ 2
  set ε := δ / Real.exp (1 / η)
  obtain ⟨hε0, h4, hδ1, hsδ, hΛ⟩ := logCutoff_params hη0 hη3
  have hδ0 : 0 < δ := by positivity
  have hεδ : 2 * ε ≤ δ := by linarith
  -- The interpolation.
  set β : M → ℝ := χ * (1 - logCutoffProfile ε δ ∘ ρ) with hβ
  set θ : M → ℝ := φ + β * (ψ - φ) with hθ
  have hβx (x : M) : β x = χ x * (1 - logCutoffProfile ε δ (ρ x)) := by
    simp only [hβ, Pi.mul_apply, Pi.sub_apply, Pi.one_apply, Function.comp_apply]
  have hθx (x : M) : θ x = φ x + β x * (ψ x - φ x) := by
    simp only [hθ, Pi.add_apply, Pi.mul_apply, Pi.sub_apply]
  have hβ01 (x : M) : β x ∈ Icc 0 1 :=
    mul_one_sub_logCutoffProfile_comp_mem_Icc hε0 hεδ (hχI x).1 (hχI x).2
  have hβs : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ β :=
    hχs.mul (contMDiff_const.sub
      ((contDiff_logCutoffProfile hδ0.ne').comp_contMDiff hρs))
  have hθs : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞ θ O := hφ.add (hβs.contMDiffOn.mul (hψ.sub hφ))
  have hθe (y : K) : θ ∘ (e y).symm = φ ∘ (e y).symm + χ ∘ (e y).symm *
      (1 - logCutoffProfile ε δ ∘ (ρ ∘ (e y).symm)) * (ψ ∘ (e y).symm - φ ∘ (e y).symm) := by
    ext; simp [hθx, hβx]
  -- The open set `V` where `θ = ψ`.
  set V := W ∩ interior {x | χ x = 1} ∩ ρ ⁻¹' Iio ε
  have hVo : IsOpen V :=
    (hWo.inter isOpen_interior).inter (isOpen_Iio.preimage (hρs.continuous))
  refine ⟨V, W, hVo, hWo, fun x hx ↦ ⟨⟨ht hx, subset_interior_iff_mem_nhdsSet.2 hχ1 hx⟩, ?_⟩,
    fun x hx ↦ hx.1.1, hWUO, θ, hθs, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨y, hy, rfl⟩ := hx
    rw [mem_preimage, mem_Iio]
    rw [(hρV₀ _ (hKV₀ ⟨y, hy, rfl⟩)).2 ⟨y, rfl⟩]
    exact hε0
  · intro x hx
    have h1 : χ x = 1 := interior_subset hx.1.2
    rw [hθx, hβx, h1, logCutoffProfile_eq_zero_of_le hεδ (le_of_lt hx.2)]
    ring
  · intro x hx
    have := notMem_tsupport_iff_eventuallyEq.1 fun h ↦ hx (hχW h)
    filter_upwards [this] with x' hx'
    simp [hθx, hβx, hx']
  · intro x hx
    obtain ⟨y, hy, hxs, hz, -⟩ := hmemW hx
    have hxO := (hWUO hx).2
    rw [isManifoldStrictlyPlurisubharmonicAt_iff_of_mem_maximalAtlas (he y) hxs
      (hC2 hθs hxO)]
    set z := e y x
    obtain ⟨hD, hDD, hDρ, hD2ρ, hLφ, hLψ, -⟩ := hdata y z hz
    rw [hθe, isStrictlyPlurisubharmonicAt_iff]
    intro v hv
    have hL := hKc hε0 h4 hδ1 ((hC2 hφ hxO).contDiffAt_comp_symm_of_mem_maximalAtlas (heR y) hxs)
      ((hC2 hψ hxO).contDiffAt_comp_symm_of_mem_maximalAtlas (heR y) hxs)
      (hρ2.contMDiffAt.contDiffAt_comp_symm_of_mem_maximalAtlas (heR y) hxs)
      (hχ2.contMDiffAt.contDiffAt_comp_symm_of_mem_maximalAtlas (heR y) hxs) (hχI _).1 (hχI _).2
      (hB y z hz).1 (hB y z hz).2 (hρ0 _) hDρ hD2ρ hD hDD v (hLφ v) (hLψ v)
    rw [hΛ, one_div_one_div, hsδ] at hL
    exact (mul_pos (sub_pos.2 (hηt y hy).1) (by positivity)).trans_le hL
  · intro x
    -- `θ x` is a convex combination of `φ x` and `ψ x`.
    have h := lineMap_mem_segment ℝ (φ x) (ψ x) (hβ01 x)
    rw [segment_eq_uIcc, ← Icc_min_max, AffineMap.lineMap_apply_ring', add_comm, ← hθx] at h
    exact h
  · intro hcrit x hx
    obtain ⟨y, hy, hxs, hz, -⟩ := hmemW hx
    have hxO := (hWUO hx).2
    set z := e y x
    obtain ⟨hD, hDD, hDρ, hD2ρ, -, -, hDφ⟩ := hdata y z hz
    have hA0 : 0 ≤ A y := (norm_nonneg (E := E →L[ℝ] E →L[ℝ] ℝ) _).trans hD2ρ
    have hf := (hC2 hφ hxO).contDiffAt_comp_symm_of_mem_maximalAtlas (heR y) hxs
    have hg := (hC2 hψ hxO).contDiffAt_comp_symm_of_mem_maximalAtlas (heR y) hxs
    have hρz := hρ2.contMDiffAt.contDiffAt_comp_symm_of_mem_maximalAtlas (heR y) hxs
    have hχz := hχ2.contMDiffAt.contDiffAt_comp_symm_of_mem_maximalAtlas (heR y) hxs
    have hk := sub_le_norm_fderiv_add_logCutoff_mul_sub hε0 h4 (hf.differentiableAt (by simp))
      (hg.differentiableAt (by simp)) (hρz.differentiableAt (by simp))
      (hχz.differentiableAt (by simp)) (hχI _).1 (hχI _).2 (hB y z hz).1 (hρ0 _) hA0 hDρ hD hDD
      (hDφ (hcrit _ ⟨y, y.property, rfl⟩))
    rw [hΛ, hsδ, div_div_eq_mul_div, div_one, ← hθe] at hk
    intro h0
    have h0' : fderiv ℝ (θ ∘ (e y).symm) z = 0 := by
      simpa using (mvfderiv_eq_zero_iff_fderiv_comp_extend_symm_eq_zero
        (IsManifold.maximalAtlas_subset_restrictScalars_of_ne_zero 1 two_ne_zero (he y)) hxs).1 h0
    rw [h0', norm_zero] at hk
    linarith [(hηt y hy).2]

end Manifold.IsSmoothEmbedding

end
