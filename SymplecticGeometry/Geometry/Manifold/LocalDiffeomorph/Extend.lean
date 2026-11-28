/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Basic
import SymplecticGeometry.LinearAlgebra.FiniteDimensional.Extension

/-!
# Extending an immersion to a local diffeomorphism

Let `u : F → M` be a smooth map from a normed space to a boundaryless finite-dimensional manifold
whose differential at `0` is injective, and let `ι : F → V` be an injective continuous linear map
into a normed space of the dimension of `M`. Then `u` extends along `ι` to a local diffeomorphism
`G : V → M` at `0`: `G (ι s) = u s` for `s` near `0`
(`SymplecticGeometry.exists_localDiffeomorph_extend`).

In the extended chart `φ` of `M` at `u 0`, choose a left inverse `π` of `ι` and a linear
equivalence `A : V ≃ E` with `A ∘ ι = d(φ ∘ u)₀`, and put
`G v = φ⁻¹ (φ (u (π v)) + A (v - ι (π v)))`. Its differential at `0` is `A`, read in the chart,
and `G ∘ ι = u` near `0`. This is the straightening map `θ (y, n) = g y + n` of Tau Ceti's
`TauCeti.exists_partialDiffeomorph_fix_immersion_compContinuousLinearMap_fderiv_eq`, with the
complement of the image of `ι` in place of the complement of the image of `dg`.

The file also records that every point `x₀` of a boundaryless manifold has a chart sending it to
`0` (`SymplecticGeometry.exists_partialDiffeomorph_apply_eq_zero`).
-/

public section

open Set Filter Function Module
open scoped Manifold ContDiff Topology

open TauCeti

namespace SymplecticGeometry

variable {E H M V F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [BoundarylessManifold I M]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Extending an immersion to a local diffeomorphism.** Let `u : F → M` be smooth near `0` with
injective differential at `0`, and let `ι : F → V` be an injective continuous linear map into a
space of the dimension of `M`. Then some `G : V → M` is a smooth local diffeomorphism at `0`
with `G (ι s) = u s` for all `s` near `0`. -/
theorem exists_localDiffeomorph_extend {u : F → M} {ι : F →L[ℝ] V} (hι : Injective ι)
    (hu : ∀ᶠ s in 𝓝 0, ContMDiffAt 𝓘(ℝ, F) I ∞ u s)
    (hinj : Injective (mfderiv 𝓘(ℝ, F) I u 0)) (hdim : finrank ℝ V = finrank ℝ E) :
    ∃ G : V → M, IsLocalDiffeomorphAt 𝓘(ℝ, V) I ∞ G 0 ∧ ∀ᶠ s in 𝓝 0, G (ι s) = u s := by
  set φ := extChartAt I (u 0)
  have hint : φ (u 0) ∈ interior φ.target :=
    (ModelWithCorners.isInteriorPoint_iff (I := I)).mp BoundarylessManifold.isInteriorPoint
  have hsrc : ∀ᶠ s in 𝓝 0, u s ∈ φ.source :=
    hu.self_of_nhds.continuousAt.preimage_mem_nhds (extChartAt_source_mem_nhds (u 0))
  -- `u` read in the chart `φ` is smooth near `0`.
  have hu₁ : ∀ᶠ s in 𝓝 0, ContDiffAt ℝ ∞ (φ ∘ u) s := by
    filter_upwards [hu, hsrc] with s hs hs'
    exact contMDiffAt_iff_contDiffAt.1
      ((contMDiffAt_extChartAt' (by rwa [← extChartAt_source (I := I)])).comp s hs)
  -- Its derivative `D` at `0` is injective, since the chart is a local diffeomorphism.
  set D := fderiv ℝ (φ ∘ u) 0
  have hφ : IsLocalDiffeomorphAt I 𝓘(ℝ, E) ∞ φ (u 0) :=
    isLocalDiffeomorphAt_extChartAt (mem_extChartAt_source (u 0)) hint
  have hD : Injective D := by
    have hc : Injective (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) (φ ∘ u) 0) :=
      TauCeti.injective_mfderiv_comp (J := I) (hφ.isInvertible_mfderiv (by simp)).injective hinj
    rwa [mfderiv_eq_fderiv, ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_comp,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.coe_coe, EquivLike.comp_injective,
      EquivLike.injective_comp] at hc
  obtain ⟨π, hπ⟩ := (ι : F →ₗ[ℝ] V).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 hι)
  obtain ⟨A, hA⟩ := LinearMap.exists_linearEquiv_comp_eq_of_injective hι hD
    (by rw [hdim])
  let π' : V →L[ℝ] F := LinearMap.toContinuousLinearMap π
  let A' : V ≃L[ℝ] E := A.toContinuousLinearEquiv
  have hπι (s : F) : π' (ι s) = s := LinearMap.congr_fun hπ s
  have hAι (s : F) : A' (ι s) = D s := LinearMap.congr_fun hA s
  -- The extension, read in the chart.
  let Gc : V → E := fun v ↦ φ (u (π' v)) + A' (v - ι (π' v))
  have hGcι (s : F) : Gc (ι s) = φ (u s) := by simp [Gc, hπι]
  obtain ⟨O, hOsub, hOo, hO0⟩ := mem_nhds_iff.1 hu₁
  have hGcO : ContDiffOn ℝ ∞ Gc (π' ⁻¹' O) := fun v (hv : π' v ∈ O) ↦ by
    have h₁ : ContDiffAt ℝ ∞ ((φ ∘ u) ∘ π') v :=
      (hOsub hv : ContDiffAt ℝ ∞ (φ ∘ u) (π' v)).comp v π'.contDiff.contDiffAt
    have h₂ : ContDiff ℝ ∞ (fun v ↦ A' (v - ι (π' v))) :=
      A'.contDiff.comp (contDiff_id.sub (ι.contDiff.comp π'.contDiff))
    exact (h₁.add h₂.contDiffAt).contDiffWithinAt
  have hGcd : fderiv ℝ Gc 0 = (A' : V →L[ℝ] E) := by
    have hd : HasFDerivAt (φ ∘ u) D (π' 0) := by
      rw [map_zero]
      have h0 : ContDiffAt ℝ ∞ (φ ∘ u) 0 := hOsub hO0
      exact (h0.differentiableAt (by simp)).hasFDerivAt
    have h := (hd.comp 0 π'.hasFDerivAt).add
      ((A' : V →L[ℝ] E).hasFDerivAt.comp 0
        ((hasFDerivAt_id 0).sub ((ι.comp π').hasFDerivAt)))
    refine h.fderiv.trans (ContinuousLinearMap.ext fun v ↦ ?_)
    simp [← hAι]
  have hGcloc : IsLocalDiffeomorphAt 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ Gc 0 :=
    isLocalDiffeomorphAt_of_fderiv_eq hGcO (hOo.preimage π'.continuous)
      (by simpa using hO0) (by simp) hGcd.symm
  have hGc0 : Gc 0 = φ (u 0) := by simpa using hGcι 0
  have hφs : IsLocalDiffeomorphAt 𝓘(ℝ, E) I ∞ φ.symm (Gc 0) := by
    rw [hGc0]
    exact isLocalDiffeomorphAt_extChartAt_symm hint
  refine ⟨φ.symm ∘ Gc, hGcloc.comp (K := I) (P := M) hφs, ?_⟩
  filter_upwards [hsrc] with s hs
  simp [hGcι, φ.left_inv hs]

omit [FiniteDimensional ℝ E] in
/-- **Centred charts.** Every point `x₀` of a boundaryless manifold lies in the source of a smooth
partial diffeomorphism into the model space which sends `x₀` to `0`: the extended chart at `x₀`
followed by a translation. -/
theorem exists_partialDiffeomorph_apply_eq_zero (x₀ : M) :
    ∃ c : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞, x₀ ∈ c.source ∧ c x₀ = 0 := by
  let a := extChartAt I x₀ x₀
  let τ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞ :=
    PartialDiffeomorph.ofOpenPartialHomeomorph (Homeomorph.addRight (-a)).toOpenPartialHomeomorph
      (by simpa using (contDiff_id.add contDiff_const : ContDiff ℝ ∞ fun v : E ↦ v + -a).contDiffOn)
      (by simpa [Homeomorph.addRight_symm] using
        (contDiff_id.add contDiff_const : ContDiff ℝ ∞ fun v : E ↦ v + a).contDiffOn)
  refine ⟨(extChartPartialDiffeomorph I ∞ x₀).trans τ, ?_, ?_⟩
  · simp [τ, mem_extChartPartialDiffeomorph_source, BoundarylessManifold.isInteriorPoint]
  · simp [τ, coe_extChartPartialDiffeomorph, a]

end SymplecticGeometry
