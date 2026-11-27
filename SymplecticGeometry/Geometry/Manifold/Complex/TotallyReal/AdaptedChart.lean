/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import TauCeti.Geometry.Manifold.Complex.TotallyReal.AdaptedChart
public import TauCeti.Geometry.Manifold.IsManifold.Basic

/-!
# Adapted charts along a totally real embedding: first-order facts

For a chart `ψ : M → F × F` adapted to a subset of `M` (Tau Ceti's `TauCeti.IsAdaptedChart`),
this file gives:

* `TauCeti.IsAdaptedChart.contMDiffAt`: a chart adapted with regularity `ℓ` is `C^ℓ` at each
  point of its source;
* `TauCeti.IsAdaptedChart.snd_mfderiv_eq_zero_iff`: for a chart adapted to the image of a
  totally real embedding `ι`, at a point `ι y` of the source, a tangent vector `v` satisfies
  `(dψ v).2 = 0` exactly when it lies in the tangent image of `ι`. The tangent image lies in
  this kernel since `ψ ∘ ι` stays in `F × {0}`, and the two have the same dimension since `dι`
  is injective, `dψ` is onto and `2 · dim F = dim M` (Tau Ceti's
  `TauCeti.IsTotallyRealEmbedding.two_mul_finrank`).
-/

public section

open Set Module Filter Topology
open scoped Manifold ContDiff

namespace TauCeti.IsAdaptedChart

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {ℓ : ℕ∞}
  {J : ContMDiffAlmostComplexStructure I ℓ M} {s : Set M} {ψ : OpenPartialHomeomorph M (F × F)}

/-- A chart adapted with regularity `ℓ` is `C^ℓ` at each point of its source. -/
theorem contMDiffAt (hψ : IsAdaptedChart J s ψ) {x : M} (hx : x ∈ ψ.source) :
    ContMDiffAt I 𝓘(ℝ, F × F) ℓ ψ x :=
  (hψ.contMDiffOn x hx).contMDiffAt (ψ.open_source.mem_nhds hx)

variable {H' N : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ F H'} [TopologicalSpace N]
  [ChartedSpace H' N] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] {k : ℕ∞ω}
  {A : ∀ y : M, AlmostComplexStructure (TangentSpace I y)} {ι : N → M}

/-- **The tangent image in an adapted chart.** Let `ψ` be a chart adapted to the image of a
`C^k` totally real embedding `ι`, with `k, ℓ ≥ 1`. At a point `ι y` of the source of `ψ`, the
derivative of `ψ` sends a tangent vector into the zero section `F × {0}` exactly when the vector
is tangent to `ι`. -/
theorem snd_mfderiv_eq_zero_iff (h : IsTotallyRealEmbedding I' I k A ι) (hk : 1 ≤ k)
    (hψ : IsAdaptedChart J (range ι) ψ) (hℓ : 1 ≤ ℓ) {y : N} (hy : ι y ∈ ψ.source)
    (v : TangentSpace I (ι y)) :
    (mfderiv I 𝓘(ℝ, F × F) ψ (ι y) v).2 = 0 ↔
      v ∈ LinearMap.range (mfderiv I' I ι y).toLinearMap := by
  have hℓ0 : (ℓ : ℕ∞ω) ≠ 0 := by exact_mod_cast (zero_lt_one.trans_le hℓ).ne'
  have hψd : ψ.MDifferentiable I 𝓘(ℝ, F × F) :=
    ⟨hψ.contMDiffOn.mdifferentiableOn hℓ0, hψ.contMDiffOn_symm.mdifferentiableOn hℓ0⟩
  have hψy := hψd.mdifferentiableAt hy
  have hιy : MDifferentiableAt I' I ι y :=
    (h.isSmoothEmbedding.contMDiff y).mdifferentiableAt (zero_lt_one.trans_le hk).ne'
  set D := mfderiv I 𝓘(ℝ, F × F) ψ (ι y)
  set K := LinearMap.ker ((LinearMap.snd ℝ F F).comp D.toLinearMap)
  -- Membership in `K` is by definition the vanishing of `(dψ v).2`.
  change v ∈ K ↔ _
  -- `ψ ∘ ι` stays in the zero section near `y`, so `dψ ∘ dι` takes values in `F × {0}`.
  have hle : LinearMap.range (mfderiv I' I ι y).toLinearMap ≤ K := by
    have hzero : Prod.snd ∘ ψ ∘ ι =ᶠ[𝓝 y] fun _ ↦ (0 : F) :=
      eventually_of_mem (h.isSmoothEmbedding.contMDiff.continuous.continuousAt.preimage_mem_nhds
        (ψ.open_source.mem_nhds hy)) fun z hz ↦ (hψ.isImage hz).2 (mem_range_self z)
    have hcomp := (hasFDerivAt_snd.hasMFDerivAt.comp y
      (hψy.hasMFDerivAt.comp y hιy.hasMFDerivAt)).mfderiv
    rw [hzero.mfderiv_eq, mfderiv_const] at hcomp
    rintro _ ⟨t, rfl⟩
    exact congr($hcomp.symm t)
  -- Both have the dimension of `F`: `dι` is injective and `dψ` is onto.
  suffices hK : LinearMap.range (mfderiv I' I ι y).toLinearMap = K by rw [hK]
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  have hsurj : LinearMap.range ((LinearMap.snd ℝ F F).comp D.toLinearMap) = ⊤ :=
    LinearMap.range_eq_top.2 ((LinearMap.snd_surjective (R := ℝ) (M := F) (M₂ := F)).comp
      (hψd.mfderiv_surjective hy))
  have hrn := LinearMap.finrank_range_add_finrank_ker ((LinearMap.snd ℝ F F).comp D.toLinearMap)
  rw [hsurj, finrank_top, TauCeti.finrank_tangentSpace, ← h.two_mul_finrank] at hrn
  rw [LinearMap.finrank_range_of_inj (h.mfderiv_injective y), TauCeti.finrank_tangentSpace]
  -- Unfold `K`, so that `omega` sees the kernel of `hrn`.
  change _ = finrank ℝ (LinearMap.ker ((LinearMap.snd ℝ F F).comp D.toLinearMap))
  omega

end TauCeti.IsAdaptedChart

end
