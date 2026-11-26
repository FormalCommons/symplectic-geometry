/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Codisc
public import TauCeti.Geometry.Manifold.VectorBundle.FiberScaling
import TauCeti.Geometry.Manifold.VectorBundle.Scalar

/-!
# Compact sublevel sets of the norm on a cotangent bundle

Let `M` be a Riemannian manifold and `K ⊆ M` compact. Tau Ceti proves that the part of the unit
codisc bundle `D*M = {z | ‖z.2‖ ≤ 1}` over `K` is compact
(`TauCeti.CotangentBundle.isCompact_codiscBundle_inter_preimage_proj`). This file deduces that
the covectors over `K` with `‖z.2‖ ≤ r` form a compact set, for every `r`
(`TauCeti.CotangentBundle.isCompact_setOf_norm_snd_le_inter_preimage_proj`): that set lies in
the image of `D*M ∩ π⁻¹ K` under the fibrewise dilation by `max r 1`
(`TauCeti.vectorBundleScalarDiffeomorph`), which keeps each covector over its base point, and is
cut out of that compact image by the closed condition `‖z.2‖ ≤ r`. When `M` is compact, every
sublevel set `{z | ‖z.2‖ ≤ r}` is compact (`TauCeti.CotangentBundle.isCompact_setOf_norm_snd_le`).

Tau Ceti's `TauCeti.isCompact_setOf_norm_le_bundle` and `IsCompact.norm_le_bundle` need fibres
with an inner product, so they do not apply to covectors, whose norm is an operator norm.

It also records that fibre scaling by `t ∈ [0, 1]` multiplies the norm of a covector by `t`
(`TauCeti.CotangentBundle.norm_snd_vectorBundleFiberScaling`).

## Main results

* `TauCeti.CotangentBundle.norm_snd_vectorBundleFiberScaling`: `‖(t • z).2‖ = t ‖z.2‖`.
* `TauCeti.CotangentBundle.isCompact_setOf_norm_snd_le_inter_preimage_proj`: the covectors of
  norm at most `r` over a compact set form a compact set.
* `TauCeti.CotangentBundle.isCompact_setOf_norm_snd_le`: on a compact Riemannian manifold, the
  covectors of norm at most `r` form a compact set.
-/

public section

open Bundle Set
open scoped Manifold

namespace TauCeti.CotangentBundle

section FiberScaling

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- On a Riemannian manifold, fibre scaling by `t ∈ [0, 1]` multiplies the norm of a covector
by `t`. -/
theorem norm_snd_vectorBundleFiberScaling (z : CotangentBundle I M) (t : Icc (0 : ℝ) 1) :
    ‖(vectorBundleFiberScaling (E →L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ)
      (z, t)).snd‖ = t * ‖z.snd‖ := by
  rw [vectorBundleFiberScaling_apply]
  -- This is `norm_smul`; instance search does not find `NormSMulClass` for covectors of the
  -- Riemannian fibre norm, so it is supplied from the `NormedSpace` instance, as in Tau Ceti.
  rw [(NormedSpace.toNormSMulClass (𝕜 := ℝ) (E := TangentSpace I z.proj →L[ℝ] ℝ)).norm_smul,
    Real.norm_of_nonneg t.property.1]

end FiberScaling

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 0 E (fun x : M ↦ TangentSpace I x)]

/-- On a Riemannian manifold, the covectors of norm at most `r` lying over a compact set `K` form
a compact subset of the cotangent bundle. -/
theorem isCompact_setOf_norm_snd_le_inter_preimage_proj {K : Set M} (hK : IsCompact K) (r : ℝ) :
    IsCompact ({z : CotangentBundle I M | ‖z.snd‖ ≤ r} ∩
      π (E →L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) ⁻¹' K) := by
  -- The set lies in the image of `D*M ∩ π⁻¹ K` under the dilation by `c = max r 1 > 0`, which
  -- keeps each covector over its base point.
  have hc : 0 < max r 1 := lt_max_of_lt_right one_pos
  let m := vectorBundleScalarDiffeomorph (I := I) (F := E →L[ℝ] ℝ)
    (V := fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) (n := 0) (fun _ ↦ max r 1) contMDiff_const
    fun _ ↦ hc.ne'
  have hS : IsClosed {z : CotangentBundle I M | ‖z.snd‖ ≤ r} :=
    isClosed_le continuous_norm_snd continuous_const
  have hC := ((isCompact_codiscBundle_inter_preimage_proj (I := I) hK).image m.continuous)
    |>.inter_right hS
  convert hC using 1
  ext z
  constructor
  · rintro ⟨hz, hzK⟩
    refine ⟨⟨m.symm z, ⟨?_, by simpa [m, vectorBundleScalarDiffeomorph_symm] using hzK⟩,
      m.apply_symm_apply z⟩, hz⟩
    rw [mem_codiscBundle, vectorBundleScalarDiffeomorph_symm, vectorBundleScalarDiffeomorph_apply]
    -- This is `norm_smul`; instance search does not find `NormSMulClass` for covectors of the
    -- Riemannian fibre norm, so it is supplied from the `NormedSpace` instance, as in Tau Ceti.
    rw [(NormedSpace.toNormSMulClass (𝕜 := ℝ) (E := TangentSpace I z.proj →L[ℝ] ℝ)).norm_smul,
      Real.norm_of_nonneg (inv_nonneg.2 hc.le), inv_mul_le_one₀ hc]
    exact le_max_of_le_left hz
  · rintro ⟨⟨w, ⟨-, hwK⟩, rfl⟩, hz⟩
    exact ⟨hz, by simpa [m] using hwK⟩

/-- On a compact Riemannian manifold, the covectors of norm at most `r` form a compact subset of
the cotangent bundle. -/
theorem isCompact_setOf_norm_snd_le [CompactSpace M] (r : ℝ) :
    IsCompact {z : CotangentBundle I M | ‖z.snd‖ ≤ r} := by
  simpa using isCompact_setOf_norm_snd_le_inter_preimage_proj (I := I) (isCompact_univ (X := M)) r

end TauCeti.CotangentBundle

end
