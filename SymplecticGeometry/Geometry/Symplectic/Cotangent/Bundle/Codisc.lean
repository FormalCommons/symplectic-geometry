/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Codisc
import TauCeti.Geometry.Manifold.VectorBundle.Scalar

/-!
# Compact sublevel sets of the norm on a cotangent bundle

Let `M` be a compact Riemannian manifold. Tau Ceti proves that its unit codisc bundle
`D*M = {z | ‖z.2‖ ≤ 1}` is compact (`TauCeti.CotangentBundle.isCompact_codiscBundle`). This file
deduces that every sublevel set `{z | ‖z.2‖ ≤ r}` of the norm of covectors is compact
(`TauCeti.CotangentBundle.isCompact_setOf_norm_snd_le`): it is closed, and contained in the image
of `D*M` under the fibrewise dilation by `max r 1` (`TauCeti.vectorBundleScalarDiffeomorph`).

Tau Ceti's `TauCeti.isCompact_setOf_norm_le_bundle` and `IsCompact.norm_le_bundle` need fibres
with an inner product, so they do not apply to covectors, whose norm is an operator norm.

## Main results

* `TauCeti.CotangentBundle.isCompact_setOf_norm_snd_le`: on a compact Riemannian manifold, the
  covectors of norm at most `r` form a compact set.
-/

public section

open Bundle Set
open scoped Manifold

namespace TauCeti.CotangentBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 0 E (fun x : M ↦ TangentSpace I x)] [CompactSpace M]

/-- On a compact Riemannian manifold, the covectors of norm at most `r` form a compact subset of
the cotangent bundle. -/
theorem isCompact_setOf_norm_snd_le (r : ℝ) :
    IsCompact {z : CotangentBundle I M | ‖z.snd‖ ≤ r} := by
  -- The set lies in the image of `D*M` under the dilation by `c = max r 1 > 0`.
  have hc : 0 < max r 1 := lt_max_of_lt_right one_pos
  let m := vectorBundleScalarDiffeomorph (I := I) (F := E →L[ℝ] ℝ)
    (V := fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) (n := 0) (fun _ ↦ max r 1) contMDiff_const
    fun _ ↦ hc.ne'
  refine ((isCompact_codiscBundle (I := I) (M := M)).image m.continuous).of_isClosed_subset
    (isClosed_le continuous_norm_snd continuous_const)
    fun z hz ↦ ⟨m.symm z, ?_, m.apply_symm_apply z⟩
  rw [mem_codiscBundle, vectorBundleScalarDiffeomorph_symm, vectorBundleScalarDiffeomorph_apply]
  -- This is `norm_smul`; instance search does not find `NormSMulClass` for covectors of the
  -- Riemannian fibre norm, so it is supplied from the `NormedSpace` instance, as in Tau Ceti.
  rw [(NormedSpace.toNormSMulClass (𝕜 := ℝ) (E := TangentSpace I z.proj →L[ℝ] ℝ)).norm_smul,
    Real.norm_of_nonneg (inv_nonneg.2 hc.le), inv_mul_le_one₀ hc]
  exact le_max_of_le_left hz

end TauCeti.CotangentBundle

end
