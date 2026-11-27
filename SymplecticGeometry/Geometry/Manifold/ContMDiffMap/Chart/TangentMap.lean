/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiffMap
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Submersion
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic

/-!
# The bundled tangent map of a `C^n` map and its chart expression

For a `C^n` map `f : M → M'` and `m + 1 ≤ n`, the tangent map `tangentMap I I' f` is a `C^m` map
`TM → TM'` (Mathlib's `ContMDiff.contMDiff_tangentMap`); `ContMDiffMap.tangentMap` bundles it.

In the charts of the tangent bundles that Mathlib builds from base charts, the tangent map reads
as `(z, v) ↦ (f̃ z, Df̃(z) v)`, where `f̃ = extChartAt I' y ∘ f ∘ (extChartAt I x).symm` is the
chart expression of `f` in the base charts and the derivative is taken within the target of the
chart at `x` (`ContinuousAt.extChartAt_tangentMap_extChartAt_symm`). The fibre coordinate of a
tangent-bundle chart is a tangent coordinate change, so this rests on Tau Ceti's
`ContinuousAt.fderivWithin_extChartAt_comp_extChartAt_symm`, which writes the derivative of `f̃`
within `range I` as `mfderiv I I' f` conjugated by tangent coordinate changes. The targets and
sources of the tangent-bundle charts are described by Mathlib's `FiberBundle.extChartAt_target`
and `TangentBundle.mem_chart_source_iff`.

## Main definitions and results

* `ContMDiffMap.tangentMap`: the tangent map of a `C^n` map, as a `C^m` map of tangent bundles,
  with `ContMDiffMap.coe_tangentMap`.
* `ContinuousAt.extChartAt_tangentMap_extChartAt_symm`: the chart expression of a tangent map.

## References

* [M. W. Hirsch, *Differential Topology*][Hirsch1976], Chapter 1, §2
-/

public section

open scoped Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  [IsManifold I 1 M] [IsManifold I' 1 M']

/-- **Chart expression of a tangent map.** Let `p` be a tangent vector of `M` and `q` one of
`M'`. A point `w = (z, v)` of the target of the tangent-bundle chart at `p` whose base point
`x = (extChartAt I p.proj).symm z` is sent by `f` into the source of the chart at `q.proj` is
sent by the tangent map of `f`, read in the tangent-bundle charts at `p` and `q`, to
`(f̃ z, Df̃(z) v)`, where `f̃ = extChartAt I' q.proj ∘ f ∘ (extChartAt I p.proj).symm` and the
derivative is taken within the target of the chart at `p.proj`. Only continuity of `f` at `x` is
assumed: where `f` is not differentiable both derivatives are zero. -/
theorem ContinuousAt.extChartAt_tangentMap_extChartAt_symm {f : M → M'}
    {p : TangentBundle I M} {q : TangentBundle I' M'} {w : E × E}
    (hw : w ∈ (extChartAt I.tangent p).target)
    (hc : ContinuousAt f ((extChartAt I p.proj).symm w.1))
    (hf : f ((extChartAt I p.proj).symm w.1) ∈ (extChartAt I' q.proj).source) :
    extChartAt I'.tangent q (tangentMap I I' f ((extChartAt I.tangent p).symm w)) =
      ((extChartAt I' q.proj ∘ f ∘ (extChartAt I p.proj).symm) w.1,
        fderivWithin 𝕜 (extChartAt I' q.proj ∘ f ∘ (extChartAt I p.proj).symm)
          (extChartAt I p.proj).target w.1 w.2) := by
  set b := (extChartAt I.tangent p).symm w
  set x := (extChartAt I p.proj).symm w.1
  have hz : w.1 ∈ (extChartAt I p.proj).target := Bundle.fst_mem_extChartAt_target p hw
  have hbx : b.proj = x := Bundle.proj_extChartAt_symm p hw
  have hx : x ∈ (extChartAt I p.proj).source := (extChartAt I p.proj).map_target hz
  have hxw : extChartAt I p.proj x = w.1 := (extChartAt I p.proj).right_inv hz
  obtain ⟨-, hbv⟩ := TauCeti.Manifold.extChartAt_tangent_symm_mem_baseSet_and_snd p hw
  rw [TangentBundle.trivializationAt_snd_eq_tangentCoordChange b.snd, hbx] at hbv
  have hfb : (tangentMap I I' f b).proj ∈
      (trivializationAt E' (TangentSpace I') q.proj).baseSet := by
    rw [tangentMap_proj, hbx]
    exact TangentBundle.mem_trivializationAt_baseSet_of_mem_extChartAt_source hf
  rw [Bundle.extChartAt_apply_of_mem_baseSet q hfb]
  refine Prod.ext ?_ ?_
  · simp [tangentMap_proj, hbx, x]
  clear_value b x
  obtain ⟨y, u⟩ := b
  obtain rfl : y = x := hbx
  rw [fderivWithin_congr_set (extChartAt_target_eventuallyEqSet_of_mem hz), ← hxw,
    hc.fderivWithin_extChartAt_comp_extChartAt_symm hx hf, ← hbv, tangentMap,
    TangentBundle.trivializationAt_snd_eq_tangentCoordChange]
  -- `TangentSpace I y` is `E` by definition, which hides the composite from
  -- `ContinuousLinearMap.comp_apply`; it is the nested application by definition.
  exact congrArg _ (congrArg _
    (TauCeti.tangentCoordChange_tangentCoordChange (mem_extChartAt_source y) hx u).symm)

namespace ContMDiffMap

variable {m n : WithTop ℕ∞}

/-- The tangent map of a `C^n` map `f : M → M'`, as a `C^m` map of tangent bundles, for
`m + 1 ≤ n`. -/
noncomputable def tangentMap (f : C^n⟮I, M; I', M'⟯) (hmn : m + 1 ≤ n) :
    C^m⟮I.tangent, TangentBundle I M; I'.tangent, TangentBundle I' M'⟯ :=
  ⟨_root_.tangentMap I I' f, f.contMDiff.contMDiff_tangentMap hmn⟩

@[simp]
theorem coe_tangentMap (f : C^n⟮I, M; I', M'⟯) (hmn : m + 1 ≤ n) :
    ⇑(f.tangentMap hmn) = _root_.tangentMap I I' f :=
  (rfl)

end ContMDiffMap

end
