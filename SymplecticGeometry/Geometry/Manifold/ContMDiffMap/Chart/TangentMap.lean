/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiffMap
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import SymplecticGeometry.Geometry.Manifold.ContMDiffMap.Basic

/-!
# The bundled tangent map of a `C^n` map

For a `C^n` map `f : M → M'` and `m + 1 ≤ n`, the tangent map `tangentMap I I' f` is a `C^m` map
`TM → TM'` (Mathlib's `ContMDiff.contMDiff_tangentMap`); `ContMDiffMap.tangentMap` bundles it.
It is functorial: it sends composites to composites and the identity to the identity.

Its expression in the charts of the tangent bundles is
`ContinuousAt.extChartAt_tangentMap_extChartAt_symm`, in
`SymplecticGeometry/Geometry/Manifold/MFDeriv/Chart.lean`, which is stated for any map continuous
at the point and applies to a bundled map through `ContMDiffMap.coe_tangentMap`.

## Main definitions and results

* `ContMDiffMap.tangentMap`: the tangent map of a `C^n` map, as a `C^m` map of tangent bundles,
  with `ContMDiffMap.coe_tangentMap`.
* `ContMDiffMap.tangentMap_comp`, `ContMDiffMap.tangentMap_id`: functoriality.

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
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 E'' H''}
  {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H'' M'']
  [IsManifold I 1 M] [IsManifold I' 1 M'] [IsManifold I'' 1 M'']

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

/-- The tangent map of a composite of `C^n` maps is the composite of their tangent maps. -/
theorem tangentMap_comp (g : C^n⟮I', M'; I'', M''⟯) (f : C^n⟮I, M; I', M'⟯)
    (hmn : m + 1 ≤ n) :
    (g.comp f).tangentMap hmn = (g.tangentMap hmn).comp (f.tangentMap hmn) := by
  have hn : n ≠ 0 := by
    rintro rfl
    exact absurd hmn (by simp)
  refine ContMDiffMap.ext fun p ↦ ?_
  rw [comp_apply, coe_tangentMap, coe_tangentMap, coe_tangentMap, coe_comp,
    _root_.tangentMap_comp (g.contMDiff.mdifferentiable hn) (f.contMDiff.mdifferentiable hn),
    Function.comp_apply]

/-- The tangent map of the identity is the identity. -/
@[simp]
theorem tangentMap_id (hmn : m + 1 ≤ n) :
    (ContMDiffMap.id : C^n⟮I, M; I, M⟯).tangentMap hmn = ContMDiffMap.id := by
  refine ContMDiffMap.ext fun p ↦ ?_
  rw [coe_tangentMap, coe_id, _root_.tangentMap_id, coe_id]

end ContMDiffMap

end
