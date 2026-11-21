/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The differential of a partial diffeomorphism followed by a linear equivalence

For a partial diffeomorphism `φ` from a manifold into a normed space `F` and a continuous linear
equivalence `e : F ≃L[𝕜] F'`, the differential of the composite `φ.trans e.toPartialDiffeomorph`
at a point of the source of `φ` is `e` composed with the differential of `φ`
(`PartialDiffeomorph.mvfderiv_trans_toPartialDiffeomorph_apply`). That the composite has the
source of `φ` and the values of `e ∘ φ` is found by `simp`.
-/

public section

open scoped Manifold

namespace PartialDiffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E H M F F' : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {n : WithTop ℕ∞} (φ : PartialDiffeomorph I 𝓘(𝕜, F) M F n) (e : F ≃L[𝕜] F')

/-- On the source of a partial diffeomorphism `φ` into a normed space, the differential of `φ`
followed by a continuous linear equivalence `e` is `e` applied to the differential of `φ`. -/
theorem mvfderiv_trans_toPartialDiffeomorph_apply (hn : n ≠ 0) {x : M}
    (hx : x ∈ φ.source) (v : TangentSpace I x) :
    mvfderiv I (φ.trans e.toPartialDiffeomorph) x v = e (mvfderiv I φ x v) := by
  have h : ⇑(φ.trans e.toPartialDiffeomorph) = (e : F →L[𝕜] F') ∘ φ :=
    funext fun _ ↦ by simp
  rw [h, ContinuousLinearMap.mvfderiv_comp_apply _ (φ.mdifferentiableAt hn hx),
    ContinuousLinearEquiv.coe_coe]

end PartialDiffeomorph

end
