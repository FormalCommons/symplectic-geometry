/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.ZeroSection
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Liouville

/-!
# The canonical symplectic form along the zero section

Let `T*L = TauCeti.CotangentBundle I L` be the cotangent bundle of a manifold `L`, with canonical
symplectic form `ω = -dλ` (`TauCeti.CotangentBundle.symplecticForm`). At a point `0_q` of the zero
section, Tau Ceti's splitting `TauCeti.Bundle.zeroSectionTangentEquiv q` identifies the tangent
space `T_{0_q}(T*L)` with `T_q L × T*_q L`: the first summand is the image of the differential of
the zero section, the second the vertical tangent space.

This file computes `ω` in this splitting: for `v, w ∈ T_q L` and `a, b ∈ T*_q L`,

`ω((v, a), (w, b)) = b v - a w`

(`TauCeti.CotangentBundle.eval₂_symplecticForm_zeroSectionTangentEquiv_symm`). So at the zero
section `ω` is the linear form `TauCeti.strongDualCotangentSymplecticForm` of `T_q L × T*_q L`,
with its sign. The base may have boundary or corners, and nothing here assumes finite dimension.

## Main results

* `TauCeti.CotangentBundle.eval₂_symplecticForm_zeroSectionTangentEquiv_symm`: the canonical
  symplectic form at `0_q`, read in the splitting `T_q L × T*_q L`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Exercise 3.1.19.
-/

public section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti.CotangentBundle

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {L : Type*} [TopologicalSpace L] [ChartedSpace H L]

/-- **The canonical symplectic form along the zero section.** At the point `0_q` of the zero
section of `T*L`, read the tangent space of `T*L` as `T_q L × T*_q L` through
`TauCeti.Bundle.zeroSectionTangentEquiv q`. Then the canonical symplectic form
`ω = TauCeti.CotangentBundle.symplecticForm I L` pairs `(v, a)` and `(w, b)` to `b v - a w`. -/
theorem eval₂_symplecticForm_zeroSectionTangentEquiv_symm [IsManifold I ∞ L] (q : L)
    (v w : TangentSpace I q) (a b : TangentSpace I q →L[ℝ] ℝ) :
    SmoothBundleForm.eval₂ (symplecticForm I L)
        (zeroSection (E →L[ℝ] ℝ) (fun x : L ↦ TangentSpace I x →L[ℝ] ℝ) q)
        ((Bundle.zeroSectionTangentEquiv (I := I) q).symm (v, a))
        ((Bundle.zeroSectionTangentEquiv (I := I) q).symm (w, b)) =
      b v - a w := by
  rw [eval₂_symplecticForm, Bundle.zeroSectionTangentEquiv_symm_apply,
    Bundle.zeroSectionTangentEquiv_symm_apply, continuousLinearMapAt_trivializationAt_self,
    continuousLinearMapAt_trivializationAt_self]
  exact strongDualCotangentSymplecticForm_apply (V := E) (v, a) (w, b)

end TauCeti.CotangentBundle

end
