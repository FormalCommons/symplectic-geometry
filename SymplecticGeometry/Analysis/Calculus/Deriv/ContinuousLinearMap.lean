/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap

/-!
# Derivatives of paths of skew-symmetric bilinear maps

If `ω s` is a skew-symmetric continuous bilinear map for every `s` near `t`, then so is
`deriv ω t`. This is the skew analogue of Tau Ceti's `TauCeti.fderiv_apply_apply_comm`, and it
follows from Tau Ceti's `TauCeti.clm_apply_fderiv_eq_zero`, applied to the continuous linear map
`β ↦ β v w + β w v`.

No differentiability is assumed: where the path is not differentiable its `deriv` is zero, and
the identity is trivial.

## Main results

* `SymplecticGeometry.deriv_apply_apply_eq_neg`: the derivative of a path of skew forms is skew.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  proof of Corollary 2.5.14, where this identity is used.
-/

public section

open Filter
open scoped Topology

namespace SymplecticGeometry

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- If `ω s` is skew-symmetric for every `s` near `t`, then so is `deriv ω t`. -/
theorem deriv_apply_apply_eq_neg {F G : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] {ω : 𝕜 → F →L[𝕜] F →L[𝕜] G} {t : 𝕜}
    (hskew : ∀ᶠ s in 𝓝 t, ∀ v w, ω s v w = -ω s w v) (v w : F) :
    deriv ω t v w = -deriv ω t w v := by
  open ContinuousLinearMap in
  have h := TauCeti.clm_apply_fderiv_eq_zero (𝕜 := 𝕜) (E := 𝕜) (F := F →L[𝕜] F →L[𝕜] G) (G := G)
    (L := (apply 𝕜 G w).comp (apply 𝕜 _ v) + (apply 𝕜 G v).comp (apply 𝕜 _ w)) (g := ω)
    (hskew.mono fun s hs => by simp [hs v w]) 1
  simpa [eq_neg_iff_add_eq_zero] using h

end SymplecticGeometry

end
