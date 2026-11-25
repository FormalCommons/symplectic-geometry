/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.HomotopyInvariance
import SymplecticGeometry.Geometry.Manifold.DeRham.Map.FromTauCeti

/-!
# De Rham cohomology of a smoothly contractible manifold

This file is a part of Tau Ceti's file `TauCeti/Geometry/Manifold/DeRham/HomotopyInvariance.lean`,
as of the commit `b952d20066` of Tau Ceti's main branch. It contains only the theorem that this
commit adds there, `TauCeti.subsingleton_deRhamCohomology_of_contraction`: a constant map pulls
forms of positive degree back to zero, so by homotopy invariance a smoothly contractible manifold
has no de Rham cohomology in positive degrees.

It is stated under its Tau Ceti name and namespace, with Tau Ceti's statement, proof, docstring
and variables. The one change is to the imports: in place of Tau Ceti's file, this file imports the
pinned version of it, together with
`SymplecticGeometry/Geometry/Manifold/DeRham/Map/FromTauCeti.lean`, for
`TauCeti.deRhamCohomology.map_const_eq_zero`, which the same commit adds to Tau Ceti's
`TauCeti/Geometry/Manifold/DeRham/Map.lean`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 17, section Homotopy
  Invariance.
* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, GTM 82, §4.
-/

public section

noncomputable section

open Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E H E' H' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'}
  {M M' : Type*}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace M'] [ChartedSpace H' M']

/-- **De Rham cohomology of a smoothly contractible manifold vanishes in positive degrees.** If
`F : M × [0, 1] → M` is a smooth homotopy from the identity of `M` to the constant map at `c`,
then `H^k(M) = 0` for `k ≠ 0`. The manifold `M` may have boundary or corners. -/
theorem subsingleton_deRhamCohomology_of_contraction {F : M × Icc (0 : ℝ) 1 → M}
    (hF : ContMDiff (I.prod (𝓡∂ 1)) I ∞ F) {c : M} (hF₀ : ∀ x, F (x, 0) = x)
    (hF₁ : ∀ x, F (x, 1) = c) {k : ℕ} (hk : k ≠ 0) :
    Subsingleton (deRhamCohomology I M k) := by
  have h := deRhamCohomology.map_eq_of_homotopy contMDiff_id contMDiff_const hF hF₀ hF₁ k
  rw [deRhamCohomology.map_id, deRhamCohomology.map_const_eq_zero hk] at h
  exact subsingleton_of_forall_eq 0 fun a ↦ by simpa using LinearMap.congr_fun h a

end TauCeti
