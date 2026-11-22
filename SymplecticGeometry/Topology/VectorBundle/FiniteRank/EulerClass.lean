/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Pullback
public import TauCeti.Topology.VectorBundle.Orientation.Complex.FiberwiseEquiv
public import SymplecticGeometry.Topology.VectorBundle.FiniteRank.Basic

/-!
# The Euler class of a complex finite-rank core

Two facts about Tau Ceti's `TauCeti.complexEulerClass` of the bundle of a complex finite-rank
core `A : TauCeti.FiniteRankBundleCore ℂ B`:

* `TauCeti.FiniteRankBundleCore.complexEulerClass_eq_of_iso`: isomorphic cores have the same
  Euler class;
* `TauCeti.FiniteRankBundleCore.complexEulerClass_pullback`: the Euler class of the pull-back
  core `A.pullback f` is the pull-back of the Euler class of `A`.

Both follow from Tau Ceti's `TauCeti.complexEulerClass_eq_of_fiberwise` and
`TauCeti.complexEulerClass_eq_singularCohomologyMap_of_fiberwise`; the first is applied to the
fibrewise equivalences `TauCeti.FiniteRankBundleCore.isoFiberEquiv` of the isomorphism.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §9 and §14 (naturality of the Euler class).
-/

public section

open CategoryTheory Module TauCeti

namespace TauCeti.FiniteRankBundleCore

variable {B : Type} [TopologicalSpace B] {r : ℕ}

/-- **Isomorphic complex finite-rank cores have the same Euler class.** -/
theorem complexEulerClass_eq_of_iso {A D : FiniteRankBundleCore ℂ B} (e : A ≅ D)
    (hA : finrank ℂ (Fin A.rank → ℂ) = r + 1) (hD : finrank ℂ (Fin D.rank → ℂ) = r + 1) :
    complexEulerClass (Fin A.rank → ℂ) A.core.Fiber hA =
      complexEulerClass (Fin D.rank → ℂ) D.core.Fiber hD :=
  complexEulerClass_eq_of_fiberwise hD hA (continuous_isoFiberEquiv e)

/-- **Naturality of the Euler class of a complex finite-rank core**: the Euler class of the
pull-back core `A.pullback f` is the pull-back of the Euler class of `A`. -/
theorem complexEulerClass_pullback {X : Type} [TopologicalSpace X] (A : FiniteRankBundleCore ℂ B)
    (f : C(X, B)) (hA : finrank ℂ (Fin A.rank → ℂ) = r + 1) :
    complexEulerClass (Fin (A.pullback f).rank → ℂ) (A.pullback f).core.Fiber hA =
      TopCat.singularCohomologyMap (TopCat.ofHom f) (2 * r + 2)
        (complexEulerClass (Fin A.rank → ℂ) A.core.Fiber hA) :=
  complexEulerClass_eq_singularCohomologyMap_of_fiberwise hA hA
    (φ := fun _ ↦ ContinuousLinearEquiv.refl ℂ (Fin A.rank → ℂ))
    ((A.continuous_pullbackLift f).congr fun p ↦ A.pullbackLift_eq_mk f p rfl rfl)

end TauCeti.FiniteRankBundleCore

end
