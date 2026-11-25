/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Contact.Reeb
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.Smooth

/-!
# Reeb vectors under a local pullback of contact forms

A map `f` that is `C²` at `x`, has surjective differential there, and pulls a contact form `β`
back to a contact form `α` on a neighbourhood of `x`, carries the Reeb vector of `α` at `x` to the
Reeb vector of `β` at `f x`
(`TauCeti.SmoothForm.IsContactForm.mfderiv_reebVectorField_of_eventuallyEq_mpullback`). The proof
adapts that of Tau Ceti's `TauCeti.SmoothForm.IsContactForm.mfderiv_reebVectorField_mpullback`,
which asks for a global pullback by a smooth map whose differentials are all bijective; here only
the germ of the pullback at `x` and the differential at `x` enter.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge Studies in Advanced Mathematics
  109, Cambridge University Press, 2008, §1.1 (cited by Tau Ceti's contact files).
-/

public section

open Filter
open scoped Manifold ContDiff Topology

namespace TauCeti

namespace SmoothForm.IsContactForm

variable {E H M F G N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 2 M] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [TopologicalSpace N] [ChartedSpace G N]
  [IsManifold J 2 N] {α : SmoothForm I M ℝ 1} {β : SmoothForm J N ℝ 1}

/-- A map that is of class `C²` at `x`, has surjective differential there, and pulls the contact
form `β` back to the contact form `α` near `x`, carries the Reeb vector of `α` at `x` to the Reeb
vector of `β` at its image. -/
theorem mfderiv_reebVectorField_of_eventuallyEq_mpullback (hα : α.IsContactForm)
    (hβ : β.IsContactForm) {f : M → N} {x : M} (hf : ContMDiffAt I J 2 f x)
    (hsurj : Function.Surjective (mfderiv I J f x))
    (hpb : ∀ᶠ y in 𝓝 x, α.val y = TauCeti.mpullback I J f β.val y) :
    mfderiv I J f x (α.reebVectorField x) = β.reebVectorField (f x) := by
  refine hβ.eq_reebVectorField_iff.2 ⟨?_, fun w ↦ ?_⟩
  · have h := hα.apply_reebVectorField x
    rw [hpb.self_of_nhds, TauCeti.mpullback_apply] at h
    convert h using 2
    -- The outer `Eq.symm` makes Lean read the vector off the goal's right side.
    exact Eq.symm (FinVec.etaExpand_eq _).symm
  · obtain ⟨u, rfl⟩ := hsurj w
    have hd := mextDerivₗ_apply_eq_of_eventuallyEq_mpullback hf hpb
    rw [← mpullback_apply_pair, mpullback_apply_eq_compContinuousLinearMap, ← mextDerivₗ_apply,
      ← hd, mextDerivₗ_apply]
    exact hα.mextDeriv_reebVectorField_left x u

end SmoothForm.IsContactForm

end TauCeti

end
