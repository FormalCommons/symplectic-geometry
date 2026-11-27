/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.RegularValue
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import TauCeti.Algebra.Group.Prod
import TauCeti.Geometry.Manifold.RegularValue.Open

/-!
# Regular points of the slices of a map on a product

For a map `F : P × Q → M`, the slice through `p` is `q ↦ F (p.1, q)`. It is regular at `p.2`
exactly when the map `p ↦ (p.1, F p)` is regular at `p`. With Tau Ceti's
`TauCeti.isOpen_setOf_isRegularPoint`, this shows that for a `C¹` map `F` between
finite-dimensional manifolds the points at which the slice is regular form an open set.

## Main results

* `TauCeti.isRegularPoint_fst_prodMk_iff`: the map `p ↦ (p.1, F p)` is regular at `p` exactly
  when the slice `q ↦ F (p.1, q)` is regular at `p.2`.
* `TauCeti.isOpen_setOfPred_isRegularPoint_slice`: for a `C¹` map `F : P × Q → M`, the points `p`
  where the slice `q ↦ F (p.1, q)` is regular form an open set.
-/

public section

open scoped Manifold ContDiff

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EP : Type*} [NormedAddCommGroup EP] [NormedSpace 𝕜 EP]
  {HP : Type*} [TopologicalSpace HP] {IP : ModelWithCorners 𝕜 EP HP}
  {P : Type*} [TopologicalSpace P] [ChartedSpace HP P]
  {EQ : Type*} [NormedAddCommGroup EQ] [NormedSpace 𝕜 EQ]
  {HQ : Type*} [TopologicalSpace HQ] {IQ : ModelWithCorners 𝕜 EQ HQ}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace HQ Q]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- The map `p ↦ (p.1, F p)` is regular at `p` exactly when the slice `q ↦ F (p.1, q)` of `F` is
regular at `p.2`. -/
theorem isRegularPoint_fst_prodMk_iff {F : P × Q → M} {p : P × Q}
    (hF : MDifferentiableAt (IP.prod IQ) I F p) :
    IsRegularPoint (IP.prod IQ) (IP.prod I) (fun p ↦ (p.1, F p)) p ↔
      IsRegularPoint IQ I (fun q ↦ F (p.1, q)) p.2 := by
  obtain ⟨x, q⟩ := p
  have hslice : mfderiv IQ I (fun q ↦ F (x, q)) q =
      (mfderiv (IP.prod IQ) I F (x, q)).comp
        (ContinuousLinearMap.inr 𝕜 (TangentSpace IP x) (TangentSpace IQ q)) := by
    have h := mfderiv_comp (I := IQ) (I' := IP.prod IQ) (f := fun q : Q ↦ (x, q)) (g := F) q hF
      (mdifferentiableAt_const.prodMk mdifferentiableAt_id)
    rw [mfderiv_prod_right] at h
    exact h
  rw [isRegularPoint_iff, isRegularPoint_iff, mfderiv_prodMk mdifferentiableAt_fst hF,
    mfderiv_fst, hslice]
  exact (mfderiv (IP.prod IQ) I F (x, q)).toLinearMap.toAddMonoidHom.surjective_fst_prod_iff

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 EP] [FiniteDimensional 𝕜 E]
  [IsManifold IP 1 P] [IsManifold IQ 1 Q] [IsManifold I 1 M]

/-- **Regularity of slices is an open condition.** For a `C¹` map `F : P × Q → M`, the points `p`
of `P × Q` at which the slice `q ↦ F (p.1, q)` is regular form an open set. -/
theorem isOpen_setOfPred_isRegularPoint_slice {n : ℕ∞ω} {F : P × Q → M}
    (hF : ContMDiff (IP.prod IQ) I n F) (hn : 1 ≤ n) :
    IsOpen {p : P × Q | IsRegularPoint IQ I (fun q ↦ F (p.1, q)) p.2} := by
  have hF' : ContMDiff (IP.prod IQ) (IP.prod I) n fun p : P × Q ↦ (p.1, F p) :=
    contMDiff_fst.prodMk hF
  convert isOpen_setOf_isRegularPoint hF' hn using 1
  ext p
  exact (isRegularPoint_fst_prodMk_iff
    ((hF p).mdifferentiableAt (zero_lt_one.trans_le hn).ne')).symm


end TauCeti

end
