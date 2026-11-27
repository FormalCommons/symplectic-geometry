/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.IsFundamentalClass

/-!
# Orientations and integral fundamental classes

Let `M` be a compact Hausdorff manifold modelled on a finite-dimensional real normed space `E`
with `finrank ℝ E = n`. Tau Ceti attaches to every integral fundamental class `μ` of
`Hₙ(M; ℤ)` a homological orientation, `TauCeti.HomologicalOrientation.ofIsFundamentalClass`,
whose fundamental class is `μ`
(`TauCeti.HomologicalOrientation.fundamentalClass_ofIsFundamentalClass`), and the orientation of
the fundamental class of an orientation `o` is `o`
(`TauCeti.HomologicalOrientation.ofIsFundamentalClass_fundamentalClass`). This file packages these
two facts as a bijection between orientations and integral fundamental classes.

## Main definitions

* `TauCeti.HomologicalOrientation.equivIsFundamentalClass`: on a compact manifold with
  `finrank ℝ E = n`, the bijection between orientations and integral fundamental classes.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3.
-/

public section

noncomputable section

open CategoryTheory Module

universe w

namespace TauCeti.HomologicalOrientation

variable {M E : Type w} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M] {n : ℕ}

/-- **Orientations and fundamental classes correspond.** On a compact manifold with
`finrank ℝ E = n`, the bijection between the homological orientations of `M` and the integral
fundamental classes of `Hₙ(M; ℤ)` that sends an orientation to its fundamental class. Its inverse
is `ofIsFundamentalClass`. -/
def equivIsFundamentalClass {M E : Type} [TopologicalSpace M] [T2Space M]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
    [CompactSpace M] (hn : finrank ℝ E = n) :
    HomologicalOrientation M E n ≃
      {μ : ((TopCat.toSSet.obj (TopCat.of M)).homology (ModuleCat.of ℤ (ULift.{0} ℤ)) n :
        ModuleCat.{0} ℤ) // IsFundamentalClass μ} where
  toFun o := ⟨o.fundamentalClass hn, o.isFundamentalClass_fundamentalClass hn⟩
  invFun μ := ofIsFundamentalClass μ.property
  left_inv o := ofIsFundamentalClass_fundamentalClass o hn
  right_inv μ := Subtype.ext (fundamentalClass_ofIsFundamentalClass hn μ.property)

/-- The equivalence `equivIsFundamentalClass` sends an orientation to its fundamental class. -/
@[simp]
theorem coe_equivIsFundamentalClass_apply {M E : Type} [TopologicalSpace M] [T2Space M]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
    [CompactSpace M] (hn : finrank ℝ E = n) (o : HomologicalOrientation M E n) :
    (equivIsFundamentalClass hn o : ((TopCat.toSSet.obj (TopCat.of M)).homology
      (ModuleCat.of ℤ (ULift.{0} ℤ)) n : ModuleCat.{0} ℤ)) = o.fundamentalClass hn :=
  (rfl)

/-- The inverse of `equivIsFundamentalClass` sends a fundamental class to its orientation. -/
@[simp]
theorem equivIsFundamentalClass_symm_apply {M E : Type} [TopologicalSpace M] [T2Space M]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
    [CompactSpace M] (hn : finrank ℝ E = n)
    (μ : {μ : ((TopCat.toSSet.obj (TopCat.of M)).homology (ModuleCat.of ℤ (ULift.{0} ℤ)) n :
      ModuleCat.{0} ℤ) // IsFundamentalClass μ}) :
    (equivIsFundamentalClass (E := E) hn).symm μ = ofIsFundamentalClass μ.property :=
  (rfl)

end TauCeti.HomologicalOrientation

end
