/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.IsFundamentalClass

/-!
# The orientation of an integral fundamental class

Let `M` be a Hausdorff manifold modelled on a finite-dimensional real normed space `E`, and `μ` an
integral class of `Hₙ(M; ℤ)` that is a fundamental class (`TauCeti.IsFundamentalClass`). Its
images `Hₙ(M; ℤ) → Hₙ(M, M ∖ {x}; ℤ)` in the local homology are local orientations
(`TauCeti.isFundamentalClass_iff_forall_isLocalOrientation`), and they are carried to one another
by transport along paths, since restrictions of a global class are
(`TauCeti.localHomologyRestriction_univ_comp_localHomologyTransport`). So they form a homological
orientation, `TauCeti.HomologicalOrientation.ofIsFundamentalClass`. When `M` is compact and
`finrank ℝ E = n`, the fundamental class of that orientation is `μ` again
(`TauCeti.HomologicalOrientation.fundamentalClass_ofIsFundamentalClass`), by the uniqueness of the
fundamental class (`TauCeti.HomologicalOrientation.eq_fundamentalClass`). This is the converse of
Tau Ceti's `TauCeti.HomologicalOrientation.isFundamentalClass_fundamentalClass`.

Neither connectedness nor compactness is needed for the orientation itself.

## Main definitions

* `TauCeti.HomologicalOrientation.ofIsFundamentalClass`: the orientation whose local orientation
  at `x` is the image of the fundamental class `μ` in the local homology at `x`.

## Main results

* `TauCeti.HomologicalOrientation.coe_ofIsFundamentalClass_apply`: its value at `x`.
* `TauCeti.HomologicalOrientation.fundamentalClass_ofIsFundamentalClass`: on a compact manifold,
  its fundamental class is `μ`.

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

/-- **The orientation of an integral fundamental class.** For a fundamental class `μ` of
`Hₙ(M; ℤ)`, the homological orientation whose local orientation at each point `x` is the image of
`μ` in the local homology `Hₙ(M, M ∖ {x}; ℤ)`. -/
def ofIsFundamentalClass
    {μ : ((TopCat.toSSet.obj (TopCat.of M)).homology (ModuleCat.of ℤ (ULift.{w} ℤ)) n :
      ModuleCat.{w} ℤ)}
    (hμ : IsFundamentalClass μ) : HomologicalOrientation M E n where
  toFun x := ⟨singularHomologyToLocalHomology (ModuleCat.of ℤ (ULift.{w} ℤ)) x n μ,
    (isFundamentalClass_iff_forall_isLocalOrientation μ).1 hμ x⟩
  localOrientationTransport_toFun' f := by
    ext : 1
    rw [coe_localOrientationTransport]
    dsimp only
    rw [singularHomologyToLocalHomology_apply, singularHomologyToLocalHomology_apply,
      ← ConcreteCategory.comp_apply, localHomologyRestriction_univ_comp_localHomologyTransport]

/-- The local orientation at `x` of the orientation of a fundamental class `μ` is the image of `μ`
in the local homology at `x`. -/
@[simp]
theorem coe_ofIsFundamentalClass_apply
    {μ : ((TopCat.toSSet.obj (TopCat.of M)).homology (ModuleCat.of ℤ (ULift.{w} ℤ)) n :
      ModuleCat.{w} ℤ)}
    (hμ : IsFundamentalClass μ) (x : M) :
    ((ofIsFundamentalClass (E := E) hμ x : LocalOrientation M x n) :
        (localHomology (ModuleCat.of ℤ (ULift.{w} ℤ)) ({x} : Set M) n : ModuleCat.{w} ℤ)) =
      singularHomologyToLocalHomology (ModuleCat.of ℤ (ULift.{w} ℤ)) x n μ :=
  (rfl)

/-- **A fundamental class is the fundamental class of its orientation**: on a compact manifold of
dimension `n`, the fundamental class of the orientation of an integral fundamental class `μ` is
`μ`. -/
@[simp]
theorem fundamentalClass_ofIsFundamentalClass {M E : Type} [TopologicalSpace M] [T2Space M]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
    [CompactSpace M] (hn : finrank ℝ E = n)
    {μ : ((TopCat.toSSet.obj (TopCat.of M)).homology (ModuleCat.of ℤ (ULift.{0} ℤ)) n :
      ModuleCat.{0} ℤ)}
    (hμ : IsFundamentalClass μ) :
    (ofIsFundamentalClass (E := E) hμ).fundamentalClass hn = μ :=
  ((ofIsFundamentalClass (E := E) hμ).eq_fundamentalClass hn fun x ↦
    coe_ofIsFundamentalClass_apply (E := E) hμ x).symm

end TauCeti.HomologicalOrientation

end
