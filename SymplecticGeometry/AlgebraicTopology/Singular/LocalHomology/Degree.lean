/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.Orientation.FundamentalClass
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.LocalIndex

/-!
# Fundamental classes under maps of degree `±1`

Let `M` and `N` be compact Hausdorff `n`-manifolds, `N` preconnected, with integral fundamental
classes `μ` and `ν`. A continuous map `f : M → N` for which some point `x` is the only point over
`f x`, and which is a local homeomorphism at `x`, sends `μ` to `ν` or to `-ν` in `Hₙ(N; ℤ)`.

The statement is about fundamental classes rather than orientations. The proof orients `M` and `N`
by `μ` and `ν` (`TauCeti.HomologicalOrientation.ofIsFundamentalClass`), whose fundamental classes
are `μ` and `ν` again; then the image of `μ` is `deg f • ν`
(`TauCeti.HomologicalOrientation.mapFundamentalClass_eq_degree_smul`), and `deg f = ±1`
(`TauCeti.HomologicalOrientation.degree_eq_one_or_eq_neg_one_of_isLocalHomeomorphOn`).

## Main results

* `TauCeti.IsFundamentalClass.map_eq_or_eq_neg_of_isLocalHomeomorphOn`: the image of `μ` is `ν`
  or `-ν`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3.
-/

public section

open CategoryTheory Module AlgebraicTopology

namespace TauCeti.IsFundamentalClass

variable {M N E F : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [TopologicalSpace N] [T2Space N] [CompactSpace N] [PreconnectedSpace N]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [ChartedSpace F N] {n : ℕ}

/-- **A map with a one-point fibre at which it is a local homeomorphism sends a fundamental class
to `±` the other.** Let `M`, `N` be compact `n`-manifolds, `N` preconnected, with
integral fundamental classes `μ` and `ν`. If `f : M → N` is a local homeomorphism on a set
containing `x`, and `x` is the only point sent to `f x`, then `f_* μ = ν` or `f_* μ = -ν`. -/
theorem map_eq_or_eq_neg_of_isLocalHomeomorphOn (hE : finrank ℝ E = n) (hF : finrank ℝ F = n)
    {μ : ((TopCat.toSSet.obj (TopCat.of M)).homology (ModuleCat.of ℤ (ULift.{0} ℤ)) n :
      ModuleCat.{0} ℤ)}
    {ν : ((TopCat.toSSet.obj (TopCat.of N)).homology (ModuleCat.of ℤ (ULift.{0} ℤ)) n :
      ModuleCat.{0} ℤ)}
    (hμ : IsFundamentalClass μ) (hν : IsFundamentalClass ν) {f : C(M, N)} {x : M}
    (hfib : f ⁻¹' {f x} = {x}) {s : Set M} (hs : IsLocalHomeomorphOn f s) (hx : x ∈ s) :
    (((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj (ModuleCat.of ℤ (ULift.{0} ℤ))).map
        (TopCat.ofHom f)).hom μ = ν ∨
      (((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj (ModuleCat.of ℤ (ULift.{0} ℤ))).map
        (TopCat.ofHom f)).hom μ = -ν := by
  set o := HomologicalOrientation.ofIsFundamentalClass (E := E) hμ
  set o' := HomologicalOrientation.ofIsFundamentalClass (E := F) hν
  have h := o.mapFundamentalClass_eq_degree_smul o' hE hF f
  rw [HomologicalOrientation.mapFundamentalClass_def,
    HomologicalOrientation.fundamentalClass_ofIsFundamentalClass,
    HomologicalOrientation.fundamentalClass_ofIsFundamentalClass] at h
  rw [h]
  rcases o.degree_eq_one_or_eq_neg_one_of_isLocalHomeomorphOn o' hE hF f.continuous.isProperMap
    hfib hs hx with hd | hd
  · exact Or.inl (by rw [hd, one_zsmul])
  · exact Or.inr (by rw [hd, neg_one_zsmul])

end TauCeti.IsFundamentalClass

end
