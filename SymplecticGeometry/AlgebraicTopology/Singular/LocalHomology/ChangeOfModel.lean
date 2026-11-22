/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Homological

/-!
# Local homology transport does not depend on the model

Tau Ceti defines the transport of local homology along path classes of a Hausdorff space `M`
charted on a finite-dimensional real normed space `E` (`TauCeti.localHomologyTransport R M E k`),
and with it the transport of local orientations (`TauCeti.localOrientationTransport M E d`). The
definition goes through the atlas of `M`, but the result does not depend on it: if `M` is also
charted on a space `F` of the same dimension, by any atlas, the two transports agree.

The proof uses the characterization of the transport by compact convex sets in charts
(`TauCeti.eq_localHomologyTransport`): a chart `φ : M → E` followed by a linear equivalence
`L : E ≃L[ℝ] F` is a chart into `F`, and a compact convex set `K` of `E` goes to the compact convex
set `L '' K` of `F`, so the transport for `F` has the property that characterizes the one for `E`.

So a homological orientation for one atlas is one for the other
(`TauCeti.HomologicalOrientation.changeModel`). This lets a homological orientation of `M` be
compared, through an open embedding, with one of a space charted on another model of the same
dimension.

## Main definitions and results

* `TauCeti.localHomologyTransport_eq_of_finrank_eq`: the local homology transports for two
  models of the same dimension agree.
* `TauCeti.localOrientationTransport_eq_of_finrank_eq`: so do the transports of local
  orientations.
* `TauCeti.HomologicalOrientation.changeModel`: a homological orientation for the atlas on `E`,
  as one for the atlas on `F`.

## References

* A. Hatcher, *Algebraic Topology*, Section 3.3, where local orientations are compared through
  balls in charts, without reference to an atlas.
-/

public section

noncomputable section

open CategoryTheory Module

universe u v w

namespace TauCeti

variable {A : Type u} [Category.{v} A] [Limits.HasCoproducts.{w} A] [Abelian A] (R : A)
  {M : Type w} [TopologicalSpace M] [T2Space M]
  {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [ChartedSpace F M]

/-- **Local homology transport does not depend on the model.** If `M` is charted on two
finite-dimensional real normed spaces `E` and `F` of the same dimension, by any two atlases, the
transports of local homology along a path class defined through either atlas agree. -/
theorem localHomologyTransport_eq_of_finrank_eq (h : finrank ℝ E = finrank ℝ F) (k : ℕ)
    {x y : FundamentalGroupoid M} (f : x ⟶ y) :
    localHomologyTransport R M E k f = localHomologyTransport R M F k f := by
  let L : E ≃L[ℝ] F := ContinuousLinearEquiv.ofFinrankEq h
  refine (eq_localHomologyTransport (E := E) R k (fun f ↦ localHomologyTransport R M F k f)
    (fun f g ↦ localHomologyTransport_comp R M F k f g) ?_ f).symm
  intro φ K hK hKc hKφ x y γ hγ
  -- Read `φ` through `L`: the compact convex set `L '' K` lies in the target of `φ` followed by
  -- `L`, and the inverse of that chart maps it onto `φ.symm '' K`.
  have hKφ' : ⇑L.toHomeomorph '' K ⊆ (φ.transHomeomorph L.toHomeomorph).target := by
    rw [OpenPartialHomeomorph.transHomeomorph_target]
    rintro _ ⟨z, hz, rfl⟩
    simpa using hKφ hz
  have himage : (φ.transHomeomorph L.toHomeomorph).symm '' (⇑L.toHomeomorph '' K) =
      φ.symm '' K := by
    rw [← Set.image_comp]
    refine Set.image_congr fun z _ ↦ ?_
    simp
  revert hγ
  rw [← himage]
  exact fun hγ ↦ localHomologyRestriction_comp_localHomologyTransport R
    (φ.transHomeomorph L.toHomeomorph) (hK.linear_image L.toLinearMap) (hKc.image L.continuous)
    hKφ' γ hγ k

/-- **Local orientation transport does not depend on the model.** If `M` is charted on two
finite-dimensional real normed spaces `E` and `F` of the same dimension, the transports of local
orientations along a path class defined through either atlas agree. -/
theorem localOrientationTransport_eq_of_finrank_eq (h : finrank ℝ E = finrank ℝ F) (d : ℕ)
    {x y : FundamentalGroupoid M} (f : x ⟶ y) :
    localOrientationTransport M E d f = localOrientationTransport M F d f := by
  ext z : 2
  rw [coe_localOrientationTransport, coe_localOrientationTransport,
    localHomologyTransport_eq_of_finrank_eq _ h]

namespace HomologicalOrientation

variable {d : ℕ}

variable (F) in
/-- A homological orientation of `M` for its atlas on `E`, read as one for an atlas on a space `F`
of the same dimension: the local orientations are the same, and they are compatible with the
transport for `F` since it is the transport for `E`
(`TauCeti.localOrientationTransport_eq_of_finrank_eq`). -/
def changeModel (o : HomologicalOrientation M E d) (h : finrank ℝ E = finrank ℝ F) :
    HomologicalOrientation M F d where
  toFun := o
  localOrientationTransport_toFun' f := by
    rw [← localOrientationTransport_eq_of_finrank_eq h, localOrientationTransport_apply]

@[simp]
theorem changeModel_apply (o : HomologicalOrientation M E d) (h : finrank ℝ E = finrank ℝ F)
    (x : M) : o.changeModel F h x = o x :=
  (rfl)

@[simp]
theorem changeModel_neg (o : HomologicalOrientation M E d) (h : finrank ℝ E = finrank ℝ F) :
    (-o).changeModel F h = -o.changeModel F h :=
  ext fun x ↦ by simp

end HomologicalOrientation

end TauCeti

end
