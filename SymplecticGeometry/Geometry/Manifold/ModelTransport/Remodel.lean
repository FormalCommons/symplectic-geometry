/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.ModelTransport.Diffeomorph

/-!
# A manifold re-modelled along a diffeomorphism of model spaces

Let `Φ : H ≃ₘ^n⟮I, I'⟯ H'` be a `C^n` diffeomorphism between two model spaces, and let `M` be a
space charted on `H`. Composing the charts of `M` with `Φ` charts `M` on `H'`
(`ChartedSpace.comp`), and a `C^n` manifold modelled on `I` becomes a `C^n` manifold modelled on
`I'` (Tau Ceti's `Diffeomorph.isManifold_chartedSpaceComp`). This file names that manifold, as a
type synonym of `M` carrying the new atlas as an instance, and the identity of `M` as a `C^n`
diffeomorphism onto it (by Tau Ceti's `Diffeomorph.contMDiff_chartedSpaceComp_iff`). For
instance, a product of an interval and a manifold over `ℝⁿ`, or an open subset of `ℂ`, can so be
modelled on a Euclidean space `EuclideanSpace ℝ (Fin m)`, as a piece of a gluing over it.

## Main definitions

* `SymplecticGeometry.Remodel Φ M`: the space `M`, with charts in `H'`.
* `SymplecticGeometry.remodelHomeomorph Φ M`: the identity of `M`, as a homeomorphism onto
  `Remodel Φ M`.
* `SymplecticGeometry.remodelDiffeomorph Φ M`: the identity of `M`, as a `C^n` diffeomorphism
  from the model `I` to the model `I'`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Springer GTM 218 (2013),
  Chapter 1 (smooth structures and the smooth manifold chart lemma).
-/

public section

noncomputable section

open scoped Manifold ContDiff

namespace SymplecticGeometry

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H}
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {n : ℕ∞ω}
  (Φ : H ≃ₘ^n⟮I, I'⟯ H') (M : Type*) [TopologicalSpace M]

/-- A space `M` charted on `H`, to be charted on `H'` through a diffeomorphism of models
`Φ : H ≃ₘ^n⟮I, I'⟯ H'`: a copy of `M`, with the same points and topology, whose charts are those
of `M` followed by `Φ`. -/
@[expose, nolint unusedArguments]
def Remodel (_Φ : H ≃ₘ^n⟮I, I'⟯ H') (M : Type*) : Type _ := M

instance : TopologicalSpace (Remodel Φ M) := inferInstanceAs (TopologicalSpace M)

instance [T2Space M] : T2Space (Remodel Φ M) := inferInstanceAs (T2Space M)

/-- The charts of `Remodel Φ M` are the charts of `M` followed by `Φ`. -/
instance [ChartedSpace H M] : ChartedSpace H' (Remodel Φ M) :=
  letI := Φ.toHomeomorph.toOpenPartialHomeomorph.singletonChartedSpace (by simp)
  ChartedSpace.comp H' H M

instance [ChartedSpace H M] [IsManifold I n M] : IsManifold I' n (Remodel Φ M) :=
  Φ.isManifold_chartedSpaceComp M

/-- The identity of `M`, as a homeomorphism onto its copy `Remodel Φ M`. -/
def remodelHomeomorph : M ≃ₜ Remodel Φ M := Homeomorph.refl M

/-- The homeomorphism sends each point of `M` to the same point of the copy. -/
theorem coe_remodelHomeomorph : ⇑(remodelHomeomorph Φ M) = id := (rfl)

/-- The inverse homeomorphism sends each point of the copy to the same point of `M`. -/
theorem coe_remodelHomeomorph_symm : ⇑(remodelHomeomorph Φ M).symm = id := (rfl)

/-- The homeomorphism sends a point `x` of `M` to `x`, as a point of the copy. -/
@[simp]
theorem remodelHomeomorph_apply (x : M) : remodelHomeomorph Φ M x = (x : Remodel Φ M) := (rfl)

/-- The inverse homeomorphism sends a point `x` of the copy to `x`, as a point of `M`. -/
@[simp]
theorem remodelHomeomorph_symm_apply (x : Remodel Φ M) :
    (remodelHomeomorph Φ M).symm x = (x : M) := (rfl)

variable [ChartedSpace H M]

/-- The identity of `M`, as a `C^n` diffeomorphism from `M`, modelled on `I`, to `Remodel Φ M`,
modelled on `I'`. -/
def remodelDiffeomorph : M ≃ₘ^n⟮I, I'⟯ Remodel Φ M where
  toEquiv := (remodelHomeomorph Φ M).toEquiv
  contMDiff_toFun :=
    (Φ.contMDiff_chartedSpaceComp_iff (M := M) (f := id)).2 contMDiff_id
  contMDiff_invFun :=
    (Φ.contMDiff_chartedSpaceComp_iff (X := Remodel Φ M) (M := M)
      (f := (id : Remodel Φ M → M))).1 contMDiff_id

@[simp]
theorem coe_remodelDiffeomorph : ⇑(remodelDiffeomorph Φ M) = remodelHomeomorph Φ M := (rfl)

@[simp]
theorem coe_remodelDiffeomorph_symm :
    ⇑(remodelDiffeomorph Φ M).symm = (remodelHomeomorph Φ M).symm := (rfl)

end SymplecticGeometry

end
