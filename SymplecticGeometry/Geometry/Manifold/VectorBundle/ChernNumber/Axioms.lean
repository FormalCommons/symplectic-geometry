/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Singular.SurfaceGenus
public import SymplecticGeometry.Geometry.Manifold.Orientation.EulerCharacteristic
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.ChernNumber.Basic
public import SymplecticGeometry.Geometry.Symplectic.Manifold.ComplexOrientation
public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Genus
public import TauCeti.Geometry.Manifold.Morse.CWModel

/-!
# The axioms of the first Chern number of symplectic bundles over surfaces

This file is meant to hold the axioms that characterize the first Chern number
`SymplecticGeometry.Bundle.symplecticChernNumber` of symplectic vector bundles over closed
oriented surfaces, and the proof that it satisfies them. Here it contains the normalization
axiom:

* `symplecticChernNumber_tangent`: on a closed connected surface `M` with an area form `σ`
  inducing the orientation `o`, the tangent bundle with the form `σ` has first Chern number
  `2 - 2 g`, for `g = TauCeti.surfaceGenus M`.

## Proof

Take a complex structure `J` on `TM` compatible with `σ`, so that the number is that of the
complex line bundle `(TM, J)` (`symplecticChernNumber_eq_chernNumber`): the Euler class of
`(TM, J)`, oriented as a complex line, evaluated on the fundamental class
(`firstChernClass_eq_complexEulerClass`). Since `σ` tames `J` and induces `o`, this Euler class
is that of `TM` oriented by `o`
(`TauCeti.SmoothTwoForm.IsNondegenerate.complexEulerClass_eq_eulerClass`). By Poincaré–Hopf its
evaluation is the Euler characteristic
(`TauCeti.Manifold.Orientation.evalFundamentalClass_eulerClass_eq_eulerChar`). The first Betti
number of `M` is even (`TauCeti.HomologicalOrientation.even_finrank_singularHomology_one`), so
the Euler characteristic is `2 - 2 g`
(`TauCeti.HomologicalOrientation.eulerChar_eq_two_sub_two_mul_genus_iff_even_finrank` and
`TauCeti.HomologicalOrientation.genus_eq_surfaceGenus`). The same route, for the complex
orientation of a complex manifold, gives
`SymplecticGeometry.evalFundamentalClass_chernClass_eq_eulerChar`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.7
  (Theorem 2.7.1).
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §11 (the Euler class of the tangent bundle evaluated on the fundamental class
  is the Euler characteristic) and §14 (the top Chern class of a complex bundle is the Euler class
  of its realification).
-/

public section

open Bundle Module TauCeti TauCeti.Bundle
open scoped Manifold ContDiff

namespace SymplecticGeometry

namespace Bundle

variable {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
  {EM : Type} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [FiniteDimensional ℝ EM]
  [ChartedSpace EM M] [IsManifold 𝓘(ℝ, EM) ∞ M] (hn : finrank ℝ EM = 2)
  (o : Manifold.Orientation 𝓘(ℝ, EM) M (Fin 2))
  (G : Type*) [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  [Fact (finrank ℝ EM = 2 * finrank ℂ G)]

/-- **The first Chern number of the tangent bundle of a closed surface.** Let `M` be a compact
connected Hausdorff smooth surface with an orientation `o`, and `σ` an area form on `M` (a
nondegenerate smooth two-form) whose symplectic orientation is `o`. Then the tangent bundle of
`M` with the form `σ` has first Chern number `2 - 2 g`, computed with any complex model `G`, for
`g = TauCeti.surfaceGenus M` the genus of `M`. -/
theorem symplecticChernNumber_tangent {σ : SmoothTwoForm 𝓘(ℝ, EM) M} (hσ : σ.IsNondegenerate)
    (ho : hσ.volumeOrientation (n := 1) hn = o) :
    symplecticChernNumber (o.toHomologicalOrientation hn) hn G
      (ContMDiffTwoForm.tangentEquiv.symm σ) = 2 - 2 * surfaceGenus M := by
  have : Fact (finrank ℝ EM = 2 * finrank ℂ ℂ) := ⟨by rw [hn, finrank_self]⟩
  let := FiniteCWType.of_isManifold (I := 𝓘(ℝ, EM)) M
  obtain ⟨J, hJ⟩ :=
    (ContMDiffTwoForm.isNondegenerate_tangentEquiv_symm_iff.2 hσ).exists_compatible
  rw [symplecticChernNumber_congr_model _ hn ℂ G,
    symplecticChernNumber_eq_chernNumber _ hn ℂ hJ.tames, chernNumber_def,
    firstChernClass_eq_complexEulerClass _ (finrank_self ℂ),
    hσ.complexEulerClass_eq_eulerClass hn hJ.tames, ho,
    Manifold.Orientation.evalFundamentalClass_eulerClass_eq_eulerChar,
    ((o.toHomologicalOrientation hn).eulerChar_eq_two_sub_two_mul_genus_iff_even_finrank hn).2
      ((o.toHomologicalOrientation hn).even_finrank_singularHomology_one hn),
    (o.toHomologicalOrientation hn).genus_eq_surfaceGenus hn]

end Bundle

end SymplecticGeometry

end
