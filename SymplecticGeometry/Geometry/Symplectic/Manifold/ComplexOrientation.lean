/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Symplectic.ComplexStructure.Basic
public import SymplecticGeometry.Geometry.Symplectic.Manifold.Volume
public import SymplecticGeometry.Topology.VectorBundle.Orientation.Complex.LineBundle
public import SymplecticGeometry.Topology.VectorBundle.Orientation.Complex.Structure
public import TauCeti.Topology.VectorBundle.Orientation.Complex.EulerClass
public import SymplecticGeometry.Topology.VectorBundle.Complex.RestrictScalars
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Dual

/-!
# The symplectic orientation of a surface is the orientation of a tamed complex structure

Let `σ` be a nondegenerate smooth two-form on a manifold `M` modelled on a real plane, and `J` a
complex structure on the tangent bundle of `M` tamed by `σ`: `σ(v, J v) > 0` for every nonzero
tangent vector `v`. Then every tangent plane carries two orientations: the symplectic orientation
of `σ` (`TauCeti.SmoothTwoForm.IsNondegenerate.volumeOrientation`), and the canonical orientation
of the complex line `(T_x M, J)` (`TauCeti.VectorBundleOrientation.complex`), that of a basis
`(v, J v)`. They agree.

## Main results

* `TauCeti.SmoothTwoForm.IsNondegenerate.map_fiberEquiv_complex_eq_orientationAt`: the
  identification of the fibre of the complex bundle `J.Fiber` with the tangent plane carries the
  canonical orientation of the complex line to the symplectic orientation of `σ`.
* `TauCeti.SmoothTwoForm.IsNondegenerate.complexEulerClass_eq_eulerClass`: hence the Euler class
  `TauCeti.complexEulerClass` of the complex line bundle `(TM, J)` is the Euler class of the
  tangent bundle oriented by the symplectic orientation of `σ`. It follows from
  `TauCeti.Bundle.ContinuousComplexStructure.complexEulerClass_eq_eulerClass` for `J`, since
  by `TauCeti.Bundle.ContinuousComplexStructure.map_fiberEquiv_complex` and the previous result
  the complex orientation of `J` is the symplectic orientation of `σ`.

## Proof

For a nonzero `w` in the fibre, the map `c ↦ c • w` carries the orientation of `ℂ`, that of the
basis `(1, i)`, to the complex orientation of the fibre
(`TauCeti.VectorBundleOrientation.map_toSpanSingletonEquiv`), so this orientation is that of the
basis `(w, J w)`. On a surface the symplectic orientation of `σ` is the orientation on which `σ`
is positive (`TauCeti.SmoothTwoForm.IsNondegenerate.volumeOrientation_eq_ofTopForm`), and
`σ(w, J w) > 0` because `σ` tames `J`.

Tau Ceti's `TauCeti.SymplecticForm.Tames.orientation_reindex` is the linear statement in every
dimension, for the orientation of a symplectic vector space defined through Darboux bases; on a
plane the direct argument above needs neither Darboux bases nor that orientation.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.5
  (complex structures tamed by a symplectic form).
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §14 (the canonical orientation of a complex vector space).
-/

public section

open Bundle Module SymplecticGeometry.Bundle
open scoped Manifold ContDiff

namespace TauCeti.SmoothTwoForm

section Orientation

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {σ : SmoothTwoForm I M} {m : ℕ∞}
  {J : ContMDiffComplexStructure I m E (TangentSpace I : M → Type _)}
  [Fact (finrank ℝ E = 2 * finrank ℂ ℂ)]

open scoped VectorBundle.ComplexToReal

/-- **A tamed complex structure induces the symplectic orientation of a surface.** Let `σ` be a
nondegenerate smooth two-form on a manifold modelled on a plane, and `J` a complex structure on
the tangent bundle, of any regularity, tamed by `σ`. Then at every point `x`, the identification
`J.Fiber x ≃ T_x M` carries the canonical orientation of the complex line `J.Fiber x` to the
symplectic orientation of `σ` at `x`. -/
theorem IsNondegenerate.map_fiberEquiv_complex_eq_orientationAt (h : σ.IsNondegenerate)
    (hE : finrank ℝ E = 2) (hJ : (ContMDiffTwoForm.tangentEquiv.symm σ).Tames J) (x : M) :
    Orientation.map (Fin 2) (J.toContinuousComplexStructure.fiberEquiv x).toLinearEquiv
        (VectorBundleOrientation.reindex (finCongr (by simp))
          (VectorBundleOrientation.complex ℂ J.toContinuousComplexStructure.Fiber) x) =
      (h.volumeOrientation (n := 1) hE).orientationAt x := by
  set K := J.toContinuousComplexStructure
  -- A nonzero tangent vector `w`, read in the fibre of `K.Fiber`. The tangent space is `E` by
  -- definition, which carries the instances.
  have : Nontrivial E :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (M := E) (by omega)
  obtain ⟨w, hw⟩ := exists_ne (0 : TangentSpace I x)
  have hw' : (K.fiberEquiv x).symm w ≠ 0 := by simpa using hw
  set e := VectorBundle.toSpanSingletonEquiv ℂ (finrank_self ℂ) _ hw'
  rw [← VectorBundleOrientation.map_toSpanSingletonEquiv (finrank_self ℂ) _ hw',
    Complex.orientation, ← Basis.orientation_map, ← Basis.orientation_map,
    h.volumeOrientation_eq_ofTopForm hE,
    Manifold.Orientation.orientation_eq_orientationAt_ofTopForm_iff]
  -- The basis is `(w, J w)`, on which `σ` is positive since it tames `J`.
  have hb : ⇑((Complex.basisOneI.map (e.restrictScalars' ℝ).toLinearEquiv).map
      (K.fiberEquiv x).toLinearEquiv) = ![w, J x w] := by
    ext i
    fin_cases i <;> simp [K, e, Bundle.ContinuousComplexStructure.fiberEquiv_I_smul,
      ContMDiffComplexStructure.toContinuousComplexStructure_apply]
  rw [hb]
  simpa using hJ.apply_pos hw

end Orientation

section EulerClass

/-! Euler classes need the base and the fibres in `Type`. -/

variable {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {σ : SmoothTwoForm I M} {m : ℕ∞}
  {J : ContMDiffComplexStructure I m E (TangentSpace I : M → Type)}
  [Fact (finrank ℝ E = 2 * finrank ℂ ℂ)]

open scoped VectorBundle.ComplexToReal

/-- **The Euler class of a tamed complex structure on a surface.** Let `σ` be a nondegenerate
smooth two-form on a manifold `M` modelled on a plane, and `J` a complex structure on the tangent
bundle, of any regularity, tamed by `σ`. Then the Euler class of the complex line bundle
`(TM, J)` is the Euler class of the tangent bundle oriented by the symplectic orientation of
`σ`. -/
theorem IsNondegenerate.complexEulerClass_eq_eulerClass (h : σ.IsNondegenerate)
    (hE : finrank ℝ E = 2) (hJ : (ContMDiffTwoForm.tangentEquiv.symm σ).Tames J) :
    complexEulerClass ℂ J.toContinuousComplexStructure.Fiber (r := 0) (finrank_self ℂ) =
      (h.volumeOrientation (n := 1) hE).toVectorBundleOrientation.eulerClass hE := by
  set K := J.toContinuousComplexStructure
  rw [K.complexEulerClass_eq_eulerClass ℂ hE]
  congr 1
  ext x
  rw [Manifold.Orientation.toVectorBundleOrientation_apply]
  exact (K.map_fiberEquiv_complex ℂ hE x).symm.trans
    (h.map_fiberEquiv_complex_eq_orientationAt hE hJ x)

end EulerClass

end TauCeti.SmoothTwoForm

end
