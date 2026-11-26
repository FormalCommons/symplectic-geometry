/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Cohomology.FundamentalClass
public import SymplecticGeometry.Geometry.Manifold.Complex.HomologicalOrientation
public import SymplecticGeometry.Geometry.Manifold.Orientation.EulerCharacteristic
public import SymplecticGeometry.Topology.VectorBundle.Complex.ChernClass.EulerClass
public import TauCeti.Topology.VectorBundle.Orientation.FiberwiseEquiv
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.RestrictScalars
public import SymplecticGeometry.Topology.VectorBundle.Complex.RestrictScalars

/-!
# The top Chern class of a compact complex manifold and its Euler characteristic

Let `M` be a complex manifold modelled on `𝓘(ℂ, E)`, with `finrank ℂ E = r + 1`. Its tangent bundle
is a complex vector bundle, `TangentSpace 𝓘(ℂ, E)`, and with the same charts `M` is a real
manifold, whose tangent bundle `TangentSpace 𝓘(ℝ, E)` has the same total space: Tau Ceti's
`TangentBundle.restrictScalarsHomeomorph` identifies the two, and on the fibre over `x` its
inverse is the identity of `E`, as the map
`(tangentSpaceCastModel 𝓘(ℝ, E) x).trans`
`((tangentSpaceCastModel 𝓘(ℂ, E) x).restrictScalars ℝ).symm`.

* `TauCeti.map_orientationAt_complexManifoldOrientation_eq_complex`: this
  identification carries the canonical orientation `TauCeti.complexManifoldOrientation E M` of
  the real tangent space at `x` to the canonical orientation
  `TauCeti.VectorBundleOrientation.complex` of the complex one. Both are the orientation
  `TauCeti.complexOrientation E` of the model, by Tau Ceti's
  `TauCeti.orientationAt_complexManifoldOrientation_eq_complexOrientation` and
  `TauCeti.VectorBundleOrientation.complex_apply`.
* `SymplecticGeometry.complexEulerClass_tangentSpace`: hence the Euler class of the complex
  tangent bundle, `TauCeti.complexEulerClass`, is the Euler class of the real tangent bundle
  oriented by `complexManifoldOrientation E M`, reindexed
  (`SymplecticGeometry.complexManifoldOrientationOfFinrank`), by
  `TauCeti.VectorBundleOrientation.eulerClass_eq_of_fiberwise`.
* `SymplecticGeometry.evalFundamentalClass_chernClass_eq_eulerChar`: for `M` compact, Hausdorff
  and smooth, `⟨c_{r+1}(TM), [M]⟩ = χ(M)`, the fundamental class being that of the canonical
  orientation. The top Chern class is the Euler class
  (`SymplecticGeometry.Bundle.chernClass_finrank_eq_complexEulerClass`), read in integral
  cohomology through `TopCat.uliftIntegralCohomologyIso`, which does not change its evaluation
  (`TauCeti.HomologicalOrientation.evalFundamentalClass_uliftIntegralCohomologyIso_hom`); by the
  previous item it is the Euler class of the oriented real tangent bundle, whose evaluation on
  the fundamental class is the Euler characteristic
  (`TauCeti.Manifold.Orientation.evalFundamentalClass_eulerClass_eq_eulerChar_of_finiteCWType`).

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §11 (the Euler class of the tangent bundle evaluated on the fundamental class
  is the Euler characteristic) and §14 (complex bundles are oriented as real bundles, and
  their top Chern class is their Euler class).
* [R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §11 and §20.
-/

public section

open Bundle Module TauCeti
open scoped Manifold ContDiff TauCeti.ComplexManifold

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M]

namespace TauCeti

variable [IsManifold 𝓘(ℂ, E) 1 M]

/-- The identification of the real tangent space of a complex manifold at `x` with its complex
tangent space, the fibre of the inverse of `TangentBundle.restrictScalarsHomeomorph`, carries the
canonical orientation `complexManifoldOrientation E M` to the canonical orientation of the complex
tangent space. -/
theorem map_orientationAt_complexManifoldOrientation_eq_complex (x : M) :
    Orientation.map _ ((tangentSpaceCastModel 𝓘(ℝ, E) x).trans
        ((tangentSpaceCastModel 𝓘(ℂ, E) x).restrictScalars ℝ).symm).toLinearEquiv
        ((complexManifoldOrientation E M).orientationAt x) =
      VectorBundleOrientation.complex E (TangentSpace 𝓘(ℂ, E) : M → Type) x := by
  -- `tangentSpaceCastModel 𝓘(ℝ, E) x` is the identity of `E` by definition, and Mathlib states no
  -- lemma for it.
  have h : ((tangentSpaceCastModel 𝓘(ℝ, E) x).trans
      ((tangentSpaceCastModel 𝓘(ℂ, E) x).restrictScalars ℝ).symm).toLinearEquiv =
      ((tangentSpaceCastModel 𝓘(ℂ, E) x).symm.toLinearEquiv).restrictScalars ℝ :=
    LinearEquiv.ext fun _ ↦ rfl
  rw [h, VectorBundleOrientation.complex_apply,
    orientationAt_complexManifoldOrientation_eq_complexOrientation]
  -- The left side is an orientation of `TangentSpace 𝓘(ℝ, E) x`, which is `E` by definition.
  exact (tangentSpaceCastModel 𝓘(ℂ, E) x).symm.toLinearEquiv.map_complexOrientation

end TauCeti

namespace SymplecticGeometry

section

variable [IsManifold 𝓘(ℂ, E) 1 M]

open scoped VectorBundle.ComplexToReal

/-- **The Euler class of the tangent bundle of a complex manifold.** For `finrank ℂ E = r + 1`, the
Euler class of the complex tangent bundle, `complexEulerClass`, is the Euler class of the real
tangent bundle oriented by the canonical orientation `complexManifoldOrientation E M`, reindexed
along `2 * finrank ℂ E = 2 r + 2` (`complexManifoldOrientationOfFinrank E M hE`). -/
theorem complexEulerClass_tangentSpace {r : ℕ} (hE : finrank ℂ E = r + 1) :
    complexEulerClass E (TangentSpace 𝓘(ℂ, E) : M → Type) hE =
      (complexManifoldOrientationOfFinrank E M hE).toVectorBundleOrientation.eulerClass
        (finrank_real_of_finrank_complex_eq_add_one hE) := by
  -- On total spaces the fibrewise identification is the inverse of `restrictScalarsHomeomorph`.
  have hφ : Continuous fun v : TotalSpace E (TangentSpace 𝓘(ℝ, E) : M → Type) ↦
      TotalSpace.mk' E v.proj ((tangentSpaceCastModel 𝓘(ℝ, E) v.proj).trans
        ((tangentSpaceCastModel 𝓘(ℂ, E) v.proj).restrictScalars ℝ).symm v.snd) := by
    refine (TangentBundle.restrictScalarsHomeomorph ℝ (𝕜' := ℂ) M).symm.continuous.congr ?_
    rintro ⟨x, v⟩
    rw [TangentBundle.restrictScalarsHomeomorph_symm_apply]
    -- Both sides are `⟨x, v⟩`: the two casts are the identity of `E` by definition.
    rfl
  rw [complexEulerClass_def, complexManifoldOrientationOfFinrank_def]
  refine (VectorBundleOrientation.eulerClass_eq_of_fiberwise _ _ _ _
    (φ := fun x ↦ (tangentSpaceCastModel 𝓘(ℝ, E) x).trans
      ((tangentSpaceCastModel 𝓘(ℂ, E) x).restrictScalars ℝ).symm)
    hφ fun x ↦ ?_).symm
  rw [Manifold.Orientation.toVectorBundleOrientation_apply,
    Manifold.Orientation.orientationAt_reindex, VectorBundleOrientation.reindex_apply,
    Orientation.map_reindex,
    map_orientationAt_complexManifoldOrientation_eq_complex]

end

variable [CompactSpace M] [T2Space M] [IsManifold 𝓘(ℂ, E) ∞ M] [FiniteCWType M]

/-- **The top Chern number of a compact complex manifold is its Euler characteristic.** Let `M` be
a compact Hausdorff smooth complex manifold modelled on `𝓘(ℂ, E)`, of complex dimension
`finrank ℂ E = r + 1`, oriented by its complex structure
(`complexManifoldHomologicalOrientation E M hE`). Then the top Chern class `c_{r+1}(TM)` evaluated
on the fundamental class of `M` (`complexManifoldEvalFundamentalClass E M hE`) is the Euler
characteristic `TauCeti.eulerChar M`. A finite CW type of `M`, which `eulerChar` needs, is given
by `TauCeti.ComplexManifold.finiteCWType`. -/
theorem evalFundamentalClass_chernClass_eq_eulerChar {r : ℕ} (hE : finrank ℂ E = r + 1) :
    complexManifoldEvalFundamentalClass E M hE
        (Bundle.chernClass E (TangentSpace 𝓘(ℂ, E) : M → Type) (r + 1)) =
      eulerChar M := by
  rw [complexManifoldEvalFundamentalClass_def, complexManifoldHomologicalOrientation_def,
    Bundle.chernClass_finrank_eq_complexEulerClass hE,
    HomologicalOrientation.evalFundamentalClass_uliftIntegralCohomologyIso_hom,
    complexEulerClass_tangentSpace hE,
    Manifold.Orientation.evalFundamentalClass_eulerClass_eq_eulerChar_of_finiteCWType]

end SymplecticGeometry

end
