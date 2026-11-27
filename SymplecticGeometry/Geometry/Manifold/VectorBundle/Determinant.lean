/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Basic
public import TauCeti.Topology.VectorBundle.Determinant
import Mathlib.Analysis.Normed.Operator.Mul
import SymplecticGeometry.Geometry.Manifold.VectorBundle.RestrictScalars
import SymplecticGeometry.Topology.VectorBundle.DetBundle.Trivialization
import TauCeti.Analysis.Calculus.FDeriv.Det.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Hom

/-!
# The determinant line of a smooth vector bundle is smooth

Let `𝕜'` be a complete normed field that is a normed algebra over the complete field `𝕜`, and let
`E` be a vector bundle over `𝕜'` with finite-dimensional model `G`, over a manifold `B` with a
model `I` over `𝕜`. Suppose that `E` is also a vector bundle over `𝕜`, with the same
trivializations, and that it is `C^n` over `𝕜`. The main case is a complex vector bundle over a
real manifold, with its real structure from `open scoped VectorBundle.ComplexToReal` (and the
finite dimension of `G` over `ℝ` from `FiniteDimensional.complexToReal`); the case `𝕜 = 𝕜'` is
that of a `C^n` vector bundle over `𝕜`.

This file shows that Tau Ceti's determinant line `TauCeti.DetBundle 𝕜' G E` is then a `C^n` line
bundle over `𝕜`. Its trivializations are induced by those of `E`
(`TauCeti.DetBundle.exists_eq_trivialization`), and its coordinate changes are multiplication by
the determinants over `𝕜'` of the coordinate changes of `E`
(`TauCeti.DetBundle.coordChangeL_trivialization`). The coordinate changes of `E` over `𝕜'` are
`C^n` over `𝕜` (`contMDiffOn_coordChangeL_of_restrictScalars`), and the determinant is a
polynomial, so it is `C^n` over `𝕜'` (`ContinuousLinearMap.contDiff_det`), hence over `𝕜`.

For a line bundle, Tau Ceti identifies the determinant line with the bundle itself
(`TauCeti.DetBundle.lineHomeomorph`). Read in the trivializations at a point, this identification
multiplies the coordinate by the vector of the basis `Module.finBasis 𝕜' G` of the model line
(`TauCeti.DetBundle.snd_apply_lineEquiv`), and its inverse takes the coordinate along that
vector. A fibrewise map that is a fixed continuous linear map in these trivializations is `C^n`
(`TauCeti.contMDiff_bundleMap_of_constant_coordinates`), so both are `C^n`. This needs no
smoothness of `E`.

## Main results

* `TauCeti.DetBundle.contMDiffVectorBundle`: the determinant line of a `C^n` vector bundle is a
  `C^n` vector bundle.
* `TauCeti.DetBundle.contMDiff_lineHomeomorph`, `TauCeti.DetBundle.contMDiff_lineHomeomorph_symm`:
  for a line bundle, the identification of its determinant line with itself is `C^n` in both
  directions.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton University Press, 1974, §3.
* D. Huybrechts, *Complex Geometry: An Introduction*, §2.2.
-/

public section

open Bundle Module
open scoped Manifold

namespace TauCeti.DetBundle

variable {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜]
  [NontriviallyNormedField 𝕜'] [CompleteSpace 𝕜'] [NormedAlgebra 𝕜 𝕜']
  {EB HB B : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] [TopologicalSpace HB]
  {I : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B] {n : WithTop ℕ∞}
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜' G] [NormedSpace 𝕜 G] [IsScalarTower 𝕜 𝕜' G]
  [FiniteDimensional 𝕜' G]
  {E : B → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜' (E x)]
  [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace G E)]
  [FiberBundle G E] [VectorBundle 𝕜' G E]

section Smooth

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 G] [∀ x, Module 𝕜 (E x)] [VectorBundle 𝕜 G E]
  [ContMDiffVectorBundle n G E I]
  [∀ x, Module 𝕜 (DetBundle 𝕜' G E x)] [VectorBundle 𝕜 𝕜' (DetBundle 𝕜' G E)]

/-- **The determinant line of a `C^n` vector bundle is a `C^n` line bundle.** For a vector bundle
`E` over `𝕜'` with finite-dimensional model, which is also a `C^n` vector bundle over `𝕜` with
the same trivializations, the coordinate changes of its determinant line, multiplication by the
determinants over `𝕜'` of those of `E`, are `C^n` over `𝕜`. For instance, the determinant line of
a smooth complex vector bundle over a real manifold is a smooth complex line bundle. -/
instance contMDiffVectorBundle : ContMDiffVectorBundle n 𝕜' (DetBundle 𝕜' G E) I where
  contMDiffOn_coordChangeL e e' _ _ := by
    obtain ⟨e₀, _, rfl⟩ := exists_eq_trivialization e
    obtain ⟨e₀', _, rfl⟩ := exists_eq_trivialization e'
    rw [trivialization_baseSet, trivialization_baseSet]
    have hdet : ContMDiffOn I 𝓘(𝕜, 𝕜') n
        (fun b ↦ (e₀.coordChangeL 𝕜' e₀' b : G →L[𝕜'] G).det)
        (e₀.baseSet ∩ e₀'.baseSet) :=
      (ContDiff.restrict_scalars 𝕜 ContinuousLinearMap.contDiff_det).contMDiff.comp_contMDiffOn
        (contMDiffOn_coordChangeL_of_restrictScalars e₀ e₀')
    refine ((ContinuousLinearMap.mul 𝕜 𝕜').contMDiff.comp_contMDiffOn hdet).congr fun b hb ↦ ?_
    ext c
    rw [Function.comp_apply, ContinuousLinearMap.mul_apply',
      ← coordChangeL_trivialization e₀ e₀' hb c,
      ← Trivialization.restrictScalars_coordChangeL 𝕜 𝕜', ContinuousLinearMap.coe_restrictScalars',
      ContinuousLinearEquiv.coe_coe]

end Smooth

section Line

/-- **The identification of a line bundle with its determinant line is `C^n`.** For a vector
bundle `L` whose model fibre is a line, the map `det L → L` of total spaces,
`TauCeti.DetBundle.lineHomeomorph`, is `C^n`. -/
theorem contMDiff_lineHomeomorph (hF : finrank 𝕜' G = 1) :
    ContMDiff (I.prod 𝓘(𝕜, 𝕜')) (I.prod 𝓘(𝕜, G)) n (lineHomeomorph (E := E) hF) := by
  have : Unique (Fin (finrank 𝕜' G)) := (finCongr hF).unique
  -- In trivializations, the map multiplies the coordinate by the basis vector of the model.
  let L : 𝕜' →L[𝕜] G :=
    ((ContinuousLinearMap.id 𝕜' 𝕜').smulRight (Module.finBasis 𝕜' G default)).restrictScalars 𝕜
  refine (TauCeti.contMDiff_bundleMap_of_constant_coordinates (IB := I) (n := n)
    (fun x ↦ lineEquiv (E := E) hF x) L fun a x hx v ↦ ?_).congr
      fun p ↦ by simp [lineHomeomorph_apply]
  rw [trivializationAt_eq, trivialization_baseSet, Set.inter_self] at hx
  rw [snd_apply_lineEquiv hF _ hx v default, trivializationAt_eq, trivialization_apply_mk _ hx]
  simp [L]

/-- **The identification of a line bundle with its determinant line is `C^n`.** For a vector
bundle `L` whose model fibre is a line, the inverse `L → det L` of
`TauCeti.DetBundle.lineHomeomorph` is `C^n`. -/
theorem contMDiff_lineHomeomorph_symm (hF : finrank 𝕜' G = 1) :
    ContMDiff (I.prod 𝓘(𝕜, G)) (I.prod 𝓘(𝕜, 𝕜')) n (lineHomeomorph (E := E) hF).symm := by
  have : Unique (Fin (finrank 𝕜' G)) := (finCongr hF).unique
  -- In trivializations, the map reads the coordinate of a vector along the basis of the model.
  let L : G →L[𝕜] 𝕜' :=
    (LinearMap.toContinuousLinearMap ((Module.finBasis 𝕜' G).coord default)).restrictScalars 𝕜
  refine (TauCeti.contMDiff_bundleMap_of_constant_coordinates (IB := I) (n := n)
    (fun x ↦ (lineEquiv (E := E) hF x).symm) L fun a x hx u ↦ ?_).congr
      fun p ↦ by simp [lineHomeomorph_symm_apply]
  rw [trivializationAt_eq, trivialization_baseSet, Set.inter_self] at hx
  have h := snd_apply_lineEquiv hF _ hx ((lineEquiv hF x).symm u) default
  rw [ContinuousLinearEquiv.apply_symm_apply] at h
  rw [h, trivializationAt_eq, trivialization_apply_mk _ hx]
  simp [L]

end Line

end TauCeti.DetBundle

end
