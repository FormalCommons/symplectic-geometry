/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Basic
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
public import TauCeti.Analysis.Matrix.Normed
public import SymplecticGeometry.Analysis.Complex.SiegelUpperHalfSpace.Basic
import SymplecticGeometry.LinearAlgebra.Matrix.Symmetric
import Mathlib.Analysis.LocallyConvex.HahnBanach
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import SymplecticGeometry.Geometry.Manifold.ContMDiff.Submodule

/-!
# The Siegel upper half space as a complex manifold

The Siegel upper half space `SiegelUpperHalfSpace ι` is an open subset of the complex symmetric
`ι × ι` matrices (`SiegelUpperHalfSpace.isOpenEmbedding_toSymm`), so it is a manifold with a
single chart, modelled on the complex vector space of symmetric matrices. The model is
Mathlib's submodule `selfAdjointMatricesSubmodule (1 : Matrix ι ι ℂ)` of the matrices that are
self-adjoint for the bilinear form of the identity, which are the symmetric matrices
(`Matrix.isSelfAdjoint_one_iff_isSymm`). The chart is the inclusion `toSymm`, followed by the
homeomorphism `Homeomorph.subtype` of the identity of matrices onto that submodule.

The model space carries the `L∞` operator norm of `Matrix.Norms.Operator`. The smooth structure
does not depend on that choice, but an instance must name one. The topology of that norm agrees
with Mathlib's topology on matrices only after unfolding instances, so, as in Tau Ceti's
`TauCeti/Geometry/Manifold/Instances/GeneralLinearGroup.lean`, the file selects Tau Ceti's
`Matrix.linftyOpTopologicalSpace` as a local instance. The manifold instances need no such
instance; to state `chartAt` or smoothness into the matrices, `open scoped Matrix.Norms.Operator`
and enable `attribute [local instance] Matrix.linftyOpTopologicalSpace`.

The model is a complex normed space, and the manifold structure is stated over every normed
field `𝕜` over which `ℂ` is a normed algebra, so the same atlas makes the Siegel upper half
space a real and a complex manifold, smooth and analytic.

## Main definitions and results

* The `ChartedSpace (selfAdjointMatricesSubmodule (1 : Matrix ι ι ℂ)) (SiegelUpperHalfSpace ι)`
  instance, whose single chart sends `Z` to the matrix `Z` (`chartAt_eq`, `coe_chartAt_apply`),
  and the instance `IsManifold 𝓘(𝕜, selfAdjointMatricesSubmodule (1 : Matrix ι ι ℂ)) n _`, for
  `𝕜 = ℂ` and `𝕜 = ℝ` alike and every order `n`.
* `SiegelUpperHalfSpace.contMDiff_coe`: the inclusion into the matrices is smooth, and
  `SiegelUpperHalfSpace.hasMFDerivAt_coe`: its differential is the inclusion of the model.
* `SiegelUpperHalfSpace.contMDiff_iff_coe_comp`: a map into the Siegel upper half space is smooth
  exactly when its matrix is.

The charted space and the `IsManifold` instance adapt Mathlib's instances `ChartedSpace ℂ ℍ`
and `IsManifold 𝓘(ℂ) ω ℍ` in `Mathlib/Analysis/Complex/UpperHalfPlane/Manifold.lean`, the case
of index one, and `contMDiff_coe` has the statement of Mathlib's `UpperHalfPlane.contMDiff_coe`.
The proof of `contMDiff_coe`, composing the smoothness of the continuous linear inclusion of the
model with that of the open embedding, adapts Tau Ceti's `Matrix.contMDiff_coe_posDefOpens` in
`TauCeti/Geometry/Manifold/Instances/PositiveDefiniteMatrix.lean`, as does the note above on
the scope to open and the local instance to enable. The local instance itself is chosen as in
the setup of Tau Ceti's `TauCeti/Geometry/Manifold/Instances/GeneralLinearGroup.lean`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.5
-/

public section

noncomputable section

open Matrix Topology
open scoped Manifold ContDiff Matrix.Norms.Operator

attribute [local instance] Matrix.linftyOpTopologicalSpace

namespace SymplecticGeometry

namespace SiegelUpperHalfSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The model space: the complex symmetric matrices, as Mathlib's submodule of matrices that are
self-adjoint for the bilinear form of the identity. -/
local notation "𝒮" ι => selfAdjointMatricesSubmodule (1 : Matrix ι ι ℂ)

/-- The open embedding that defines the charted space: `Z` as a symmetric matrix, in the
submodule `𝒮 ι`. -/
theorem isOpenEmbedding_subtype_comp_toSymm :
    IsOpenEmbedding ((Homeomorph.subtype (Homeomorph.refl (Matrix ι ι ℂ))
      fun _ ↦ by simp : {Z : Matrix ι ι ℂ // Z.IsSymm} ≃ₜ 𝒮 ι) ∘ toSymm) :=
  (Homeomorph.isOpenEmbedding _).comp isOpenEmbedding_toSymm

/-- The Siegel upper half space is a manifold with one chart, modelled on the complex symmetric
matrices: the chart sends a point to its matrix. -/
instance : ChartedSpace (𝒮 ι) (SiegelUpperHalfSpace ι) :=
  isOpenEmbedding_subtype_comp_toSymm.singletonChartedSpace

/-- The chart at any point sends a point `W` of the Siegel upper half space to its matrix. -/
theorem coe_chartAt_apply (Z W : SiegelUpperHalfSpace ι) :
    ((chartAt (𝒮 ι) Z W : 𝒮 ι) : Matrix ι ι ℂ) = W := by
  rw [isOpenEmbedding_subtype_comp_toSymm.singletonChartedSpace_chartAt_eq]
  simp

/-- The chart at any point sends `W` to its matrix, as an element of the model. -/
theorem chartAt_eq (Z : SiegelUpperHalfSpace ι) :
    ⇑(chartAt (𝒮 ι) Z) = fun W ↦ ⟨W, by simpa using W.isSymm⟩ :=
  funext fun W ↦ Subtype.ext (coe_chartAt_apply Z W)

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ]

/-- The Siegel upper half space is a manifold modelled on the symmetric matrices, over `ℂ` and
over `ℝ`, of every order of smoothness: its atlas has a single chart. -/
instance {n : ℕ∞ω} : IsManifold 𝓘(𝕜, 𝒮 ι) n (SiegelUpperHalfSpace ι) :=
  isOpenEmbedding_subtype_comp_toSymm.isManifold_singleton

/-- The inclusion of the Siegel upper half space into the matrices is smooth. -/
theorem contMDiff_coe {n : ℕ∞ω} :
    ContMDiff 𝓘(𝕜, 𝒮 ι) 𝓘(𝕜, Matrix ι ι ℂ) n ((↑) : SiegelUpperHalfSpace ι → Matrix ι ι ℂ) := by
  convert (((Submodule.subtypeL (𝒮 ι)).restrictScalars 𝕜).contDiff.contMDiff).comp
    (contMDiff_isOpenEmbedding (I := 𝓘(𝕜, 𝒮 ι)) (n := n) isOpenEmbedding_subtype_comp_toSymm)
    using 1
  funext Z
  simp

/-- The inclusion of the Siegel upper half space into the matrices has, at every point, the
inclusion of the symmetric matrices as its differential. -/
theorem hasMFDerivAt_coe (Z : SiegelUpperHalfSpace ι) :
    HasMFDerivAt 𝓘(𝕜, 𝒮 ι) 𝓘(𝕜, Matrix ι ι ℂ) ((↑) : SiegelUpperHalfSpace ι → Matrix ι ι ℂ) Z
      ((Submodule.subtypeL (𝒮 ι)).restrictScalars 𝕜) := by
  have hchart : HasMFDerivAt 𝓘(𝕜, 𝒮 ι) 𝓘(𝕜, 𝒮 ι) (chartAt (𝒮 ι) Z) Z
      (ContinuousLinearMap.id 𝕜 (𝒮 ι)) := by
    simpa using TauCeti.hasMFDerivAt_extChartAt_self (I := 𝓘(𝕜, 𝒮 ι)) Z
  have hfun : ((↑) : SiegelUpperHalfSpace ι → Matrix ι ι ℂ) =
      (Submodule.subtypeL (𝒮 ι)).restrictScalars 𝕜 ∘ chartAt (𝒮 ι) Z :=
    funext fun W ↦ (coe_chartAt_apply Z W).symm
  rw [hfun]
  exact ((Submodule.subtypeL (𝒮 ι)).restrictScalars 𝕜).hasMFDerivAt.comp Z hchart

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}

/-- A map into the Siegel upper half space is smooth exactly when its matrix is. -/
theorem contMDiff_iff_coe_comp {f : M → SiegelUpperHalfSpace ι} :
    ContMDiff I 𝓘(𝕜, 𝒮 ι) n f ↔
      ContMDiff I 𝓘(𝕜, Matrix ι ι ℂ) n fun x ↦ (f x : Matrix ι ι ℂ) := by
  refine ⟨contMDiff_coe.comp, fun hf ↦ ?_⟩
  refine ContMDiff.of_comp_isOpenEmbedding isOpenEmbedding_subtype_comp_toSymm ?_
  refine ((Submodule.ClosedComplemented.of_finiteDimensional (𝒮 ι)).contMDiff_iff_subtypeL_comp
    (𝕜 := 𝕜)).2 ?_
  convert hf using 2 with x
  simp

end SiegelUpperHalfSpace

end SymplecticGeometry

end
