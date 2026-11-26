/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.DegreeOne
public import TauCeti.Geometry.Manifold.Distribution
import SymplecticGeometry.Geometry.Manifold.Distribution.VectorBundle
import TauCeti.Geometry.Manifold.VectorBundle.ConstantRank

/-!
# The kernels of a surjective vector-valued one-form

Let `α` be a smooth one-form on a finite-dimensional manifold `M` with values in a real normed
space `F`. Through Tau Ceti's `TauCeti.SmoothForm.degreeOneEquiv`, `α` is a smooth section of the
bundle of linear maps from the tangent bundle to the trivial bundle with fibre `F`. If `α_x` is
onto `F` at every point, then `F` is finite-dimensional and this bundle map has constant rank
`dim F`, so its kernels have smooth local frames (Tau Ceti's
`TauCeti.hasLocalContMDiffSubbundleFrames_ker_of_surjective`), and by
`TauCeti.HasLocalContMDiffSubbundleFrames.isContMDiffDistribution` (in
`SymplecticGeometry.Geometry.Manifold.Distribution.VectorBundle`) they form a smooth
distribution of rank `dim M - dim F`
(`TauCeti.SmoothForm.isContMDiffDistribution_ker_degreeOneEquiv`).

For `F = ℝ` this is Tau Ceti's `TauCeti.SmoothForm.isContMDiffDistribution_kerDistribution`, on
the kernels of a nowhere vanishing real one-form, which Tau Ceti proves by writing down a frame.
The kernels of a connection form on a principal bundle, with values in the Lie algebra of the
structure group, are an instance with `F` of any dimension.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Theorem 10.34 (kernels of constant-rank bundle maps).
-/

public section

noncomputable section

open Bundle Function Module
open scoped ContDiff Manifold

namespace TauCeti.SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **The kernels of a surjective one-form are a smooth distribution.** If a smooth one-form `α`
with values in `F` is onto `F` at every point, then its kernels form a `C^n` distribution of rank
`dim M - dim F`, for every `n ≤ ∞`. -/
theorem isContMDiffDistribution_ker_degreeOneEquiv {n : ℕ∞ω} [ENat.LEInfty n]
    [IsManifold I 1 M] [IsManifold I (n + 1) M] (α : SmoothForm I M F 1)
    (hα : ∀ x, Surjective (degreeOneEquiv α x)) :
    IsContMDiffDistribution I n (finrank ℝ E - finrank ℝ F)
      fun x ↦ (degreeOneEquiv α x).ker := by
  let : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  exact (hasLocalContMDiffSubbundleFrames_ker_of_surjective (E₂ := Trivial M F)
    ((degreeOneEquiv α).contMDiff.of_le ENat.LEInfty.out) hα).isContMDiffDistribution

end TauCeti.SmoothForm
