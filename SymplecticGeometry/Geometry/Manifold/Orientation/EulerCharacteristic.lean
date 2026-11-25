/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.OrientedChart
public import SymplecticGeometry.Topology.VectorBundle.Orientation.SectionIndex.Derivative
public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Manifold
public import TauCeti.Geometry.Manifold.Morse.Generic.Basic
public import TauCeti.Geometry.Manifold.Morse.PoincareHopf
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Existence
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# The Euler class of the tangent bundle and the Euler characteristic

Let `M` be a Hausdorff boundaryless `C¹` manifold modelled on a real normed space `E` of dimension
`m + 1`, with an orientation `o`. The orientation makes the tangent bundle an oriented vector
bundle (`o.toVectorBundleOrientation`) and `M` a homologically oriented manifold
(`o.toHomologicalOrientation`), so a continuous vector field has a local index at each isolated
zero, Tau Ceti's `TauCeti.VectorBundleOrientation.sectionIndex`.

* `Manifold.Orientation.sectionIndex_eq_sign_det_vectorFieldChartDerivative_of_mdifferentiableAt`:
  at a zero `z` of a vector field `X` differentiable at `z`, where the chart derivative
  `TauCeti.vectorFieldChartDerivative I X z` is invertible, the local index of `X` is the sign of
  the determinant of the chart derivative.
* `TauCeti.Manifold.Orientation.evalFundamentalClass_eulerClass_eq_sum_finrank_singularHomology`:
  for `M` compact and smooth, the Euler class of the tangent bundle evaluated on the fundamental
  class is `∑ᵢ (-1)ⁱ dim Hᵢ(M; k)` over any division ring `k`, the sum running over `i ≤ m + 1`.
* `TauCeti.Manifold.Orientation.evalFundamentalClass_eulerClass_eq_eulerChar_of_finiteCWType`: the
  same number is the Euler characteristic `TauCeti.eulerChar M`.

Tau Ceti proves the first and last of these, without the suffixes, for the model `𝓘(ℝ, X)` of an
inner product space `X`, without the differentiability hypothesis or `TauCeti.FiniteCWType M`;
the versions here hold for any boundaryless model `I`.

Odd dimensions are included: then both sides vanish, which the statements do not need to say.

## Proof

For the local index, Tau Ceti's
`TauCeti.VectorBundleOrientation.sectionIndex_eq_sign_det_of_hasFDerivAt` computes it as the sign
of the derivative of the section read in a trivialization and a chart; its form
`TauCeti.VectorBundleOrientation.sectionIndex_eq_sign_det_of_hasFDerivAt_of_eventually`, from
`SymplecticGeometry/Topology/VectorBundle/Orientation/SectionIndex/Derivative.lean`, finds the
neighbourhood in which `z` is the only zero itself. We take the trivialization
of the tangent bundle at `z` and the chart at `z` followed by the model embedding, in which `X`
reads as its coordinate field
(`VectorField.trivializationAt_snd_eventuallyEq_mpullbackWithin_extChartAt_symm`), so that the
derivative is the chart derivative. The chart hypothesis of that theorem is
`TauCeti.Manifold.Orientation.localHomologyMap_sub_toHomologicalOrientation`, from
`SymplecticGeometry/AlgebraicTopology/Singular/LocalHomology/OrientedChart.lean`. The overall
shape of the argument follows `SymplecticGeometry.Bundle.chernNumber_eq_sum_sign_of_transverse`.

For the Euler number, take a Morse function `f` (`TauCeti.exists_isMorse`) and a `C¹` Riemannian
metric (`TauCeti.nonempty_contMDiffRiemannianMetric`). Adding up the local indices of the
gradient of `f` over its zeros gives the Euler number
(`TauCeti.VectorBundleOrientation.evalFundamentalClass_eulerClass_eq_sum_sectionIndex`), each is the
sign of the determinant of its chart derivative by the first theorem, and Tau Ceti's Poincaré–Hopf
theorem for gradients of Morse functions
(`TauCeti.IsMorse.finsum_sign_det_vectorFieldChartDerivative_mgradient`) sums these signs to the
alternating sum of the Betti numbers. Euler–Poincaré
(`TauCeti.eulerChar_eq_sum_range_finrank_singularHomology`) gives the Euler characteristic.

## References

* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia (1965),
  §6 (the index of a zero of a vector field, and the Poincaré–Hopf theorem).
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §11 (the Euler class of the tangent bundle evaluated on the fundamental class
  is the Euler characteristic).
* [R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §11.
-/

public section

open Bundle CategoryTheory Module Set Filter TauCeti AlgebraicTopology
open scoped ContDiff Manifold Topology

namespace TauCeti.Manifold.Orientation

variable {E H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [ChartedSpace E M]
  {m : ℕ} (hE : finrank ℝ E = m + 1) (o : Manifold.Orientation I M (Fin (m + 1)))

section Index

variable [IsManifold I 1 M]

/-- **The local index of a nondegenerate zero of a vector field.** Let `X` be a continuous vector
field on `M`, differentiable at a zero `z` whose chart derivative
`vectorFieldChartDerivative I X z` has nonzero determinant. Then the local index of `X` at `z`, as
a section of the tangent bundle oriented by `o`, with the homological orientation of `M` given by
`o`, is the sign of that determinant. -/
theorem sectionIndex_eq_sign_det_vectorFieldChartDerivative_of_mdifferentiableAt
    {X : (x : M) → TangentSpace I x}
    (hX : Continuous fun x ↦ TotalSpace.mk' E x (X x)) {z : M}
    (hXz : MDifferentiableAt I I.tangent (fun y ↦ (X y : TangentBundle I M)) z) (hz : X z = 0)
    (hdet : LinearMap.det (vectorFieldChartDerivative I X z) ≠ 0) :
    o.toVectorBundleOrientation.sectionIndex hE (o.toHomologicalOrientation hE) hX z =
      SignType.sign (LinearMap.det (vectorFieldChartDerivative I X z)) := by
  set e := trivializationAt E (TangentSpace I) z
  have hze : z ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' z
  set φ : OpenPartialHomeomorph M E := (chartAt H z).transHomeomorph I.toHomeomorph
  have hzφ : z ∈ φ.source := by simp [φ]
  have hφz : φ z = extChartAt I z z := by simp [φ]
  -- The derivative `A` of the coordinate field of `X` in the chart at `z`.
  set A : E →L[ℝ] E := fderiv ℝ (VectorField.mpullback 𝓘(ℝ, E) I (extChartAt I z).symm X)
    (extChartAt I z z)
  have hdetA : A.det = LinearMap.det (vectorFieldChartDerivative I X z) := by
    rw [vectorFieldChartDerivative_def]
  -- The section read in `e` and `φ` is the coordinate field near `φ z`.
  set f : E → E := fun y ↦ (e (TotalSpace.mk' E (φ.symm y) (X (φ.symm y)))).2 with hf
  have hfeq : f =ᶠ[𝓝 (φ z)] VectorField.mpullback 𝓘(ℝ, E) I (extChartAt I z).symm X := by
    have h := VectorField.trivializationAt_snd_eventuallyEq_mpullbackWithin_extChartAt_symm X z
    rw [I.range_eq_univ, nhdsWithin_univ, VectorField.mpullbackWithin_univ] at h
    rw [hφz]
    filter_upwards [h] with y hy
    have hφs : φ.symm y = (extChartAt I z).symm y := by simp [φ, extChartAt]
    simp only [hf]
    rw [hφs]
    exact hy
  have hA : HasFDerivAt f A (φ z) := by
    have hU := hXz.differentiableAt_mpullbackWithin_extChartAt_symm
    rw [I.range_eq_univ, VectorField.mpullbackWithin_univ] at hU
    rw [hφz] at hfeq ⊢
    exact hU.hasFDerivAt.congr_of_eventuallyEq hfeq
  rw [VectorBundleOrientation.sectionIndex_eq_sign_det_of_hasFDerivAt_of_eventually
    o.toVectorBundleOrientation hE (o.toHomologicalOrientation hE) hX e φ hz hze hzφ
    (o.toVectorBundleOrientation.eventually_mapOrientation_eq o.card_eq e hze)
    (localHomologyMap_sub_toHomologicalOrientation hE o z) hA (hdetA ▸ hdet), hdetA]

end Index

section Euler

variable [CompactSpace M] [IsManifold I ∞ M]

/-- **The Euler number of the tangent bundle is the alternating sum of the Betti numbers.** On a
compact boundaryless smooth manifold `M` of dimension `m + 1` with an orientation `o`, the Euler
class of the tangent bundle, oriented by `o`, evaluated on the fundamental class of `M` given by
`o`, is `∑ᵢ (-1)ⁱ dim Hᵢ(M; k)`, for singular homology with coefficients in any division ring
`k`. -/
theorem evalFundamentalClass_eulerClass_eq_sum_finrank_singularHomology (k : Type)
    [DivisionRing k] :
    ((o.toHomologicalOrientation hE).evalFundamentalClass hE (ModuleCat.of ℤ (ULift.{0} ℤ))
      (ContinuousMap.id M) (o.toVectorBundleOrientation.eulerClass hE)).down =
      ∑ i ∈ Finset.range (m + 2), (-1 : ℤ) ^ i *
        finrank k (((singularHomologyFunctor (ModuleCat.{0} k) i).obj (ModuleCat.of k k)).obj
          (TopCat.of M)) := by
  -- A Morse function `f` and a `C¹` metric, and the gradient `X` of `f`.
  obtain ⟨f, hf⟩ := exists_isMorse (I := I) (M := M)
  obtain ⟨g⟩ := nonempty_contMDiffRiemannianMetric (IB := I) (n := 1) (F := E)
    (E := fun x : M ↦ TangentSpace I x)
  let : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
    Bundle.instIsContMDiffRiemannianBundle g
  have hf2 : ContMDiff I 𝓘(ℝ) 2 f := hf.contMDiff.of_le (by norm_num)
  have hXd := Manifold.mdifferentiable_mgradient hf2
  have hX : Continuous fun x ↦ TotalSpace.mk' E x (Manifold.mgradient I f x) := hXd.continuous
  have hZ : {x | Manifold.mgradient I f x = 0}.Finite := by
    refine hf.finite_criticalPoints.subset fun x hx ↦ ?_
    rw [mem_criticalPoints, ← Manifold.mgradient_eq_zero_iff]
    exact hx
  have hPH := hf.finsum_sign_det_vectorFieldChartDerivative_mgradient k
  rw [hE] at hPH
  rw [VectorBundleOrientation.evalFundamentalClass_eulerClass_eq_sum_sectionIndex _ hE _ hX hE hZ,
    ← finsum_mem_eq_finite_toFinset_sum _ hZ, ← finsum_set_coe_eq_finsum_mem]
  refine (finsum_congr fun x ↦ ?_).trans hPH
  exact sectionIndex_eq_sign_det_vectorFieldChartDerivative_of_mdifferentiableAt hE o hX (hXd x)
    x.property
    (hf.det_vectorFieldChartDerivative_mgradient_ne_zero x.property)

/-- **The Euler number of the tangent bundle is the Euler characteristic.** On a compact
boundaryless smooth manifold `M` of dimension `m + 1` with an orientation `o`, the Euler class of
the tangent bundle, oriented by `o`, evaluated on the fundamental class of `M` given by `o`, is the
Euler characteristic `TauCeti.eulerChar M`. The finite CW type of `M` that `eulerChar` needs is
always available, as `TauCeti.FiniteCWType.of_isManifold`. -/
theorem evalFundamentalClass_eulerClass_eq_eulerChar_of_finiteCWType [FiniteCWType M] :
    ((o.toHomologicalOrientation hE).evalFundamentalClass hE (ModuleCat.of ℤ (ULift.{0} ℤ))
      (ContinuousMap.id M) (o.toVectorBundleOrientation.eulerClass hE)).down = eulerChar M := by
  rw [evalFundamentalClass_eulerClass_eq_sum_finrank_singularHomology hE o ℚ,
    eulerChar_eq_sum_range_finrank_singularHomology (E := E) M ℚ, hE]

end Euler

end TauCeti.Manifold.Orientation
