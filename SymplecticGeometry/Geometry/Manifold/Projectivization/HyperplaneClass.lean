/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Complex.HomologicalOrientation
public import SymplecticGeometry.Topology.VectorBundle.Complex.ChernClass.ProjectiveSpace
public import TauCeti.Geometry.Manifold.Instances.Projectivization

import SymplecticGeometry.Geometry.Manifold.Projectivization.TwistCore
import SymplecticGeometry.Topology.VectorBundle.Orientation.Complex.Tensor
import SymplecticGeometry.Topology.VectorBundle.Orientation.SectionIndex.ComplexLinear
import TauCeti.Geometry.Manifold.Projectivization.LineBundle

/-!
# The hyperplane class evaluates to one on a projective line

Let `h ∈ H²(ℙ ℂ W; ℤ)` be the hyperplane class (`Projectivization.hyperplaneClass`). This file
proves that `h` pulled back to a projective line `ℙ ℂ (Fin 2 → ℂ) → ℙ ℂ W`, induced by an injective
linear map `ℂ² → W`, pairs to `1` with the fundamental class of the line for its complex
orientation (`SymplecticGeometry.complexManifoldEvalFundamentalClass`). With
`Projectivization.bijective_zsmul_hyperplaneClass_pow` this says that `h` is the positive
generator of `H²(ℂℙᵐ; ℤ)` for the complex orientation.

## Main results

* `Projectivization.complexManifoldEvalFundamentalClass_hyperplaneClass`: `⟨h, [ℂℙ¹]⟩ = 1`.
* `Projectivization.complexManifoldEvalFundamentalClass_map_hyperplaneClass`: the same for the
  pull-back of the hyperplane class of `ℙ ℂ W` along the map induced by an injective linear map
  `ℂ² → W`.

## Proof

By `Projectivization.hyperplaneClass_map` the pull-back of `h` along a linear embedding of
projective spaces is `h`, so it suffices to treat `ℂℙ¹` itself. There `h` is the Euler class of
`𝒪(1)` (`Projectivization.complexEulerClass_twistCore_one`). The linear form `v ↦ v 0` is a
section of `𝒪(1)` (Tau Ceti's `Projectivization.homogeneousSection`), whose only zero is the point
`[0 : 1]`. In the standard chart at that point, which is also the chart of the preferred
trivialization of `𝒪(1)` there, the section reads `y ↦ y 0`, a complex-linear isomorphism
`ℂ¹ → ℂ`; so its index there is `1` (`SymplecticGeometry.sectionIndex_eq_one_of_complexLinear`).
`SymplecticGeometry.complexManifoldEvalFundamentalClass_complexEulerClass_eq_sum_sectionIndex`,
a form of Tau Ceti's
`TauCeti.VectorBundleOrientation.evalFundamentalClass_eulerClass_eq_sum_sectionIndex`, then gives
`⟨h, [ℂℙ¹]⟩ = 1`. This is the argument of
`SymplecticGeometry.SmoothProjectiveHypersurface.evalFundamentalClass_hyperplaneClass_pow` for a
single linear form on the projective line.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §11 (the Euler class as a sum of indices of a section) and §14 (the
  cohomology of complex projective space).
* [P. Griffiths and J. Harris, *Principles of Algebraic Geometry*][GriffithsHarris1978],
  Chapter 1, §1 (sections of `𝒪(1)` given by linear forms).
-/

public section

open Bundle Module MvPolynomial SymplecticGeometry TauCeti
open scoped LinearAlgebra.Projectivization Manifold VectorBundle.ComplexToReal

namespace Projectivization

/-- The point `[0 : 1]` of the projective line, the zero of the linear form `v ↦ v 0`. -/
private noncomputable abbrev pointAtInfinity : ℙ ℂ (Fin 2 → ℂ) :=
  mk ℂ (Pi.single 1 1) (by simp)

/-- The section `v ↦ v 0` of `𝒪(1)` vanishes exactly at `[0 : 1]`. -/
private theorem homogeneousSection_X_zero_eq_zero_iff (x : ℙ ℂ (Fin 2 → ℂ)) :
    homogeneousSection (𝕜 := ℂ) (n := 1) 1 (X 0) x = 0 ↔ x = pointAtInfinity := by
  induction x using ind with | h v hv =>
  rw [homogeneousSection_mk_eq_zero_iff (isHomogeneous_X ℂ 0), eval_X, mk_eq_mk_iff']
  constructor
  · intro h0
    refine ⟨v 1, funext fun i ↦ ?_⟩
    fin_cases i <;> simp [h0]
  · rintro ⟨a, rfl⟩
    simp

/-- **The hyperplane class evaluates to one on the projective line.** The hyperplane class of
`ℂℙ¹ = ℙ ℂ (Fin 2 → ℂ)`, evaluated on the fundamental class of `ℂℙ¹` for its complex orientation,
is `1`. -/
theorem complexManifoldEvalFundamentalClass_hyperplaneClass :
    complexManifoldEvalFundamentalClass (Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ)) (finrank_fin_fun ℂ)
      (hyperplaneClass (Fin 2 → ℂ)) = 1 := by
  set s : ∀ x, (twistCore (𝕜 := ℂ) (n := 1) 1).Fiber x :=
    homogeneousSection (𝕜 := ℂ) (n := 1) 1 (X 0)
  have hs : Continuous fun x ↦ TotalSpace.mk' ℂ x (s x) := by
    have h := contMDiff_homogeneousSection (𝕜 := ℂ) (n := 1) (isHomogeneous_X ℂ 0) 0
    rw [Nat.cast_one] at h
    exact h.continuous
  have hZ : {x | s x = 0} = {pointAtInfinity} :=
    Set.ext homogeneousSection_X_zero_eq_zero_iff
  have hfin : {x | s x = 0}.Finite := hZ ▸ Set.finite_singleton _
  rw [← complexEulerClass_twistCore_one (n := 1),
    complexManifoldEvalFundamentalClass_complexEulerClass_eq_sum_sectionIndex _ _ hs hfin]
  rw [show hfin.toFinset = {pointAtInfinity} by simp [hZ], Finset.sum_singleton]
  -- At `[0 : 1]` the section reads `y ↦ y 0`, a complex-linear isomorphism, so its index is `1`.
  have hA : HasFDerivAt (fun y ↦ (trivializationAt ℂ (twistCore (𝕜 := ℂ) (n := 1) 1).Fiber
      pointAtInfinity ⟨(chartAt (Fin 1 → ℂ) pointAtInfinity).symm y,
        s ((chartAt (Fin 1 → ℂ) pointAtInfinity).symm y)⟩).2)
      (((ContinuousLinearEquiv.funUnique (Fin 1) ℂ ℂ : (Fin 1 → ℂ) ≃L[ℂ] ℂ) :
        (Fin 1 → ℂ) →L[ℂ] ℂ).restrictScalars ℝ)
      (chartAt (Fin 1 → ℂ) pointAtInfinity pointAtInfinity) := by
    convert ContinuousLinearMap.hasFDerivAt _ using 1
    funext y
    rw [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.coe_funUnique, Function.eval, Fin.default_eq_zero]
    have h := trivializationAt_homogeneousSection_chartAt_symm (isHomogeneous_X ℂ 0)
      pointAtInfinity y
    rw [Nat.cast_one] at h
    rw [h, twistCore_indexAt_mk_single]
    simp
  exact sectionIndex_eq_one_of_complexLinear (finrank_fin_fun ℂ) hs
    ((homogeneousSection_X_zero_eq_zero_iff _).2 rfl) _
    (mem_baseSet_trivializationAt _ _ _) _ hA

/-- **Normalization of the hyperplane class.** For an injective linear map
`ι : ℂ² → W`, the pull-back of the hyperplane class of `ℙ ℂ W` along the induced map
`ℂℙ¹ → ℙ ℂ W`, evaluated on the fundamental class of `ℂℙ¹` for its complex orientation, is `1`.

Milestone: *First Chern class of a complex vector bundle*. -/
theorem complexManifoldEvalFundamentalClass_map_hyperplaneClass {W : Type}
    [NormedAddCommGroup W] [NormedSpace ℂ W] (ι : (Fin 2 → ℂ) →ₗ[ℂ] W)
    (hι : Function.Injective ι) :
    complexManifoldEvalFundamentalClass (Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ)) (finrank_fin_fun ℂ)
      (TopCat.singularCohomologyMap
        (TopCat.ofHom (mapContinuousMap ι hι))
        2 (hyperplaneClass W)) = 1 := by
  rw [hyperplaneClass_map]
  exact complexManifoldEvalFundamentalClass_hyperplaneClass

end Projectivization

end
