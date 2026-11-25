/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.ZeroOneForm
import TauCeti.Geometry.Manifold.VectorBundle.Hom

/-!
# The `(0,1)`-projection as a smooth section of a hom bundle

For an almost complex structure `j` on `M` and a complex vector bundle `V → M`, Tau Ceti's
`TauCeti.SmoothAlmostComplexStructure.zeroOnePart` is, at every point `x`, a real-linear map of
the `V`-valued one-forms at `x` to themselves, and
`TauCeti.SmoothAlmostComplexStructure.contMDiff_totalSpace_zeroOnePart` says that it is a smooth
map of total spaces. This file bundles it at `x` as a continuous real-linear endomorphism
`TauCeti.SmoothAlmostComplexStructure.zeroOnePartL j x` of the one-forms at `x`, and shows that
these endomorphisms form a smooth section of the bundle of endomorphisms of the bundle of
`V`-valued one-forms (`TauCeti.SmoothAlmostComplexStructure.contMDiff_zeroOnePartL`), by Tau
Ceti's `TauCeti.contMDiff_hom_bundle_iff`. In this form the projection can act on Sobolev
sections of one-forms as a smooth coefficient.

## Main definitions and results

* `TauCeti.SmoothAlmostComplexStructure.zeroOnePartL`: the `(0,1)`-projection at a point.
* `TauCeti.SmoothAlmostComplexStructure.contMDiff_zeroOnePartL`: it is a smooth section of the
  endomorphism bundle of the one-forms.

## References

* [D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*][McDuffSalamon2012],
  Appendix C.1.
-/

public section

open Bundle
open scoped Manifold ContDiff

noncomputable section

namespace TauCeti.SmoothAlmostComplexStructure

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  (j : SmoothAlmostComplexStructure I M)
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [∀ x, IsScalarTower ℝ ℂ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [∀ x, ContinuousSMul ℂ (V x)]

/-- The `(0,1)`-projection `η ↦ ½ (η + i • η ∘ j)` of the `V`-valued one-forms at `x`, as a
continuous real-linear endomorphism. -/
def zeroOnePartL (x : M) :
    (TangentSpace I x →L[ℝ] V x) →L[ℝ] TangentSpace I x →L[ℝ] V x where
  toLinearMap := (j.zeroOnePartLinearMap x).restrictScalars ℝ
  cont := by
    refine ((continuous_const_smul (2⁻¹ : ℝ)).comp (continuous_id.add
      ((continuous_const_smul Complex.I).comp
        (ContinuousLinearMap.precomp (V x) (j.toEndomorphism x)).continuous))).congr
          fun η ↦ ?_
    ext v
    simp [zeroOnePart_apply]

/-- `zeroOnePartL j x` is the `(0,1)`-projection of one-forms at `x`. -/
@[simp]
theorem zeroOnePartL_apply (x : M) (η : TangentSpace I x →L[ℝ] V x) :
    j.zeroOnePartL x η = j.zeroOnePart η :=
  j.zeroOnePartLinearMap_apply x η

variable [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  [VectorBundle ℂ F V] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- The `(0,1)`-projections at the points of `M` form a `C^n` section of the bundle of
endomorphisms of the bundle of `V`-valued one-forms, for every `n ≤ ∞`. -/
theorem contMDiff_zeroOnePartL {n : ℕ∞ω} (hn : n ≤ ∞) :
    ContMDiff I (I.prod 𝓘(ℝ, (E →L[ℝ] F) →L[ℝ] E →L[ℝ] F)) n fun x ↦
      TotalSpace.mk' ((E →L[ℝ] F) →L[ℝ] E →L[ℝ] F)
        (E := fun x ↦ (TangentSpace I x →L[ℝ] V x) →L[ℝ] TangentSpace I x →L[ℝ] V x) x
        (j.zeroOnePartL x) :=
  (contMDiff_hom_bundle_iff _).2 (by
    simpa only [zeroOnePartL_apply] using j.contMDiff_totalSpace_zeroOnePart (F := F) (V := V) hn)

end TauCeti.SmoothAlmostComplexStructure
