/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.FirstJet.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Linearization

/-!
# The first jet of a section at a zero

At a zero `x` of a section `σ` of a `C^1` vector bundle `V → M`, the value part of the first jet
`j¹σ(x)` vanishes, so the jet lies in the image of the inclusion `Hom(TₓM, Vₓ) → J¹Vₓ`
(`TauCeti.FirstJetBundle.ofDeriv`). This file shows that it is the image of the intrinsic
linearization `TauCeti.sectionLinearization I id σ x` of `σ` at `x`. No differentiability of `σ`
is needed, since both sides are computed by the same derivative in the trivialization at `x`.

## Main results

* `TauCeti.FirstJetBundle.jet_eq_ofDeriv_sectionLinearization`: at a zero, the first jet of a
  section is the jet of its linearization.

## References

* [D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*][McDuffSalamon2012],
  Appendix A.3 (the linearization of a section at a zero).
-/

public section

open Bundle
open scoped Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul 𝕜 (V x)] [FiberBundle F V] [VectorBundle 𝕜 F V]
  [IsManifold I 1 M] [ContMDiffVectorBundle 1 F V I] {σ : Π x : M, V x} {x : M}

namespace TauCeti.FirstJetBundle

/-- At a zero `x` of a section `σ`, the first jet `j¹σ(x)` is the jet, under the inclusion
`Hom(TₓM, Vₓ) → J¹Vₓ`, of the linearization of `σ` at `x`. -/
theorem jet_eq_ofDeriv_sectionLinearization (hzero : σ x = 0) :
    jet I F σ x = ofDeriv I F x (sectionLinearization (F := F) I id σ x) := by
  have hx := mem_baseSet_trivializationAt F V x
  refine Prod.ext ?_ ?_
  · rw [jet_fst, ofDeriv_fst, hzero]
    exact congrArg Prod.snd ((trivializationAt F V x).zeroSection 𝕜 hx)
  · rw [ofDeriv_snd, jet_snd_eq_mvfderiv]
    ext v
    simp only [ContinuousLinearMap.comp_apply, sectionLinearization_def, id_eq,
      (trivializationAt F V x).continuousLinearMapAt_symmL hx]

end TauCeti.FirstJetBundle

end
