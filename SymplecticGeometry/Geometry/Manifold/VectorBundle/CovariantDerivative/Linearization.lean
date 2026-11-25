/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.FirstJet.Connection
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Linearization

/-!
# Covariant derivatives at a zero of a section

Let `σ` be a section of a `C^1` vector bundle `V → M` of finite rank, differentiable at a zero
`x`. Its intrinsic linearization `TauCeti.sectionLinearization I id σ x : TₓM → Vₓ` is defined
without any connection, by differentiating `σ` in a trivialization. This file shows that every
covariant derivative `∇` computes it: `∇σ(x)` is this linearization.

The proof goes through first jets: at a zero, the first jet `j¹σ(x)` is the jet of its
linearization under the inclusion `Hom(TₓM, Vₓ) → J¹Vₓ`, and Tau Ceti's splitting
`TauCeti.FirstJetBundle.covariantDerivative` of the first-jet sequence by `∇` sends `j¹σ(x)` to
`∇σ(x)` and is a left inverse of that inclusion.

## Main results

* `TauCeti.FirstJetBundle.jet_eq_ofDeriv_sectionLinearization`: at a zero, the first jet of a
  section is the jet of its linearization.
* `IsCovariantDerivativeOn.apply_eq_sectionLinearization`: a covariant derivative on a set
  containing a zero `x` of a section differentiable at `x` sends it to its linearization at `x`;
  `CovariantDerivative.apply_eq_sectionLinearization` is the case of a global covariant
  derivative.

## References

* [D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*][McDuffSalamon2012],
  Appendix A.3 (the linearization of a section at a zero).
-/

public section

open Bundle
open scoped Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul 𝕜 (V x)] [FiberBundle F V] [VectorBundle 𝕜 F V] [FiniteDimensional 𝕜 F]
  [IsManifold I 1 M] [ContMDiffVectorBundle 1 F V I] {σ : Π x : M, V x} {x : M}

namespace TauCeti.FirstJetBundle

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] in
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


namespace IsCovariantDerivativeOn

/-- **Covariant derivatives at a zero are the linearization.** If `cov` is a covariant derivative
on a set `u` containing a zero `x` of a section `σ` differentiable at `x`, then `cov σ x` is the
intrinsic linearization of `σ` at `x`. -/
theorem apply_eq_sectionLinearization
    {cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)} {u : Set M}
    (hcov : IsCovariantDerivativeOn F cov u) (hx : x ∈ u) (hσ : MDiffAt (T% σ) x)
    (hzero : σ x = 0) :
    cov σ x = TauCeti.sectionLinearization (F := F) I id σ x := by
  rw [← TauCeti.FirstJetBundle.covariantDerivative_jet hcov hx hσ,
    TauCeti.FirstJetBundle.jet_eq_ofDeriv_sectionLinearization hzero,
    TauCeti.FirstJetBundle.covariantDerivative_ofDeriv]

end IsCovariantDerivativeOn

namespace CovariantDerivative

/-- **A covariant derivative at a zero is the linearization.** At a zero `x` of a section `σ`
differentiable at `x`, the covariant derivative `cov σ x` is the intrinsic linearization of `σ`
at `x`. -/
theorem apply_eq_sectionLinearization (cov : CovariantDerivative I F V)
    (hσ : MDiffAt (T% σ) x) (hzero : σ x = 0) :
    cov σ x = TauCeti.sectionLinearization (F := F) I id σ x :=
  cov.isCovariantDerivativeOn.apply_eq_sectionLinearization (Set.mem_univ x) hσ hzero

end CovariantDerivative
