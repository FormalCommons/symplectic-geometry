/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Pullback

/-!
# Pulling back the almost complex structure of a complex manifold

Let `φ : M → N` be a smooth diffeomorphism of the real manifolds underlying two complex manifolds,
and let `i` denote their almost complex structures `ofComplexManifold`. The pull-back `φ^* i` is
`i` exactly when `φ` is holomorphic
(`TauCeti.SmoothAlmostComplexStructure.pullback_ofComplexManifold_eq_iff`); then its inverse is
holomorphic too (`TauCeti.SmoothAlmostComplexStructure.mdifferentiable_symm_of_pullback_eq`), since
the inverse of a diffeomorphism pulling `J` back to `K` pulls `K` back to `J`
(`TauCeti.SmoothAlmostComplexStructure.pullback_symm_eq_of_pullback_eq`).

Both directions come from Tau Ceti: a diffeomorphism is pseudoholomorphic from `φ^* i` to `i`
(`isPseudoholomorphic_pullback`), the pseudoholomorphic maps between complex manifolds are the
holomorphic ones (`isPseudoholomorphic_ofComplexManifold_iff`), and `φ^* i` is characterized by
the commutation of the differentials of `φ` with the structures (`eq_pullback_iff`).

## References

* [D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*][McDuffSalamon2012]
-/

public section

open scoped Manifold ContDiff TauCeti.ComplexManifold

namespace TauCeti.SmoothAlmostComplexStructure

section Inverse

variable {E H M E' H' N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' ∞ N]

/-- If a diffeomorphism `φ` pulls `J` back to `K`, then its inverse pulls `K` back to `J`. -/
theorem pullback_symm_eq_of_pullback_eq (φ : M ≃ₘ⟮I, I'⟯ N) {J : SmoothAlmostComplexStructure I' N}
    {K : SmoothAlmostComplexStructure I M} (h : J.pullback φ = K) : K.pullback φ.symm = J := by
  rw [← h, ← pullback_trans, Diffeomorph.symm_trans_self, pullback_refl]

end Inverse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] [FiniteDimensional ℝ E']
  {N : Type*} [TopologicalSpace N] [ChartedSpace E' N] [IsManifold 𝓘(ℂ, E') ∞ N]

/-- A smooth diffeomorphism between the real manifolds underlying two complex manifolds pulls the
almost complex structure of the target back to that of the source exactly when it is
holomorphic. -/
theorem pullback_ofComplexManifold_eq_iff (φ : M ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, E')⟯ N) :
    (ofComplexManifold E' N).pullback φ = ofComplexManifold E M ↔
      MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, E') φ := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hφ := isPseudoholomorphic_pullback φ (ofComplexManifold E' N)
    rw [h] at hφ
    exact isPseudoholomorphic_ofComplexManifold_iff.1 hφ
  · exact ((eq_pullback_iff φ _).2 fun x v ↦ (h x).mfderiv_ofComplexManifold_apply v).symm

/-- If a smooth diffeomorphism between the real manifolds underlying two complex manifolds pulls
the almost complex structure of the target back to that of the source, then its inverse is
holomorphic. -/
theorem mdifferentiable_symm_of_pullback_eq (φ : M ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, E')⟯ N)
    (h : (ofComplexManifold E' N).pullback φ = ofComplexManifold E M) :
    MDifferentiable 𝓘(ℂ, E') 𝓘(ℂ, E) φ.symm :=
  (pullback_ofComplexManifold_eq_iff φ.symm).1 (pullback_symm_eq_of_pullback_eq φ h)

end TauCeti.SmoothAlmostComplexStructure

end
