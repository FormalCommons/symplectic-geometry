/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Group
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Pullback

/-!
# Pulling back almost complex structures along inverses and in the diffeomorphism group

For a smooth diffeomorphism `φ : M → N`, an almost complex structure `J` on `N` and one `K` on
`M`, the inverse `φ⁻¹` pulls `K` back to `J` exactly when `φ` pulls `J` back to `K`
(`TauCeti.SmoothAlmostComplexStructure.pullback_symm_eq_iff`). This complements Tau Ceti's
`pullback_refl` and `pullback_trans`, from which it follows.

In the group `TauCeti.Diff I M ∞` of smooth self-diffeomorphisms, where `φ * ψ = ψ.trans φ`,
those two lemmas become `pullback_one` and `pullback_mul`: pulling back is a right action. The
group form of `pullback_symm_eq_iff` is `pullback_inv_eq_iff`.

## References

* [D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*][McDuffSalamon2012]
-/

public section

open scoped Manifold ContDiff

namespace TauCeti.SmoothAlmostComplexStructure

variable {E H M E' H' N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' ∞ N]

/-- The inverse of a diffeomorphism `φ` pulls `K` back to `J` exactly when `φ` pulls `J` back
to `K`. -/
theorem pullback_symm_eq_iff (φ : M ≃ₘ⟮I, I'⟯ N) {J : SmoothAlmostComplexStructure I' N}
    {K : SmoothAlmostComplexStructure I M} : K.pullback φ.symm = J ↔ J.pullback φ = K := by
  constructor <;> rintro rfl
  · rw [← pullback_trans, Diffeomorph.self_trans_symm, pullback_refl]
  · rw [← pullback_trans, Diffeomorph.symm_trans_self, pullback_refl]

/-- Pulling back along the identity of the diffeomorphism group does nothing. -/
@[simp]
theorem pullback_one (J : SmoothAlmostComplexStructure I M) :
    J.pullback (1 : TauCeti.Diff I M ∞) = J := by
  rw [Diffeomorph.one_def, pullback_refl]

/-- Pulling back along a product `φ * ψ` (first `ψ`, then `φ`) is pulling back along `φ`, then
along `ψ`. -/
theorem pullback_mul (J : SmoothAlmostComplexStructure I M) (φ ψ : TauCeti.Diff I M ∞) :
    J.pullback (φ * ψ) = (J.pullback φ).pullback ψ := by
  rw [Diffeomorph.mul_def, pullback_trans]

/-- In the diffeomorphism group, `φ⁻¹` pulls `K` back to `J` exactly when `φ` pulls `J` back to
`K`. -/
theorem pullback_inv_eq_iff (φ : TauCeti.Diff I M ∞) {J K : SmoothAlmostComplexStructure I M} :
    K.pullback φ⁻¹ = J ↔ J.pullback φ = K := by
  rw [Diffeomorph.inv_def, pullback_symm_eq_iff]

end TauCeti.SmoothAlmostComplexStructure

end
