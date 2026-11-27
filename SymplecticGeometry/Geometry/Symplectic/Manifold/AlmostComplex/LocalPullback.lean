/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Descent
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Restriction
public import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic

/-!
# Pulling back almost complex structures along diffeomorphisms of open sets

Tau Ceti's `TauCeti.SmoothAlmostComplexStructure.localPullback` pulls a smooth almost complex
structure back along a local diffeomorphism. This file treats the case of a diffeomorphism `Ψ`
from an open set `U` of `X` onto an open set `V` of `Y`, followed by the inclusion of `V`: if a
map `f : X → Y` agrees with `Ψ` on `U`, then at each point of `U` the differential of `f` is
complex linear for the pullback and the structure of `Y`
(`TauCeti.SmoothAlmostComplexStructure.mfderiv_apply_localPullback_subtypeVal_comp`). This is how
a structure defined on an open set by a pullback is compared with maps defined on the whole
manifold, such as the blowdown and the map to the model in the complex blowup.

Such a pullback is also the pullback along `Ψ`, in the sense of
`TauCeti.SmoothAlmostComplexStructure.pullback`, of the restriction of the structure of `Y` to `V`
(`TauCeti.SmoothAlmostComplexStructure.localPullback_subtypeVal_comp_eq_pullback`); this extends
Tau Ceti's `TauCeti.SmoothAlmostComplexStructure.localPullback_eq_pullback`, the case `V = Y`
without the inclusion.
-/

public section

open TopologicalSpace
open scoped Manifold ContDiff

namespace TauCeti.SmoothAlmostComplexStructure

variable {E H X E' H' Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y]
  {U : Opens X} {V : Opens Y}

/-- Let `f : X → Y` agree on an open set `U` with a diffeomorphism `Ψ` from `U` onto an open set
`V`. Then at each point of `U`, the differential of `f` is complex linear for the pullback of a
structure `K` of `Y` along `Ψ` (followed by the inclusion of `V`) and for `K`. -/
theorem mfderiv_apply_localPullback_subtypeVal_comp (Ψ : U ≃ₘ^∞⟮I, I'⟯ V) {f : X → Y}
    (hf : ∀ x : U, f x = Ψ x) (K : SmoothAlmostComplexStructure I' Y) (x : U)
    (v : TangentSpace I x) :
    mfderiv I I' f x (localPullback Ψ.isLocalDiffeomorph_subtypeVal_comp K x v) =
      K (f x) (mfderiv I I' f x v) := by
  have hΨ : (fun u : U ↦ (Ψ u : Y)) = f ∘ Subtype.val := funext fun u ↦ (hf u).symm
  have hmf : ∀ w : TangentSpace I x,
      mfderiv I I' (fun u : U ↦ (Ψ u : Y)) x w = mfderiv I I' f x w := fun w ↦ by
    rw [hΨ]
    exact TauCeti.Manifold.mfderiv_comp_subtype_val_apply w
  rw [← hmf, mfderiv_localPullback_apply, hmf, hf x]

/-- The pullback of a structure `K` of `Y` along a diffeomorphism `Ψ` from `U` onto an open set
`V`, followed by the inclusion of `V`, is the pullback along `Ψ` of the restriction of `K` to
`V`. -/
@[simp]
theorem localPullback_subtypeVal_comp_eq_pullback [FiniteDimensional ℝ E']
    (Ψ : U ≃ₘ^∞⟮I, I'⟯ V) (K : SmoothAlmostComplexStructure I' Y) :
    localPullback Ψ.isLocalDiffeomorph_subtypeVal_comp K = pullback Ψ (K.restrictOpen V) :=
  ((eq_localPullback_iff_isPseudoholomorphic _ _ _).2
    ((isPseudoholomorphic_subtype_val K V).comp (isPseudoholomorphic_pullback Ψ _))).symm

end TauCeti.SmoothAlmostComplexStructure
