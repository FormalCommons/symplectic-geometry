/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Complex.Blowup.AlmostComplex
import SymplecticGeometry.Geometry.Manifold.Diffeomorph.RestrictScalars

/-!
# The blowup of a point in complex dimension one

For `n = 0`, so that `M` is modelled on `Fin 1 → ℂ`, the projective space `ℙ ℂ (Fin 1 → ℂ)` is a
single point. Blowing up a point of `M` then replaces it by a single point, and the blowdown
`SymplecticGeometry.Blowup.blowdown c : Blowup c → M` is a diffeomorphism which carries the
almost complex blowup `J̃` of `J` to `J`. This is the case `n = 0` of the first Chern class
formula for the blowup, which there follows by naturality.

## Main results

* `SymplecticGeometry.Blowup.subsingleton_exceptionalDivisor`: the exceptional divisor has at
  most one point.
* `SymplecticGeometry.Blowup.bijective_blowdown`: the blowdown is bijective. Off the divisor it is
  injective (`injOn_blowdown`), the divisor is the fibre over `p₀`, and `M ∖ {p₀}` is the image
  of `inl`.
* `SymplecticGeometry.Blowup.isLocalDiffeomorph_blowdown`: the blowdown is a local
  diffeomorphism. Off the divisor this is `isLocalDiffeomorphAt_blowdown_real`. On the range of
  `inr`, `c ∘ π` agrees near each point with the model blowdown after `lift c`, a composition of
  local diffeomorphisms by `BlowupModel.blowdownDiffeomorphDimOne` and `isLocalDiffeomorphAt_lift`,
  and Tau Ceti's `IsLocalDiffeomorphAt.of_comp_left` cancels the chart `c`.
* `SymplecticGeometry.Blowup.blowdownDiffeomorphDimOne`: the blowdown as a diffeomorphism
  `Blowup c ≃ₘ^∞ M`, by Mathlib's `IsLocalDiffeomorph.diffeomorphOfBijective`.
* `SymplecticGeometry.Blowup.almostComplexStructure_eq_pullback`: the almost complex blowup is the
  pullback of `J` by this diffeomorphism (Tau Ceti's
  `TauCeti.SmoothAlmostComplexStructure.pullback`), as the blowdown is pseudoholomorphic at every
  point (`mfderiv_blowdown_almostComplexStructure_apply`).

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §7.1.
* [P. Griffiths, J. Harris, *Principles of Algebraic Geometry*][GriffithsHarris1978],
  Chapter 1, §4.
-/

public section

open Set Function
open scoped Manifold ContDiff LinearAlgebra.Projectivization TauCeti.ComplexManifold

namespace SymplecticGeometry

namespace Blowup

open BlowupModel TauCeti TauCeti.SmoothAlmostComplexStructure

open GluedAlong (inl inr)

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Fin 1 → ℂ) M] {p₀ : M}
  (c : BlowupChart (n := 0) M p₀)

/-- For `n = 0` the exceptional divisor has at most one point, since `ℙ ℂ (Fin 1 → ℂ)` has one
point. -/
theorem subsingleton_exceptionalDivisor : (exceptionalDivisor c).Subsingleton := by
  have : Subsingleton (ℙ ℂ (Fin 1 → ℂ)) :=
    Projectivization.subsingleton_of_rank_le_one (by simp)
  rw [exceptionalDivisor_def]
  rintro _ ⟨ℓ, rfl⟩ _ ⟨ℓ', rfl⟩
  rw [Subsingleton.elim ℓ ℓ']

/-- For `n = 0` the blowdown `Blowup c → M` is bijective. -/
theorem bijective_blowdown : Bijective (blowdown c) := by
  refine ⟨fun z w h => ?_, fun x => ?_⟩
  · by_cases hz : z ∈ exceptionalDivisor c
    · exact subsingleton_exceptionalDivisor c hz
        ((blowdown_eq_center_iff c).1 (h ▸ (blowdown_eq_center_iff c).2 hz))
    · exact injOn_blowdown c hz (fun hw => hz ((blowdown_eq_center_iff c).1
        (h.trans ((blowdown_eq_center_iff c).2 hw)))) h
  · by_cases hx : x = p₀
    · exact ⟨ofDirection c (Classical.arbitrary _), hx ▸ blowdown_ofDirection c _⟩
    · exact ⟨inl (gluingHomeomorph c) ⟨x, (mem_puncturedOpens c).2 hx⟩, blowdown_inl c _⟩

variable [IsManifold 𝓘(ℝ, Fin 1 → ℂ) ∞ M]
  [hc : Fact (c.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas 𝓘(ℝ, Fin 1 → ℂ) ∞ M)]

/-- For `n = 0` the blowdown `Blowup c → M` is a local diffeomorphism of real manifolds,
also at the point of the exceptional divisor. -/
theorem isLocalDiffeomorph_blowdown :
    IsLocalDiffeomorph 𝓘(ℝ, Fin 1 → ℂ) 𝓘(ℝ, Fin 1 → ℂ) ∞ (blowdown c) := by
  intro z
  rcases GluedAlong.exists_inl_or_exists_inr _ z with ⟨x, rfl⟩ | ⟨y, rfl⟩
  · exact isLocalDiffeomorphAt_blowdown_real c (inl_notMem_exceptionalDivisor c x)
  have hz : inr (gluingHomeomorph c) y ∈ range (inr (gluingHomeomorph c)) := mem_range_self y
  have hbd : IsLocalDiffeomorphAt 𝓘(ℝ, Fin 1 → ℂ) 𝓘(ℝ, Fin 1 → ℂ) ∞ BlowupModel.blowdown
      (lift c (inr (gluingHomeomorph c) y)) := by
    simpa only [Diffeomorph.coe_ofLE, Diffeomorph.coe_restrictScalars',
      coe_blowdownDiffeomorphDimOne] using
      ((BlowupModel.blowdownDiffeomorphDimOne.restrictScalars' ℝ).ofLE le_top).isLocalDiffeomorph
        _
  exact IsLocalDiffeomorphAt.of_comp_left
    (((isLocalDiffeomorphAt_lift c hz).comp (hg := hbd)).congr_of_eventuallyEq
      (comp_blowdown_eventuallyEq_blowdown_comp_lift c hz))
    (c.toOpenPartialHomeomorph.isLocalDiffeomorphAt_of_mem_maximalAtlas hc.out
      (blowdown_mem_source c hz))
    (blowdown c).continuous.continuousAt

/-- **The blowdown in complex dimension one.** For `n = 0`, the blowdown `Blowup c → M` is a
diffeomorphism of real manifolds. -/
noncomputable def blowdownDiffeomorphDimOne :
    Blowup c ≃ₘ^∞⟮𝓘(ℝ, Fin 1 → ℂ), 𝓘(ℝ, Fin 1 → ℂ)⟯ M :=
  (isLocalDiffeomorph_blowdown c).diffeomorphOfBijective (bijective_blowdown c)

@[simp]
theorem coe_blowdownDiffeomorphDimOne : ⇑(blowdownDiffeomorphDimOne c) = blowdown c :=
  IsLocalDiffeomorph.coe_diffeomorphOfBijective _ _

variable (J : SmoothAlmostComplexStructure 𝓘(ℝ, Fin 1 → ℂ) M)
  (hJ : IsPseudoholomorphicOn J (ofComplexManifold (Fin 1 → ℂ) (Fin 1 → ℂ)) c c.source)

/-- For `n = 0`, the almost complex blowup `J̃` is the pullback of `J` by the blowdown
diffeomorphism `π`: `J̃ = (dπ)⁻¹ ∘ J ∘ dπ` at every point. -/
theorem almostComplexStructure_eq_pullback :
    almostComplexStructure c J hJ = pullback (blowdownDiffeomorphDimOne c) J :=
  (eq_pullback_iff _ _).2 fun z v => by
    rw [coe_blowdownDiffeomorphDimOne]
    exact mfderiv_blowdown_almostComplexStructure_apply c J hJ z v

end Blowup

end SymplecticGeometry

end
