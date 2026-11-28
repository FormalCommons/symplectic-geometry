/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Diffeomorphism.Sphere.Mobius
public import SymplecticGeometry.Geometry.Diffeomorphism.Sphere.Uniformization
import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.Pullback
import TauCeti.Geometry.Diffeomorphism.Inversion

/-!
# The trivialization of `Diff⁺(S²)` over the tame complex structures

Let `S²` be the Riemann sphere `OnePoint ℂ`, seen as a real surface, `i` its complex structure,
`𝒥` the smooth almost complex structures tamed by the Fubini–Study form (a local notation), and
`p : Diff⁺(S²) → 𝒥`, `φ ↦ φ^* i`, the map `SymplecticGeometry.complexStructureMap`. The
uniformizing diffeomorphism `σ(J) = SymplecticGeometry.uniformizingDiffeomorph J` is a
continuous section of `p` (`SymplecticGeometry.continuous_uniformizingDiffeomorph`).
Multiplying on the left by an element of the Möbius group `SymplecticGeometry.mobiusSubgroup`,
the stabilizer of `i`, does not change `p`
(`SymplecticGeometry.complexStructureMap_inclusion_mul`). Together with `σ`, this identifies
`Diff⁺(S²)` with the product `𝒥 × mobiusSubgroup`, so `p` is a trivial principal bundle.

## Main definitions and results

* `SymplecticGeometry.mul_inv_uniformizingDiffeomorph_mem_mobiusSubgroup`: `φ σ(φ^* i)⁻¹` is a
  Möbius transformation, since it pulls `i` back to `(σ(φ^* i)⁻¹)^* (φ^* i) = i`.
* `SymplecticGeometry.diffPlusTrivialization`: for every covering frame system giving `𝒥` its
  `C^∞` topology, the homeomorphism `Diff⁺(S²) ≃ₜ 𝒥 × mobiusSubgroup`,
  `φ ↦ (φ^* i, φ σ(φ^* i)⁻¹)`, with inverse `(J, g) ↦ g σ(J)`. Continuity of the two maps
  comes from `SymplecticGeometry.continuous_complexStructureMap`,
  `SymplecticGeometry.continuous_uniformizingDiffeomorph` and Tau Ceti's
  `Diffeomorph.isTopologicalGroup`. Its lemmas
  `SymplecticGeometry.diffPlusTrivialization_apply_fst`,
  `SymplecticGeometry.coe_diffPlusTrivialization_apply_snd` and
  `SymplecticGeometry.coe_diffPlusTrivialization_symm_apply` give the two maps, and
  `SymplecticGeometry.diffPlusTrivialization_mul` says that `Φ (g φ) = ((Φ φ).1, g (Φ φ).2)` for a
  Möbius transformation `g`.
  `SymplecticGeometry.diffPlusTrivialization_inclusion` and
  `SymplecticGeometry.diffPlusTrivialization_uniformizingDiffeomorph` give its values
  `Φ g = (i, g)` on the Möbius group and `Φ σ(J) = (J, 1)` on the section.
* `SymplecticGeometry.exists_continuous_section_homeomorph_prod_mobiusSubgroup`: the milestone,
  which collects these facts with the uniqueness of `σ(J)`
  (`SymplecticGeometry.eq_uniformizingDiffeomorph_iff`) and the invariance of the fibres of `p`
  under the Möbius group (`SymplecticGeometry.complexStructureMap_inclusion_mul`).

## References

* [C. J. Earle, J. Eells, *The diffeomorphism group of a compact Riemann
  surface*][EarleEells1967], Theorems 1 (a) and 2 (a), in genus zero.
-/

public section

open scoped OnePoint Manifold ContDiff TauCeti.ComplexManifold TauCeti.DiffeomorphWeakWhitney
open TauCeti

namespace SymplecticGeometry

/-- The smooth almost complex structures on the Riemann sphere tamed by the Fubini–Study form. -/
local notation "𝒥" =>
  {J : SmoothAlmostComplexStructure 𝓘(ℝ, ℂ) (OnePoint ℂ) // OnePoint.fubiniStudyForm.Tames J}

/-- For `φ ∈ Diff⁺(S²)`, the diffeomorphism `φ σ(φ^* i)⁻¹` is a Möbius transformation. -/
theorem mul_inv_uniformizingDiffeomorph_mem_mobiusSubgroup (φ : diffPlus) :
    (φ * (uniformizingDiffeomorph (complexStructureMap φ))⁻¹ :
      TauCeti.Diff 𝓘(ℝ, ℂ) (OnePoint ℂ) ((⊤ : ℕ∞) : ℕ∞ω)) ∈ mobiusSubgroup := by
  rw [mem_mobiusSubgroup_iff, SmoothAlmostComplexStructure.pullback_mul]
  exact (SmoothAlmostComplexStructure.pullback_inv_eq_iff _).2
    ((pullback_uniformizingDiffeomorph _).trans (coe_complexStructureMap φ))

variable {ι : Type*}
  (e : ι → Bundle.Trivialization (ℂ →L[ℝ] ℂ) (Bundle.TotalSpace.proj (F := ℂ →L[ℝ] ℂ)
    (E := fun x : OnePoint ℂ ↦ TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) x)))
  [∀ k, MemTrivializationAtlas (e k)] (U : ι → TopologicalSpace.Opens (OnePoint ℂ))
  (hU : ∀ k, (U k : Set (OnePoint ℂ)) ⊆ (e k).baseSet) (hcover : ∀ x, ∃ k, x ∈ U k)

/-- **The trivialization of `Diff⁺(S²)` over `𝒥`.** For a covering frame system giving the
structures tamed by the Fubini–Study form the `C^∞` topology, and the weak Whitney topology on
diffeomorphisms, the homeomorphism `Diff⁺(S²) ≃ₜ 𝒥 × mobiusSubgroup` that sends `φ` to
`(φ^* i, φ σ(φ^* i)⁻¹)`, with inverse `(J, g) ↦ g σ(J)`. -/
noncomputable def diffPlusTrivialization :
    letI := SmoothAlmostComplexStructure.frameTopology e U hU
    diffPlus ≃ₜ 𝒥 × mobiusSubgroup :=
  letI := SmoothAlmostComplexStructure.frameTopology e U hU
  have hp := continuous_complexStructureMap e U hU
  have hσ := continuous_uniformizingDiffeomorph e U hU hcover
  { toFun φ := (complexStructureMap φ,
      ⟨φ * (uniformizingDiffeomorph (complexStructureMap φ))⁻¹,
        mul_inv_uniformizingDiffeomorph_mem_mobiusSubgroup φ⟩)
    invFun Jg := Subgroup.inclusion mobiusSubgroup_le_diffPlus Jg.2 * uniformizingDiffeomorph Jg.1
    left_inv φ := by
      refine Subtype.ext ?_
      simp
    right_inv := fun ⟨J, g⟩ ↦ by
      refine Prod.ext (complexStructureMap_inclusion_mul g _ |>.trans
        (complexStructureMap_uniformizingDiffeomorph J)) (Subtype.ext ?_)
      simp only [complexStructureMap_inclusion_mul, complexStructureMap_uniformizingDiffeomorph,
        Subgroup.coe_mul, Subgroup.coe_inclusion, Subgroup.coe_inv, mul_inv_cancel_right]
    continuous_toFun := hp.prodMk <| continuous_induced_rng.2 <|
      (continuous_subtypeVal.mul (continuous_subtypeVal.comp (hσ.comp hp)).inv)
    continuous_invFun :=
      ((continuous_inclusion mobiusSubgroup_le_diffPlus).comp continuous_snd).mul
        (hσ.comp continuous_fst) }

/-- The first component of `diffPlusTrivialization` is `complexStructureMap`, `φ ↦ φ^* i`. -/
@[simp]
theorem diffPlusTrivialization_apply_fst (φ : diffPlus) :
    letI := SmoothAlmostComplexStructure.frameTopology e U hU
    (diffPlusTrivialization e U hU hcover φ).1 = complexStructureMap φ :=
  (rfl)

/-- The second component of `diffPlusTrivialization` is `φ σ(φ^* i)⁻¹`. -/
@[simp]
theorem coe_diffPlusTrivialization_apply_snd (φ : diffPlus) :
    letI := SmoothAlmostComplexStructure.frameTopology e U hU
    ((diffPlusTrivialization e U hU hcover φ).2 :
        TauCeti.Diff 𝓘(ℝ, ℂ) (OnePoint ℂ) ((⊤ : ℕ∞) : ℕ∞ω)) =
      φ * (uniformizingDiffeomorph (complexStructureMap φ))⁻¹ :=
  (rfl)

/-- The inverse of `diffPlusTrivialization` sends `(J, g)` to `g σ(J)`. -/
@[simp]
theorem coe_diffPlusTrivialization_symm_apply (J : 𝒥) (g : mobiusSubgroup) :
    letI := SmoothAlmostComplexStructure.frameTopology e U hU
    ((diffPlusTrivialization e U hU hcover).symm (J, g) :
      TauCeti.Diff 𝓘(ℝ, ℂ) (OnePoint ℂ) ((⊤ : ℕ∞) : ℕ∞ω)) = g * uniformizingDiffeomorph J :=
  (rfl)

/-- `diffPlusTrivialization` is equivariant: it turns left multiplication by a Möbius
transformation `g` on `Diff⁺(S²)` into left multiplication by `g` on the `mobiusSubgroup`
component. -/
@[simp]
theorem diffPlusTrivialization_mul (g : mobiusSubgroup) (φ : diffPlus) :
    letI := SmoothAlmostComplexStructure.frameTopology e U hU
    diffPlusTrivialization e U hU hcover (Subgroup.inclusion mobiusSubgroup_le_diffPlus g * φ) =
      ((diffPlusTrivialization e U hU hcover φ).1,
        g * (diffPlusTrivialization e U hU hcover φ).2) := by
  refine Prod.ext (by simp) (Subtype.ext ?_)
  rw [coe_diffPlusTrivialization_apply_snd, complexStructureMap_inclusion_mul, Subgroup.coe_mul,
    Subgroup.coe_mul, Subgroup.coe_inclusion, coe_diffPlusTrivialization_apply_snd, mul_assoc]

/-- `diffPlusTrivialization` sends a Möbius transformation `g` to `(i, g)`. -/
@[simp]
theorem diffPlusTrivialization_inclusion (g : mobiusSubgroup) :
    letI := SmoothAlmostComplexStructure.frameTopology e U hU
    diffPlusTrivialization e U hU hcover (Subgroup.inclusion mobiusSubgroup_le_diffPlus g) =
      (tameOfComplexManifold, g) := by
  refine Prod.ext (by simp) (Subtype.ext ?_)
  simp

/-- `diffPlusTrivialization` sends the uniformizing diffeomorphism `σ(J)` to `(J, 1)`. -/
@[simp]
theorem diffPlusTrivialization_uniformizingDiffeomorph (J : 𝒥) :
    letI := SmoothAlmostComplexStructure.frameTopology e U hU
    diffPlusTrivialization e U hU hcover (uniformizingDiffeomorph J) = (J, 1) := by
  refine Prod.ext (by simp) (Subtype.ext ?_)
  simp

include hcover in
/-- **`Diff⁺(S²)` is a trivial principal bundle over the tame complex structures.** Give the
smooth almost complex structures on the Riemann sphere tamed by the Fubini–Study form the `C^∞`
topology of a covering frame system, and diffeomorphisms the weak Whitney topology. Then:
* `σ = uniformizingDiffeomorph` is a continuous section of `p = complexStructureMap`,
  `φ ↦ φ^* i`;
* for each `J`, `σ(J)` is the unique diffeomorphism of the sphere that pulls `i` back to `J` and
  fixes `0`, `1` and `∞`;
* left multiplication by an element `g` of the Möbius group `mobiusSubgroup`, the stabilizer of
  `i`, does not change `p`: `p (g φ) = p φ`;
* there is a homeomorphism `Φ : Diff⁺(S²) ≃ₜ 𝒥 × mobiusSubgroup` with
  `Φ φ = (φ^* i, φ σ(φ^* i)⁻¹)`, whose inverse is `(J, g) ↦ g σ(J)`, and which turns left
  multiplication by `g` into left multiplication by `g` on the `mobiusSubgroup` component.

Milestone: *Diffeomorphisms of the 2-sphere form a trivial principal bundle over the complex
structures*. -/
theorem exists_continuous_section_homeomorph_prod_mobiusSubgroup :
    letI := SmoothAlmostComplexStructure.frameTopology e U hU
    Continuous uniformizingDiffeomorph ∧
      (∀ J, complexStructureMap (uniformizingDiffeomorph J) = J) ∧
      (∀ (J : 𝒥) (φ : TauCeti.Diff 𝓘(ℝ, ℂ) (OnePoint ℂ) ((⊤ : ℕ∞) : ℕ∞ω)),
        φ = uniformizingDiffeomorph J ↔
          (SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ)).pullback φ = J.val ∧
            φ (0 : ℂ) = (0 : ℂ) ∧ φ (1 : ℂ) = (1 : ℂ) ∧ φ ∞ = (∞ : OnePoint ℂ)) ∧
      (∀ (g : mobiusSubgroup) (φ : diffPlus),
        complexStructureMap (Subgroup.inclusion mobiusSubgroup_le_diffPlus g * φ) =
          complexStructureMap φ) ∧
      ∃ Φ : diffPlus ≃ₜ 𝒥 × mobiusSubgroup,
        (∀ φ, (Φ φ).1 = complexStructureMap φ) ∧
        (∀ φ, ((Φ φ).2 : TauCeti.Diff 𝓘(ℝ, ℂ) (OnePoint ℂ) ((⊤ : ℕ∞) : ℕ∞ω)) =
          φ * (uniformizingDiffeomorph (complexStructureMap φ))⁻¹) ∧
        (∀ J g, (Φ.symm (J, g) : TauCeti.Diff 𝓘(ℝ, ℂ) (OnePoint ℂ) ((⊤ : ℕ∞) : ℕ∞ω)) =
          g * uniformizingDiffeomorph J) ∧
        ∀ g φ, Φ (Subgroup.inclusion mobiusSubgroup_le_diffPlus g * φ) = ((Φ φ).1, g * (Φ φ).2) :=
  ⟨continuous_uniformizingDiffeomorph e U hU hcover,
    complexStructureMap_uniformizingDiffeomorph, eq_uniformizingDiffeomorph_iff,
    complexStructureMap_inclusion_mul, diffPlusTrivialization e U hU hcover,
    diffPlusTrivialization_apply_fst e U hU hcover,
    coe_diffPlusTrivialization_apply_snd e U hU hcover,
    coe_diffPlusTrivialization_symm_apply e U hU hcover,
    diffPlusTrivialization_mul e U hU hcover⟩

end SymplecticGeometry

end
