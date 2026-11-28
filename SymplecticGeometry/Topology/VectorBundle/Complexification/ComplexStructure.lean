/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.LinearAlgebra.Complex.Complexification
public import TauCeti.Topology.VectorBundle.Complex.Structure
public import TauCeti.Topology.VectorBundle.Complexification
public import TauCeti.Topology.VectorBundle.Conjugate
import SymplecticGeometry.Topology.FiberBundle.Prod
import TauCeti.Topology.VectorBundle.Hom
import TauCeti.Topology.VectorBundle.Section

/-!
# The complexification of a real bundle with a complex structure

Let `J` be a continuous complex structure on a real vector bundle `V`, and `J.Fiber` the complex
vector bundle it defines. The complexification `fun b ↦ ℂ ⊗[ℝ] V b` of `V` splits as the direct
sum of `J.Fiber` and of its conjugate: on each fibre, `z ⊗ v ↦ (z v, z̄ v)` is a complex-linear
isomorphism `ℂ ⊗[ℝ] V b ≃ J.Fiber b × Conjugate (J.Fiber b)`, where `z v` is the action of `ℂ`
on `J.Fiber b`, `re z • v + im z • J v`. It is the base change of the identification of `V b`
with `J.Fiber b`, followed by the splitting `TauCeti.Conjugate.complexificationEquiv` of the
complexification of a complex vector space.

In the real coordinates `u = 1 ⊗ x + i ⊗ y` of the complexification, the map is
`(x, y) ↦ (x + J y, x - J y)`. This is continuous on total spaces, since `J` is, by Tau Ceti's
`TauCeti.continuous_complexification_totalSpace_iff`; Tau Ceti's `TauCeti.bundleHomeomorph` then
makes the fibrewise isomorphisms a homeomorphism of total spaces. The proof of continuity
adapts that of Tau Ceti's `TauCeti.complexificationTotalSpaceHomeomorphProd`, which splits the
complexification of a sum of bundles in the same way.

## Main definitions

* `TauCeti.Bundle.ContinuousComplexStructure.complexificationEquiv`: the complex-linear
  isomorphism `ℂ ⊗[ℝ] V b ≃ J.Fiber b × Conjugate (J.Fiber b)`, `z ⊗ v ↦ (z v, z̄ v)`.
* `TauCeti.Bundle.ContinuousComplexStructure.complexificationHomeomorph`: the induced
  homeomorphism from the total space of the complexification of `V` to that of
  `J.Fiber ×ᵇ ConjugateBundle J.Fiber`, with its value on pure tensors
  (`TauCeti.Bundle.ContinuousComplexStructure.complexificationHomeomorph_tmul`).

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §15 (the complexification of a complex vector bundle is isomorphic to the
  sum of the bundle and its conjugate).
-/

public section

noncomputable section

open Bundle Module TauCeti TauCeti.Conjugate ComplexConjugate
open scoped TensorProduct

namespace TauCeti.Bundle.ContinuousComplexStructure

variable {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [∀ b, AddCommGroup (V b)] [∀ b, Module ℝ (V b)] [∀ b, TopologicalSpace (V b)]
  [∀ b, IsTopologicalAddGroup (V b)] [∀ b, ContinuousSMul ℝ (V b)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  (J : ContinuousComplexStructure F V)

/-! ### The fibrewise isomorphism -/

/-- The complex-linear isomorphism `ℂ ⊗[ℝ] V b ≃ J.Fiber b × Conjugate (J.Fiber b)`,
`z ⊗ v ↦ (z v, z̄ v)`, where `ℂ` acts on `J.Fiber b` through `J b`: the base change of the
identification of `V b` with `J.Fiber b`, followed by `TauCeti.Conjugate.complexificationEquiv`. -/
def complexificationEquiv (b : B) :
    ℂ ⊗[ℝ] V b ≃ₗ[ℂ] J.Fiber b × ConjugateBundle J.Fiber b :=
  (LinearEquiv.baseChange ℝ ℂ _ _ (J.fiberEquiv b).toLinearEquiv.symm).trans
    (Conjugate.complexificationEquiv (J.Fiber b))

/-- `J.complexificationEquiv b` is the base change of `(J.fiberEquiv b).symm` followed by
`TauCeti.Conjugate.complexificationEquiv (J.Fiber b)`. -/
theorem complexificationEquiv_def (b : B) :
    J.complexificationEquiv b =
      (LinearEquiv.baseChange ℝ ℂ _ _ (J.fiberEquiv b).toLinearEquiv.symm).trans
        (Conjugate.complexificationEquiv (J.Fiber b)) :=
  (rfl)

/-- On a pure tensor, `J.complexificationEquiv b` is `z ⊗ v ↦ (z v, z̄ v)`; in the conjugate
bundle, the second component is `z • toConj v`. -/
@[simp]
theorem complexificationEquiv_tmul (b : B) (z : ℂ) (v : V b) :
    J.complexificationEquiv b (z ⊗ₜ[ℝ] v) =
      (z • (J.fiberEquiv b).symm v, z • toConj ((J.fiberEquiv b).symm v)) := by
  simp [complexificationEquiv_def]

/-- The first component of `J.complexificationEquiv b u`, read in `V b`, is `x + J y`, for
`x` and `y` the real and imaginary parts of `u`. -/
@[simp]
theorem fiberEquiv_complexificationEquiv_fst (b : B) (u : ℂ ⊗[ℝ] V b) :
    J.fiberEquiv b (J.complexificationEquiv b u).1 =
      realPart (V b) u + J b (imaginaryPart (V b) u) := by
  simp [complexificationEquiv_def]

/-- The second component of `J.complexificationEquiv b u`, read in `V b`, is `x - J y`, for
`x` and `y` the real and imaginary parts of `u`. -/
@[simp]
theorem fiberEquiv_ofConj_complexificationEquiv_snd (b : B) (u : ℂ ⊗[ℝ] V b) :
    J.fiberEquiv b (ofConj (J.complexificationEquiv b u).2) =
      realPart (V b) u - J b (imaginaryPart (V b) u) := by
  simp [complexificationEquiv_def]

/-! ### The homeomorphism of total spaces -/

section Homeomorph

variable [FiniteDimensional ℝ F] (G : Type*) [NormedAddCommGroup G] [NormedSpace ℂ G]
  [FiniteDimensional ℂ G] [Fact (finrank ℝ F = 2 * finrank ℂ G)]
  [∀ b, TopologicalSpace (ℂ ⊗[ℝ] V b)] [∀ b, IsComplexificationTopology (V b)]

/-- The fibrewise map `J.complexificationEquiv` is continuous on total spaces. -/
theorem continuous_complexificationEquiv :
    Continuous fun p : TotalSpace (Complexification F) (fun b ↦ ℂ ⊗[ℝ] V b) ↦
      TotalSpace.mk' (G × Conjugate G) (E := J.Fiber ×ᵇ ConjugateBundle J.Fiber) p.proj
        (J.complexificationEquiv p.proj p.snd) := by
  obtain ⟨hre, him⟩ := (continuous_complexification_totalSpace_iff (F := F) (E := V)).mp
    continuous_id
  have hJ := (continuous_hom_bundle_iff (fun b ↦ J b)).1 J.continuous
  have hJim := hJ.comp him
  rw [Bundle.Prod.continuous_totalSpace_prod_iff]
  constructor
  · refine ((J.totalSpaceHomeomorph G).symm.continuous.comp
      (hre.add_totalSpace ℝ hJim)).congr fun p ↦ ?_
    simp only [Function.comp_apply, id_eq, totalSpaceHomeomorph_symm_apply,
      ← fiberEquiv_complexificationEquiv_fst, ContinuousLinearEquiv.symm_apply_apply]
  · refine ((ConjugateBundle.toConjHomeomorph G J.Fiber).continuous.comp
      ((J.totalSpaceHomeomorph G).symm.continuous.comp (hre.add_totalSpace ℝ
        ((continuous_const (y := (-1 : ℝ))).smul_totalSpace hJim)))).congr fun p ↦ ?_
    simp only [Function.comp_apply, id_eq, totalSpaceHomeomorph_symm_apply,
      ConjugateBundle.toConjHomeomorph_apply, neg_one_smul, ← sub_eq_add_neg,
      ← fiberEquiv_ofConj_complexificationEquiv_snd, ContinuousLinearEquiv.symm_apply_apply,
      toConj_ofConj]

/-- The complexification of a real vector bundle `V` with a continuous complex structure `J` is
the direct sum of the complex vector bundle `J.Fiber` and of its conjugate: the fibrewise
complex-linear isomorphisms `J.complexificationEquiv`, `z ⊗ v ↦ (z v, z̄ v)`, as a homeomorphism
of total spaces. -/
def complexificationHomeomorph :
    TotalSpace (Complexification F) (fun b ↦ ℂ ⊗[ℝ] V b) ≃ₜ
      TotalSpace (G × Conjugate G) (J.Fiber ×ᵇ ConjugateBundle J.Fiber) :=
  haveI := fun b ↦ FiberBundle.t2Space (Complexification F) (fun b ↦ ℂ ⊗[ℝ] V b) b
  haveI := fun b ↦ VectorBundle.finiteDimensional ℂ (Complexification F)
    (fun b ↦ ℂ ⊗[ℝ] V b) b
  haveI := fun b ↦ FiberBundle.t2Space (G × Conjugate G) (J.Fiber ×ᵇ ConjugateBundle J.Fiber) b
  haveI := VectorBundle.isTopologicalAddGroup ℂ (G × Conjugate G)
    (J.Fiber ×ᵇ ConjugateBundle J.Fiber)
  haveI := VectorBundle.continuousSMul ℂ (G × Conjugate G) (J.Fiber ×ᵇ ConjugateBundle J.Fiber)
  bundleHomeomorph (fun b ↦ (J.complexificationEquiv b).toContinuousLinearEquiv)
    (J.continuous_complexificationEquiv G)

@[simp]
theorem complexificationHomeomorph_apply
    (p : TotalSpace (Complexification F) fun b ↦ ℂ ⊗[ℝ] V b) :
    J.complexificationHomeomorph G p = ⟨p.proj, J.complexificationEquiv p.proj p.snd⟩ :=
  (bundleHomeomorph_apply _ _ p).trans (by simp)

@[simp]
theorem complexificationHomeomorph_symm_apply
    (p : TotalSpace (G × Conjugate G) (J.Fiber ×ᵇ ConjugateBundle J.Fiber)) :
    (J.complexificationHomeomorph G).symm p =
      ⟨p.proj, (J.complexificationEquiv p.proj).symm p.snd⟩ :=
  (bundleHomeomorph_symm_apply _ _ p).trans (by simp)

theorem proj_complexificationHomeomorph
    (p : TotalSpace (Complexification F) fun b ↦ ℂ ⊗[ℝ] V b) :
    (J.complexificationHomeomorph G p).proj = p.proj := by
  simp

/-- On a pure tensor, `J.complexificationHomeomorph G` is `z ⊗ v ↦ (z v, z̄ v)`. -/
theorem complexificationHomeomorph_tmul (b : B) (z : ℂ) (v : V b) :
    J.complexificationHomeomorph G ⟨b, z ⊗ₜ[ℝ] v⟩ =
      ⟨b, (z • (J.fiberEquiv b).symm v, z • toConj ((J.fiberEquiv b).symm v))⟩ := by
  simp

end Homeomorph

end TauCeti.Bundle.ContinuousComplexStructure

end
