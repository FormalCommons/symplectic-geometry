/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.VectorBundle.Complexification
public import TauCeti.Topology.VectorBundle.Hom
public import SymplecticGeometry.Topology.Algebra.Module.Complexification
public import SymplecticGeometry.Topology.VectorBundle.Complex.ChernClass.Basic
import SymplecticGeometry.Topology.FiberBundle.Prod
import SymplecticGeometry.Topology.VectorBundle.ModelEquiv
import TauCeti.Topology.FiberBundle.Prod
import SymplecticGeometry.Topology.VectorBundle.Complex.ChernClass.Whitney
import SymplecticGeometry.Topology.VectorBundle.Complex.ChernClass.Naturality
import SymplecticGeometry.AlgebraicTopology.Cohomology.Empty

/-!
# Complexification of sums and trivial bundles

The complexification of a real vector bundle `E → B` with model fibre `F` is Tau Ceti's complex
vector bundle `fun x ↦ ℂ ⊗[ℝ] E x`, with model `TauCeti.Complexification F`, whose fibres carry
the topology of the scope `TauCeti.Complexification`. This file shows, for finite-dimensional
models, that complexification commutes with the operations that the argument for the spheres
needs:

* `continuous_baseChangeComplex_totalSpace`: a family of real-linear maps of fibres that is
  continuous on total spaces complexifies to one of complex-linear maps that is continuous too;
* `complexificationProdHomeomorph`: the complexification of `E₁ ×ᵇ E₂` is the direct sum of the
  complexifications, fibrewise by `TauCeti.complexificationProdEquiv`;
* `complexificationTrivialHomeomorph`: the complexification of `Bundle.Trivial B F` is
  `Bundle.Trivial B (Complexification F)`;
* `complexificationMapHomeomorph`: an isomorphism of real vector bundles complexifies.

Each homeomorphism of total spaces is Tau Ceti's `TauCeti.bundleHomeomorph` of a family of
complex-linear equivalences of fibres, so it covers the identity of the base, as its `_apply`
lemma shows; only the continuity of the forward map is proved here. These proofs follow Tau Ceti's
`TauCeti.complexificationTotalSpaceHomeomorphProd`, through
`TauCeti.continuous_complexification_totalSpace_iff`.

## Main results

* `Bundle.totalChernClass_complexification_prod`: over a compact base, the total Chern class of
  the complexification of `E₁ ×ᵇ E₂` is the product of those of the complexifications of `E₁`
  and `E₂`.
* `Bundle.totalChernClass_complexification_congr`: isomorphic real bundles have complexifications
  with the same total Chern class.
* `Bundle.totalChernClass_complexification_trivial`: over a compact base, the complexification
  of a trivial bundle has total Chern class `1`.
* `Bundle.totalChernClass_complexification_eq_one`: over a compact base, if the sum of `E` with a
  trivial real bundle is trivial, then the total Chern class of the complexification of `E` is `1`.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §15 (complexification of real vector bundles).
* [A. Hatcher, *Vector Bundles and K-Theory*][Hatcher2017], §3.1 (the Whitney sum formula).
-/

public section

noncomputable section

open Bundle Module TauCeti
open scoped TensorProduct TauCeti.Complexification

namespace SymplecticGeometry

/-! ### Complexification of maps of bundles -/

section Map

variable {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
  [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)] [FiberBundle F E]
  [VectorBundle ℝ F E]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
  {E' : B → Type*} [∀ x, AddCommGroup (E' x)] [∀ x, Module ℝ (E' x)]
  [TopologicalSpace (TotalSpace F' E')] [∀ x, TopologicalSpace (E' x)] [FiberBundle F' E']
  [VectorBundle ℝ F' E']

/-- A family of real-linear maps of fibres `φ b : E b →L[ℝ] E' b` that is continuous on total
spaces complexifies to a family `(φ b).baseChangeComplex` of complex-linear maps that is
continuous on the total spaces of the complexifications. -/
theorem continuous_baseChangeComplex_totalSpace {φ : ∀ b, E b →L[ℝ] E' b}
    (hφ : Continuous fun v : TotalSpace F E ↦ TotalSpace.mk' F' v.proj (φ v.proj v.snd)) :
    Continuous fun v : TotalSpace (Complexification F) (fun b ↦ ℂ ⊗[ℝ] E b) ↦
      TotalSpace.mk' (Complexification F') (E := fun b ↦ ℂ ⊗[ℝ] E' b) v.proj
        ((φ v.proj).baseChangeComplex v.snd) := by
  obtain ⟨hre, him⟩ := (continuous_complexification_totalSpace_iff (F := F) (E := E)).1
    continuous_id
  refine (continuous_complexification_totalSpace_iff (F := F') (E := E')).2 ⟨?_, ?_⟩
  · simpa [Function.comp_def] using hφ.comp hre
  · simpa [Function.comp_def] using hφ.comp him

/-- The version of `continuous_baseChangeComplex_totalSpace` for a family of real-linear
equivalences of fibres. -/
theorem continuous_baseChangeComplex_totalSpace_equiv {φ : ∀ b, E b ≃L[ℝ] E' b}
    (hφ : Continuous fun v : TotalSpace F E ↦ TotalSpace.mk' F' v.proj (φ v.proj v.snd)) :
    Continuous fun v : TotalSpace (Complexification F) (fun b ↦ ℂ ⊗[ℝ] E b) ↦
      TotalSpace.mk' (Complexification F') (E := fun b ↦ ℂ ⊗[ℝ] E' b) v.proj
        ((φ v.proj).baseChangeComplex v.snd) :=
  (continuous_baseChangeComplex_totalSpace (φ := fun b ↦ (φ b : E b →L[ℝ] E' b)) hφ).congr
    fun _ ↦ by
      simp only [← ContinuousLinearEquiv.toContinuousLinearMap_baseChangeComplex,
        ContinuousLinearEquiv.coe_coe]

variable [FiniteDimensional ℝ F] (φ : ∀ b, E b ≃L[ℝ] E' b)
  (hφ : Continuous fun v : TotalSpace F E ↦ TotalSpace.mk' F' v.proj (φ v.proj v.snd))

/-- An isomorphism of real vector bundles with finite-dimensional model, given by real-linear
equivalences of fibres `φ b` that are continuous on total spaces, complexifies: the
homeomorphism of the total spaces of the complexifications given on each fibre by the
complex-linear equivalence `(φ b).baseChangeComplex`. -/
def complexificationMapHomeomorph :
    TotalSpace (Complexification F) (fun b ↦ ℂ ⊗[ℝ] E b) ≃ₜ
      TotalSpace (Complexification F') (fun b ↦ ℂ ⊗[ℝ] E' b) :=
  bundleHomeomorph (𝕜 := ℂ) (fun b ↦ (φ b).baseChangeComplex)
    (continuous_baseChangeComplex_totalSpace_equiv hφ)

@[simp]
theorem complexificationMapHomeomorph_apply
    (v : TotalSpace (Complexification F) fun b ↦ ℂ ⊗[ℝ] E b) :
    complexificationMapHomeomorph φ hφ v = ⟨v.proj, (φ v.proj).baseChangeComplex v.snd⟩ :=
  bundleHomeomorph_apply _ _ v

@[simp]
theorem complexificationMapHomeomorph_symm_apply
    (v : TotalSpace (Complexification F') fun b ↦ ℂ ⊗[ℝ] E' b) :
    (complexificationMapHomeomorph φ hφ).symm v =
      ⟨v.proj, (φ v.proj).symm.baseChangeComplex v.snd⟩ := by
  rw [complexificationMapHomeomorph, bundleHomeomorph_symm_apply,
    ContinuousLinearEquiv.baseChangeComplex_symm]

end Map

/-! ### Complexification of a direct sum -/

section Prod

variable {B : Type*} [TopologicalSpace B]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  {E₁ : B → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module ℝ (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)] [FiberBundle F₁ E₁]
  [VectorBundle ℝ F₁ E₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  {E₂ : B → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module ℝ (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)] [FiberBundle F₂ E₂]
  [VectorBundle ℝ F₂ E₂]

/-- The map of total spaces given on each fibre by `complexificationProdEquiv`, from the
complexification of `E₁ ×ᵇ E₂` to the direct sum of the complexifications, is continuous. -/
theorem continuous_complexificationProdEquiv_totalSpace :
    Continuous fun v : TotalSpace (Complexification (F₁ × F₂)) (fun x ↦ ℂ ⊗[ℝ] (E₁ ×ᵇ E₂) x) ↦
      TotalSpace.mk' (Complexification F₁ × Complexification F₂)
        (E := (fun x ↦ ℂ ⊗[ℝ] E₁ x) ×ᵇ (fun x ↦ ℂ ⊗[ℝ] E₂ x)) v.proj
        (complexificationProdEquiv (E₁ v.proj) (E₂ v.proj) v.snd) := by
  rw [Bundle.Prod.continuous_totalSpace_prod_iff]
  obtain ⟨hre, him⟩ := (continuous_complexification_totalSpace_iff (F := F₁ × F₂)
    (E := E₁ ×ᵇ E₂)).1 continuous_id
  constructor <;> refine (continuous_complexification_totalSpace_iff).2 ⟨?_, ?_⟩
  · exact (FiberBundle.Prod.continuous_totalSpaceFst.comp hre).congr fun v ↦ by simp
  · exact (FiberBundle.Prod.continuous_totalSpaceFst.comp him).congr fun v ↦ by simp
  · exact (FiberBundle.Prod.continuous_totalSpaceSnd.comp hre).congr fun v ↦ by simp
  · exact (FiberBundle.Prod.continuous_totalSpaceSnd.comp him).congr fun v ↦ by simp

variable [FiniteDimensional ℝ F₁] [FiniteDimensional ℝ F₂]

variable (F₁ E₁ F₂ E₂) in
/-- The complexification of a direct sum `E₁ ×ᵇ E₂` of real vector bundles with
finite-dimensional models is the direct sum of the complexifications: the homeomorphism of total
spaces given on each fibre by the complex-linear equivalence `complexificationProdEquiv`. -/
def complexificationProdHomeomorph :
    TotalSpace (Complexification (F₁ × F₂)) (fun x ↦ ℂ ⊗[ℝ] (E₁ ×ᵇ E₂) x) ≃ₜ
      TotalSpace (Complexification F₁ × Complexification F₂)
        ((fun x ↦ ℂ ⊗[ℝ] E₁ x) ×ᵇ (fun x ↦ ℂ ⊗[ℝ] E₂ x)) :=
  bundleHomeomorph (𝕜 := ℂ) (fun x ↦ complexificationProdEquiv (E₁ x) (E₂ x))
    continuous_complexificationProdEquiv_totalSpace

@[simp]
theorem complexificationProdHomeomorph_apply
    (v : TotalSpace (Complexification (F₁ × F₂)) fun x ↦ ℂ ⊗[ℝ] (E₁ ×ᵇ E₂) x) :
    complexificationProdHomeomorph F₁ E₁ F₂ E₂ v =
      ⟨v.proj, complexificationProdEquiv (E₁ v.proj) (E₂ v.proj) v.snd⟩ :=
  bundleHomeomorph_apply _ _ v

@[simp]
theorem complexificationProdHomeomorph_symm_apply
    (v : TotalSpace (Complexification F₁ × Complexification F₂)
      ((fun x ↦ ℂ ⊗[ℝ] E₁ x) ×ᵇ (fun x ↦ ℂ ⊗[ℝ] E₂ x))) :
    (complexificationProdHomeomorph F₁ E₁ F₂ E₂).symm v =
      ⟨v.proj, (complexificationProdEquiv (E₁ v.proj) (E₂ v.proj)).symm v.snd⟩ :=
  bundleHomeomorph_symm_apply _ _ v

end Prod

/-! ### Complexification of a trivial bundle -/

section Trivial

variable (B : Type*) [TopologicalSpace B] (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The map of total spaces given on each fibre by
`tensorContinuousLinearEquivComplexification F`, from the complexification of
`Bundle.Trivial B F` to `Bundle.Trivial B (Complexification F)`, is continuous. -/
theorem continuous_tensorContinuousLinearEquivComplexification_totalSpace :
    Continuous fun v : TotalSpace (Complexification F) (fun x ↦ ℂ ⊗[ℝ] Trivial B F x) ↦
      TotalSpace.mk' (Complexification F) (E := Trivial B (Complexification F)) v.proj
        (tensorContinuousLinearEquivComplexification F v.snd) := by
  obtain ⟨hre, him⟩ := (continuous_complexification_totalSpace_iff (F := F)
    (E := Trivial B F)).1 continuous_id
  have hre' := (Trivial.homeomorphProd B F).continuous.comp hre
  have him' := (Trivial.homeomorphProd B F).continuous.comp him
  refine (Trivial.homeomorphProd B (Complexification F)).isInducing.continuous_iff.2 ?_
  refine continuous_prodMk.2 ⟨FiberBundle.continuous_proj _ _, ?_⟩
  refine (Complexification.equivProd F).toHomeomorph.isInducing.continuous_iff.2 ?_
  refine (hre'.snd.prodMk him'.snd).congr fun v ↦ ?_
  simp [Trivial.homeomorphProd]

variable [FiniteDimensional ℝ F]

/-- The complexification of the trivial bundle `Bundle.Trivial B F` with finite-dimensional
fibre is the trivial bundle `Bundle.Trivial B (Complexification F)`: the homeomorphism of total
spaces given on each fibre by the complex-linear equivalence
`tensorContinuousLinearEquivComplexification F`. -/
def complexificationTrivialHomeomorph :
    TotalSpace (Complexification F) (fun x ↦ ℂ ⊗[ℝ] Trivial B F x) ≃ₜ
      TotalSpace (Complexification F) (Trivial B (Complexification F)) :=
  bundleHomeomorph (𝕜 := ℂ) (fun _ ↦ tensorContinuousLinearEquivComplexification F)
    (continuous_tensorContinuousLinearEquivComplexification_totalSpace B F)

@[simp]
theorem complexificationTrivialHomeomorph_apply
    (v : TotalSpace (Complexification F) fun x ↦ ℂ ⊗[ℝ] Trivial B F x) :
    complexificationTrivialHomeomorph B F v =
      ⟨v.proj, tensorContinuousLinearEquivComplexification F v.snd⟩ :=
  bundleHomeomorph_apply _ _ v

@[simp]
theorem complexificationTrivialHomeomorph_symm_apply
    (v : TotalSpace (Complexification F) (Trivial B (Complexification F))) :
    (complexificationTrivialHomeomorph B F).symm v =
      ⟨v.proj, (tensorContinuousLinearEquivComplexification F).symm v.snd⟩ :=
  bundleHomeomorph_symm_apply _ _ v

end Trivial

/-! ### Chern classes of complexifications -/

namespace Bundle

variable {B : Type} [TopologicalSpace B] [CompactSpace B]

/-- The total Chern class of the complexification of a trivial real bundle is `1`, over a
compact base. -/
theorem totalChernClass_complexification_trivial (F : Type) [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] :
    totalChernClass (Complexification F) (fun x ↦ ℂ ⊗[ℝ] Trivial B F x) = 1 := by
  rw [totalChernClass_congr (fun _ ↦ tensorContinuousLinearEquivComplexification F)
    (continuous_tensorContinuousLinearEquivComplexification_totalSpace B F),
    totalChernClass_trivial]

/-- **Whitney sum formula for complexifications.** Over a compact base, the total Chern class
of the complexification of `E₁ ×ᵇ E₂` is the product of the total Chern classes of the
complexifications of `E₁` and `E₂`. -/
theorem totalChernClass_complexification_prod
    {F₁ : Type} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
    {E₁ : B → Type} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module ℝ (E₁ x)]
    [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)] [FiberBundle F₁ E₁]
    [VectorBundle ℝ F₁ E₁]
    {F₂ : Type} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]
    {E₂ : B → Type} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module ℝ (E₂ x)]
    [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)] [FiberBundle F₂ E₂]
    [VectorBundle ℝ F₂ E₂] :
    totalChernClass (Complexification (F₁ × F₂)) (fun x ↦ ℂ ⊗[ℝ] (E₁ ×ᵇ E₂) x) =
      totalChernClass (Complexification F₁) (fun x ↦ ℂ ⊗[ℝ] E₁ x) *
        totalChernClass (Complexification F₂) (fun x ↦ ℂ ⊗[ℝ] E₂ x) := by
  rw [totalChernClass_congr (fun x ↦ complexificationProdEquiv (E₁ x) (E₂ x))
    continuous_complexificationProdEquiv_totalSpace, totalChernClass_prod]

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {E : B → Type} [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
  [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)] [FiberBundle F E]
  [VectorBundle ℝ F E]

/-- Over a compact base, real vector bundles `E` and `E'` that are isomorphic, by real-linear
equivalences of fibres that are continuous on total spaces, have complexifications with the same
total Chern class. -/
theorem totalChernClass_complexification_congr
    {F' : Type} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    {E' : B → Type} [∀ x, AddCommGroup (E' x)] [∀ x, Module ℝ (E' x)]
    [TopologicalSpace (TotalSpace F' E')] [∀ x, TopologicalSpace (E' x)] [FiberBundle F' E']
    [VectorBundle ℝ F' E']
    (φ : ∀ b, E b ≃L[ℝ] E' b)
    (hφ : Continuous fun v : TotalSpace F E ↦ TotalSpace.mk' F' v.proj (φ v.proj v.snd)) :
    totalChernClass (Complexification F) (fun x ↦ ℂ ⊗[ℝ] E x) =
      totalChernClass (Complexification F') (fun x ↦ ℂ ⊗[ℝ] E' x) :=
  totalChernClass_congr (fun x ↦ (φ x).baseChangeComplex)
    (continuous_baseChangeComplex_totalSpace_equiv hφ)

/-- **The complexification of a stably trivial bundle has trivial Chern classes.** Over a compact
base, if the direct sum of a real vector bundle `E` with a trivial bundle `Bundle.Trivial B F₀` is
isomorphic to a trivial bundle `Bundle.Trivial B F'`, by real-linear equivalences of fibres that
are continuous on total spaces, then the total Chern class of the complexification of `E` is `1`.
-/
theorem totalChernClass_complexification_eq_one
    {F₀ : Type} [NormedAddCommGroup F₀] [NormedSpace ℝ F₀] [FiniteDimensional ℝ F₀]
    {F' : Type} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    (φ : ∀ b, (E ×ᵇ Trivial B F₀) b ≃L[ℝ] Trivial B F' b)
    (hφ : Continuous fun v : TotalSpace (F × F₀) (E ×ᵇ Trivial B F₀) ↦
      TotalSpace.mk' F' v.proj (φ v.proj v.snd)) :
    totalChernClass (Complexification F) (fun x ↦ ℂ ⊗[ℝ] E x) = 1 := by
  rcases isEmpty_or_nonempty B with _ | ⟨⟨b⟩⟩
  · exact Subsingleton.elim _ _
  have : FiniteDimensional ℝ F' :=
    (VectorBundle.modelEquiv (E := E ×ᵇ Trivial B F₀) (E' := Trivial B F') (F × F₀) F' b
      (φ b)).toLinearEquiv.finiteDimensional
  have h := totalChernClass_complexification_congr φ hφ
  rw [totalChernClass_complexification_prod, totalChernClass_complexification_trivial,
    totalChernClass_complexification_trivial, mul_one] at h
  exact h

end Bundle

end SymplecticGeometry

end
