/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import TauCeti.Topology.VectorBundle.Complexification
public import SymplecticGeometry.Topology.VectorBundle.ModelEquiv
public import SymplecticGeometry.Topology.VectorBundle.Complex.ChernClass.Whitney

/-!
# Complexification of sums and trivial bundles

The complexification of a real vector bundle `E → B` with model fibre `F` is Tau Ceti's complex
vector bundle `fun x ↦ ℂ ⊗[ℝ] E x`, with model `TauCeti.Complexification F`, whose fibres carry
the topology of the scope `TauCeti.Complexification`. This file shows that complexification
commutes with the operations that the argument for the spheres needs:

* `complexificationProdEquiv`: for real topological vector spaces, `ℂ ⊗ (W₁ × W₂)` is
  `(ℂ ⊗ W₁) × (ℂ ⊗ W₂)`, continuously and complex-linearly;
* `continuous_baseChangeComplex_totalSpace`: a family of real-linear maps of fibres that is
  continuous on total spaces complexifies to one of complex-linear maps that is continuous too;
* `complexificationProdHomeomorph`: the complexification of `E₁ ×ᵇ E₂` is the direct sum of the
  complexifications;
* `complexificationTrivialHomeomorph`: the complexification of `Bundle.Trivial B F` is
  `Bundle.Trivial B (Complexification F)`;
* `complexificationMapHomeomorph`: an isomorphism of real vector bundles complexifies.

Each homeomorphism of total spaces covers the identity of the base and is complex-linear on each
fibre, as its `_apply` lemma shows. The continuity proofs follow Tau Ceti's
`TauCeti.complexificationTotalSpaceHomeomorphProd`, through
`TauCeti.continuous_complexification_totalSpace_iff`.

## Main results

* `Bundle.totalChernClass_complexification_trivial`: over a compact base, the complexification
  of a trivial bundle has total Chern class `1`.
* `Bundle.totalChernClass_complexification_eq_one`: over a compact base, if the sum of `E` with a
  trivial real bundle is trivial, then the total Chern class of the complexification of `E` is `1`.
  This is the Whitney sum formula `Bundle.totalChernClass_prod` with
  `Bundle.totalChernClass_trivial`.

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

/-! ### Complexification of a product of vector spaces -/

section Module

variable (W₁ W₂ : Type*) [AddCommGroup W₁] [Module ℝ W₁] [AddCommGroup W₂] [Module ℝ W₂]

/-- The real part of the first component of `TensorProduct.prodRight u` is the first component of
the real part of `u`. -/
@[simp]
theorem realPart_prodRight_fst (u : ℂ ⊗[ℝ] (W₁ × W₂)) :
    realPart W₁ (TensorProduct.prodRight ℝ ℂ ℂ W₁ W₂ u).1 = (realPart (W₁ × W₂) u).1 := by
  induction u using TensorProduct.inductionOn with
  | tmul c w => simp [realPart_tmul]
  | add u v hu hv => simp only [map_add, Prod.fst_add, hu, hv]

/-- The real part of the second component of `TensorProduct.prodRight u` is the second component of
the real part of `u`. -/
@[simp]
theorem realPart_prodRight_snd (u : ℂ ⊗[ℝ] (W₁ × W₂)) :
    realPart W₂ (TensorProduct.prodRight ℝ ℂ ℂ W₁ W₂ u).2 = (realPart (W₁ × W₂) u).2 := by
  induction u using TensorProduct.inductionOn with
  | tmul c w => simp [realPart_tmul]
  | add u v hu hv => simp only [map_add, Prod.snd_add, hu, hv]

/-- The imaginary part of the first component of `TensorProduct.prodRight u` is the first
component of the imaginary part of `u`. -/
@[simp]
theorem imaginaryPart_prodRight_fst (u : ℂ ⊗[ℝ] (W₁ × W₂)) :
    imaginaryPart W₁ (TensorProduct.prodRight ℝ ℂ ℂ W₁ W₂ u).1 = (imaginaryPart (W₁ × W₂) u).1 := by
  induction u using TensorProduct.inductionOn with
  | tmul c w => simp [imaginaryPart_tmul]
  | add u v hu hv => simp only [map_add, Prod.fst_add, hu, hv]

/-- The imaginary part of the second component of `TensorProduct.prodRight u` is the second
component of the imaginary part of `u`. -/
@[simp]
theorem imaginaryPart_prodRight_snd (u : ℂ ⊗[ℝ] (W₁ × W₂)) :
    imaginaryPart W₂ (TensorProduct.prodRight ℝ ℂ ℂ W₁ W₂ u).2 = (imaginaryPart (W₁ × W₂) u).2 := by
  induction u using TensorProduct.inductionOn with
  | tmul c w => simp [imaginaryPart_tmul]
  | add u v hu hv => simp only [map_add, Prod.snd_add, hu, hv]

/-- The real part of `(TensorProduct.prodRight ℝ ℂ ℂ W₁ W₂).symm p` is the pair of the real parts
of the components of `p`. -/
@[simp]
theorem realPart_prodRight_symm (p : (ℂ ⊗[ℝ] W₁) × (ℂ ⊗[ℝ] W₂)) :
    realPart (W₁ × W₂) ((TensorProduct.prodRight ℝ ℂ ℂ W₁ W₂).symm p) =
      (realPart W₁ p.1, realPart W₂ p.2) := by
  ext
  · rw [← realPart_prodRight_fst, LinearEquiv.apply_symm_apply]
  · rw [← realPart_prodRight_snd, LinearEquiv.apply_symm_apply]

/-- The imaginary part of `(TensorProduct.prodRight ℝ ℂ ℂ W₁ W₂).symm p` is the pair of the
imaginary parts of the components of `p`. -/
@[simp]
theorem imaginaryPart_prodRight_symm (p : (ℂ ⊗[ℝ] W₁) × (ℂ ⊗[ℝ] W₂)) :
    imaginaryPart (W₁ × W₂) ((TensorProduct.prodRight ℝ ℂ ℂ W₁ W₂).symm p) =
      (imaginaryPart W₁ p.1, imaginaryPart W₂ p.2) := by
  ext
  · rw [← imaginaryPart_prodRight_fst, LinearEquiv.apply_symm_apply]
  · rw [← imaginaryPart_prodRight_snd, LinearEquiv.apply_symm_apply]

variable [TopologicalSpace W₁] [TopologicalSpace W₂]
  [TopologicalSpace (ℂ ⊗[ℝ] W₁)] [IsComplexificationTopology W₁]
  [TopologicalSpace (ℂ ⊗[ℝ] W₂)] [IsComplexificationTopology W₂]
  [TopologicalSpace (ℂ ⊗[ℝ] (W₁ × W₂))] [IsComplexificationTopology (W₁ × W₂)]

/-- The complexification of a product of real topological vector spaces is the product of the
complexifications: `TensorProduct.prodRight` as a continuous `ℂ`-linear equivalence
`ℂ ⊗[ℝ] (W₁ × W₂) ≃L[ℂ] (ℂ ⊗[ℝ] W₁) × (ℂ ⊗[ℝ] W₂)`. -/
def complexificationProdEquiv : ℂ ⊗[ℝ] (W₁ × W₂) ≃L[ℂ] (ℂ ⊗[ℝ] W₁) × (ℂ ⊗[ℝ] W₂) where
  toLinearEquiv := TensorProduct.prodRight ℝ ℂ ℂ W₁ W₂
  continuous_toFun := by
    have hre := (realPartCLM (W₁ × W₂)).continuous
    have him := (imaginaryPartCLM (W₁ × W₂)).continuous
    have h₁ : Continuous fun u ↦ (TensorProduct.prodRight ℝ ℂ ℂ W₁ W₂ u).1 :=
      continuous_complexification_iff.2
        ⟨hre.fst.congr fun u ↦ by simp, him.fst.congr fun u ↦ by simp⟩
    have h₂ : Continuous fun u ↦ (TensorProduct.prodRight ℝ ℂ ℂ W₁ W₂ u).2 :=
      continuous_complexification_iff.2
        ⟨hre.snd.congr fun u ↦ by simp, him.snd.congr fun u ↦ by simp⟩
    exact h₁.prodMk h₂
  continuous_invFun := by
    suffices h : Continuous (TensorProduct.prodRight ℝ ℂ ℂ W₁ W₂).symm from h
    refine continuous_complexification_iff.2 ⟨?_, ?_⟩
    · exact (((realPartCLM W₁).continuous.comp continuous_fst).prodMk
        ((realPartCLM W₂).continuous.comp continuous_snd)).congr fun p ↦ by simp
    · exact (((imaginaryPartCLM W₁).continuous.comp continuous_fst).prodMk
        ((imaginaryPartCLM W₂).continuous.comp continuous_snd)).congr fun p ↦ by simp

@[simp]
theorem toLinearEquiv_complexificationProdEquiv :
    (complexificationProdEquiv W₁ W₂).toLinearEquiv = TensorProduct.prodRight ℝ ℂ ℂ W₁ W₂ :=
  (rfl)

@[simp]
theorem complexificationProdEquiv_apply (u : ℂ ⊗[ℝ] (W₁ × W₂)) :
    complexificationProdEquiv W₁ W₂ u = TensorProduct.prodRight ℝ ℂ ℂ W₁ W₂ u :=
  (rfl)

@[simp]
theorem complexificationProdEquiv_symm_apply (p : (ℂ ⊗[ℝ] W₁) × (ℂ ⊗[ℝ] W₂)) :
    (complexificationProdEquiv W₁ W₂).symm p = (TensorProduct.prodRight ℝ ℂ ℂ W₁ W₂).symm p :=
  (rfl)

end Module

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

variable (φ : ∀ b, E b ≃L[ℝ] E' b)
  (hφ : Continuous fun v : TotalSpace F E ↦ TotalSpace.mk' F' v.proj (φ v.proj v.snd))
  (hφ' : Continuous fun v : TotalSpace F' E' ↦ TotalSpace.mk' F v.proj ((φ v.proj).symm v.snd))

include hφ hφ'

/-- An isomorphism of real vector bundles, given by real-linear equivalences of fibres `φ b`
that are continuous on total spaces in both directions, complexifies: the homeomorphism of the
total spaces of the complexifications given on each fibre by the complex-linear equivalence
`(φ b).baseChangeComplex`. -/
def complexificationMapHomeomorph :
    TotalSpace (Complexification F) (fun b ↦ ℂ ⊗[ℝ] E b) ≃ₜ
      TotalSpace (Complexification F') (fun b ↦ ℂ ⊗[ℝ] E' b) where
  toFun v := ⟨v.proj, (φ v.proj).baseChangeComplex v.snd⟩
  invFun v := ⟨v.proj, (φ v.proj).symm.baseChangeComplex v.snd⟩
  left_inv v := by simp [← ContinuousLinearEquiv.baseChangeComplex_symm]
  right_inv v := by simp [← ContinuousLinearEquiv.baseChangeComplex_symm]
  continuous_toFun := continuous_baseChangeComplex_totalSpace_equiv hφ
  continuous_invFun := continuous_baseChangeComplex_totalSpace_equiv (φ := fun b ↦ (φ b).symm) hφ'

@[simp]
theorem complexificationMapHomeomorph_apply
    (v : TotalSpace (Complexification F) fun b ↦ ℂ ⊗[ℝ] E b) :
    complexificationMapHomeomorph φ hφ hφ' v = ⟨v.proj, (φ v.proj).baseChangeComplex v.snd⟩ :=
  (rfl)

@[simp]
theorem complexificationMapHomeomorph_symm_apply
    (v : TotalSpace (Complexification F') fun b ↦ ℂ ⊗[ℝ] E' b) :
    (complexificationMapHomeomorph φ hφ hφ').symm v =
      ⟨v.proj, (φ v.proj).symm.baseChangeComplex v.snd⟩ :=
  (rfl)

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

variable (F₁ E₁ F₂ E₂) in
/-- The complexification of a direct sum `E₁ ×ᵇ E₂` of real vector bundles is the direct sum of
the complexifications: the homeomorphism of total spaces given on each fibre by the
complex-linear equivalence `complexificationProdEquiv`. -/
def complexificationProdHomeomorph :
    TotalSpace (Complexification (F₁ × F₂)) (fun x ↦ ℂ ⊗[ℝ] (E₁ ×ᵇ E₂) x) ≃ₜ
      TotalSpace (Complexification F₁ × Complexification F₂)
        ((fun x ↦ ℂ ⊗[ℝ] E₁ x) ×ᵇ (fun x ↦ ℂ ⊗[ℝ] E₂ x)) where
  toFun v := ⟨v.proj, complexificationProdEquiv (E₁ v.proj) (E₂ v.proj) v.snd⟩
  invFun v := ⟨v.proj, (complexificationProdEquiv (E₁ v.proj) (E₂ v.proj)).symm v.snd⟩
  left_inv v := by simp
  right_inv v := by simp
  continuous_toFun := by
    rw [(FiberBundle.Prod.isInducing_diag _ _ _ _).continuous_iff, Function.comp_def,
      continuous_prodMk]
    obtain ⟨hre, him⟩ := (continuous_complexification_totalSpace_iff (F := F₁ × F₂)
      (E := E₁ ×ᵇ E₂)).1 continuous_id
    have hre' := (FiberBundle.Prod.isInducing_diag _ _ _ _).continuous.comp hre
    have him' := (FiberBundle.Prod.isInducing_diag _ _ _ _).continuous.comp him
    simp only [Function.comp_def] at hre' him'
    constructor <;> refine (continuous_complexification_totalSpace_iff).2 ⟨?_, ?_⟩
    · exact hre'.fst.congr fun v ↦ by simp
    · exact him'.fst.congr fun v ↦ by simp
    · exact hre'.snd.congr fun v ↦ by simp
    · exact him'.snd.congr fun v ↦ by simp
  continuous_invFun := by
    have h := FiberBundle.Prod.isInducing_diag (F₁ := Complexification F₁)
      (E₁ := fun x ↦ ℂ ⊗[ℝ] E₁ x) (F₂ := Complexification F₂) (E₂ := fun x ↦ ℂ ⊗[ℝ] E₂ x)
      |>.continuous
    obtain ⟨hre₁, him₁⟩ := (continuous_complexification_totalSpace_iff (F := F₁)
      (E := E₁)).1 (continuous_fst.comp h)
    obtain ⟨hre₂, him₂⟩ := (continuous_complexification_totalSpace_iff (F := F₂)
      (E := E₂)).1 (continuous_snd.comp h)
    refine (continuous_complexification_totalSpace_iff).2 ⟨?_, ?_⟩ <;>
      refine (FiberBundle.Prod.isInducing_diag _ _ _ _).continuous_iff.2 ?_ <;>
      simp only [Function.comp_def]
    · exact (hre₁.prodMk hre₂).congr fun v ↦ by simp
    · exact (him₁.prodMk him₂).congr fun v ↦ by simp

@[simp]
theorem complexificationProdHomeomorph_apply
    (v : TotalSpace (Complexification (F₁ × F₂)) fun x ↦ ℂ ⊗[ℝ] (E₁ ×ᵇ E₂) x) :
    complexificationProdHomeomorph F₁ E₁ F₂ E₂ v =
      ⟨v.proj, complexificationProdEquiv (E₁ v.proj) (E₂ v.proj) v.snd⟩ :=
  (rfl)

@[simp]
theorem complexificationProdHomeomorph_symm_apply
    (v : TotalSpace (Complexification F₁ × Complexification F₂)
      ((fun x ↦ ℂ ⊗[ℝ] E₁ x) ×ᵇ (fun x ↦ ℂ ⊗[ℝ] E₂ x))) :
    (complexificationProdHomeomorph F₁ E₁ F₂ E₂).symm v =
      ⟨v.proj, (complexificationProdEquiv (E₁ v.proj) (E₂ v.proj)).symm v.snd⟩ :=
  (rfl)

end Prod

/-! ### Complexification of a trivial bundle -/

section Trivial

variable (B : Type*) [TopologicalSpace B] (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The complexification of the trivial bundle `Bundle.Trivial B F` is the trivial bundle
`Bundle.Trivial B (Complexification F)`: the homeomorphism of total spaces given on each fibre
by the complex-linear equivalence `tensorContinuousLinearEquivComplexification F`. -/
def complexificationTrivialHomeomorph :
    TotalSpace (Complexification F) (fun x ↦ ℂ ⊗[ℝ] Trivial B F x) ≃ₜ
      TotalSpace (Complexification F) (Trivial B (Complexification F)) where
  toFun v := ⟨v.proj, tensorContinuousLinearEquivComplexification F v.snd⟩
  invFun v := ⟨v.proj, (tensorContinuousLinearEquivComplexification F).symm v.snd⟩
  left_inv v := by simp
  right_inv v := by simp [Complexification.re_add_I_smul_im]
  continuous_toFun := by
    obtain ⟨hre, him⟩ := (continuous_complexification_totalSpace_iff (F := F)
      (E := Trivial B F)).1 continuous_id
    have hre' := (Trivial.homeomorphProd B F).continuous.comp hre
    have him' := (Trivial.homeomorphProd B F).continuous.comp him
    refine (Trivial.homeomorphProd B (Complexification F)).isInducing.continuous_iff.2 ?_
    refine continuous_prodMk.2 ⟨FiberBundle.continuous_proj _ _, ?_⟩
    refine (Complexification.equivProd F).toHomeomorph.isInducing.continuous_iff.2 ?_
    refine (hre'.snd.prodMk him'.snd).congr fun v ↦ ?_
    simp [Trivial.homeomorphProd]
  continuous_invFun := by
    have h := (Trivial.homeomorphProd B (Complexification F)).continuous
    have hz := (Complexification.equivProd F).continuous.comp h.snd
    refine (continuous_complexification_totalSpace_iff (F := F) (E := Trivial B F)).2 ⟨?_, ?_⟩ <;>
      refine (Trivial.homeomorphProd B F).isInducing.continuous_iff.2
        (continuous_prodMk.2 ⟨FiberBundle.continuous_proj _ _, ?_⟩)
    · exact hz.fst.congr fun v ↦ by simp [Trivial.homeomorphProd]
    · exact hz.snd.congr fun v ↦ by simp [Trivial.homeomorphProd]

@[simp]
theorem complexificationTrivialHomeomorph_apply
    (v : TotalSpace (Complexification F) fun x ↦ ℂ ⊗[ℝ] Trivial B F x) :
    complexificationTrivialHomeomorph B F v =
      ⟨v.proj, tensorContinuousLinearEquivComplexification F v.snd⟩ :=
  (rfl)

@[simp]
theorem complexificationTrivialHomeomorph_symm_apply
    (v : TotalSpace (Complexification F) (Trivial B (Complexification F))) :
    (complexificationTrivialHomeomorph B F).symm v =
      ⟨v.proj, (tensorContinuousLinearEquivComplexification F).symm v.snd⟩ :=
  (rfl)

end Trivial

/-! ### Chern classes of the complexification of a stably trivial bundle -/

namespace Bundle

variable {B : Type} [TopologicalSpace B] [CompactSpace B]

/-- The total Chern class of the complexification of a trivial real bundle is `1`, over a
compact base. -/
theorem totalChernClass_complexification_trivial (F : Type) [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] :
    totalChernClass (Complexification F) (fun x ↦ ℂ ⊗[ℝ] Trivial B F x) = 1 := by
  rw [totalChernClass_congr (fun _ ↦ tensorContinuousLinearEquivComplexification F)
    ((complexificationTrivialHomeomorph B F).continuous.congr
      (complexificationTrivialHomeomorph_apply B F)),
    totalChernClass_trivial]

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {E : B → Type} [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
  [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)] [FiberBundle F E]
  [VectorBundle ℝ F E]

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
  have hsum := totalChernClass_congr
    (fun x ↦ complexificationProdEquiv (E x) (Trivial B F₀ x))
    ((complexificationProdHomeomorph F E F₀ (Trivial B F₀)).continuous.congr
      complexificationProdHomeomorph_apply)
  have htriv := totalChernClass_congr (fun x ↦ (φ x).baseChangeComplex)
    (continuous_baseChangeComplex_totalSpace_equiv hφ)
  rw [totalChernClass_prod, totalChernClass_complexification_trivial, mul_one] at hsum
  rw [← hsum, htriv, totalChernClass_complexification_trivial]

end Bundle

end SymplecticGeometry

end
