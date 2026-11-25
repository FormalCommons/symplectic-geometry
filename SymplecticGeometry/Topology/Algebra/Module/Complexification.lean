/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import TauCeti.Topology.Algebra.Module.Complexification

/-!
# Complexification of a product of vector spaces

For real vector spaces `W₁` and `W₂`, Mathlib's `TensorProduct.prodRight` identifies
`ℂ ⊗[ℝ] (W₁ × W₂)` with `(ℂ ⊗[ℝ] W₁) × (ℂ ⊗[ℝ] W₂)`. This file shows how it meets Tau Ceti's
real and imaginary parts `TauCeti.realPart` and `TauCeti.imaginaryPart`, and, for topological
vector spaces whose complexifications carry the complexification topology
(`TauCeti.IsComplexificationTopology`), upgrades it to a continuous complex-linear equivalence
`TauCeti.complexificationProdEquiv`.

## Main definitions

* `TauCeti.complexificationProdEquiv`: `ℂ ⊗[ℝ] (W₁ × W₂) ≃L[ℂ] (ℂ ⊗[ℝ] W₁) × (ℂ ⊗[ℝ] W₂)`.
-/

public section

noncomputable section

open scoped TensorProduct TauCeti.Complexification

namespace TauCeti

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
    rw [LinearEquiv.invFun_eq_symm]
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

end TauCeti

end
