/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Projection
public import SymplecticGeometry.LinearAlgebra.Range

/-!
# Extending an injective linear map to a linear equivalence

Let `i : F → V` and `j : F → W` be injective linear maps into finite-dimensional vector spaces of
the same dimension. Then some linear equivalence `A : V ≃ W` satisfies `A ∘ i = j`
(`LinearMap.exists_linearEquiv_comp_eq_of_injective`). It is built from complements of the two
ranges, which have the same dimension.
-/

public section

open Module

namespace LinearMap

variable {K V W F : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] [AddCommGroup W]
  [Module K W] [AddCommGroup F] [Module K F] [FiniteDimensional K V] [FiniteDimensional K W]

/-- An injective linear map `j : F → W` extends along an injective linear map `i : F → V`, into a
space of the same finite dimension, to a linear equivalence `A : V ≃ W` with `A ∘ i = j`. -/
theorem exists_linearEquiv_comp_eq_of_injective {i : F →ₗ[K] V} {j : F →ₗ[K] W}
    (hi : Function.Injective i) (hj : Function.Injective j)
    (h : finrank K V = finrank K W) : ∃ A : V ≃ₗ[K] W, A.toLinearMap ∘ₗ i = j := by
  obtain ⟨C, hC⟩ := (range i).exists_isCompl
  obtain ⟨N, hN⟩ := (range j).exists_isCompl
  have : FiniteDimensional K F := Module.Finite.of_injective i hi
  have hCN : finrank K C = finrank K N := by
    have h₁ := Submodule.finrank_add_eq_of_isCompl hC
    have h₂ := Submodule.finrank_add_eq_of_isCompl hN
    rw [finrank_range_of_inj hi] at h₁
    rw [finrank_range_of_inj hj] at h₂
    omega
  refine ⟨(Submodule.prodEquivOfIsCompl _ _ hC).symm.trans
    (((LinearEquiv.ofInjectiveRange i j hi hj).prodCongr (LinearEquiv.ofFinrankEq C N hCN)).trans
      (Submodule.prodEquivOfIsCompl _ _ hN)), ?_⟩
  ext s
  have hs : (Submodule.prodEquivOfIsCompl _ _ hC).symm (i s) =
      ((⟨i s, mem_range_self i s⟩ : range i), (0 : C)) :=
    Submodule.prodEquivOfIsCompl_symm_apply_left _ _ hC (⟨i s, mem_range_self i s⟩ : range i)
  simp [hs]

end LinearMap
