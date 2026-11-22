/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Equiv
public import TauCeti.Topology.VectorBundle.Smul

/-!
# The total space of a real vector bundle is homotopy equivalent to the base

This file is a part of Tau Ceti's file `TauCeti/Topology/VectorBundle/Smul.lean`, copied from Tau
Ceti's main branch at commit `aa1b4e9e2a`, which the pinned version of Tau Ceti does not yet have.
It contains only `TauCeti.VectorBundle.totalSpaceHomotopyEquiv` and its two coercion lemmas; the
rest of Tau Ceti's file is in the pinned version, which this file imports. The code is unchanged.

Scaling every vector by `t ∈ [0, 1]` contracts the total space of a real vector bundle onto its
zero section, so the projection is a homotopy equivalence with homotopy inverse the zero section
(`TauCeti.VectorBundle.totalSpaceHomotopyEquiv`).
-/

public section

open Bundle Topology Filter

namespace TauCeti.VectorBundle

open scoped ContinuousMap

variable {B F : Type*} [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace ℝ F]
  (E : B → Type*) [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]

variable (F) in
/-- **The total space of a real vector bundle is homotopy equivalent to the base**: the projection
`E → B` is a homotopy equivalence, with homotopy inverse the zero section. The homotopy from the
projection followed by the zero section to the identity of `E` is the fibrewise scaling
`(t, v) ↦ t • v`. -/
def totalSpaceHomotopyEquiv : TotalSpace F E ≃ₕ B where
  toFun := ⟨π F E, FiberBundle.continuous_proj F E⟩
  invFun := ⟨zeroSection F E, Trivialization.continuous_zeroSection ℝ⟩
  left_inv := ⟨{
    toFun := fun p ↦ TotalSpace.mk' F p.2.proj ((p.1 : ℝ) • p.2.snd)
    continuous_toFun :=
      (continuous_subtypeVal.comp continuous_fst).smul_totalSpace continuous_snd
    map_zero_left := fun v ↦ congrArg (TotalSpace.mk' F v.proj) (zero_smul ℝ v.snd)
    map_one_left := fun v ↦ congrArg (TotalSpace.mk' F v.proj) (one_smul ℝ v.snd) }⟩
  right_inv := ⟨ContinuousMap.Homotopy.refl _⟩

variable (F) in
@[simp]
theorem coe_totalSpaceHomotopyEquiv : ⇑(totalSpaceHomotopyEquiv F E) = π F E :=
  (rfl)

variable (F) in
@[simp]
theorem coe_totalSpaceHomotopyEquiv_symm :
    ⇑(totalSpaceHomotopyEquiv F E).symm = zeroSection F E :=
  (rfl)

end TauCeti.VectorBundle
