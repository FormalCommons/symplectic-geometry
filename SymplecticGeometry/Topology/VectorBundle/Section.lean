/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import TauCeti.Topology.VectorBundle.Section
public import TauCeti.Topology.VectorBundle.Smul

/-!
# Pointwise continuity of fibrewise operations on maps into a vector bundle

Let `E → B` be a topological vector bundle and `X` a topological space. This file shows that the
fibrewise operations on maps `X → TotalSpace F E` preserve continuity at a point:

* `ContinuousAt.smul_totalSpace`: a map rescaled fibrewise by a scalar function, both continuous
  at a point, is continuous there. This is the pointwise form of Tau Ceti's
  `Continuous.smul_totalSpace`, and follows from the joint continuity of fibrewise scalar
  multiplication, `TauCeti.VectorBundle.continuous_smul`.
* `ContinuousAt.sum_totalSpace`: a finite fibrewise sum of maps over a common base map, each
  continuous at a point, is continuous there, provided the base map is (for the empty sum, which
  is the zero section along the base map). Its proof is adapted from Tau Ceti's
  `ContinuousAt.sum_section`, generalised from sections over the base itself to maps over a base
  map `b`: the same induction on the finite set, with the zero section along `b` in the empty
  case and Tau Ceti's `ContinuousAt.add_totalSpace` in the insert case.
-/

public section

open Bundle Topology Filter

variable {𝕜 B F X : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module 𝕜 (E b)] [∀ b, TopologicalSpace (E b)]
  [FiberBundle F E] [VectorBundle 𝕜 F E] [TopologicalSpace X]

/-- A map into the total space of a vector bundle, rescaled fibrewise by a scalar function, is
continuous at a point where both the map and the scalar function are. -/
theorem ContinuousAt.smul_totalSpace {c : X → 𝕜} {φ : X → TotalSpace F E} {x₀ : X}
    (hc : ContinuousAt c x₀) (hφ : ContinuousAt φ x₀) :
    ContinuousAt (fun x ↦ TotalSpace.mk' F (φ x).proj (c x • (φ x).snd)) x₀ :=
  (TauCeti.VectorBundle.continuous_smul 𝕜 F E).continuousAt.comp (hc.prodMk hφ)

variable (𝕜) in
include 𝕜 in
/-- A finite fibrewise sum of maps into the total space of a vector bundle over a common base
map `b`, each continuous at `x₀`, is continuous at `x₀` when `b` is. -/
theorem ContinuousAt.sum_totalSpace {ι : Type*} (T : Finset ι) {b : X → B}
    {s : ι → ∀ x, E (b x)} {x₀ : X} (hb : ContinuousAt b x₀)
    (hs : ∀ i ∈ T, ContinuousAt (fun x ↦ TotalSpace.mk' F (b x) (s i x)) x₀) :
    ContinuousAt (fun x ↦ TotalSpace.mk' F (b x) (∑ i ∈ T, s i x)) x₀ := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    -- `zeroSection F E (b x)` is `TotalSpace.mk' F (b x) 0` by definition.
    exact (Trivialization.continuous_zeroSection 𝕜 (F := F) (E := E)).continuousAt.comp hb
  | insert i T hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hs i (Finset.mem_insert_self i T)).add_totalSpace 𝕜
      (ih fun j hj ↦ hs j (Finset.mem_insert_of_mem hj))
