/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.VectorBundle.Basic

/-!
# Fibres of line bundles

Let `E → B` be a vector bundle over a complete nontrivially normed field `𝕜` whose model fibre `F`
has dimension one. A nonzero vector `v` of a fibre `E x` spans it, and the map `c ↦ c • v` is a
continuous linear equivalence `𝕜 ≃L[𝕜] E x` (`VectorBundle.toSpanSingletonEquiv`). Read in the
trivialization at `x`, it is `c ↦ c • w` for a nonzero vector `w` of `F`, which is a linear
bijection since `F` has dimension one, and so a homeomorphism, its domain `𝕜` being
finite-dimensional. A nowhere-zero section of a line bundle over a set thus identifies the
bundle there with the trivial line bundle.

## Main definitions

* `VectorBundle.toSpanSingletonEquiv`: the map `c ↦ c • v` from the scalars to the fibre of a line
  bundle containing a nonzero vector `v`, as a continuous linear equivalence.
-/

public section

noncomputable section

open Bundle Module

namespace VectorBundle

variable {𝕜 B F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {E : B → Type*}
  [TopologicalSpace (TotalSpace F E)] [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]
  [∀ x, TopologicalSpace (E x)] [FiberBundle F E] [VectorBundle 𝕜 F E]

variable (F) in
/-- For a nonzero vector `v` of a fibre of a vector bundle of rank one, the map `c ↦ c • v`, as a
continuous linear equivalence from the scalars onto the fibre. -/
def toSpanSingletonEquiv (hF : finrank 𝕜 F = 1) {x : B} (v : E x) (hv : v ≠ 0) : 𝕜 ≃L[𝕜] E x :=
  let e := (trivializationAt F E x).continuousLinearEquivAt 𝕜 x
    (FiberBundle.mem_baseSet_trivializationAt' x)
  (LinearEquiv.ofBijective (LinearMap.toSpanSingleton 𝕜 F (e v))
    ⟨smul_left_injective 𝕜 ((map_ne_zero_iff _ e.injective).2 hv),
      (finrank_eq_one_iff_of_ne_zero' _ ((map_ne_zero_iff _ e.injective).2 hv)).1 hF⟩
    ).toContinuousLinearEquiv.trans e.symm

variable (F) in
@[simp]
theorem toSpanSingletonEquiv_apply (hF : finrank 𝕜 F = 1) {x : B} (v : E x) (hv : v ≠ 0)
    (c : 𝕜) : toSpanSingletonEquiv F hF v hv c = c • v := by
  simp [toSpanSingletonEquiv, Trivialization.symm_apply_apply_mk _
    (FiberBundle.mem_baseSet_trivializationAt' x)]

end VectorBundle
