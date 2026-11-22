/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.VectorBundle.Complement

/-!
# The left inverse of a fibrewise embedding into a trivial bundle

Let `j b : E b → V` be a fibrewise injection of a finite-rank vector bundle into a
finite-dimensional inner product space, continuous on the total space. Tau Ceti's
`TauCeti.bundleComplementFiberEquiv` splits `V` as the image of `E b` plus its orthogonal
complement. Its inverse followed by the first projection sends `u ∈ V` to the vector of `E b`
whose image is the orthogonal projection of `u` onto the image of `E b`
(`TauCeti.bundleComplementFiberEquiv_symm_apply_fst`). This file shows that this left inverse of
`j` is continuous as a map from `B × V` to the total space of `E`, a consequence of the
continuity of the inverse of Tau Ceti's `TauCeti.bundleComplementHomeomorph`.

## Main results

* `TauCeti.continuous_bundleComplementFiberEquiv_symm_fst`: `(b, u) ↦ j_b⁻¹ (P_{j(E_b)} u)` is
  continuous from `B × V` to the total space of `E`.

## References

* A. Hatcher, *Vector Bundles and K-Theory*, Proposition 1.4 (complements of subbundles of a
  trivial bundle).
-/

public section

open Bundle Function

namespace TauCeti

variable {𝕜 B F V : Type*} [RCLike 𝕜] [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]
  {E : B → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)]
  [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]
  [∀ x, IsTopologicalAddGroup (E x)] [∀ x, ContinuousSMul 𝕜 (E x)]
  (j : ∀ x, E x →L[𝕜] V) (hj : Continuous (fun p : TotalSpace F E ↦ j p.proj p.snd))
  (hinj : ∀ x, Injective (j x))

include hj in
/-- The left inverse `(b, u) ↦ j_b⁻¹ (P_{j(E_b)} u)` of a continuous fibrewise embedding `j` of
a finite-rank vector bundle into a finite-dimensional inner product space, the first component of
the inverse of `TauCeti.bundleComplementFiberEquiv`, is continuous from `B × V` to the total space
of `E`. -/
theorem continuous_bundleComplementFiberEquiv_symm_fst :
    Continuous fun q : B × V ↦
      TotalSpace.mk' F q.1 ((bundleComplementFiberEquiv (F := F) j hinj q.1).symm q.2).1 := by
  let := bundleComplementFiberBundle (F := F) j hj hinj
  have h := (FiberBundle.Prod.isInducing_diag F E
    (Fin (Module.finrank 𝕜 V - Module.finrank 𝕜 F) → 𝕜)
    (fun x ↦ (bundleComplementProjection (F := F) j x).range)).continuous.comp
      (bundleComplementHomeomorph (F := F) j hj hinj).symm.continuous
  refine (continuous_fst.comp h).congr fun q ↦ ?_
  exact congrArg (fun v ↦ TotalSpace.mk' F v.proj v.snd.1)
    (bundleComplementHomeomorph_symm_apply (F := F) j hj hinj q)

end TauCeti

end
