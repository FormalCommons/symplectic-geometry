/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.GroupAction.Restrict
public import SymplecticGeometry.Topology.Algebra.GroupAction.InvariantCore
import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic

/-!
# Smooth actions on invariant open sets

Let `G` act on a manifold `M`, and let `U` be an open subset of `M` with an action of `G` for
which the inclusion `U → M` is equivariant, such as the restricted action on an invariant open set
(`TopologicalSpace.Opens.mulActionOfForallSMulMem`) or the action on the invariant core of an open
set under a compact group (`TopologicalSpace.Opens.invariantCore`). If the action on `M` is `C^n`,
so is the action on `U`, jointly or for each element: the inclusion of an open set is a smooth
embedding (`Manifold.IsSmoothEmbedding.of_opens`), and a map into a smoothly embedded manifold is
`C^n` once its composite with the embedding is (Tau Ceti's
`Manifold.IsSmoothEmbedding.contMDiffSMul` and `Manifold.IsSmoothEmbedding.contMDiff_iff_comp`).
Tau Ceti's `ContRepresentation.contMDiffConstSMul_mulActionOpens` is the case of a linear
representation on an invariant open subset of its space, and its proof is adapted here.

Restricting a form to `U` keeps invariance: the restriction of a form on `M` invariant under every
`g • ·` is invariant under every `g • ·` on `U`.

## Main results

* `TopologicalSpace.Opens.contMDiffSMul_of_coe_smul`: a `C^n` action on `M` gives a `C^n` action
  on `U`.
* `TopologicalSpace.Opens.contMDiffConstSMul_of_coe_smul`: the same for actions by `C^n` maps.
* `TauCeti.SmoothForm.mpullback_smul_mpullback_subtypeVal`: the restriction of an invariant form
  to `U` is invariant.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2013, Theorem 5.29
  (restricting the codomain of a smooth map to an embedded submanifold).
-/

public section

open Manifold
open scoped ContDiff Manifold

namespace TopologicalSpace.Opens

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] {n : ℕ∞ω} [IsManifold I' n M]
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] {U : Opens M}

/-- If `G` acts on an open set `U` so that the inclusion `U → M` is equivariant, and the action
of `G` on `M` is `C^n`, then the action of `G` on `U` is `C^n`. -/
theorem contMDiffSMul_of_coe_smul [SMul G M] [ContMDiffSMul I I' n G M] [SMul G U]
    (h : ∀ (g : G) (x : U), ((g • x : U) : M) = g • (x : M)) : ContMDiffSMul I I' n G U :=
  (IsSmoothEmbedding.of_opens U).contMDiffSMul contMDiff_id h

/-- If `Γ` acts on an open set `U` so that the inclusion `U → M` is equivariant, and every
`γ • ·` is `C^n` on `M`, then every `γ • ·` is `C^n` on `U`. -/
theorem contMDiffConstSMul_of_coe_smul {Γ : Type*} [SMul Γ M] [ContMDiffConstSMul I' n Γ M]
    [SMul Γ U] (h : ∀ (γ : Γ) (x : U), ((γ • x : U) : M) = γ • (x : M)) :
    ContMDiffConstSMul I' n Γ U where
  contMDiff_const_smul γ := by
    rw [(IsSmoothEmbedding.of_opens (I := I') (n := n) U).contMDiff_iff_comp]
    have hcomp : (Subtype.val ∘ fun x : U ↦ γ • x) = fun x : U ↦ γ • (x : M) := funext (h γ)
    exact hcomp ▸ (contMDiff_const_smul γ).comp contMDiff_subtypeVal

variable [Monoid G] [MulAction G M] [CompactSpace G] [ContinuousSMul G M]

/-- A `C^n` action of a compact group restricts to a `C^n` action on the invariant core of an
open set. -/
instance [ContMDiffSMul I I' n G M] : ContMDiffSMul I I' n G (U.invariantCore G) :=
  contMDiffSMul_of_coe_smul coe_smul_invariantCore

/-- An action of a compact group by `C^n` maps restricts to an action by `C^n` maps on the
invariant core of an open set. -/
instance [ContMDiffConstSMul I' n G M] : ContMDiffConstSMul I' n G (U.invariantCore G) :=
  contMDiffConstSMul_of_coe_smul coe_smul_invariantCore

end TopologicalSpace.Opens

namespace TauCeti.SmoothForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}
  {G : Type*} [SMul G M] [ContMDiffConstSMul I ∞ G M] {U : TopologicalSpace.Opens M} [SMul G U]

/-- If `G` acts on an open set `U` so that the inclusion `U → M` is equivariant, and every
`g • ·` is smooth on `M`, then the restriction to `U` of a smooth form `α` on `M` invariant under
every `g • ·` is invariant under every `g • ·` on `U`. -/
theorem mpullback_smul_mpullback_subtypeVal
    (h : ∀ (g : G) (x : U), ((g • x : U) : M) = g • (x : M)) {α : SmoothForm I M F k}
    (hα : ∀ g : G, TauCeti.mpullback (F := F) I I (g • ·) α.val = α.val) (g : G) :
    TauCeti.mpullback (F := F) I I (g • ·)
        (mpullback (Subtype.val : U → M) contMDiff_subtypeVal α).val =
      (mpullback (Subtype.val : U → M) contMDiff_subtypeVal α).val := by
  have hU : ContMDiffConstSMul I ∞ G U :=
    TopologicalSpace.Opens.contMDiffConstSMul_of_coe_smul h
  have hcomp : (Subtype.val ∘ fun x : U ↦ g • x) = (fun x : M ↦ g • x) ∘ Subtype.val :=
    funext (h g)
  have hval : MDifferentiable I I (Subtype.val : U → M) :=
    (contMDiff_subtypeVal (n := ∞)).mdifferentiable (by simp)
  have hgM : MDifferentiable I I (fun x : M ↦ g • x) :=
    (contMDiff_const_smul (n := ∞) g).mdifferentiable (by simp)
  have hgU : MDifferentiable I I (fun x : U ↦ g • x) :=
    (contMDiff_const_smul (n := ∞) g).mdifferentiable (by simp)
  rw [coe_mpullback, ← TauCeti.mpullback_comp hgU hval, hcomp,
    TauCeti.mpullback_comp hval hgM, hα g]

end TauCeti.SmoothForm

end
