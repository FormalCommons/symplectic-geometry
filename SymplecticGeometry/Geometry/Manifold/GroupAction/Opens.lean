/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.GroupAction.Restrict
public import SymplecticGeometry.Topology.Algebra.GroupAction.InvariantCore
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic

/-!
# Smooth actions on invariant open sets

An action by `C^n` maps restricts along an equivariant smooth embedding
(`Manifold.IsSmoothEmbedding.contMDiffConstSMul`): if `i : Z → M` is a `C^n` embedding with
`i (γ • z) = f γ • i z`, and every `γ • ·` is `C^n` on `M`, then every `γ • ·` is `C^n` on
`Z`. This is the per-element counterpart of Tau Ceti's `Manifold.IsSmoothEmbedding.contMDiffSMul`,
and its proof takes the same steps.

Let `G` act on a manifold `M`, and let `U` be an open subset of `M` with an action of `G` for
which the inclusion `U → M` is equivariant, such as the restricted action on an invariant open set
(`TopologicalSpace.Opens.mulActionOfForallSMulMem`) or the action on the invariant core of an open
set under a compact group (`TopologicalSpace.Opens.invariantCore`). If the action on `M` is `C^n`,
so is the action on `U`, jointly or for each element, since the inclusion of an open set is a
smooth embedding (`Manifold.IsSmoothEmbedding.of_opens`). Tau Ceti's
`ContRepresentation.contMDiffConstSMul_mulActionOpens` is the case of a linear representation on
an invariant open subset of its space, and Tau Ceti's
`TopologicalSpace.Opens.contMDiffSMul_invariantCore` the joint case on an invariant core.

Pulling back along a smooth map keeps invariance of forms, one element at a time: if
`f : N → M` is smooth with `f (g • x) = g • f x` for some `g`, and a form on `M` is invariant
under `g • ·`, then its pullback to `N` is invariant under `g • ·` on `N`. Restricting to `U` is
the case of the inclusion.

Equivariance passes to Tau Ceti's `PartialDiffeomorph.liftOpens`: if `G` acts on open subsets
`U` and `V` with equivariant inclusions, the lift of a partial diffeomorphism from `U` to `V`
that is equivariant on its source is equivariant on its own source, and that source is invariant
when the source of the partial diffeomorphism is.

## Main results

* `Manifold.IsSmoothEmbedding.contMDiffConstSMul`: an action by `C^n` maps restricts to an
  action by `C^n` maps along an equivariant smooth embedding.
* `TopologicalSpace.Opens.contMDiffSMul_of_coe_smul`: a `C^n` action on `M` gives a `C^n` action
  on `U`.
* `TopologicalSpace.Opens.contMDiffConstSMul_of_coe_smul`: the same for actions by `C^n` maps.
* `TauCeti.SmoothForm.mpullback_smul_mpullback`: the pullback of an invariant form along an
  equivariant smooth map is invariant.
* `PartialDiffeomorph.liftOpens_smul`, `PartialDiffeomorph.smul_mem_liftOpens_source`: the
  lift of a partial diffeomorphism between open subsets that is equivariant on its source is
  equivariant on its source, with invariant source.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2013, Theorem 5.29
  (restricting the codomain of a smooth map to an embedded submanifold).
-/

public section

open Manifold
open scoped ContDiff Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] {n : ℕ∞ω}

namespace Manifold.IsSmoothEmbedding

/-- Let `i : Z → M` be a `C^n` embedding intertwining an action of `Γ'` on `Z` with an action of
`Γ` on `M` along a map `f : Γ' → Γ`. If every `γ • ·` is `C^n` on `M`, then every `γ • ·` is
`C^n` on `Z`. -/
theorem contMDiffConstSMul {Γ : Type*} [SMul Γ M] [ContMDiffConstSMul I' n Γ M]
    {EZ : Type*} [NormedAddCommGroup EZ] [NormedSpace 𝕜 EZ]
    {HZ : Type*} [TopologicalSpace HZ] {IZ : ModelWithCorners 𝕜 EZ HZ}
    {Z : Type*} [TopologicalSpace Z] [ChartedSpace HZ Z] {Γ' : Type*} [SMul Γ' Z]
    {i : Z → M} (hi : IsSmoothEmbedding IZ I' n i) (f : Γ' → Γ)
    (hsmul : ∀ (γ : Γ') (z : Z), i (γ • z) = f γ • i z) :
    ContMDiffConstSMul IZ n Γ' Z where
  contMDiff_const_smul γ := by
    have hcomp : (i ∘ fun z : Z ↦ γ • z) = fun z ↦ f γ • i z := funext (hsmul γ)
    exact hi.contMDiff_iff_comp.2 <|
      hcomp ▸ (contMDiff_const_smul (f γ)).comp hi.isImmersion.contMDiff

end Manifold.IsSmoothEmbedding

namespace TopologicalSpace.Opens

variable [IsManifold I' n M] {G : Type*} [TopologicalSpace G] [ChartedSpace H G] {U : Opens M}

/-- If `G` acts on an open set `U` so that the inclusion `U → M` is equivariant, and the action
of `G` on `M` is `C^n`, then the action of `G` on `U` is `C^n`. -/
theorem contMDiffSMul_of_coe_smul [SMul G M] [ContMDiffSMul I I' n G M] [SMul G U]
    (h : ∀ (g : G) (x : U), ((g • x : U) : M) = g • (x : M)) : ContMDiffSMul I I' n G U :=
  (IsSmoothEmbedding.of_opens U).contMDiffSMul contMDiff_id h

/-- If `Γ` acts on an open set `U` so that the inclusion `U → M` is equivariant, and every
`γ • ·` is `C^n` on `M`, then every `γ • ·` is `C^n` on `U`. -/
theorem contMDiffConstSMul_of_coe_smul {Γ : Type*} [SMul Γ M] [ContMDiffConstSMul I' n Γ M]
    [SMul Γ U] (h : ∀ (γ : Γ) (x : U), ((γ • x : U) : M) = γ • (x : M)) :
    ContMDiffConstSMul I' n Γ U :=
  (IsSmoothEmbedding.of_opens U).contMDiffConstSMul id h

variable [Monoid G] [MulAction G M] [CompactSpace G] [ContinuousSMul G M]

/-- An action of a compact group by `C^n` maps restricts to an action by `C^n` maps on the
invariant core of an open set. -/
instance [ContMDiffConstSMul I' n G M] : ContMDiffConstSMul I' n G (U.invariantCore G) :=
  contMDiffConstSMul_of_coe_smul (coe_smul_invariantCore U)

end TopologicalSpace.Opens

namespace PartialDiffeomorph

variable {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {H'' : Type*} [TopologicalSpace H''] {J : ModelWithCorners 𝕜 E'' H''}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H'' N] {G : Type*} [SMul G M] [SMul G N]
  {U : TopologicalSpace.Opens M} {V : TopologicalSpace.Opens N} [SMul G U] [SMul G V]
  (hcU : ∀ (g : G) (x : U), ((g • x : U) : M) = g • (x : M))
  (hcV : ∀ (g : G) (y : V), ((g • y : V) : N) = g • (y : N))
  (Φ : PartialDiffeomorph I' J U V n) (hU : Nonempty U) (hV : Nonempty V)

include hcU hcV in
/-- Let `G` act on open subsets `U` and `V` so that their inclusions are equivariant. If a partial
diffeomorphism `Φ` from `U` to `V` commutes with the actions of `G` at the points of its source,
then so does `Φ.liftOpens` at the points of its source. -/
theorem liftOpens_smul (hΦ : ∀ (g : G), ∀ x ∈ Φ.source, Φ (g • x) = g • Φ x) (g : G) :
    ∀ x ∈ (Φ.liftOpens hU hV).source,
      Φ.liftOpens hU hV (g • x) = g • Φ.liftOpens hU hV x := by
  rw [liftOpens_source]
  rintro _ ⟨y, hy, rfl⟩
  rw [← hcU, liftOpens_apply_coe, liftOpens_apply_coe, hΦ g y hy, hcV]

omit [SMul G N] [SMul G V] in
include hcU in
/-- Let `G` act on an open subset `U` so that its inclusion is equivariant. If the source of a
partial diffeomorphism `Φ` from `U` to `V` is invariant under `G`, so is the source of
`Φ.liftOpens`. -/
theorem smul_mem_liftOpens_source (hs : ∀ (g : G) (x : U), x ∈ Φ.source → g • x ∈ Φ.source)
    (g : G) {x : M} (hx : x ∈ (Φ.liftOpens hU hV).source) :
    g • x ∈ (Φ.liftOpens hU hV).source := by
  rw [liftOpens_source] at hx ⊢
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨g • y, hs g y hy, hcU g y⟩

end PartialDiffeomorph

namespace TauCeti.SmoothForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' ∞ N]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}
  {G : Type*} [SMul G M] [ContMDiffConstSMul I ∞ G M]

/-- Let `f : N → M` be a smooth map with `f (g • x) = g • f x` for one `g`, where every `g • ·`
is smooth on `M` and on `N`. If a smooth form `α` on `M` is invariant under pullback along `g • ·`,
then so is its pullback to `N` along `f`. -/
theorem mpullback_smul_mpullback [SMul G N] [ContMDiffConstSMul I' ∞ G N] {f : N → M}
    (hf : ContMDiff I' I ∞ f) {g : G} (h : ∀ x : N, f (g • x) = g • f x)
    {α : SmoothForm I M F k}
    (hα : mpullback (fun x : M ↦ g • x) (contMDiff_const_smul g) α = α) :
    mpullback (fun x : N ↦ g • x) (contMDiff_const_smul g) (mpullback f hf α) =
      mpullback f hf α := by
  rw [mpullback_mpullback_of_comp_eq _ _ hf (contMDiff_const_smul g) (funext h), hα]

end TauCeti.SmoothForm

end
