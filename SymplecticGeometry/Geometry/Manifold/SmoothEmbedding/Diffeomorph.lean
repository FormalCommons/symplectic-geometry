/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Immersion.Differential
import TauCeti.Geometry.Manifold.Diffeomorph.Basic
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Diffeomorph

/-!
# Reparametrising immersions and smooth embeddings across two models

Tau Ceti's `TauCeti.isImmersion_comp_diffeomorph`, `TauCeti.isSmoothEmbedding_comp_diffeomorph`
and `TauCeti.SmoothEmbedding.compDiffeomorph` reparametrise an immersion or a smooth embedding
`f : M → N` by a diffeomorphism `e : M' ≃ M` for which `M'` and `M` have the same model with
corners. This file allows `M'` and `M` to be modelled on different spaces, when the source `M'`
and the target `N` have no boundary and `N` has a finite-dimensional model: then being an
immersion is a condition on the differential alone, and the differential of `f ∘ e` is that of
`f` after the linear isomorphism `de`.

The proof of `TauCeti.isImmersion_comp_diffeomorph_of_boundaryless` follows that of Tau Ceti's
`Diffeomorph.isImmersion_comp`, which composes on the other side, with Tau Ceti's
`Diffeomorph.mfderiv_comp_diffeomorph_injective_iff` in place of the chain rule. The
bundled `TauCeti.SmoothEmbedding.compDiffeomorphOfBoundaryless` and its lemmas follow Tau Ceti's
`TauCeti.SmoothEmbedding.compDiffeomorph` and its lemmas; its differential and the range of that
differential come from Tau Ceti's `Diffeomorph.mfderiv_comp_diffeomorph` and
`Diffeomorph.range_mfderiv_comp_diffeomorph`.

## Main results

* `TauCeti.isImmersion_comp_diffeomorph_of_boundaryless`: precomposing an immersion with a
  diffeomorphism from a manifold on another model gives an immersion.
* `TauCeti.isSmoothEmbedding_comp_diffeomorph_of_boundaryless`: the same for smooth embeddings.
* `IsLocalDiffeomorph.isSmoothEmbedding`: an injective local diffeomorphism between boundaryless
  manifolds, with a finite-dimensional target model, is a smooth embedding.

## Main definitions

* `TauCeti.SmoothEmbedding.compDiffeomorphOfBoundaryless`: a bundled smooth embedding
  reparametrised by a diffeomorphism from a manifold on another model.

## References

* M. Hirsch, *Differential Topology*, Springer GTM 33 (1976), Chapter 1, for immersions and
  embeddings and their behaviour under composition.
-/

public section

noncomputable section

namespace TauCeti

open _root_.Manifold Set
open scoped _root_.Manifold ContDiff

variable {𝕜 : Type*} [RCLike 𝕜]
  {E E' E'' H H' G M M' N : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] [FiniteDimensional 𝕜 E'']
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'} {J : ModelWithCorners 𝕜 E'' G}
  [I'.Boundaryless] [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace M'] [ChartedSpace H' M']
  [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω} [IsManifold I' n M'] [IsManifold J n N] {f : M → N}

/-- Reparametrising a `C^n` immersion `f : M → N`, `1 ≤ n`, by a diffeomorphism `e : M' ≃ M`
gives an immersion `f ∘ e`, also when `M'` has a different model from `M`, provided `M'` and `N`
have no boundary and `N` has a finite-dimensional model. -/
theorem isImmersion_comp_diffeomorph_of_boundaryless (e : M' ≃ₘ^n⟮I', I⟯ M) (hn : 1 ≤ n)
    (h : IsImmersion I J n f) : IsImmersion I' J n (f ∘ e) := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  exact (h.contMDiff.comp e.contMDiff).isImmersion_of_injective_mfderiv hn fun x ↦
    (e.mfderiv_comp_diffeomorph_injective_iff hn0).2 (h.mfderiv_injective hn0 (e x))

/-- Reparametrising a `C^n` smooth embedding `f : M → N`, `1 ≤ n`, by a diffeomorphism
`e : M' ≃ M` gives a smooth embedding `f ∘ e`, also when `M'` has a different model from `M`,
provided `M'` and `N` have no boundary and `N` has a finite-dimensional model. -/
theorem isSmoothEmbedding_comp_diffeomorph_of_boundaryless (e : M' ≃ₘ^n⟮I', I⟯ M) (hn : 1 ≤ n)
    (h : IsSmoothEmbedding I J n f) : IsSmoothEmbedding I' J n (f ∘ e) :=
  ⟨isImmersion_comp_diffeomorph_of_boundaryless e hn h.isImmersion,
    h.isEmbedding.comp e.toHomeomorph.isEmbedding⟩

/-- **Injective local diffeomorphisms are smooth embeddings.** A `C^n` local diffeomorphism
`g : M' → N`, `1 ≤ n`, that is injective is a smooth embedding, when `M'` and `N` have no boundary
and `N` has a finite-dimensional model. -/
theorem _root_.IsLocalDiffeomorph.isSmoothEmbedding {g : M' → N}
    (hg : IsLocalDiffeomorph I' J n g) (hn : 1 ≤ n) (hinj : Function.Injective g) :
    IsSmoothEmbedding I' J n g := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  refine ⟨hg.contMDiff.isImmersion_of_injective_mfderiv hn fun x ↦ ?_,
    (Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap hg.contMDiff.continuous hinj
      hg.isOpenMap).isEmbedding⟩
  rw [← hg.mfderivToContinuousLinearEquiv_coe hn0 x]
  exact (hg.mfderivToContinuousLinearEquiv hn0 x).injective

namespace SmoothEmbedding

/-- **Reparametrisation across two models.** A `C^n` diffeomorphism `e : M' ≃ M`, `1 ≤ n`, turns
a bundled smooth embedding `f : M → N` into the bundled smooth embedding `f ∘ e : M' → N`, for a
boundaryless `M'` whose model may differ from that of `M`, and a boundaryless `N` with a
finite-dimensional model. -/
def compDiffeomorphOfBoundaryless (f : SmoothEmbedding I J n M N) (e : M' ≃ₘ^n⟮I', I⟯ M)
    (hn : 1 ≤ n) : SmoothEmbedding I' J n M' N :=
  SmoothEmbedding.ofIsSmoothEmbedding (f ∘ e)
    (isSmoothEmbedding_comp_diffeomorph_of_boundaryless e hn f.isSmoothEmbedding)

@[simp]
theorem compDiffeomorphOfBoundaryless_apply (f : SmoothEmbedding I J n M N)
    (e : M' ≃ₘ^n⟮I', I⟯ M) (hn : 1 ≤ n) (x : M') :
    f.compDiffeomorphOfBoundaryless e hn x = f (e x) := by
  simp only [compDiffeomorphOfBoundaryless, ofIsSmoothEmbedding_apply, Function.comp_apply]

@[simp]
theorem coe_compDiffeomorphOfBoundaryless (f : SmoothEmbedding I J n M N)
    (e : M' ≃ₘ^n⟮I', I⟯ M) (hn : 1 ≤ n) :
    ⇑(f.compDiffeomorphOfBoundaryless e hn) = f ∘ e :=
  funext (compDiffeomorphOfBoundaryless_apply f e hn)

/-- Reparametrisation does not move the image of an embedding. Not a `simp` lemma:
`coe_compDiffeomorphOfBoundaryless` rewrites its left-hand side. -/
theorem range_compDiffeomorphOfBoundaryless (f : SmoothEmbedding I J n M N)
    (e : M' ≃ₘ^n⟮I', I⟯ M) (hn : 1 ≤ n) :
    range (f.compDiffeomorphOfBoundaryless e hn) = range f := by
  rw [coe_compDiffeomorphOfBoundaryless]
  exact (EquivLike.surjective e).range_comp _

/-- **Chain rule for reparametrisation across two models.** The differential of
`f.compDiffeomorphOfBoundaryless e hn` at `x` is that of `f` at `e x` after that of `e` at `x`. -/
theorem mfderiv_compDiffeomorphOfBoundaryless (f : SmoothEmbedding I J n M N)
    (e : M' ≃ₘ^n⟮I', I⟯ M) (hn : 1 ≤ n) (x : M') :
    mfderiv I' J (f.compDiffeomorphOfBoundaryless e hn) x =
      (mfderiv I J f (e x)).comp (mfderiv I' I e x) := by
  rw [coe_compDiffeomorphOfBoundaryless]
  exact e.mfderiv_comp_diffeomorph (by rintro rfl; simp at hn) f x

/-- Reparametrisation across two models does not move the tangent image: the range of the
differential of `f.compDiffeomorphOfBoundaryless e hn` at `x` is that of the differential of `f`
at `e x`. -/
theorem range_mfderiv_compDiffeomorphOfBoundaryless (f : SmoothEmbedding I J n M N)
    (e : M' ≃ₘ^n⟮I', I⟯ M) (hn : 1 ≤ n) (x : M') :
    (mfderiv I' J (f.compDiffeomorphOfBoundaryless e hn) x).range =
      (mfderiv I J f (e x)).range := by
  rw [coe_compDiffeomorphOfBoundaryless]
  exact e.range_mfderiv_comp_diffeomorph (by rintro rfl; simp at hn) f x

/-- On a single boundaryless model, reparametrisation across two models is Tau Ceti's
`SmoothEmbedding.compDiffeomorph`. -/
theorem compDiffeomorphOfBoundaryless_eq_compDiffeomorph {X : Type*} [TopologicalSpace X]
    [ChartedSpace H X] [I.Boundaryless] [IsManifold I n X]
    (f : SmoothEmbedding I J n M N) (e : X ≃ₘ^n⟮I, I⟯ M) (hn : 1 ≤ n) :
    f.compDiffeomorphOfBoundaryless e hn = f.compDiffeomorph e :=
  SmoothEmbedding.ext fun x ↦ by simp

/-- Reparametrising twice across two models is reparametrising by the composite
diffeomorphism. -/
@[simp]
theorem compDiffeomorphOfBoundaryless_compDiffeomorphOfBoundaryless
    {F H'' M'' : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace H'']
    {I'' : ModelWithCorners 𝕜 F H''} [I''.Boundaryless]
    [TopologicalSpace M''] [ChartedSpace H'' M''] [IsManifold I'' n M'']
    (f : SmoothEmbedding I J n M N) (e : M' ≃ₘ^n⟮I', I⟯ M) (e' : M'' ≃ₘ^n⟮I'', I'⟯ M')
    (hn : 1 ≤ n) :
    (f.compDiffeomorphOfBoundaryless e hn).compDiffeomorphOfBoundaryless e' hn =
      f.compDiffeomorphOfBoundaryless (e'.trans e) hn :=
  SmoothEmbedding.ext fun x ↦ by simp

end SmoothEmbedding

end TauCeti

end
