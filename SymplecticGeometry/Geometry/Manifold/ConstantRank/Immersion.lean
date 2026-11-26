/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Immersion.Differential
public import TauCeti.Geometry.Manifold.Instances.Sigma
public import TauCeti.Geometry.Manifold.RegularValue.Rank
import SymplecticGeometry.Geometry.Manifold.ConstantRank.Factorization
import SymplecticGeometry.Geometry.Manifold.ContMDiff.Opens
import SymplecticGeometry.Geometry.Manifold.Immersion.Basic
import SymplecticGeometry.Geometry.Manifold.MFDeriv.Sigma
import SymplecticGeometry.Topology.Sets.Opens.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Opens

/-!
# A map of constant rank as an immersion

A `C^n` map `f : M → N` of constant rank `r`, from a second countable, boundaryless,
finite-dimensional manifold to a finite-dimensional boundaryless manifold, has the same range as
an immersion `ι : S → N` from a Hausdorff, second countable manifold `S` modelled on
`EuclideanSpace 𝕜 (Fin r)`, in any universe that contains that of `𝕜`, whose tangent images are
those of `f`. Near each point, `f` is a submersion onto an open set `U` of
`EuclideanSpace 𝕜 (Fin r)` followed by a map `g` on `U` with injective derivatives
(`ContMDiffOn.exists_comp_eq_of_mfderivRank_le`); countably many of these open sets cover `M`, and
`S` is their disjoint union `Σ i : ULift ℕ, U i`, with the charts of `ChartedSpace.sigma` and `ι`
given by the maps `g` on the pieces.

## Main results

* `ContMDiff.exists_isImmersion_range_eq_of_mfderivRank_eq`: the immersion `ι`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  Theorem 4.12 (the rank theorem).
-/

public section

open Set Function Manifold TopologicalSpace TauCeti TauCeti.Manifold
open scoped ContDiff Topology

universe u v

variable {𝕜 : Type u} {E F H G M N : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
  {J : ModelWithCorners 𝕜 F G} [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω} [IsManifold I n M] [IsManifold J n N]

/-- **A map of constant rank as an immersion.** Let `f : M → N` be `C^n`, `1 ≤ n`, of constant
rank `r`, with `M` second countable and `N` finite-dimensional. Then there are a
Hausdorff, second countable `C^n` manifold `S` modelled on `EuclideanSpace 𝕜 (Fin r)`, in any
universe that contains that of `𝕜`, and an immersion `ι : S → N` with the same range as `f`, whose
tangent images are tangent images of `f`: a property of a point of `N` and a subspace of its
tangent space that holds for each `f y` and the tangent image of `f` at `y` holds for each `ι z`
and the tangent image of `ι` at `z`. -/
theorem ContMDiff.exists_isImmersion_range_eq_of_mfderivRank_eq [FiniteDimensional 𝕜 F]
    [SecondCountableTopology M] {f : M → N} (hf : ContMDiff I J n f) (hn : 1 ≤ n)
    {r : ℕ} (hr : ∀ y, mfderivRank I J f y = r) :
    ∃ (S : Type (max u v)) (_ : TopologicalSpace S)
      (_ : ChartedSpace (EuclideanSpace 𝕜 (Fin r)) S),
      IsManifold 𝓘(𝕜, EuclideanSpace 𝕜 (Fin r)) n S ∧ T2Space S ∧ SecondCountableTopology S ∧
      ∃ ι : S → N, IsImmersion 𝓘(𝕜, EuclideanSpace 𝕜 (Fin r)) J n ι ∧ range ι = range f ∧
        ∀ P : (x : N) → Submodule 𝕜 (TangentSpace J x) → Prop,
          (∀ y, P (f y) (LinearMap.range (mfderiv I J f y).toLinearMap)) →
          ∀ z, P (ι z)
            (LinearMap.range (mfderiv 𝓘(𝕜, EuclideanSpace 𝕜 (Fin r)) J ι z).toLinearMap) := by
  have := FiniteDimensional.completeSpace 𝕜 F
  -- For an empty `M`, the source is an empty disjoint union.
  rcases isEmpty_or_nonempty M with hM | ⟨⟨x₀⟩⟩
  · refine ⟨Σ _ : ULift.{v} ℕ, (⊥ : Opens (EuclideanSpace 𝕜 (Fin r))), inferInstance,
      inferInstance, inferInstance, inferInstance, inferInstance, isEmptyElim,
      IsImmersion.of_isEmpty _ J n _, ?_,
      fun _ _ ↦ isEmptyElim⟩
    rw [range_eq_empty, range_eq_empty]
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  -- Near each point, `f` is `g x ∘ q x` on `V x`, with `q x` a submersion onto `U x`.
  have hfac (x : M) := by
    have h := hf.contMDiffOn.exists_comp_eq_of_mfderivRank_le isOpen_univ (mem_univ x) hn
      fun y _ ↦ ((hr y).trans (hr x).symm).le
    rw [hr x] at h
    exact h
  choose V U q g hV hxV _ hU hqV hgq hq hqs hg hgi using hfac
  -- Countably many of the `V x` cover `M`.
  obtain ⟨s, hs, hcover⟩ := TopologicalSpace.countable_cover_nhds fun x ↦ (hV x).mem_nhds (hxV x)
  have hsne : s.Nonempty := by
    obtain ⟨y, hy, -⟩ := mem_iUnion₂.1 (hcover ▸ mem_univ x₀ : x₀ ∈ ⋃ x ∈ s, V x)
    exact ⟨y, hy⟩
  obtain ⟨e₀, rfl⟩ := hs.exists_eq_range hsne
  let e : ULift.{v} ℕ → M := e₀ ∘ ULift.down
  have hcover' : ⋃ i, V (e i) = univ := by
    rw [biUnion_range] at hcover
    exact ULift.down_surjective.iUnion_comp (V ∘ e₀) |>.trans hcover
  -- The pieces of the source and the map on their disjoint union.
  let W (i : ULift.{v} ℕ) : Opens (EuclideanSpace 𝕜 (Fin r)) := ⟨U (e i), hU (e i)⟩
  let ι : (Σ i, W i) → N := fun z ↦ g (e z.1) z.2
  have hι (i : ULift.{v} ℕ) : ι ∘ Sigma.mk i = g (e i) ∘ Subtype.val := rfl
  have hgd (x : M) {u} (hu : u ∈ U x) :=
    ((hg x).mdifferentiableOn hn0).mdifferentiableAt ((hU x).mem_nhds hu)
  refine ⟨Σ i, W i, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    ι, ContMDiff.isImmersion_of_injective_mfderiv (fun ⟨i, u⟩ ↦ contMDiffAt_sigma_iff.2 ?_) hn
      fun ⟨i, u⟩ ↦ ?_, ?_, ?_⟩
  · rw [hι]
    exact contMDiff_subtype_iff.2 (hg (e i)) u
  · rw [mfderiv_sigma, hι, mfderiv_comp u (hgd (e i) u.property)
      ((contMDiff_subtypeVal (n := 1)).mdifferentiableAt one_ne_zero), mfderiv_subtype_val]
    exact (hgi (e i) u u.property).comp (tangentSpaceOpenEquiv u).injective
  · ext z
    constructor
    · rintro ⟨⟨i, u⟩, rfl⟩
      obtain ⟨y, hy, hyu⟩ := (hqV (e i)).symm.subset u.property
      exact ⟨y, (hgq _ y hy).symm.trans (congrArg (g (e i)) hyu)⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨i, hi⟩ := mem_iUnion.1 (hcover' ▸ mem_univ y : y ∈ ⋃ i, V (e i))
      exact ⟨⟨i, q (e i) y, (hqV (e i)).subset (mem_image_of_mem _ hi)⟩, hgq _ y hi⟩
  · intro P hP
    rintro ⟨i, u, hu⟩
    obtain ⟨y, hy, rfl⟩ := (hqV (e i)).symm.subset hu
    have hgqd : MDifferentiableAt I _ (q (e i)) y :=
      ((hq (e i)).mdifferentiableOn hn0).mdifferentiableAt ((hV _).mem_nhds hy)
    -- The tangent image of `ι` at the point is that of `g (e i) ∘ q (e i)` at `y`.
    have hrange : LinearMap.range (mfderiv 𝓘(𝕜, EuclideanSpace 𝕜 (Fin r)) J ι
          ⟨i, q (e i) y, hu⟩).toLinearMap =
        LinearMap.range (mfderiv I J (g (e i) ∘ q (e i)) y).toLinearMap := by
      rw [mfderiv_sigma, hι]
      refine (range_mfderiv_comp_subtype_val (U := W i) (f := g (e i)) ⟨q (e i) y, hu⟩).trans ?_
      rw [mfderiv_comp y (hgd _ hu) hgqd, ContinuousLinearMap.toLinearMap_comp]
      exact (LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.2 (hqs _ y hy))).symm
    have heq : g (e i) ∘ q (e i) =ᶠ[𝓝 y] f :=
      Filter.eventuallyEq_of_mem ((hV _).mem_nhds hy) (hgq _)
    have hfy : (g (e i) ∘ q (e i)) y = f y := hgq _ y hy
    -- `ι` at the point is `g (e i) (q (e i) y)` by definition; `generalize` below needs that form.
    change P ((g (e i) ∘ q (e i)) y) _
    rw [hrange, heq.mfderiv_eq]
    generalize (g (e i) ∘ q (e i)) y = X at hfy ⊢
    subst hfy
    convert hP y using 2
    ext w
    exact tangentSpaceCast_self _

end
