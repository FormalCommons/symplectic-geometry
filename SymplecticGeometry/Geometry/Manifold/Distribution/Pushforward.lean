/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import TauCeti.Geometry.Manifold.Distribution
public import TauCeti.Geometry.Manifold.Submersion.Basic

/-!
# Push-forward of a distribution along a surjective submersion

Let `q : N → M` be a `C^m` map, `D` a distribution on `N`, `D'` one on `M`, and `σ` a local
section of `q` over a set `V`. If `dq_{σ y}` maps `D (σ y)` injectively onto `D' y` wherever `σ y`
lies in the domain of a local frame `X` of `D`, then `X` pushes forward to the vector fields
`y ↦ dq_{σ y} (X i (σ y))`, which form a local frame of `D'` on the part of `V` that `σ` maps
into the domain of `X`. Such fields are `C^n` when `σ` is `C^n` and `n + 1 ≤ m`,
since they are the tangent map of `q` composed with the section `X i ∘ σ` of the tangent bundle.

A surjective submersion with boundaryless source has local sections near every point of its
target (`Manifold.IsSubmersion.exists_contMDiffOn_section_of_surjective`), so `D'` is then a
`C^n` distribution of the same rank as `D`.

This is the counterpart for submersions of Tau Ceti's
`TauCeti.IsContMDiffDistribution.comap_mfderiv`, which transports a distribution through a
diffeomorphism.

## Main results

* `TauCeti.IsDistributionFrameOn.map_mfderiv_comp_section`: the push-forward of a local frame of
  `D` along a local section of `q` is a local frame of `D'`.
* `TauCeti.IsContMDiffDistribution.map_mfderiv_of_isSubmersion`: the push-forward of a `C^n`
  distribution `D` of rank `k` along a surjective `C^m` submersion `q`, `n + 1 ≤ m`, whose
  differential maps each `D z` injectively onto `D' (q z)`, is a `C^n` distribution of rank `k`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  Theorem 4.26 (local sections of submersions) and Lemma 10.32 (local frames).
-/

public section

open Set Function Bundle Manifold
open scoped Manifold ContDiff

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I 1 N]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold J 1 M]
  {n m : ℕ∞ω} {k : ℕ} {ι : Type*}
  {D : Π z : N, Submodule 𝕜 (TangentSpace I z)} {D' : Π y : M, Submodule 𝕜 (TangentSpace J y)}
  {q : N → M}

/-- Let `q` be a `C^m` map, `σ` a `C^n` section of `q` over `V` with `n + 1 ≤ m`, and `X` a `C^n`
local frame of `D` on `U`. If, at every `y ∈ V ∩ σ ⁻¹' U`, the differential of `q` at `σ y` carries
`D (σ y)` injectively onto `D' y`, then the vector fields `y ↦ dq_{σ y} (X i (σ y))` form a `C^n`
local frame of `D'` on `V ∩ σ ⁻¹' U`. -/
theorem IsDistributionFrameOn.map_mfderiv_comp_section {X : ι → Π z : N, TangentSpace I z}
    {U : Set N} {V : Set M} {σ : M → N} (hX : IsDistributionFrameOn I n D X U)
    (hq : ContMDiff I J m q) (hnm : n + 1 ≤ m) (hσ : ContMDiffOn J I n σ V)
    (hqσ : ∀ y ∈ V, q (σ y) = y)
    (hmap : ∀ y ∈ V ∩ σ ⁻¹' U, (D (σ y)).map (mfderiv I J q (σ y)).toLinearMap = D' y)
    (hinj : ∀ y ∈ V ∩ σ ⁻¹' U, InjOn (mfderiv I J q (σ y)) (D (σ y))) :
    IsDistributionFrameOn J n D'
      (fun i y ↦ (mfderiv I J q (σ y) (X i (σ y)) : TangentSpace J y)) (V ∩ σ ⁻¹' U) := by
  refine ⟨fun i ↦ ?_, fun {y} hy ↦ ?_, fun {y} hy ↦ ?_⟩
  · have hT : ContMDiffOn J I.tangent n (fun y ↦ (⟨σ y, X i (σ y)⟩ : TangentBundle I N))
        (V ∩ σ ⁻¹' U) :=
      (hX.contMDiffOn i).comp (hσ.mono inter_subset_left) fun _ hy ↦ hy.2
    refine ((hq.contMDiff_tangentMap hnm).comp_contMDiffOn hT).congr fun y hy ↦ ?_
    exact (TotalSpace.mk_cast (hqσ y hy.1).symm _).symm
  · refine (hX.linearIndependent hy.2).map_injOn (mfderiv I J q (σ y)).toLinearMap ?_
    rw [hX.span_eq hy.2]
    exact hinj y hy
  · rw [← hmap y hy, ← hX.span_eq hy.2, Submodule.map_span, ← range_comp]
    -- Besides the coercion of `mfderiv` to a linear map, the sides differ in the fibre they are
    -- typed in, `TangentSpace J (q (σ y))` or `TangentSpace J y`. Both are `F` by definition,
    -- and `hqσ` cannot be rewritten inside a type, so this needs `rfl`.
    rfl

/-- **Push-forward of a distribution along a surjective submersion.** Let `q : N → M` be a
surjective `C^m` submersion with boundaryless source, `D` a `C^n` distribution of rank `k` on
`N` with `n + 1 ≤ m`, and `D'` a distribution on `M` such that, at every `z : N`, the differential
of `q` maps `D z` injectively onto `D' (q z)`. Then `D'` is a `C^n` distribution of rank `k`. -/
theorem IsContMDiffDistribution.map_mfderiv_of_isSubmersion [I.Boundaryless]
    (hD : IsContMDiffDistribution I n k D) (hq : IsSubmersion I J m q) (hsurj : Surjective q)
    (hnm : n + 1 ≤ m) (hmap : ∀ z, (D z).map (mfderiv I J q z).toLinearMap = D' (q z))
    (hinj : ∀ z, InjOn (mfderiv I J q z) (D z)) :
    IsContMDiffDistribution J n k D' := by
  rw [isContMDiffDistribution_iff] at hD ⊢
  intro y
  obtain ⟨V, hV, hyV, σ, hσ, hqσ⟩ := hq.exists_contMDiffOn_section_of_surjective hsurj y
  obtain ⟨U, hU, hσU, X, hX⟩ := hD (σ y)
  have hσn : ContMDiffOn J I n σ V := hσ.of_le (le_self_add.trans hnm)
  exact ⟨V ∩ σ ⁻¹' U, hσn.continuousOn.isOpen_inter_preimage hV hU, ⟨hyV, hσU⟩, _,
    hX.map_mfderiv_comp_section hq.contMDiff hnm hσn hqσ
      (fun y hy ↦ by have h := hmap (σ y); rwa [hqσ y hy.1] at h) (fun _ _ ↦ hinj _)⟩

end TauCeti

end
