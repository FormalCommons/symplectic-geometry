/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Moser.Field
public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Basic
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic
import SymplecticGeometry.Geometry.Diffeomorphism.Diffeotopy.Velocity
import SymplecticGeometry.Geometry.Manifold.TubularNeighborhood.OneFormCorrection
import SymplecticGeometry.Geometry.Symplectic.Manifold.Family
import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Flow
import TauCeti.Geometry.Manifold.PartitionOfUnity.Compact

/-!
# Moser's argument along a family and with a parameter

This file holds two forms of Moser's argument near a compact set: along a family of two-forms
running in the Moser time and fixing a compact submanifold, and for the segments
`ω₀ + s dβ_t`, `s ∈ [0, 1]`, for every value of a parameter `t`, relative to a compact set. Both
use the cut-off Moser field `SymplecticGeometry.moserField`.

## Moser's argument along a family

Let `σ` be a two-form and `γ` a one-form on `ℝ × M`, with slices `σ_t` and `γ_t`, such that for
`t ∈ [0, 1]` the slice `σ_t` is closed and `∂_t σ_t = dγ_t` near a compact set `K`. If `γ_t`
vanishes and `σ_t` is nondegenerate at the points of `K`, the flow from time `0` of the cut-off
Moser field `SymplecticGeometry.moserField σ γ ρ`, for a cutoff `ρ` on `ℝ × M` equal to `1` near
`[0, 1] × K`, is a compactly supported diffeotopy `Ψ` fixing `K` with `Ψ_t^* σ_t = σ_0` near `K`
for every `t ∈ [0, 1]`: Moser's equation holds where `ρ = 1`, and trajectories starting near `K`
stay there up to time `1`. For a compact embedded submanifold `f : Q → M` it is enough that
`f^* γ_t = 0`: the correction `γ_t - dφ_t` of
`TauCeti.SmoothEmbedding.exists_contMDiff_mextDeriv_eq_mpullback_prodMk` has the same exterior
derivative and vanishes at the points of `f(Q)`.

## Main results

* `TauCeti.SmoothForm.exists_diffeotopy_fix_eventually_mpullback_eq_of_timeDeriv`: Moser's
  argument along a family, relative to a compact set on which the primitives vanish.
* `TauCeti.SmoothEmbedding.exists_diffeotopy_fix_eventually_mpullback_eq_of_timeDeriv`: Moser's
  argument along a family, fixing a compact embedded submanifold to which the primitives pull
  back to `0`.

The proof of `TauCeti.SmoothForm.exists_diffeotopy_fix_eventually_mpullback_eq_of_timeDeriv`
adapts Tau Ceti's
`TauCeti.SmoothTwoForm.exists_diffeomorph_fix_eventually_mpullback_eq_of_mextDeriv_eq_sub`
(`TauCeti/Geometry/Symplectic/Manifold/RelativeMoser.lean`), whose trajectory argument it runs
for every time `t ∈ [0, 1]` along a general family instead of for time one along a
reparametrized segment.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §3.2
  (Moser's argument).
-/

public section

open Set TauCeti
open scoped Manifold ContDiff

namespace TauCeti.SmoothForm

open Filter SymplecticGeometry
open scoped Topology

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-- **Moser's argument along a family, relative to a compact set.** Let `σ` be a two-form and `γ`
a one-form on `ℝ × M`, `M` boundaryless and Hausdorff, with slices `σ_t` and `γ_t` at `t ∈ ℝ`.
Let `K ⊆ M` be compact, and suppose that for `t ∈ [0, 1]` the slice `σ_t` is closed, `σ_t` is
nondegenerate and `γ_t` vanishes at the points of `K`, and that `∂_t σ_t = dγ_t` near
`[0, 1] × K`. Then there is a diffeotopy `Ψ` which fixes every point outside a compact set at all
times, fixes every point of `K` at all times, and satisfies `Ψ_t^* σ_t = σ_0` for every
`t ∈ [0, 1]` on one neighbourhood of `K`. -/
theorem exists_diffeotopy_fix_eventually_mpullback_eq_of_timeDeriv
    (σ : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) ℝ 2)
    (hσ : ∀ t ∈ Icc (0 : ℝ) 1,
      (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) σ).IsClosed)
    (γ : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) ℝ 1) {K : Set M} (hK : IsCompact K)
    (hγ : ∀ᶠ p in 𝓝ˢ (Icc (0 : ℝ) 1 ×ˢ K),
      (SmoothForm.mpullback (Prod.mk p.1) (contMDiff_const.prodMk contMDiff_id)
          σ.timeDeriv).val p.2 =
        mextDeriv (SmoothForm.mpullback (Prod.mk p.1) (contMDiff_const.prodMk contMDiff_id)
          γ).val p.2)
    (hγK : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ K,
      (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) γ).val x = 0)
    (hnd : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ K,
      ((SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id)
        σ).bilinFormAt x).Nondegenerate) :
    ∃ Ψ : Diffeotopy I ∞ M, (∃ C, IsCompact C ∧ ∀ t, ∀ x ∉ C, Ψ (t, x) = x) ∧
      (∀ t, ∀ x ∈ K, Ψ (t, x) = x) ∧
      ∀ᶠ x in 𝓝ˢ K, ∀ t : unitInterval,
        (SmoothForm.mpullback (Ψ.timeSlice t) (Ψ.timeSlice t).contMDiff
          (SmoothForm.mpullback (Prod.mk (t : ℝ)) (contMDiff_const.prodMk contMDiff_id)
            σ)).val x =
          (SmoothForm.mpullback (Prod.mk 0) (contMDiff_const.prodMk contMDiff_id) σ).val x := by
  -- The points `(t, x)` at which `σ_t` is nondegenerate form an open set containing `[0, 1] × K`.
  set O := {p : ℝ × M | (SmoothTwoForm.flat
    (SmoothForm.mpullback (Prod.mk p.1) (contMDiff_const.prodMk contMDiff_id) σ)
      p.2).IsInvertible}
  have hO : IsOpen O := SmoothTwoForm.isOpen_setOf_isInvertible_flat_mpullback_prodMk σ
  have hKO : Icc (0 : ℝ) 1 ×ˢ K ⊆ O := fun p hp ↦
    SmoothTwoForm.isInvertible_flat_iff.2 (hnd _ hp.1 _ hp.2)
  obtain ⟨ρ, hρ, hρ1, hρc, hρO, -⟩ :=
    (isCompact_Icc.prod hK).exists_contMDiff_one_nhds_tsupport_subset (𝓘(ℝ, ℝ).prod I) hO hKO
  set X := moserField σ γ ρ
  have hX := contMDiff_moserField σ γ hρ fun p hp ↦ hρO hp
  have hX₁ := hX.of_le (m := 1) (by simp)
  set C := Prod.snd '' tsupport ρ
  have hC : IsCompact C := hρc.isCompact.image continuous_snd
  have hXC (u : ℝ) (y : M) (hy : y ∉ C) : X u y = 0 :=
    moserField_eq_zero_of_notMem_tsupport fun h ↦ hy ⟨_, h, rfl⟩
  have hc := isCompleteVectorField_timeDependentSuspensionField hX₁ hC hXC
  let Ψ := timeDependentFlowDiffeotopy (by simp) hX hc
  -- The flow from time `0` to a time `t ∈ [0, 1]` fixes `K`, where the field vanishes up to `t`.
  have hfix (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (x : M) (hx : x ∈ K) :
      timeDependentFlowOf X 0 t x = x :=
    timeDependentFlowOf_eq_self_of_forall_mem_uIcc_eq_zero hX₁ 0 t fun u hu ↦
      moserField_eq_zero_of_apply_eq_zero
        (hγK u (Icc_subset_Icc_right ht.2 ((uIcc_of_le ht.1).subset hu)) x hx)
  refine ⟨Ψ, ⟨C, hC, fun t x hx ↦ timeDependentFlowDiffeotopy_apply_of_forall_eq_zero _ _ _
    (fun u ↦ hXC u x hx) t⟩, fun t x hx ↦
    (timeDependentFlowDiffeotopy_apply _ _ _ _).trans (hfix t t.property x hx), ?_⟩
  -- `S`: the points near which `ρ = 1`, `σ_t` is nondegenerate and `∂_t σ_t = dγ_t`, where
  -- Moser's equation holds.
  set S := {p : ℝ × M | ∀ᶠ q in 𝓝 p, ρ q = 1 ∧ q ∈ O ∧
    (SmoothForm.mpullback (Prod.mk q.1) (contMDiff_const.prodMk contMDiff_id)
        σ.timeDeriv).val q.2 =
      mextDeriv (SmoothForm.mpullback (Prod.mk q.1) (contMDiff_const.prodMk contMDiff_id)
        γ).val q.2}
  have hOK : ∀ᶠ q in 𝓝ˢ (Icc (0 : ℝ) 1 ×ˢ K), q ∈ O := hO.mem_nhdsSet.2 hKO
  have hKS : Icc (0 : ℝ) 1 ×ˢ K ⊆ S :=
    eventually_nhdsSet_iff_forall.1 (hρ1.and (hOK.and hγ))
  -- The trajectories starting near `K` stay in `S` up to time `1`.
  have hφ : Continuous fun p : ℝ × M ↦ (p.1, timeDependentFlowOf X 0 p.1 p.2) :=
    continuous_fst.prodMk ((contMDiff_timeDependentFlowOf hc le_top hX).comp
      ((contMDiff_const.prodMk contMDiff_fst).prodMk contMDiff_snd)).continuous
  have hT : IsOpen {p : ℝ × M | (p.1, timeDependentFlowOf X 0 p.1 p.2) ∈ S} :=
    isOpen_setOfPred_eventually_nhds.preimage hφ
  obtain ⟨u, W, -, hW, hu, hKW, huW⟩ := generalized_tube_lemma isCompact_Icc hK hT
    fun p hp ↦ by
      rw [mem_ofPred_eq, hfix p.1 hp.1 p.2 hp.2]
      exact hKS ⟨hp.1, hp.2⟩
  -- Moser's equation holds at every point `(s, y)` of `S` with `s ∈ [0, 1]`.
  have hrate (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (y : M) (hy : (s, y) ∈ S) :
      (TauCeti.mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk s)
          (mlieDerivForm (fun _ ↦ ((1 : ℝ), (0 : E))) σ.val) +
        mlieDerivForm (X s) (TauCeti.mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk s) σ.val)) y = 0 :=
    moserField_rate_eq_zero (congrFun ((SmoothForm.isClosed_def _).1 (hσ s hs)) y)
      (((Continuous.prodMk_right s).continuousAt.eventually hy).mono fun _ hz ↦ ⟨hz.1, hz.2.1⟩)
      hy.self_of_nhds.2.2
  filter_upwards [hW.mem_nhdsSet.2 hKW] with x hx t
  have hJ : uIcc (0 : ℝ) t ⊆ Icc 0 1 :=
    (uIcc_of_le t.property.1).trans_subset (Icc_subset_Icc_right t.property.2)
  have h := mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_of_forall_mem_uIcc
    (hX.of_le (by simp)) hc (fun _ _ ↦ (σ.contMDiff.of_le (by simp)).contMDiffAt)
    (s := 0) (t := t) (x := x) fun s hs ↦ hrate s (hJ hs) _ (huW (mk_mem_prod (hu (hJ hs)) hx))
  rw [SmoothForm.coe_mpullback, Diffeotopy.timeSlice_timeDependentFlowDiffeotopy,
    SmoothForm.coe_mpullback, SmoothForm.coe_mpullback]
  exact h

end TauCeti.SmoothForm

namespace TauCeti.SmoothEmbedding

open Filter
open scoped Topology

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SecondCountableTopology M]
  {E' H' Q : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [J.Boundaryless]
  [TopologicalSpace Q] [ChartedSpace H' Q] [IsManifold J ∞ Q] [CompactSpace Q]

/-- **Moser's argument along a family fixing a compact submanifold.** Let `σ` be a two-form and
`γ` a one-form on `ℝ × M`, `M` boundaryless, Hausdorff and second-countable, with slices `σ_t`
and `γ_t` at `t ∈ ℝ`, and let `f : Q → M` be a compact embedded submanifold. Suppose that for
`t ∈ [0, 1]` the slice `σ_t` is closed and nondegenerate at the points of `f(Q)` and
`f^* γ_t = 0`, and that `∂_t σ_t = dγ_t` near `[0, 1] × f(Q)`. Then there is a diffeotopy `Ψ`
which fixes every point outside a compact set at all times, fixes every point of `f(Q)` at all
times, and satisfies `Ψ_t^* σ_t = σ_0` for every `t ∈ [0, 1]` on one neighbourhood of `f(Q)`. -/
theorem exists_diffeotopy_fix_eventually_mpullback_eq_of_timeDeriv
    (f : SmoothEmbedding J I ∞ Q M)
    (σ : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) ℝ 2)
    (hσ : ∀ t ∈ Icc (0 : ℝ) 1,
      (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) σ).IsClosed)
    (γ : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) ℝ 1)
    (hγ : ∀ᶠ p in 𝓝ˢ (Icc (0 : ℝ) 1 ×ˢ range f),
      (SmoothForm.mpullback (Prod.mk p.1) (contMDiff_const.prodMk contMDiff_id)
          σ.timeDeriv).val p.2 =
        mextDeriv (SmoothForm.mpullback (Prod.mk p.1) (contMDiff_const.prodMk contMDiff_id)
          γ).val p.2)
    (hγf : ∀ t ∈ Icc (0 : ℝ) 1, SmoothForm.mpullback f f.contMDiff
      (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) γ) = 0)
    (hnd : ∀ t ∈ Icc (0 : ℝ) 1, ∀ q,
      ((SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id)
        σ).bilinFormAt (f q)).Nondegenerate) :
    ∃ Ψ : Diffeotopy I ∞ M, (∃ C, IsCompact C ∧ ∀ t, ∀ x ∉ C, Ψ (t, x) = x) ∧
      (∀ t q, Ψ (t, f q) = f q) ∧
      ∀ᶠ x in 𝓝ˢ (range f), ∀ t : unitInterval,
        (SmoothForm.mpullback (Ψ.timeSlice t) (Ψ.timeSlice t).contMDiff
          (SmoothForm.mpullback (Prod.mk (t : ℝ)) (contMDiff_const.prodMk contMDiff_id)
            σ)).val x =
          (SmoothForm.mpullback (Prod.mk 0) (contMDiff_const.prodMk contMDiff_id) σ).val x := by
  -- Correct `γ` by the differential of a function `φ` on `ℝ × M`, so that the slices of the
  -- corrected form `γ'` vanish along `f(Q)` as covectors on `M`.
  obtain ⟨φ, hφ, -, -, hdφ⟩ :=
    f.exists_contMDiff_mextDeriv_eq_mpullback_prodMk γ isOpen_univ (subset_univ _)
  set Φ : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) ℝ 0 := SmoothForm.ofFunction ⟨φ, hφ⟩
  have hΦ : Φ.val = RoughForm.ofFunction (𝓘(ℝ, ℝ).prod I) φ := SmoothForm.coe_ofFunction _
  set γ' := γ - mextDerivₗ (𝓘(ℝ, ℝ).prod I) 0 Φ
  have hslice (t : ℝ) :
      SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) γ' =
        SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) γ -
          mextDerivₗ I 0 (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id)
            Φ) := by
    rw [map_sub, SmoothForm.mextDerivₗ_mpullback]
  -- The slices of `γ'` have the same exterior derivative as those of `γ`.
  have hdγ' (t : ℝ) :
      mextDeriv (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) γ').val =
        mextDeriv (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id)
          γ).val := by
    rw [← mextDerivₗ_apply, ← mextDerivₗ_apply, hslice, map_sub, AddSubgroupClass.coe_sub,
      mextDerivₗ_apply, mextDerivₗ_apply, mextDerivₗ_apply, SmoothForm.mextDeriv_mextDeriv,
      sub_zero]
  -- They vanish at the points of `f(Q)` for `t ∈ [0, 1]`.
  have hγ'f (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (q : Q) :
      (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) γ').val (f q) =
        0 := by
    have hq := hdφ t q (by rw [hγf t ht, ZeroMemClass.coe_zero, Pi.zero_apply])
    rw [hslice, AddSubgroupClass.coe_sub, Pi.sub_apply, mextDerivₗ_apply,
      SmoothForm.coe_mpullback (Prod.mk t) _ Φ, hΦ, mpullback_ofFunction, ← hq,
      Function.comp_def, sub_self]
  obtain ⟨Ψ, hΨC, hΨf, hΨ⟩ :=
    SmoothForm.exists_diffeotopy_fix_eventually_mpullback_eq_of_timeDeriv σ hσ γ'
      (isCompact_range f.contMDiff.continuous) (hγ.mono fun p hp ↦ by rw [hp, hdγ'])
      (by rintro t ht _ ⟨q, rfl⟩; exact hγ'f t ht q)
      (by rintro t ht _ ⟨q, rfl⟩; exact hnd t ht q)
  exact ⟨Ψ, hΨC, fun t q ↦ hΨf t _ (mem_range_self q), hΨ⟩

end TauCeti.SmoothEmbedding
