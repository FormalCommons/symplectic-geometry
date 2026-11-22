/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Moser.Field
public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Basic
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic
import SymplecticGeometry.Geometry.Diffeomorphism.Diffeotopy.Real
import SymplecticGeometry.Geometry.Diffeomorphism.Diffeotopy.Velocity
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Flow.Family
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.TimeExtension
import SymplecticGeometry.Geometry.Manifold.Flow.TimeDependent
import SymplecticGeometry.Geometry.Manifold.TubularNeighborhood.OneFormCorrection
import SymplecticGeometry.Geometry.Symplectic.Manifold.Family
import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Flow
import TauCeti.Geometry.Manifold.PartitionOfUnity.Compact

/-!
# Moser's argument along a family and with a parameter

This file holds two forms of Moser's argument near a compact set. In the first, a family of
two-forms runs in the Moser time, and the argument is relative to a compact set or fixes a compact
embedded submanifold. In the second, every value `t ∈ [0, 1]` of a parameter has its own Moser
problem, and the solutions form one diffeotopy in `t`. All of them use the cut-off Moser field
`SymplecticGeometry.moserField`.

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

## Moser's argument with a parameter

Let `ω₀` be a closed two-form on `N`, and `σ` a two-form and `β` a one-form on `[0, 1] × N`
with `dβ_t = σ_t - ω₀` and `β_0 = 0`. If every `β_t` vanishes at the points of a compact set `K`
and the forms `ω₀ + s (σ_t - ω₀)`, `s ∈ [0, 1]`, are nondegenerate there, Moser's argument for
the segment from `ω₀` to `σ_t` with the primitive `β_t`, constant in `s`, gives a time-one map
`χ_t` with `χ_t^* σ_t = ω₀` near `K`. To make `χ_t` smooth in `t`, the slices of `σ` and `β`
are extended to all `t ∈ ℝ` (`TauCeti.SmoothForm.timeExtendSlice`), and the Moser fields
`X_{t,s}` are those of one family of two-forms over the points `(t, s)` of `ℝ × ℝ`, with one
cutoff on `(ℝ × ℝ) × N`. They are then jointly smooth in `(t, s, x)`, and so are their flows, by
`TauCeti.contMDiff_timeDependentFlowOf_param`. The family `t ↦ χ_t` over `ℝ` starts at the
identity because `β_0 = 0`, and `TauCeti.Diffeotopy.ofReal` restricts it to a diffeotopy.

## Main results

* `TauCeti.SmoothForm.exists_diffeotopy_fix_eventually_mpullback_eq_of_timeDeriv`: Moser's
  argument along a family, relative to a compact set on which the primitives vanish.
* `TauCeti.SmoothEmbedding.exists_diffeotopy_fix_eventually_mpullback_eq_of_timeDeriv`: Moser's
  argument along a family, fixing a compact embedded submanifold to which the primitives pull
  back to `0`.
* `TauCeti.SmoothTwoForm.exists_diffeotopy_fix_eventually_mpullback_eq_of_mextDeriv_eq_sub`:
  Moser's argument with a parameter in `[0, 1]`, relative to a compact set on which the
  primitives vanish.

Both proofs adapt that of Tau Ceti's
`TauCeti.SmoothTwoForm.exists_diffeomorph_fix_eventually_mpullback_eq_of_mextDeriv_eq_sub`
(`TauCeti/Geometry/Symplectic/Manifold/RelativeMoser.lean`). The proof of
`TauCeti.SmoothForm.exists_diffeotopy_fix_eventually_mpullback_eq_of_timeDeriv` runs its
trajectory argument for every time `t ∈ [0, 1]` along a general family instead of for time one
along a reparametrized segment. The proof of
`TauCeti.SmoothTwoForm.exists_diffeotopy_fix_eventually_mpullback_eq_of_mextDeriv_eq_sub` runs
it for time one along the segments `ω₀ + s (σ_t - ω₀)`, with one neighbourhood of `K` for all
values of the parameter.

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

namespace TauCeti.SmoothTwoForm

open Filter SymplecticGeometry
open scoped Topology

variable {E H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]

/-- A step of `exists_diffeotopy_fix_eventually_mpullback_eq_of_mextDeriv_eq_sub`: Moser's
argument at one point for the segment `ω₀ + s (α - ω₀)` from a closed form `ω₀`, with a primitive
`γ` of `α - ω₀` constant in `s`. If, up to time `1`, the trajectory of `x` under the cut-off Moser
field stays at points near which the cutoff is `1` and the segment is nondegenerate, the time-one
map pulls `α` back to `ω₀` at `x`. -/
private theorem mpullback_timeDependentFlowOf_moserField_lineMapFamily_apply
    {ω₀ α : SmoothTwoForm I N} (hω₀ : ω₀.IsClosed) {γ : SmoothForm I N ℝ 1}
    (hγ : α - ω₀ = mextDerivₗ I 1 γ) {ρ : ℝ × N → ℝ}
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent ∞ (fun p : ℝ × N ↦
      (⟨p.2, moserField (SmoothForm.lineMapFamily ω₀ α contDiff_id)
        (SmoothForm.mpullback Prod.snd contMDiff_snd γ) ρ p.1 p.2⟩ : TangentBundle I N)))
    (hc : IsCompleteVectorField (timeDependentSuspensionField
      (moserField (SmoothForm.lineMapFamily ω₀ α contDiff_id)
        (SmoothForm.mpullback Prod.snd contMDiff_snd γ) ρ)))
    {x : N} (hx : ∀ s ∈ Icc (0 : ℝ) 1, ∀ᶠ z in 𝓝 (timeDependentFlowOf
      (moserField (SmoothForm.lineMapFamily ω₀ α contDiff_id)
        (SmoothForm.mpullback Prod.snd contMDiff_snd γ) ρ) 0 s x),
      ρ (s, z) = 1 ∧ (SmoothTwoForm.flat (ω₀ + s • (α - ω₀)) z).IsInvertible) :
    TauCeti.mpullback I I (timeDependentFlowOf
      (moserField (SmoothForm.lineMapFamily ω₀ α contDiff_id)
        (SmoothForm.mpullback Prod.snd contMDiff_snd γ) ρ) 0 1) α.val x = ω₀.val x := by
  set Λ := SmoothForm.lineMapFamily ω₀ α contDiff_id
  -- Moser's equation holds along the trajectory of `x` up to time `1`.
  have hrate (s : ℝ) (hs : s ∈ uIcc (0 : ℝ) 1) :
      (TauCeti.mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk s)
          (mlieDerivForm (fun _ ↦ ((1 : ℝ), (0 : E))) Λ.val) +
        mlieDerivForm (moserField Λ (SmoothForm.mpullback Prod.snd contMDiff_snd γ) ρ s)
          (TauCeti.mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk s) Λ.val))
        (timeDependentFlowOf
          (moserField Λ (SmoothForm.mpullback Prod.snd contMDiff_snd γ) ρ) 0 s x) = 0 := by
    have hcl : (SmoothForm.mpullback (Prod.mk s) (contMDiff_const.prodMk contMDiff_id)
        Λ).IsClosed := by
      rw [SmoothForm.mpullback_prodMk_lineMapFamily, hγ]
      exact hω₀.add ((SmoothForm.isClosed_mextDerivₗ _).smul _)
    refine moserField_rate_eq_zero (congrFun ((SmoothForm.isClosed_def _).1 hcl) _)
      (by simpa only [Λ, SmoothForm.mpullback_prodMk_lineMapFamily, id] using
        hx s (uIcc_of_le (zero_le_one (α := ℝ)) ▸ hs)) ?_
    rw [SmoothForm.mpullback_prodMk_timeDeriv_lineMapFamily, deriv_id, one_smul,
      SmoothForm.mpullback_prodMk_mpullback_snd, hγ, mextDerivₗ_apply]
  have h := mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_of_forall_mem_uIcc
    (hX.of_le (by simp)) hc (fun _ _ ↦ (Λ.contMDiff.of_le (by simp)).contMDiffAt)
    (s := 0) (t := 1) (x := x) hrate
  have h1 : SmoothForm.mpullback (Prod.mk 1) (contMDiff_const.prodMk contMDiff_id) Λ = α := by
    rw [SmoothForm.mpullback_prodMk_lineMapFamily, id, one_smul, add_sub_cancel]
  have h0 : SmoothForm.mpullback (Prod.mk 0) (contMDiff_const.prodMk contMDiff_id) Λ = ω₀ := by
    rw [SmoothForm.mpullback_prodMk_lineMapFamily, id, zero_smul, add_zero]
  rw [← h1, SmoothForm.coe_mpullback, ← h0, SmoothForm.coe_mpullback]
  exact h

/-- **Moser's argument with a parameter, relative to a compact set.** Let `N` be a boundaryless
Hausdorff manifold, `ω₀` a closed two-form on `N`, and `σ` a two-form and `β` a one-form on
`[0, 1] × N`, with slices `σ_t` and `β_t`, such that `dβ_t = σ_t - ω₀` for every `t` and
`β_0 = 0`. Let `K ⊆ N` be compact, and suppose that every `β_t` vanishes at the points of `K` and
that every form `ω₀ + s (σ_t - ω₀)`, `s ∈ [0, 1]`, is nondegenerate at the points of `K`. Then
there is a diffeotopy `χ` which fixes every point of `K` at all times, fixes every point outside
a compact set at all times, is the identity at every time `t` with `β_t = 0`, and satisfies
`χ_t^* σ_t = ω₀` for every `t` on one neighbourhood of `K`. -/
theorem exists_diffeotopy_fix_eventually_mpullback_eq_of_mextDeriv_eq_sub
    {ω₀ : SmoothTwoForm I N} (hω₀ : ω₀.IsClosed)
    (σ : SmoothForm ((𝓡∂ 1).prod I) (unitInterval × N) ℝ 2)
    (β : SmoothForm ((𝓡∂ 1).prod I) (unitInterval × N) ℝ 1)
    (hβ : ∀ t, mextDeriv
      (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) β).val =
        (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) σ - ω₀).val)
    (hβ₀ : SmoothForm.mpullback (Prod.mk 0) (contMDiff_const.prodMk contMDiff_id) β = 0)
    {K : Set N} (hK : IsCompact K)
    (hβK : ∀ t, ∀ x ∈ K,
      (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) β).val x = 0)
    (hnd : ∀ t, ∀ x ∈ K, ∀ s ∈ Icc (0 : ℝ) 1, ((ω₀ + s •
      (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) σ - ω₀)).bilinFormAt
        x).Nondegenerate) :
    ∃ χ : Diffeotopy I ∞ N, (∀ t, ∀ x ∈ K, χ (t, x) = x) ∧
      (∃ C, IsCompact C ∧ ∀ t, ∀ x ∉ C, χ (t, x) = x) ∧
      (∀ t, SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) β = 0 →
        ∀ x, χ (t, x) = x) ∧
      ∀ᶠ x in 𝓝ˢ K, ∀ t,
        (SmoothForm.mpullback (χ.timeSlice t) (χ.timeSlice t).contMDiff
          (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) σ)).val x =
          ω₀.val x := by
  -- Extend the slices `σ_t` and `β_t` to all real `t`.
  set σ' := SmoothForm.timeExtendSlice σ
  set β' := SmoothForm.timeExtendSlice β
  have hσ' {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) : σ' τ =
      SmoothForm.mpullback (Prod.mk ⟨τ, hτ⟩) (contMDiff_const.prodMk contMDiff_id) σ :=
    SmoothForm.timeExtendSlice_coe σ ⟨τ, hτ⟩
  have hβ' {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) : β' τ =
      SmoothForm.mpullback (Prod.mk ⟨τ, hτ⟩) (contMDiff_const.prodMk contMDiff_id) β :=
    SmoothForm.timeExtendSlice_coe β ⟨τ, hτ⟩
  -- The forms `ω₀ + s (σ'_τ - ω₀)` and `β'_τ`, as families over the points `(τ, s)` of `ℝ × ℝ`.
  obtain ⟨Ω, hΩ⟩ := isSmoothFamily_def.mp <| show IsSmoothFamily (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))
      (fun p : ℝ × ℝ ↦ ω₀ + p.2 • (σ' p.1 - ω₀)) from
    (isSmoothFamily_const ω₀).add ((((isSmoothFamily_timeExtendSlice σ).comp Prod.fst
      contMDiff_fst).sub (isSmoothFamily_const ω₀)).fun_smul contMDiff_snd)
  obtain ⟨B, hB⟩ := isSmoothFamily_def.mp <|
    show IsSmoothFamily (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (fun p : ℝ × ℝ ↦ β' p.1) from
    (isSmoothFamily_timeExtendSlice β).comp Prod.fst contMDiff_fst
  -- A cutoff near `[0, 1]² × K`, supported where the forms of `Ω` are nondegenerate.
  set O := {p : (ℝ × ℝ) × N | (SmoothTwoForm.flat
    (SmoothForm.mpullback (Prod.mk p.1) (contMDiff_const.prodMk contMDiff_id) Ω)
      p.2).IsInvertible}
  have hO : IsOpen O := SmoothTwoForm.isOpen_setOf_isInvertible_flat_mpullback_prodMk Ω
  have hKO : (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ×ˢ K ⊆ O := by
    rintro ⟨⟨τ, s⟩, x⟩ ⟨⟨hτ, hs⟩, hx⟩
    simp only [O, mem_ofPred_eq, hΩ]
    rw [SmoothTwoForm.isInvertible_flat_iff, hσ' hτ]
    exact hnd _ x hx s hs
  obtain ⟨ρ, hρ, hρ1, hρc, hρO, -⟩ :=
    ((isCompact_Icc.prod isCompact_Icc).prod hK).exists_contMDiff_one_nhds_tsupport_subset
      ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) hO hKO
  -- The Moser fields `Y τ s`, jointly smooth in `(τ, s, x)` and supported in a compact set.
  set Y : ℝ → ℝ → (x : N) → TangentSpace I x := fun τ s ↦ moserField Ω B ρ (τ, s)
  have hY : ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) I.tangent ∞
      (fun p : (ℝ × ℝ) × N ↦ (⟨p.2, Y p.1.1 p.1.2 p.2⟩ : TangentBundle I N)) :=
    contMDiff_moserField Ω B hρ fun p hp ↦ hρO hp
  have hYτ (τ : ℝ) : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent ∞
      (fun p : ℝ × N ↦ (⟨p.2, Y τ p.1 p.2⟩ : TangentBundle I N)) :=
    hY.comp ((contMDiff_const.prodMk contMDiff_fst).prodMk contMDiff_snd)
  have hY0 {τ : ℝ} {x : N} (h : (β' τ).val x = 0) (s : ℝ) : Y τ s x = 0 :=
    moserField_eq_zero_of_apply_eq_zero (by rw [hB]; exact h)
  set C := Prod.snd '' tsupport ρ
  have hC : IsCompact C := hρc.isCompact.image continuous_snd
  have hYC (τ s : ℝ) (y : N) (hy : y ∉ C) : Y τ s y = 0 :=
    moserField_eq_zero_of_notMem_tsupport fun h ↦ hy ⟨_, h, rfl⟩
  have hc (τ : ℝ) := isCompleteVectorField_timeDependentSuspensionField
    ((hYτ τ).of_le (m := 1) (by simp)) hC (hYC τ)
  have hflow := contMDiff_timeDependentFlowOf_param le_top hY hc
  -- `χ_τ` is the time-one map of the flow of `Y τ`.
  set ψ : ℝ → N ≃ₘ⟮I, I⟯ N := fun τ ↦ timeDependentFlowDiffeomorph (hc τ) le_top (hYτ τ) 0 1
  have hψ (τ : ℝ) (x : N) : ψ τ x = timeDependentFlowOf (Y τ) 0 1 x :=
    timeDependentFlowDiffeomorph_apply _ _ _ _ _ _
  have hψs : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × N ↦ ψ p.1 p.2) :=
    (hflow.comp ((contMDiff_fst.prodMk (contMDiff_const (c := ((0 : ℝ), (1 : ℝ))))).prodMk
      contMDiff_snd)).congr fun p ↦ hψ p.1 p.2
  have hψ0 (τ : ℝ) (x : N) (h : ∀ s, Y τ s x = 0) : ψ τ x = x := by
    rw [hψ]
    exact timeDependentFlowOf_eq_self_of_forall_eq_zero ((hYτ τ).of_le (by simp)) h 0 1
  have hψ₀ (x : N) : ψ 0 x = x := hψ0 0 x <| hY0 <| by
    rw [← Set.Icc.coe_zero, hβ' (0 : unitInterval).property, Subtype.coe_eta, hβ₀,
      ZeroMemClass.coe_zero, Pi.zero_apply]
  let χ := Diffeotopy.ofReal ψ hψs hψ₀
  have hχ (t : unitInterval) (x : N) : χ (t, x) = ψ t x := Diffeotopy.ofReal_apply ψ hψs hψ₀ _
  refine ⟨χ, fun t x hx ↦ (hχ t x).trans (hψ0 t x (hY0 (by rw [hβ' t.property]; exact hβK t x hx))),
    ⟨C, hC, fun t x hx ↦ (hχ t x).trans (hψ0 t x fun s ↦ hYC t s x hx)⟩,
    fun t ht x ↦ (hχ t x).trans (hψ0 t x (hY0 (by
      rw [hβ' t.property, ht, ZeroMemClass.coe_zero, Pi.zero_apply]))), ?_⟩
  -- `S`: the points near which `ρ = 1` and the forms of `Ω` are nondegenerate, where Moser's
  -- equation holds.
  set S := {p : (ℝ × ℝ) × N | ∀ᶠ q in 𝓝 p, ρ q = 1 ∧ q ∈ O}
  have hKS : (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ×ˢ K ⊆ S :=
    eventually_nhdsSet_iff_forall.1 (hρ1.and (hO.mem_nhdsSet.2 hKO))
  -- The trajectories starting near `K` stay in `S` up to time `1`, for every `τ ∈ [0, 1]`.
  have hφ :
      Continuous fun p : (ℝ × ℝ) × N ↦ (p.1, timeDependentFlowOf (Y p.1.1) 0 p.1.2 p.2) :=
    continuous_fst.prodMk (hflow.comp ((contMDiff_fst.fst.prodMk
      ((contMDiff_const (c := (0 : ℝ))).prodMk contMDiff_fst.snd)).prodMk
        contMDiff_snd)).continuous
  have hT : IsOpen {p : (ℝ × ℝ) × N | (p.1, timeDependentFlowOf (Y p.1.1) 0 p.1.2 p.2) ∈ S} :=
    isOpen_setOfPred_eventually_nhds.preimage hφ
  obtain ⟨u, W, -, hW, hu, hKW, huW⟩ :=
    generalized_tube_lemma (isCompact_Icc.prod isCompact_Icc) hK hT fun p hp ↦ by
      have hp0 : ∀ s, Y p.1.1 s p.2 = 0 := hY0 (by
        rw [hβ' hp.1.1]
        exact hβK _ _ hp.2)
      rw [mem_ofPred_eq, timeDependentFlowOf_eq_self_of_forall_eq_zero
        ((hYτ _).of_le (by simp)) hp0 0 p.1.2]
      exact hKS hp
  filter_upwards [hW.mem_nhdsSet.2 hKW] with x hx t
  -- For this `t`, `Y t` is the Moser field of the segment `ω₀ + s (σ_t - ω₀)`, with the
  -- primitive `β_t` constant in `s`.
  have hYt : Y t = moserField (SmoothForm.lineMapFamily ω₀ (σ' t) contDiff_id)
      (SmoothForm.mpullback Prod.snd contMDiff_snd (β' t)) fun q ↦ ρ ((t, q.1), q.2) := by
    funext s y
    rw [moserField_def, SmoothForm.mpullback_prodMk_lineMapFamily, id, ← hΩ ((t : ℝ), s),
      SmoothForm.mpullback_prodMk_mpullback_snd, ← hB ((t : ℝ), s)]
    exact moserField_def Ω B ρ _ y
  have hYt' := hYτ t
  have hct := hc t
  rw [hYt] at hYt' hct
  rw [SmoothForm.coe_mpullback, Diffeotopy.timeSlice_ofReal, funext (hψ t), ← hσ' t.property,
    hYt]
  refine mpullback_timeDependentFlowOf_moserField_lineMapFamily_apply hω₀
    (Subtype.ext (by rw [mextDerivₗ_apply, hσ' t.property, hβ' t.property, hβ t])) hYt' hct
    fun s hs ↦ ?_
  -- The trajectory stays in `S`, where `ρ = 1` and the forms of `Ω` are nondegenerate.
  have hS : (((t : ℝ), s), timeDependentFlowOf (Y t) 0 s x) ∈ S :=
    huW (mk_mem_prod (hu (mk_mem_prod t.property hs)) hx)
  rw [hYt] at hS
  refine ((Continuous.prodMk_right ((t : ℝ), s)).continuousAt.eventually hS).mono
    fun z hz ↦ ⟨hz.1, ?_⟩
  have h := hz.2
  simp only [O, mem_ofPred_eq, hΩ] at h
  exact h

end TauCeti.SmoothTwoForm
