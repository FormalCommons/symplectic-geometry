/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Compactness.SigmaCompact
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic
import SymplecticGeometry.Data.Set.Function
import TauCeti.Geometry.Manifold.Immersion.Basic

/-!
# Proper smooth rays as limits of embeddings

Let `γ j : ℝ → M` be smooth embeddings and `T j` a monotone sequence of reals tending to `+∞`, such
that `γ (j + 1)` agrees with `γ j` on `(-∞, T j]`. Then the maps stabilise on every half-line
`(-∞, T j]`, and their limit is again a function `ℝ → M`. If moreover `K` is a compact exhaustion
of `M` and `γ (j + 1)` maps the new arc `[T j, T (j + 1)]` outside `K j`, the limit maps
`[T j, ∞)` outside `K j` for every `j`, tends to infinity as `t → ∞`, and is a smooth embedding.
What each `γ (j + 1)` does beyond `T (j + 1)` does not matter.

Near each parameter the limit agrees with one of the `γ j`, so it is a smooth immersion; that the
complements of the immersions at different points can be taken to be one is Tau Ceti's
`TauCeti.isImmersion_iff_forall_isImmersionAt`, which needs a finite-dimensional model for `M`.
It is a topological embedding because a point near `γ t`, inside a fixed `K i`, can only be the
image of a parameter below a fixed `T j`, where the limit is the embedding `γ j`.

Growing a ray in stages, one arc at a time, then only needs each stage to be a smooth embedding of
all of `ℝ`, without matching charts where successive arcs meet.

## Main results

* `TauCeti.SmoothEmbedding.exists_eqOn_Iic_tendsto_cocompact`: the limit of smooth embeddings of
  `ℝ` that agree on increasing initial half-lines, and whose new arcs leave a compact
  exhaustion, is a smooth embedding tending to infinity.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Theorem 7.3.1, an h-principle on open manifolds. The library proves it with rays that are
  grown in stages and closed up by this lemma.
-/

public section

open Set Filter Topology Manifold
open scoped ContDiff

namespace TauCeti.SmoothEmbedding

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] {n : ℕ∞ω} {γ : ℕ → SmoothEmbedding 𝓘(ℝ) I n ℝ M} {T : ℕ → ℝ}

/-- **A proper smooth ray as a limit.** Let `γ j` be smooth embeddings of `ℝ` in `M` and `T` a
monotone sequence tending to `+∞`, such that `γ (j + 1)` agrees with `γ j` on `(-∞, T j]` and maps
`[T j, T (j + 1)]` outside `K j`, for a compact exhaustion `K` of `M`. Then there is a smooth
embedding `δ` of `ℝ` in `M` that agrees with each `γ j` on `(-∞, T j]`, maps `[T j, ∞)` outside
`K j`, and tends to infinity as `t → ∞`. -/
theorem exists_eqOn_Iic_tendsto_cocompact (hT : Monotone T) (hT' : Tendsto T atTop atTop)
    (K : CompactExhaustion M) (hγ : ∀ j, EqOn (γ (j + 1)) (γ j) (Iic (T j)))
    (hK : ∀ j, MapsTo (γ (j + 1)) (Icc (T j) (T (j + 1))) (K j)ᶜ) :
    ∃ δ : SmoothEmbedding 𝓘(ℝ) I n ℝ M, (∀ j, EqOn δ (γ j) (Iic (T j))) ∧
      (∀ j, MapsTo δ (Ici (T j)) (K j)ᶜ) ∧ Tendsto δ atTop (cocompact M) := by
  have hex (t : ℝ) : ∃ k, t < T k := (hT'.eventually_gt_atTop t).exists
  let N (t : ℝ) : ℕ := (hex t).choose
  let f (t : ℝ) : M := γ (N t) t
  have hS : Monotone fun j ↦ Iic (T j) := fun _ _ h ↦ Iic_subset_Iic.2 (hT h)
  have hf {k : ℕ} {t : ℝ} (ht : t ≤ T k) : f t = γ k t := by
    have hN : t ≤ T (N t) := (hex t).choose_spec.le
    rcases le_total (N t) k with h | h
    · exact (eqOn_of_eqOn_succ (f := (γ ·)) hS hγ h hN).symm
    · exact eqOn_of_eqOn_succ (f := (γ ·)) hS hγ h ht
  have hfK {j : ℕ} {t : ℝ} (ht : T j ≤ t) : f t ∉ K j := by
    obtain ⟨k, hk⟩ := (hT'.eventually_ge_atTop t).exists_forall_of_atTop
    have htk := hk (max k (j + 1)) (le_max_left _ _)
    rw [hf htk]
    exact mapsTo_Icc_compl_of_eqOn_succ (f := (γ ·)) K.subset hγ hK
      (by omega : j < max k (j + 1)) ⟨ht, htk⟩
  have hfeq (t : ℝ) {k : ℕ} (hk : t < T k) : f =ᶠ[𝓝 t] γ k :=
    eventually_of_mem (Iio_mem_nhds hk) fun s hs ↦ hf (le_of_lt hs)
  have hcont : Continuous f := continuous_iff_continuousAt.2 fun t ↦
    ((γ (hex t).choose).isEmbedding.continuous.continuousAt).congr
      (hfeq t (hex t).choose_spec).symm
  have himm : IsImmersion 𝓘(ℝ) I n f := isImmersion_iff_forall_isImmersionAt.2 fun t ↦
    ((γ (hex t).choose).isImmersion.isImmersionAt t).congr_of_eventuallyEq
      (hfeq t (hex t).choose_spec).symm
  have hinj : Function.Injective f := fun s t hst ↦ by
    obtain ⟨k, hk⟩ := hex (max s t)
    rw [hf (le_max_left s t |>.trans hk.le), hf (le_max_right s t |>.trans hk.le)] at hst
    exact (γ k).isEmbedding.injective hst
  have hind : IsInducing f := isInducing_iff_nhds.2 fun t ↦ by
    refine le_antisymm (hcont.tendsto t).le_comap fun U hU ↦ ?_
    obtain ⟨i, hi⟩ := K.exists_mem_nhds (f t)
    obtain ⟨j, hj⟩ := ((hT'.eventually_gt_atTop t).and (eventually_ge_atTop i)).exists
    rw [(γ j).isEmbedding.isInducing.nhds_eq_comap t, ← hf hj.1.le] at hU
    obtain ⟨V, hV, hVU⟩ := hU
    refine ⟨V ∩ K i, inter_mem hV hi, fun s ⟨hsV, hsK⟩ ↦ hVU ?_⟩
    have hs : s ≤ T j := le_of_not_ge fun h ↦ hfK h (K.subset hj.2 hsK)
    rwa [mem_preimage, ← hf hs]
  refine ⟨ofIsSmoothEmbedding f ⟨himm, hind, hinj⟩, ?_⟩
  rw [coe_ofIsSmoothEmbedding]
  refine ⟨fun j t ht ↦ hf ht, fun j t ht ↦ hfK ht, ?_⟩
  refine hasBasis_cocompact.tendsto_right_iff.2 fun C hC ↦ ?_
  obtain ⟨i, hi⟩ := K.exists_superset_of_isCompact hC
  exact (eventually_ge_atTop (T i)).mono fun t ht hCt ↦ hfK ht (hi hCt)

end TauCeti.SmoothEmbedding

end
