/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Uniform continuity in one variable on a compact rectangle

Let `X` be a topological space, `K ⊆ X` compact and `g : ℝ × X → ℝ` continuous on the rectangle
`[a, b] × K`.

* `IsCompact.exists_pos_abs_sub_lt_of_continuousOn`: `g` is uniformly continuous in its first
  variable, uniformly in `r ∈ K`. By Mathlib's parametric Heine–Cantor lemma
  `IsCompact.mem_uniformity_of_prod`, the functions `ℓ ↦ g (ℓ, r)` on `[a, b]`, for `r ∈ K`,
  form an equicontinuous family, which is uniformly equicontinuous since `[a, b]` is compact
  (`CompactSpace.uniformEquicontinuous_of_equicontinuous`).
* `IsCompact.exists_mem_Ioo_forall_abs_sub_lt_of_continuousOn`: as a consequence, `g` stays
  uniformly close to its values on the side `{b} × K` over `[c, b] × K`, for some `c < b`.
-/

public section

open Set

variable {X : Type*} [TopologicalSpace X] {K : Set X} {a b : ℝ} {g : ℝ × X → ℝ}

/-- A real function continuous on the compact rectangle `[a, b] × K`, with `K` in a topological
space, is uniformly continuous in its first variable: for every `ε > 0` there is `h > 0` such that
moving `ℓ ∈ [a, b]` by at most `h` changes its value at `(ℓ, r)` by less than `ε`, for every
`r ∈ K`. -/
theorem IsCompact.exists_pos_abs_sub_lt_of_continuousOn (hK : IsCompact K)
    (hg : ContinuousOn g (Icc a b ×ˢ K)) {ε : ℝ} (hε : 0 < ε) :
    ∃ h > 0, ∀ r ∈ K, ∀ ℓ ∈ Icc a b, ∀ ℓ' ∈ Icc a b, |ℓ' - ℓ| ≤ h →
      |g (ℓ', r) - g (ℓ, r)| < ε := by
  let F : K → Icc a b → ℝ := fun r ℓ ↦ g (ℓ, r)
  have hF : Equicontinuous F := by
    intro ℓ₀ u hu
    have hg' : ContinuousOn (fun (ℓ : Icc a b) (r : X) ↦ g (ℓ, r)).uncurry (univ ×ˢ K) :=
      hg.comp (continuous_subtypeVal.prodMap continuous_id).continuousOn
        fun p hp ↦ ⟨p.1.property, hp.2⟩
    obtain ⟨v, hv, H⟩ := hK.mem_uniformity_of_prod hg' (mem_univ ℓ₀) (symm_le_uniformity hu)
    rw [nhdsWithin_univ] at hv
    exact Filter.mem_of_superset hv fun ℓ hℓ r ↦ H ℓ hℓ r r.property
  obtain ⟨δ, hδ, H⟩ := Metric.mem_uniformity_dist.1
    (CompactSpace.uniformEquicontinuous_of_equicontinuous hF _ (Metric.dist_mem_uniformity hε))
  refine ⟨δ / 2, half_pos hδ, fun r hr ℓ hℓ ℓ' hℓ' hl ↦ ?_⟩
  have hd : dist (⟨ℓ', hℓ'⟩ : Icc a b) ⟨ℓ, hℓ⟩ < δ := by
    rw [Subtype.dist_eq, Real.dist_eq]
    linarith
  simpa [F, Real.dist_eq] using H hd ⟨r, hr⟩

/-- A real function continuous on the compact rectangle `[a, b] × K`, with `K` in a topological
space, is close to its values on the side `{b} × K` near that side: for every `ε > 0` and
`c₀ ∈ [a, b)` there is `c ∈ (c₀, b)` such that `|g (ℓ, r) - g (b, r)| < ε` for all `ℓ ∈ [c, b]`
and `r ∈ K`. -/
theorem IsCompact.exists_mem_Ioo_forall_abs_sub_lt_of_continuousOn (hK : IsCompact K)
    (hg : ContinuousOn g (Icc a b ×ˢ K)) {ε c₀ : ℝ} (hε : 0 < ε) (hac₀ : a ≤ c₀) (hc₀b : c₀ < b) :
    ∃ c ∈ Ioo c₀ b, ∀ ℓ ∈ Icc c b, ∀ r ∈ K, |g (ℓ, r) - g (b, r)| < ε := by
  obtain ⟨h, hh, H⟩ := hK.exists_pos_abs_sub_lt_of_continuousOn hg hε
  have hm : 0 < min h ((b - c₀) / 2) := lt_min hh (by linarith)
  have hm' : min h ((b - c₀) / 2) ≤ (b - c₀) / 2 := min_le_right _ _
  refine ⟨b - min h ((b - c₀) / 2), ⟨by linarith, by linarith⟩, fun ℓ hℓ r hr ↦
    H r hr b (right_mem_Icc.2 (hac₀.trans hc₀b.le)) ℓ ⟨by linarith [hℓ.1], hℓ.2⟩ ?_⟩
  rw [abs_le]
  constructor <;> linarith [hℓ.1, hℓ.2, min_le_left h ((b - c₀) / 2)]

end
