/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiffMap
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Topology
import SymplecticGeometry.Analysis.Calculus.IteratedFDeriv.CompLinear
import SymplecticGeometry.Analysis.Calculus.IteratedFDeriv.FDerivWithinApply
import SymplecticGeometry.Geometry.Manifold.ContMDiffMap.Basic
import SymplecticGeometry.Geometry.Manifold.MFDeriv.Chart
import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Evaluation
import TauCeti.Geometry.Manifold.VectorBundle.Submersion

/-!
# The bundled tangent map of a `C^n` map

For a `C^n` map `f : M → M'` and `m + 1 ≤ n`, the tangent map `tangentMap I I' f` is a `C^m` map
`TM → TM'` (Mathlib's `ContMDiff.contMDiff_tangentMap`); `ContMDiffMap.tangentMap` bundles it.
It is functorial: it sends composites to composites and the identity to the identity.

Its expression in the charts of the tangent bundles is
`ContinuousAt.extChartAt_tangentMap_extChartAt_symm`, in
`SymplecticGeometry/Geometry/Manifold/MFDeriv/Chart.lean`, which is stated for any map continuous
at the point and applies to a bundled map through `ContMDiffMap.coe_tangentMap`.

For smooth maps, `f ↦ f.tangentMap` is continuous for Tau Ceti's weak Whitney topologies
(`TauCeti.ManifoldWeakWhitney`), with no local compactness and with boundary and corners allowed.
On a compact set `K` of a tangent-bundle chart target, the chart expression of `f.tangentMap`
is `(z, v) ↦ (f̃ z, Df̃(z) v)`; the iterated derivatives of the difference of these expressions
for `f` and `f₀` are bounded by those of `f̃ - f̃₀` of one order more
(`Prod.norm_iteratedFDerivWithin_comp_fst_sub` and
`norm_iteratedFDerivWithin_fderivWithin_apply_sub_le`),
taken on a relatively open part of the base chart target where both maps are visible, and those
converge uniformly on the compact set of base points of `K` by Tau Ceti's
`ContMDiffMap.tendstoUniformlyOn_iteratedFDerivWithin_extChartAt`. The last step, a thickening of
the compact image of the derivative of `f₀.tangentMap` inside the open set of the test, follows
the proof of Tau Ceti's `ContMDiffMap.continuous_prodMk_manifoldWeakWhitney`.

## Main definitions and results

* `ContMDiffMap.tangentMap`: the tangent map of a `C^n` map, as a `C^m` map of tangent bundles,
  with `ContMDiffMap.coe_tangentMap`.
* `ContMDiffMap.tangentMap_comp`, `ContMDiffMap.tangentMap_id`: functoriality.
* `ContMDiffMap.continuous_tangentMap_manifoldWeakWhitney`: the tangent map of smooth maps is
  continuous for the weak Whitney topologies.

## References

* [M. W. Hirsch, *Differential Topology*][Hirsch1976], Chapter 1, §2, and Chapter 2, §1
-/

public section

open scoped Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 E'' H''}
  {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H'' M'']

namespace ContMDiffMap

variable {m n : WithTop ℕ∞}

section Functoriality

variable [IsManifold I 1 M] [IsManifold I' 1 M'] [IsManifold I'' 1 M'']

/-- The tangent map of a `C^n` map `f : M → M'`, as a `C^m` map of tangent bundles, for
`m + 1 ≤ n`. -/
noncomputable def tangentMap (f : C^n⟮I, M; I', M'⟯) (hmn : m + 1 ≤ n) :
    C^m⟮I.tangent, TangentBundle I M; I'.tangent, TangentBundle I' M'⟯ :=
  ⟨_root_.tangentMap I I' f, f.contMDiff.contMDiff_tangentMap hmn⟩

@[simp]
theorem coe_tangentMap (f : C^n⟮I, M; I', M'⟯) (hmn : m + 1 ≤ n) :
    ⇑(f.tangentMap hmn) = _root_.tangentMap I I' f :=
  (rfl)

/-- The tangent map of a composite of `C^n` maps is the composite of their tangent maps. -/
theorem tangentMap_comp (g : C^n⟮I', M'; I'', M''⟯) (f : C^n⟮I, M; I', M'⟯)
    (hmn : m + 1 ≤ n) :
    (g.comp f).tangentMap hmn = (g.tangentMap hmn).comp (f.tangentMap hmn) := by
  have hn : n ≠ 0 := by
    rintro rfl
    exact absurd hmn (by simp)
  refine ContMDiffMap.ext fun p ↦ ?_
  rw [comp_apply, coe_tangentMap, coe_tangentMap, coe_tangentMap, coe_comp,
    _root_.tangentMap_comp (g.contMDiff.mdifferentiable hn) (f.contMDiff.mdifferentiable hn),
    Function.comp_apply]

/-- The tangent map of the identity is the identity. -/
@[simp]
theorem tangentMap_id (hmn : m + 1 ≤ n) :
    (ContMDiffMap.id : C^n⟮I, M; I, M⟯).tangentMap hmn = ContMDiffMap.id := by
  refine ContMDiffMap.ext fun p ↦ ?_
  rw [coe_tangentMap, coe_id, _root_.tangentMap_id, coe_id]

end Functoriality

section WeakWhitney

/-! ### Continuity for the weak Whitney topologies -/

open Set Filter Topology
open scoped ContDiff TauCeti.ManifoldWeakWhitney

variable [IsManifold I ∞ M] [IsManifold I' ∞ M']

/-- The `j`-th chart derivatives of the tangent maps of two smooth maps `f` and `f₀`, at a point
`w = (z, v)` of the target of a tangent-bundle chart where both maps are visible in the base
target chart, differ at most by the larger of the differences of the `j`-th chart derivatives of
`f` and `f₀` at `z` and `(1 + ‖v‖)` times a weighted sum of the differences of their chart
derivatives of orders `1` to `j + 1` at `z`. -/
private theorem dist_iteratedFDerivWithin_extChartAt_tangentMap_le
    (f f₀ : C^∞⟮I, M; I', M'⟯) {p : TangentBundle I M}
    {q : TangentBundle I' M'} {w : E × E} (hw : w ∈ (extChartAt I.tangent p).target)
    (hf : f ((extChartAt I p.proj).symm w.1) ∈ (extChartAt I' q.proj).source)
    (hf₀ : f₀ ((extChartAt I p.proj).symm w.1) ∈ (extChartAt I' q.proj).source) (j : ℕ) :
    dist (iteratedFDerivWithin 𝕜 j (extChartAt I'.tangent q ∘ f.tangentMap ENat.coe_top_add_one.le ∘
          (extChartAt I.tangent p).symm) (extChartAt I.tangent p).target w)
        (iteratedFDerivWithin 𝕜 j (extChartAt I'.tangent q ∘ f₀.tangentMap ENat.coe_top_add_one.le ∘
          (extChartAt I.tangent p).symm) (extChartAt I.tangent p).target w) ≤
      max ‖iteratedFDerivWithin 𝕜 j (extChartAt I' q.proj ∘ f ∘ (extChartAt I p.proj).symm)
            (extChartAt I p.proj).target w.1 -
          iteratedFDerivWithin 𝕜 j (extChartAt I' q.proj ∘ f₀ ∘ (extChartAt I p.proj).symm)
            (extChartAt I p.proj).target w.1‖
        ((1 + ‖w.2‖) * ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          ‖iteratedFDerivWithin 𝕜 (i + 1) (extChartAt I' q.proj ∘ f ∘ (extChartAt I p.proj).symm)
              (extChartAt I p.proj).target w.1 -
            iteratedFDerivWithin 𝕜 (i + 1)
              (extChartAt I' q.proj ∘ f₀ ∘ (extChartAt I p.proj).symm)
              (extChartAt I p.proj).target w.1‖) := by
  set φ := extChartAt I p.proj
  set ψ := extChartAt I' q.proj
  set T := φ.target
  have hwT : w.1 ∈ T := Bundle.fst_mem_extChartAt_target p hw
  -- A relatively open part `s = T ∩ O` of the chart target on which both maps are visible.
  have hcont : ContinuousOn (fun z ↦ (f (φ.symm z), f₀ (φ.symm z))) T :=
    ((map_continuous f).comp_continuousOn (continuousOn_extChartAt_symm _)).prodMk
      ((map_continuous f₀).comp_continuousOn (continuousOn_extChartAt_symm _))
  obtain ⟨O, hO, hOT⟩ := continuousOn_iff'.mp hcont (ψ.source ×ˢ ψ.source)
    ((isOpen_extChartAt_source _).prod (isOpen_extChartAt_source _))
  set s := T ∩ O
  have hsrc {z : E} (hz : z ∈ s) : f (φ.symm z) ∈ ψ.source ∧ f₀ (φ.symm z) ∈ ψ.source := by
    have : z ∈ O ∩ T := ⟨hz.2, hz.1⟩
    rw [← hOT] at this
    exact this.1
  have hwO : w.1 ∈ O := by
    have : w.1 ∈ (fun z ↦ (f (φ.symm z), f₀ (φ.symm z))) ⁻¹' (ψ.source ×ˢ ψ.source) ∩ T :=
      ⟨⟨hf, hf₀⟩, hwT⟩
    rw [hOT] at this
    exact this.1
  have hws : w.1 ∈ s := ⟨hwT, hwO⟩
  have hs : UniqueDiffOn 𝕜 s := (uniqueDiffOn_extChartAt_target _).inter hO
  have hS : s ×ˢ (univ : Set E) = (extChartAt I.tangent p).target ∩ O ×ˢ univ := by
    rw [TangentBundle.extChartAt_target, prod_inter_prod, inter_univ]
  have hwS : w ∈ s ×ˢ (univ : Set E) := ⟨hws, mem_univ _⟩
  have hj : ((j + 1 : ℕ) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  -- For each of the two maps: smoothness of its chart expression on `s`, and the chart
  -- expression of its tangent map on `s ×ˢ univ`.
  have hsm (g : C^∞⟮I, M; I', M'⟯) (hg : ∀ z ∈ s, g (φ.symm z) ∈ ψ.source) :
      ContDiffOn 𝕜 (j + 1) (ψ ∘ g ∘ φ.symm) s := fun z hz ↦
    (((g.contDiffWithinAt_extChartAt hz.1 (hg z hz)).of_le (by exact_mod_cast hj)).mono
      inter_subset_left)
  have hD (g : C^∞⟮I, M; I', M'⟯) (hg : ∀ z ∈ s, g (φ.symm z) ∈ ψ.source) :
      iteratedFDerivWithin 𝕜 j (extChartAt I'.tangent q ∘ g.tangentMap ENat.coe_top_add_one.le ∘
          (extChartAt I.tangent p).symm) (extChartAt I.tangent p).target w =
        (iteratedFDerivWithin 𝕜 j ((ψ ∘ g ∘ φ.symm) ∘ Prod.fst) (s ×ˢ univ) w).prod
          (iteratedFDerivWithin 𝕜 j (fun r : E × E ↦ fderivWithin 𝕜 (ψ ∘ g ∘ φ.symm) s r.1 r.2)
            (s ×ˢ univ) w) := by
    have hg' := hsm g hg
    have hOS : IsOpen (O ×ˢ (univ : Set E)) := hO.prod isOpen_univ
    rw [← iteratedFDerivWithin_inter_open hOS (show w ∈ O ×ˢ univ from ⟨hwO, mem_univ _⟩), ← hS,
      iteratedFDerivWithin_congr (f := fun r : E × E ↦ (((ψ ∘ g ∘ φ.symm) ∘ Prod.fst) r,
        fderivWithin 𝕜 (ψ ∘ g ∘ φ.symm) s r.1 r.2)) (fun r hr ↦ ?_) hwS]
    · refine iteratedFDerivWithin_prodMk ?_ ?_ (hs.prod uniqueDiffOn_univ) hwS le_rfl
      · exact ((hg'.comp contDiffOn_fst fun (r : E × E) (hr : r ∈ s ×ˢ univ) ↦ hr.1).of_le
          (by exact_mod_cast Nat.le_succ j)) w hwS
      · exact (((hg'.fderivWithin hs le_rfl).comp contDiffOn_fst
          fun (r : E × E) (hr : r ∈ s ×ˢ univ) ↦ hr.1).clm_apply contDiffOn_snd) w hwS
    · have hrT : r ∈ (extChartAt I.tangent p).target := (hS ▸ hr).1
      rw [Function.comp_apply, Function.comp_apply, coe_tangentMap,
        (map_continuous g).continuousAt.extChartAt_tangentMap_extChartAt_symm hrT (hg _ hr.1)]
      have h : fderivWithin 𝕜 (ψ ∘ g ∘ φ.symm) s r.1 = fderivWithin 𝕜 (ψ ∘ g ∘ φ.symm) T r.1 :=
        fderivWithin_inter (hO.mem_nhds hr.1.2)
      exact Prod.ext rfl (congrArg (fun L : E →L[𝕜] E' ↦ L r.2) h.symm)
  have hinter (i : ℕ) (g : E → E') :
      iteratedFDerivWithin 𝕜 i g s w.1 = iteratedFDerivWithin 𝕜 i g T w.1 :=
    iteratedFDerivWithin_inter_open hO hwO
  rw [hD f fun z hz ↦ (hsrc hz).1, hD f₀ fun z hz ↦ (hsrc hz).2]
  simp only [← hinter]
  -- `ContinuousMultilinearMap.prodL` is an isometry, so the distance of the pairs is the larger
  -- of the distances of the components.
  refine (((ContinuousMultilinearMap.prodL 𝕜 (fun _ : Fin j ↦ E × E) E' E').dist_map
    (_, _) (_, _)).trans Prod.dist_eq).trans_le ?_
  rw [dist_eq_norm, dist_eq_norm]
  exact max_le_max
    (Prod.norm_iteratedFDerivWithin_comp_fst_sub (hsm f fun z hz ↦ (hsrc hz).1)
      (hsm f₀ fun z hz ↦ (hsrc hz).2) hs (by exact_mod_cast Nat.le_succ j) hws).le
    (SymplecticGeometry.norm_iteratedFDerivWithin_fderivWithin_apply_sub_le hs
      (hsm f fun z hz ↦ (hsrc hz).1) (hsm f₀ fun z hz ↦ (hsrc hz).2) hws w.2)

/-- The bundled tangent map `f ↦ f.tangentMap`, from `C^∞⟮I, M; I', M'⟯` to
`C^∞⟮I.tangent, TM; I'.tangent, TM'⟯`, is continuous for the weak Whitney topologies. -/
theorem continuous_tangentMap_manifoldWeakWhitney :
    Continuous fun f : C^∞⟮I, M; I', M'⟯ ↦ f.tangentMap ENat.coe_top_add_one.le := by
  have hmn : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := ENat.coe_top_add_one.le
  refine continuous_iff_continuousAt.mpr fun f₀ ↦ ?_
  refine tendsto_manifoldWeakWhitney_iff.mpr fun p q j hj K hK V hV h₀ ↦ ?_
  set φ := extChartAt I p.proj
  set ψ := extChartAt I' q.proj
  -- The base points of `K` form a compact subset `C` of the base chart target.
  set C : Set E := Prod.fst '' (Subtype.val '' K)
  have hCc : IsCompact C := (hK.image continuous_subtypeVal).image continuous_fst
  have hCT : C ⊆ φ.target := by
    rintro _ ⟨_, ⟨w, -, rfl⟩, rfl⟩
    exact Bundle.fst_mem_extChartAt_target p w.property
  have h₀' (w : (extChartAt I.tangent p).target) (hw : w ∈ K) :
      f₀ (φ.symm w.val.1) ∈ ψ.source :=
    (tangentMap_extChartAt_symm_mem_extChartAt_source_iff f₀).mp
      ((mem_chartJetSet.mp h₀) w hw).1
  have hC₀ : ∀ z ∈ C, f₀ (φ.symm z) ∈ ψ.source := by
    rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    exact h₀' w hw
  set K₁ : Set φ.target := Subtype.val ⁻¹' C
  have hK₁ : IsCompact K₁ := by
    refine Topology.IsEmbedding.subtypeVal.isCompact_iff.2 ?_
    rwa [Subtype.image_preimage_coe, inter_eq_right.2 hCT]
  -- On `K`, the chart derivative of the tangent map of `f₀` stays in a compact subset of `V`.
  let D (w : (extChartAt I.tangent p).target) := iteratedFDerivWithin 𝕜 j
    (extChartAt I'.tangent q ∘ f₀.tangentMap hmn ∘ (extChartAt I.tangent p).symm)
    (extChartAt I.tangent p).target w
  have hS : IsCompact (D '' K) :=
    hK.image_of_continuousOn fun w hw ↦ ((((f₀.tangentMap hmn).contDiffWithinAt_extChartAt
      w.property ((mem_chartJetSet.mp h₀) w hw).1).continuousWithinAt_iteratedFDerivWithin
        (uniqueDiffOn_extChartAt_target p) hj w.property).comp
          continuous_subtypeVal.continuousWithinAt fun v _ ↦ v.property)
  have hSV : D '' K ⊆ V := by
    rintro _ ⟨w, hw, rfl⟩
    exact ((mem_chartJetSet.mp h₀) w hw).2
  obtain ⟨δ, hδ, hδV⟩ := hS.exists_thickening_subset_open hV hSV
  -- A bound for the fibre coordinates on `K`, and the precision needed in the base.
  obtain ⟨R, hR⟩ := (hK.image (continuous_norm.comp
    (continuous_snd.comp continuous_subtypeVal))).bddAbove
  set A : ℝ := ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)
  have hA : 0 ≤ A := Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _
  set ε := δ / ((1 + |R|) * (A + 1))
  have hε : 0 < ε := div_pos hδ (by positivity)
  -- Nearby maps are visible in the base charts on `C` with nearby chart derivatives there.
  have hvis : chartJetSet (J := I') (n := ∞) p.proj q.proj 0 K₁ univ ∈ 𝓝 f₀ :=
    (isOpen_chartJetSet _ _ 0 (by simp) hK₁ isOpen_univ).mem_nhds
      (mem_chartJetSet.mpr fun z hz ↦ ⟨hC₀ z hz, mem_univ _⟩)
  have hunif : ∀ i ∈ Finset.range (j + 2), ∀ᶠ f : C^∞⟮I, M; I', M'⟯ in 𝓝 f₀, ∀ z ∈ C,
      dist (iteratedFDerivWithin 𝕜 i (ψ ∘ f₀ ∘ φ.symm) φ.target z)
        (iteratedFDerivWithin 𝕜 i (ψ ∘ f ∘ φ.symm) φ.target z) < ε := fun i _ ↦
    Metric.tendstoUniformlyOn_iff.mp (tendstoUniformlyOn_iteratedFDerivWithin_extChartAt hCc hCT
      hC₀ (by exact_mod_cast le_top)) ε hε
  filter_upwards [hvis, (eventually_all_finset _).2 hunif] with f hf hfu
  have hfC (z : E) (hz : z ∈ C) : f (φ.symm z) ∈ ψ.source :=
    ((mem_chartJetSet.mp hf) ⟨z, hCT hz⟩ hz).1
  refine mem_chartJetSet.mpr fun w hw ↦ ⟨?_, hδV (Metric.mem_thickening_iff.mpr
    ⟨_, mem_image_of_mem D hw, ?_⟩)⟩
  · rw [coe_tangentMap, tangentMap_extChartAt_symm_mem_extChartAt_source_iff f]
    exact hfC _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
  have hwC : w.val.1 ∈ C := ⟨_, ⟨w, hw, rfl⟩, rfl⟩
  have hd (i : ℕ) (hi : i ≤ j + 1) :
      ‖iteratedFDerivWithin 𝕜 i (ψ ∘ f ∘ φ.symm) φ.target w.val.1 -
        iteratedFDerivWithin 𝕜 i (ψ ∘ f₀ ∘ φ.symm) φ.target w.val.1‖ < ε := by
    rw [← dist_eq_norm, dist_comm]
    exact hfu i (Finset.mem_range.mpr (by omega)) _ hwC
  have hv : ‖w.val.2‖ ≤ |R| := (hR ⟨w, hw, rfl⟩).trans (le_abs_self R)
  have hR0 : 0 ≤ |R| := abs_nonneg R
  refine (dist_iteratedFDerivWithin_extChartAt_tangentMap_le f f₀ w.property
    (hfC _ hwC) (hC₀ _ hwC) j).trans_lt (max_lt ?_ ?_)
  · refine (hd j (Nat.le_succ j)).trans_le ?_
    exact div_le_self hδ.le (by nlinarith [mul_nonneg hR0 hA])
  · have hsum : ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
        ‖iteratedFDerivWithin 𝕜 (i + 1) (ψ ∘ f ∘ φ.symm) φ.target w.val.1 -
          iteratedFDerivWithin 𝕜 (i + 1) (ψ ∘ f₀ ∘ φ.symm) φ.target w.val.1‖ ≤ A * ε := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun i hi ↦ ?_
      gcongr
      exact (hd (i + 1) (by have := Finset.mem_range.mp hi; omega)).le
    have hδε : δ = (1 + |R|) * (A + 1) * ε := by
      rw [mul_div_cancel₀ _ (by positivity)]
    calc (1 + ‖w.val.2‖) * _ ≤ (1 + |R|) * (A * ε) := by gcongr
      _ < δ := by rw [hδε]; nlinarith

end WeakWhitney

end ContMDiffMap

end
