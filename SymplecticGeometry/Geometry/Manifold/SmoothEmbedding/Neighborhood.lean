/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Geometry.Manifold.ContMDiff.Constructions
public import Mathlib.Geometry.Manifold.Instances.Real
public import TauCeti.Geometry.Manifold.SmoothIsotopy.Basic
import Mathlib.Topology.MetricSpace.Thickening
import TauCeti.Geometry.Manifold.Immersion.Differential
import TauCeti.Geometry.Manifold.Immersion.Family
import TauCeti.Geometry.Manifold.Immersion.LocalDiffeomorph

/-!
# Embeddings near a compact set

Let `G : Q × P → M` be a smooth family of maps between finite-dimensional manifolds, `P` and `M`
without boundary. Suppose that for every parameter `q` of a compact set `T`, the slice
`x ↦ G (q, x)` is injective on a compact set `K ⊆ P`, with injective differential at every point
of `K`. Then there are an open `U ⊇ T` and an open `V ⊇ K` such that every slice with parameter
in `U` is a smooth embedding of `V`.

The proof first shows that the slices near a point `(q₀, x₀)` at which the slice at `q₀` has
injective differential are injective on one neighbourhood of `x₀`, for all `q` near `q₀`. In the
charts at `x₀` and at `G (q₀, x₀)`, the partial derivatives in the space variable are close to
the one at `(q₀, x₀)`, which is injective. By the mean value inequality each slice differs from
that derivative by a map of small Lipschitz constant on a ball, so it is injective there
(`AntilipschitzWith.add_sub_lipschitzWith`). Only the derivative in the space variable is used, so the parameter manifold may
have boundary, as `unitInterval` does. Then the map `(q, x) ↦ (q, G (q, x))` is injective on
`T ×ˢ K` and locally injective there, so it is injective near `T ×ˢ K`
(`Set.InjOn.exists_isOpen_superset`), and injective differentials persist near `T ×ˢ K`
(Tau Ceti's `ContMDiffAt.eventually_injective_mfderiv`). The tube lemma makes these
neighbourhoods products. On an open `V ⊇ K` with compact closure inside them, every slice is an
injective immersion that extends injectively to the compact closure of `V`, hence a topological
embedding of `V`.

## Main results

* `ContMDiffAt.exists_mem_nhds_injOn_of_injective_mfderiv`: in a `C¹` family whose slice at `q₀`
  has injective differential at `x₀`, the slices near `q₀` are injective on one neighbourhood
  of `x₀`.
* `TauCeti.exists_isOpen_superset_forall_isSmoothEmbedding_of_injOn`: the slices with parameters
  near a compact set `T` are smooth embeddings near `K`, for any parameter manifold.
* `TauCeti.exists_isOpen_forall_isSmoothEmbedding_of_injOn`: the case of `unitInterval`, where the
  slices at all times are smooth embeddings of one open `V ⊇ K`.
* `TauCeti.exists_pos_forall_isSmoothEmbedding_of_injOn`: for a family over `ℝ` whose slices at
  times in `[0, 1]` are injective immersions on `K`, the slices at times in `(-δ, 1 + δ)` are
  smooth embeddings of one open `V ⊇ K`, for some `δ > 0`.
* `TauCeti.exists_isOpen_isSmoothEmbedding_of_injOn`: a smooth map, injective on a compact set
  with injective differential there, is a smooth embedding of an open neighbourhood of it.
* `TauCeti.SmoothIsotopy.ofForallIsSmoothEmbedding`: a family over `unitInterval`, smooth on
  `unitInterval × V` with embedding slices, as a smooth isotopy of `V`.

## References

* M. Hirsch, *Differential Topology*, Springer GTM 33 (1976), Chapter 1, §3 (immersions and
  embeddings) and Chapter 8, §1 (isotopies of embeddings, which this file serves).

The step from local to global injectivity is Mathlib's `Set.InjOn.exists_isOpen_superset`, as in
Tau Ceti's `Set.InjOn.exists_isOpen_superset_isLocalDiffeomorphOn`.
-/

public section

open Set Function Filter Topology Manifold
open scoped ContDiff Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H' P]
  {EQ : Type*} [NormedAddCommGroup EQ] [NormedSpace ℝ EQ]
  {HQ : Type*} [TopologicalSpace HQ] {IQ : ModelWithCorners ℝ EQ HQ}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace HQ Q]

/-- **Uniform local injectivity in a family.** Let `G : Q × P → M` be `C¹` at `(q₀, x₀)`, with `P`
boundaryless and finite-dimensional, and let the slice `x ↦ G (q₀, x)` have injective differential
at `x₀`. Then there are neighbourhoods `U` of `q₀` and `V` of `x₀` such that the slice
`x ↦ G (q, x)` is injective on `V` for every `q ∈ U`. The parameter manifold `Q` may have
boundary. -/
theorem ContMDiffAt.exists_mem_nhds_injOn_of_injective_mfderiv [J.Boundaryless]
    [FiniteDimensional ℝ E'] {G : Q × P → M} {q₀ : Q} {x₀ : P} {n : ℕ∞ω}
    (hG : ContMDiffAt (IQ.prod J) I n G (q₀, x₀)) (hn : 1 ≤ n)
    (hinj : Injective (mfderiv J I (fun x ↦ G (q₀, x)) x₀)) :
    ∃ U ∈ 𝓝 q₀, ∃ V ∈ 𝓝 x₀, ∀ q ∈ U, InjOn (fun x ↦ G (q, x)) V := by
  set χ := extChartAt IQ q₀
  set φ := extChartAt J x₀
  set ψ := extChartAt I (G (q₀, x₀))
  -- `G` read in the charts at `q₀`, `x₀` and `G (q₀, x₀)`.
  set g : EQ × E' → E := fun p ↦ ψ (G (χ.symm p.1, φ.symm p.2)) with hg_def
  set S : Set (EQ × E') := range IQ ×ˢ univ
  set z₀ : EQ × E' := (χ q₀, φ x₀)
  have hz₀ : z₀ ∈ S := ⟨mem_range_self _, mem_univ _⟩
  have hg : ContDiffWithinAt ℝ 1 g S z₀ := by
    have h := (contMDiffAt_iff.1 (hG.of_le hn)).2
    rw [extChartAt_prod, PartialEquiv.prod_coe_symm, ModelWithCorners.range_prod,
      J.range_eq_univ] at h
    exact h
  -- Partial derivatives in the space variable, continuous at `z₀` within `S`.
  obtain ⟨v, hv, -, f', hf', hf'c⟩ := ContDiffWithinAt.hasFDerivWithinAt_nhds (n := 0)
    (f := fun (z : EQ × E') (w : E') ↦ g (z.1, w)) (g := Prod.snd) (t := univ) (by simp)
    (by
      rw [insert_eq_of_mem hz₀, zero_add]
      exact ContDiffWithinAt.comp (g := g) (f := fun z : (EQ × E') × E' ↦ (z.1.1, z.2))
        (t := S) (s := S ×ˢ univ) (z₀, z₀.2) hg
        ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd).contDiffWithinAt
        fun z hz ↦ ⟨hz.1.1, mem_univ _⟩)
    contDiff_snd.contDiffWithinAt univ_mem
  rw [insert_eq_of_mem hz₀] at hv
  set D₀ := f' z₀
  -- `D₀` is the differential of the slice at `q₀`, read in charts.
  have hD₀ : HasFDerivAt (writtenInExtChartAt J I x₀ fun x ↦ G (q₀, x)) D₀ (φ x₀) := by
    have h := hasFDerivWithinAt_univ.1 (hf' z₀ (mem_of_mem_nhdsWithin hz₀ hv))
    have heq : (fun w ↦ g (z₀.1, w)) = writtenInExtChartAt J I x₀ fun x ↦ G (q₀, x) := by
      ext w
      simp [hg_def, z₀, χ, φ, ψ, writtenInExtChartAt]
    rwa [heq] at h
  have hinjD : Injective D₀ := by
    have hmd : MDifferentiableAt J I (fun x ↦ G (q₀, x)) x₀ :=
      ((hG.of_le hn).comp x₀ (contMDiffAt_const.prodMk contMDiffAt_id)).mdifferentiableAt
        one_ne_zero
    rw [hmd.mfderiv, J.range_eq_univ, fderivWithin_univ, hD₀.fderiv] at hinj
    simpa only [ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe,
      EquivLike.comp_injective, EquivLike.injective_comp] using hinj
  obtain ⟨K, hK, hKD⟩ := (LinearMap.injective_iff_antilipschitz (D₀ : E' →ₗ[ℝ] E)).1 hinjD
  obtain ⟨ε, hε, hεK⟩ := exists_between (inv_pos.2 hK)
  -- Near `z₀`, the partial derivatives stay within `ε` of `D₀`.
  have hnear : ∀ᶠ z in 𝓝[S] z₀, z ∈ v ∧ ‖f' z - D₀‖₊ ≤ ε := by
    filter_upwards [hv, hf'c.continuousWithinAt.tendsto.eventually
      (Metric.closedBall_mem_nhds D₀ (NNReal.coe_pos.2 hε))] with z hz hz'
    refine ⟨hz, ?_⟩
    rw [← NNReal.coe_le_coe, coe_nnNorm]
    simpa [dist_eq_norm] using hz'
  rw [nhdsWithin_prod_eq, nhdsWithin_univ] at hnear
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_prod_iff.1 hnear
  obtain ⟨r, hr, hrB⟩ := Metric.mem_nhds_iff.1 hB
  have hAq : χ ⁻¹' A ∈ 𝓝 q₀ := by
    rw [← map_extChartAt_nhds] at hA
    exact hA
  refine ⟨χ ⁻¹' A ∩ χ.source, inter_mem hAq (extChartAt_source_mem_nhds q₀),
    φ.source ∩ φ ⁻¹' Metric.ball (φ x₀) r, inter_mem (extChartAt_source_mem_nhds x₀)
      ((continuousAt_extChartAt x₀).preimage_mem_nhds (Metric.ball_mem_nhds _ hr)), ?_⟩
  rintro q ⟨hqA, hq⟩ x ⟨hx, hxr⟩ y ⟨hy, hyr⟩ (hxy : G (q, x) = G (q, y))
  have hgq : ∀ x ∈ φ.source, g (χ q, φ x) = ψ (G (q, x)) := fun x hx ↦ by
    simp only [hg_def, χ.left_inv hq, φ.left_inv hx]
  -- On the ball, the slice at `q` read in charts differs from `D₀` by an `ε`-Lipschitz map, so it
  -- is injective there.
  have hlip := (convex_ball (φ x₀) r).lipschitzOnWith_of_nnNorm_hasFDerivWithin_le
    (f := fun w ↦ g (χ q, w) - D₀ w) (f' := fun w ↦ f' (χ q, w) - D₀) (C := ε)
    (fun w hw ↦ ((hasFDerivWithinAt_univ.1 (hf' (χ q, w)
      (hAB (mk_mem_prod hqA (hrB hw))).1)).sub D₀.hasFDerivAt).hasFDerivWithinAt)
    fun w hw ↦ (hAB (mk_mem_prod hqA (hrB hw))).2
  have hinjq : InjOn (fun w ↦ g (χ q, w)) (Metric.ball (φ x₀) r) :=
    injOn_iff_injective.2
      ((hKD.domRestrict _).add_sub_lipschitzWith hlip.to_restrict hεK).injective
  exact φ.injOn hx hy (hinjq hxr hyr (by simp only [hgq x hx, hgq y hy, hxy]))

namespace TauCeti

section

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [I.Boundaryless] [J.Boundaryless]
  [IsManifold I ∞ M] [IsManifold J ∞ P] [T2Space P] [T2Space M]

/-- **Embeddings near a compact set, uniformly in a compact set of parameters.** Let
`G : Q × P → M` be smooth on an open `W ⊇ T ×ˢ K`, with `T` and `K` compact, and let each slice
`x ↦ G (q, x)` with `q ∈ T` be injective on `K` with injective differential at each point of `K`.
Then there are open sets `U ⊇ T` and `V ⊇ K`, with `U ×ˢ V ⊆ W`, such that each slice with
`q ∈ U` is a smooth embedding of `V`. -/
theorem exists_isOpen_superset_forall_isSmoothEmbedding_of_injOn [IsManifold IQ ∞ Q]
    [T2Space Q] {G : Q × P → M} {W : Set (Q × P)} (hW : IsOpen W)
    (hG : ContMDiffOn (IQ.prod J) I ∞ G W) {T : Set Q} (hT : IsCompact T) {K : Set P}
    (hK : IsCompact K) (hTK : T ×ˢ K ⊆ W) (hinj : ∀ q ∈ T, InjOn (fun x ↦ G (q, x)) K)
    (himm : ∀ q ∈ T, ∀ x ∈ K, Injective (mfderiv J I (fun x ↦ G (q, x)) x)) :
    ∃ U : Set Q, IsOpen U ∧ T ⊆ U ∧ ∃ V : TopologicalSpace.Opens P, K ⊆ V ∧
      U ×ˢ (V : Set P) ⊆ W ∧
        ∀ q ∈ U, Manifold.IsSmoothEmbedding J I ∞ (fun x : V ↦ G (q, x)) := by
  have hGat : ∀ p ∈ W, ContMDiffAt (IQ.prod J) I ∞ G p := fun p hp ↦
    hG.contMDiffAt (hW.mem_nhds hp)
  -- The track `(q, x) ↦ (q, G (q, x))` is injective near `T ×ˢ K`.
  have htrack : ∀ {s : Set (Q × P)}, (∀ q, InjOn (fun x ↦ G (q, x)) {x | (q, x) ∈ s}) →
      InjOn (fun p : Q × P ↦ (p.1, G p)) s := by
    rintro s hs ⟨q, x⟩ hx ⟨q', y⟩ hy hxy
    obtain ⟨rfl, hxy⟩ := Prod.ext_iff.1 hxy
    exact congrArg (Prod.mk q) (hs q hx hy hxy)
  obtain ⟨W₁, hW₁o, hTKW₁, hW₁⟩ := Set.InjOn.exists_isOpen_superset
    (htrack (s := T ×ˢ K) fun q x hx y hy ↦ hinj q hx.1 hx.2 hy.2) (hT.prod hK)
    (fun p hp ↦ continuousAt_fst.prodMk (hGat p (hTK hp)).continuousAt) fun p hp ↦ by
      obtain ⟨U, hU, V, hV, h⟩ := (hGat p (hTK hp)).exists_mem_nhds_injOn_of_injective_mfderiv
        (by simp) (himm p.1 hp.1 p.2 hp.2)
      exact ⟨U ×ˢ V, prod_mem_nhds hU hV,
        htrack (s := U ×ˢ V) fun q x hx y hy ↦ h q hx.1 hx.2 hy.2⟩
  -- Injective differentials persist near `T ×ˢ K`.
  have hdiff : ∀ᶠ p in 𝓝ˢ (T ×ˢ K), Injective (mfderiv J I (fun x ↦ G (p.1, x)) p.2) :=
    eventually_nhdsSet_iff_forall.2 fun p hp ↦
      ContMDiffAt.eventually_injective_mfderiv (F := curry G) (hGat p (hTK hp)) (by simp)
        (himm p.1 hp.1 p.2 hp.2)
  have hW₁' : ∀ᶠ p in 𝓝ˢ (T ×ˢ K), p ∈ W₁ := hW₁o.mem_nhdsSet.2 hTKW₁
  have hW' : ∀ᶠ p in 𝓝ˢ (T ×ˢ K), p ∈ W := hW.mem_nhdsSet.2 hTK
  obtain ⟨N, hNo, hTKN, hN⟩ := mem_nhdsSet_iff_exists.1 (hW₁'.and (hW'.and hdiff))
  obtain ⟨U, V₁, hUo, hV₁o, hTU, hKV₁, hUV₁⟩ := generalized_tube_lemma hT hK hNo hTKN
  have := Manifold.locallyCompact_of_finiteDimensional (M := P) J
  obtain ⟨V, hVo, hKV, hVV₁, hVc⟩ := exists_open_between_and_isCompact_closure hK hV₁o hKV₁
  have hUV : ∀ {q x}, q ∈ U → x ∈ closure V → (q, x) ∈ N := fun hq hx ↦ hUV₁ ⟨hq, hVV₁ hx⟩
  refine ⟨U, hUo, hTU, ⟨V, hVo⟩, hKV, fun p hp ↦ (hN (hUV hp.1 (subset_closure hp.2))).2.1,
    fun q hq ↦ ?_⟩
  have hsm : ContMDiffOn J I ∞ (fun x ↦ G (q, x)) {x | (q, x) ∈ W} :=
    hG.comp (contMDiffOn_const.prodMk contMDiffOn_id) fun x hx ↦ hx
  have hWo : IsOpen {x | (q, x) ∈ W} := hW.preimage (Continuous.prodMk_right q)
  have hcW : closure V ⊆ {x | (q, x) ∈ W} := fun x hx ↦ (hN (hUV hq hx)).2.1
  refine ⟨isImmersion_comp_subtypeVal_iff.2 fun x hx ↦
    (hsm.isImmersionAt_iff_injective_mfderiv hWo (hcW (subset_closure hx)) (by simp)).2
      (hN (hUV hq (subset_closure hx))).2.2, ?_⟩
  -- The slice is injective and continuous on the compact closure of `V`.
  have hcinj : Injective ((closure V).domRestrict fun x ↦ G (q, x)) := fun x y hxy ↦
    Subtype.ext (congrArg Prod.snd (hW₁ (hN (hUV hq x.property)).1 (hN (hUV hq y.property)).1
      (Prod.ext rfl hxy : ((q, (x : P)).1, G (q, x)) = ((q, (y : P)).1, G (q, y)))))
  have : CompactSpace (closure V) := isCompact_iff_compactSpace.1 hVc
  have hce := ((hsm.continuousOn.mono hcW).domRestrict).isClosedEmbedding hcinj
  exact hce.isEmbedding.comp (IsEmbedding.inclusion subset_closure)

/-- **Embeddings near a compact set, along an isotopy.** Let `G : unitInterval × P → M` be smooth
on `unitInterval × O`, for an open `O ⊇ K` with `K` compact, and let each slice `x ↦ G (t, x)` be
injective on `K` with injective differential at each point of `K`. Then there is an open `V`
with `K ⊆ V ⊆ O` such that every slice is a smooth embedding of `V`. -/
theorem exists_isOpen_forall_isSmoothEmbedding_of_injOn {G : unitInterval × P → M} {O : Set P}
    (hO : IsOpen O) (hG : ContMDiffOn ((𝓡∂ 1).prod J) I ∞ G (univ ×ˢ O)) {K : Set P}
    (hK : IsCompact K) (hKO : K ⊆ O) (hinj : ∀ t, InjOn (fun x ↦ G (t, x)) K)
    (himm : ∀ t, ∀ x ∈ K, Injective (mfderiv J I (fun x ↦ G (t, x)) x)) :
    ∃ V : TopologicalSpace.Opens P, K ⊆ V ∧ (V : Set P) ⊆ O ∧
      ∀ t, Manifold.IsSmoothEmbedding J I ∞ (fun x : V ↦ G (t, x)) := by
  obtain ⟨U, -, hU, V, hKV, hVW, hV⟩ := exists_isOpen_superset_forall_isSmoothEmbedding_of_injOn
    (isOpen_univ.prod hO) hG isCompact_univ hK (prod_mono subset_rfl hKO)
    (fun t _ ↦ hinj t) fun t _ ↦ himm t
  exact ⟨V, hKV, fun x hx ↦ (hVW (mk_mem_prod (hU (mem_univ 0)) hx)).2,
    fun t ↦ hV t (hU (mem_univ t))⟩

/-- **Embeddings near a compact set, for times near `[0, 1]`.** Let `G : ℝ × P → M` be smooth on
an open `W ⊇ [0, 1] ×ˢ K`, with `K` compact, and let each slice `x ↦ G (t, x)` with `t ∈ [0, 1]`
be injective on `K` with injective differential at each point of `K`. Then there are `δ > 0` and
an open `V ⊇ K`, with `(-δ, 1 + δ) ×ˢ V ⊆ W`, such that every slice at a time in `(-δ, 1 + δ)`
is a smooth embedding of `V`. -/
theorem exists_pos_forall_isSmoothEmbedding_of_injOn {G : ℝ × P → M} {W : Set (ℝ × P)}
    (hW : IsOpen W) (hG : ContMDiffOn (𝓘(ℝ).prod J) I ∞ G W) {K : Set P} (hK : IsCompact K)
    (hKW : Icc 0 1 ×ˢ K ⊆ W) (hinj : ∀ t ∈ Icc (0 : ℝ) 1, InjOn (fun x ↦ G (t, x)) K)
    (himm : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ K, Injective (mfderiv J I (fun x ↦ G (t, x)) x)) :
    ∃ δ > 0, ∃ V : TopologicalSpace.Opens P, K ⊆ V ∧ Ioo (-δ) (1 + δ) ×ˢ (V : Set P) ⊆ W ∧
      ∀ t ∈ Ioo (-δ) (1 + δ), Manifold.IsSmoothEmbedding J I ∞ (fun x : V ↦ G (t, x)) := by
  obtain ⟨U, hUo, hU, V, hKV, hVW, hV⟩ := exists_isOpen_superset_forall_isSmoothEmbedding_of_injOn
    hW hG isCompact_Icc hK hKW hinj himm
  obtain ⟨δ, hδ, hδU⟩ := isCompact_Icc.exists_thickening_subset_open hUo hU
  have hIoo : Ioo (-δ) (1 + δ) ⊆ U := fun t ht ↦ hδU <| Metric.mem_thickening_iff.2
    ⟨max 0 (min t 1), ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩, by
      rcases le_total t 0 with h0 | h0
      · rw [min_eq_left (h0.trans zero_le_one), max_eq_left h0, Real.dist_eq, sub_zero, abs_lt]
        constructor <;> linarith [ht.1]
      · rcases le_total t 1 with h1 | h1
        · rwa [min_eq_left h1, max_eq_right h0, dist_self]
        · rw [min_eq_right h1, max_eq_right zero_le_one, Real.dist_eq, abs_lt]
          constructor <;> linarith [ht.2]⟩
  exact ⟨δ, hδ, V, hKV, (prod_mono hIoo subset_rfl).trans hVW, fun t ht ↦ hV t (hIoo ht)⟩

/-- **Injective immersions of a compact set.** Let `f : P → M` be smooth on an open `O ⊇ K`, with
`K` compact, injective on `K` with injective differential at each point of `K`. Then there is an
open `V` with `K ⊆ V ⊆ O` on which `f` is a smooth embedding. -/
theorem exists_isOpen_isSmoothEmbedding_of_injOn {f : P → M} {O : Set P} (hO : IsOpen O)
    (hf : ContMDiffOn J I ∞ f O) {K : Set P} (hK : IsCompact K) (hKO : K ⊆ O) (hinj : InjOn f K)
    (himm : ∀ x ∈ K, Injective (mfderiv J I f x)) :
    ∃ V : TopologicalSpace.Opens P, K ⊆ V ∧ (V : Set P) ⊆ O ∧
      Manifold.IsSmoothEmbedding J I ∞ (fun x : V ↦ f x) := by
  obtain ⟨V, hKV, hVO, hV⟩ := exists_isOpen_forall_isSmoothEmbedding_of_injOn
    (G := fun p : unitInterval × P ↦ f p.2) hO
    (hf.comp contMDiffOn_snd fun _ hp ↦ hp.2) hK hKO (fun _ ↦ hinj) fun _ ↦ himm
  exact ⟨V, hKV, hVO, hV 0⟩

end

namespace SmoothIsotopy

/-- The smooth isotopy of an open `V ⊆ P` given by a family `G : unitInterval × P → M` that is
smooth on `unitInterval × V` and whose slices are smooth embeddings of `V`, from the slice `f₀`
at time `0` to the slice `f₁` at time `1`. -/
def ofForallIsSmoothEmbedding {V : TopologicalSpace.Opens P} {G : unitInterval × P → M}
    (hG : ContMDiffOn ((𝓡∂ 1).prod J) I ∞ G (univ ×ˢ (V : Set P)))
    (hemb : ∀ t, Manifold.IsSmoothEmbedding J I ∞ (fun x : V ↦ G (t, x)))
    {f₀ f₁ : C^∞⟮J, V; I, M⟯} (h₀ : ∀ x : V, G (0, x) = f₀ x) (h₁ : ∀ x : V, G (1, x) = f₁ x) :
    SmoothIsotopy f₀ f₁ where
  toContMDiffMap := ⟨fun p ↦ G (p.1, p.2),
    hG.comp_contMDiff (contMDiff_fst.prodMk (contMDiff_subtypeVal.comp contMDiff_snd))
      fun p ↦ ⟨mem_univ _, p.2.property⟩⟩
  map_zero_left := h₀
  map_one_left := h₁
  isSmoothEmbedding := hemb

@[simp]
theorem ofForallIsSmoothEmbedding_apply {V : TopologicalSpace.Opens P}
    {G : unitInterval × P → M} (hG : ContMDiffOn ((𝓡∂ 1).prod J) I ∞ G (univ ×ˢ (V : Set P)))
    (hemb : ∀ t, Manifold.IsSmoothEmbedding J I ∞ (fun x : V ↦ G (t, x)))
    {f₀ f₁ : C^∞⟮J, V; I, M⟯} (h₀ : ∀ x : V, G (0, x) = f₀ x) (h₁ : ∀ x : V, G (1, x) = f₁ x)
    (p : unitInterval × V) : ofForallIsSmoothEmbedding hG hemb h₀ h₁ p = G (p.1, p.2) :=
  (rfl)

end SmoothIsotopy

end TauCeti

end
