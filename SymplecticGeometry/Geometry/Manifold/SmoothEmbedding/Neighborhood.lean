/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Constructions
public import Mathlib.Geometry.Manifold.Instances.Real
public import TauCeti.Geometry.Manifold.SmoothIsotopy.Basic
import Mathlib.Topology.MetricSpace.Thickening
import TauCeti.Geometry.Manifold.Immersion.Differential
import TauCeti.Geometry.Manifold.Immersion.Family
import TauCeti.Geometry.Manifold.Immersion.LocalDiffeomorph
import TauCeti.Geometry.Manifold.MFDeriv.Basic
import TauCeti.Geometry.Manifold.MFDeriv.LocalInjectivity
import TauCeti.Geometry.Manifold.MFDeriv.Prod

/-!
# Embeddings near a compact set

Let `G : Q × P → M` be a smooth family of maps between finite-dimensional manifolds, `P` and `M`
without boundary. Suppose that for every parameter `q` of a compact set `T`, the slice
`x ↦ G (q, x)` is injective on a compact set `K ⊆ P`, with injective differential at every point
of `K`. Then there are an open `U ⊇ T` and an open `V ⊇ K` such that every slice with parameter
in `U` is a smooth embedding of `V`.

The proof works with the map `(q, x) ↦ (q, G (q, x))`. Its differential at `(q, x)` is injective
when that of the slice at `q` is (Tau Ceti's `MDifferentiableAt.injective_mfderiv_fst_prod_iff`),
so it is locally injective near `T ×ˢ K` (Tau Ceti's `ContMDiffAt.exists_mem_nhds_injOn`, which
allows the boundary of a parameter manifold such as `unitInterval`). Being injective on
`T ×ˢ K`, it is injective near `T ×ˢ K` (`Set.InjOn.exists_isOpen_superset`). Injective
differentials of the slices persist near `T ×ˢ K`
(Tau Ceti's `ContMDiffAt.eventually_injective_mfderiv`). The tube lemma makes these
neighbourhoods products. On an open `V ⊇ K` with compact closure inside them, every slice is an
injective immersion that extends injectively to the compact closure of `V`, hence a topological
embedding of `V`.

## Main results

* `TauCeti.exists_isOpen_superset_forall_isSmoothEmbedding_of_injOn`: the slices with parameters
  near a compact set `T` are smooth embeddings near `K`, for any finite-dimensional parameter
  manifold.
* `TauCeti.exists_isOpen_forall_isSmoothEmbedding_of_injOn`: the case of `unitInterval`, where the
  slices at all times are smooth embeddings of one open `V ⊇ K`.
* `TauCeti.exists_pos_forall_isSmoothEmbedding_of_injOn`: for a family over `ℝ` whose slices at
  times in `[0, 1]` are injective immersions on `K`, the slices at times in `(-δ, 1 + δ)` are
  smooth embeddings of one open `V ⊇ K`, for some `δ > 0`.
* `TauCeti.exists_pos_forall_isSmoothEmbedding_of_eventuallyEq`: a map that agrees near a compact
  set with embeddings at times in `[0, 1]` has embedding slices near that set at nearby times.
* `TauCeti.exists_isOpen_isSmoothEmbedding_of_injOn`: a smooth map, injective on a compact set
  with injective differential there, is a smooth embedding of an open neighbourhood of it.
* `TauCeti.SmoothIsotopy.ofForallIsSmoothEmbedding`: a family over `unitInterval`, `Cⁿ` on
  `unitInterval × V` with `Cⁿ` embedding slices, as an isotopy of `V`.

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

namespace TauCeti

section

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [I.Boundaryless] [J.Boundaryless]
  [IsManifold I ∞ M] [IsManifold J ∞ P] [T2Space P] [T2Space M]

/-- **Embeddings near a compact set, uniformly in a compact set of parameters.** Let
`G : Q × P → M` be smooth on an open `W ⊇ T ×ˢ K`, with `T` and `K` compact, and let each slice
`x ↦ G (q, x)` with `q ∈ T` be injective on `K` with injective differential at each point of `K`.
Then there are open sets `U ⊇ T` and `V ⊇ K`, with `U ×ˢ V ⊆ W`, such that each slice with
`q ∈ U` is a smooth embedding of `V`. -/
theorem exists_isOpen_superset_forall_isSmoothEmbedding_of_injOn [FiniteDimensional ℝ EQ]
    [IsManifold IQ ∞ Q] [T2Space Q] {G : Q × P → M} {W : Set (Q × P)} (hW : IsOpen W)
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
      have h := hGat p (hTK hp)
      exact (contMDiffAt_fst.prodMk h).exists_mem_nhds_injOn (by simp)
        ((h.mdifferentiableAt (by simp)).injective_mfderiv_fst_prod_iff.2 (himm p.1 hp.1 p.2 hp.2))
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

omit [FiniteDimensional ℝ E'] [T2Space P] in
/-- **Embedding slices near `[0, 1]`.** Let `G : ℝ × P → M` be smooth on an open set `S`
containing `[0, 1] ×ˢ A`, with `A` compact, and let `F` be a family over `[0, 1]` of smooth
embeddings of `P` into `M` such that, at each time `t ∈ [0, 1]`, the slice of `G` agrees with that
of `F` near `A`. Then there are `δ > 0` and an open `V ⊇ A` with `(-δ, 1 + δ) ×ˢ V ⊆ S` such
that the slices of `G` at times in `(-δ, 1 + δ)` are smooth embeddings of `V`. -/
theorem exists_pos_forall_isSmoothEmbedding_of_eventuallyEq {S : Set (ℝ × P)} (hS : IsOpen S)
    {G : ℝ × P → M} (hG : ContMDiffOn (𝓘(ℝ).prod J) I ∞ G S) {A : Set P} (hA : IsCompact A)
    (hAS : Icc 0 1 ×ˢ A ⊆ S) {F : unitInterval × P → M}
    (hF : ∀ t, Manifold.IsSmoothEmbedding J I ∞ fun x ↦ F (t, x))
    (hGF : ∀ t (ht : t ∈ Icc (0 : ℝ) 1),
      (fun x ↦ G (t, x)) =ᶠ[𝓝ˢ A] fun x ↦ F (⟨t, ht⟩, x)) :
    ∃ δ > 0, ∃ V : TopologicalSpace.Opens P, A ⊆ V ∧ Ioo (-δ) (1 + δ) ×ˢ (V : Set P) ⊆ S ∧
      ∀ t ∈ Ioo (-δ) (1 + δ), Manifold.IsSmoothEmbedding J I ∞ (fun x : V ↦ G (t, x)) := by
  rcases isEmpty_or_nonempty P with _ | ⟨⟨x₀⟩⟩
  · -- For an empty `P`, the empty open set will do.
    refine ⟨1, one_pos, ⊥, fun x _ ↦ isEmptyElim x, fun p _ ↦ isEmptyElim p.2, fun t _ ↦ ?_⟩
    have h : (fun x : (⊥ : TopologicalSpace.Opens P) ↦ G (t, x)) =
        fun x : (⊥ : TopologicalSpace.Opens P) ↦ F (0, x) :=
      funext fun x ↦ isEmptyElim (x : P)
    exact h ▸ (hF 0).comp_subtypeVal ⊥
  -- `P` is Hausdorff and its model finite-dimensional, since `F` embeds `P` into `M`.
  have : T2Space P := (hF 0).isEmbedding.t2Space
  have : FiniteDimensional ℝ E' :=
    finiteDimensional_of_injective_mfderiv ((hF 0).isImmersion.mfderiv_injective (by simp) x₀)
  exact exists_pos_forall_isSmoothEmbedding_of_injOn hS hG hA hAS
    (fun t ht x hx y hy hxy ↦ (hF ⟨t, ht⟩).isEmbedding.injective <| by
      simpa only [(hGF t ht).self_of_nhdsSet hx, (hGF t ht).self_of_nhdsSet hy] using hxy)
    fun t ht x hx ↦ by
      rw [((hGF t ht).filter_mono (nhds_le_nhdsSet hx)).mfderiv_eq]
      exact (hF ⟨t, ht⟩).isImmersion.mfderiv_injective (by simp) x

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
`Cⁿ` on `unitInterval × V` and whose slices are `Cⁿ` embeddings of `V`, from the slice `f₀`
at time `0` to the slice `f₁` at time `1`. -/
def ofForallIsSmoothEmbedding {n : WithTop ℕ∞} {V : TopologicalSpace.Opens P}
    {G : unitInterval × P → M}
    (hG : ContMDiffOn ((𝓡∂ 1).prod J) I n G (univ ×ˢ (V : Set P)))
    (hemb : ∀ t, Manifold.IsSmoothEmbedding J I n (fun x : V ↦ G (t, x)))
    {f₀ f₁ : C^n⟮J, V; I, M⟯} (h₀ : ∀ x : V, G (0, x) = f₀ x) (h₁ : ∀ x : V, G (1, x) = f₁ x) :
    SmoothIsotopy f₀ f₁ where
  toContMDiffMap := ⟨fun p ↦ G (p.1, p.2),
    hG.comp_contMDiff (contMDiff_fst.prodMk (contMDiff_subtypeVal.comp contMDiff_snd))
      fun p ↦ ⟨mem_univ _, p.2.property⟩⟩
  map_zero_left := h₀
  map_one_left := h₁
  isSmoothEmbedding := hemb

@[simp]
theorem ofForallIsSmoothEmbedding_apply {n : WithTop ℕ∞} {V : TopologicalSpace.Opens P}
    {G : unitInterval × P → M} (hG : ContMDiffOn ((𝓡∂ 1).prod J) I n G (univ ×ˢ (V : Set P)))
    (hemb : ∀ t, Manifold.IsSmoothEmbedding J I n (fun x : V ↦ G (t, x)))
    {f₀ f₁ : C^n⟮J, V; I, M⟯} (h₀ : ∀ x : V, G (0, x) = f₀ x) (h₁ : ∀ x : V, G (1, x) = f₁ x)
    (p : unitInterval × V) : ofForallIsSmoothEmbedding hG hemb h₀ h₁ p = G (p.1, p.2) :=
  (rfl)

end SmoothIsotopy

end TauCeti

end
