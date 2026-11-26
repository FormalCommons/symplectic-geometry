/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Geometry.Manifold.ContMDiffMap
public import TauCeti.Geometry.Manifold.Morse.Hessian
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic
import Mathlib.Geometry.Manifold.Algebra.Monoid
import SymplecticGeometry.Analysis.Calculus.Morse.HalfCylinder
import SymplecticGeometry.Geometry.Manifold.Morse.Hessian
import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.Indicator
import TauCeti.Geometry.Manifold.ContMDiff.Prod
import TauCeti.Geometry.Manifold.Morse.Generic.Strong
import SymplecticGeometry.Geometry.Manifold.ProperRay
import SymplecticGeometry.Geometry.Manifold.TubularNeighborhood.Ray
import SymplecticGeometry.Geometry.Manifold.Morse.PositiveDirection
import SymplecticGeometry.Topology.Compactness.Paracompact
import SymplecticGeometry.Topology.Maps.Proper
import SymplecticGeometry.Geometry.Manifold.IsManifold.SecondCountable

/-!
# Morse functions on open manifolds without critical points of top index

On a manifold of dimension `n ≠ 1` with no compact connected component, there is a proper Morse
function, bounded below, with no critical point of index `n`
(`TauCeti.exists_isMorse_isProperMap_manifoldMorseIndex_lt`). The main step raises a function
inside tubes. Let `M` be a boundaryless manifold of dimension `dim V + 1`, and let
`Φ i : ℝ × V → M` be smooth embeddings whose half-cylinders `Φ i '' S`,
`S = [-1, ∞) × closedBall 0 1`, are closed, pairwise disjoint and locally finite.
If a smooth `g₀ : M → ℝ` has, in each half-cylinder, no critical point other than `Φ i 0`, then
`g₀` can be raised inside the half-cylinders to a smooth `g₁` at whose critical points in them the
critical Hessian is positive on some vector, so none of these critical points is a nondegenerate
local maximum.

## Main results

* `TauCeti.exists_le_criticalHessian_pos_of_tubes`: the function `g₁`.
* `TauCeti.exists_isMorse_isProperMap_manifoldMorseIndex_lt`: proper Morse functions without
  critical points of top index.

## Construction

For each `i`, `SymplecticGeometry.exists_nonneg_halfCylinder_hessian_pos` applied to `g₀ ∘ Φ i`
gives `μ i ≥ 0` supported in `S`. Pushed forward along `Φ i` and extended by zero off its range,
`μ i` becomes a smooth function on `M` supported in `Φ i '' S`
(`TauCeti.SmoothEmbedding.contMDiff_indicator_range_comp_invFunOn`), and
`g₁ := g₀ + ∑ᶠ i, μ i ∘ (Φ i)⁻¹`. Near a point of `Φ i '' S` the
other half-cylinders are absent, so there `g₁ ∘ Φ i = g₀ ∘ Φ i + μ i`, and critical points and
positive Hessian directions are read through `Φ i`
(`TauCeti.SmoothEmbedding.mem_criticalPoints_iff_fderiv_comp_eq_zero_prod`,
`TauCeti.SmoothEmbedding.exists_criticalHessian_pos_iff_fderiv_fderiv_comp_prod`).

For the theorem, start from a proper Morse function `g₀` bounded below
(`TauCeti.exists_isMorse_isProperMap_bddBelow`), and let `P` be its critical points of index `n`
and `Q` the others; both are closed and discrete. Rays from `P` avoiding `Q`
(`SymplecticGeometry.exists_rays`) get pairwise disjoint, locally finite open neighbourhoods
`O p` missing `Q` (`LocallyFinite.exists_isOpen_superset_pairwise_disjoint`), and tubes `Φ p`
around them whose closed parts `Φ p '' ([-2, ∞) × closedBall 0 2)` lie in `O p`
(`TauCeti.SmoothEmbedding.exists_rayTube`). In such a closed part the only critical point of
`g₀` is `p`. Raising `g₀` inside the tubes gives `g₁`, with a positive Hessian direction at its
critical points in the union `A` of these closed parts. A strong `C²` control keeps this
property (`TauCeti.exists_strongCkControl_criticalHessian_pos`), and a Morse approximation `g`
of `g₁` in it that equals `g₁` near the complement of the interior of `A`
(`ContMDiffMap.exists_isMorse_isProperMap_mem_ball`) has, outside `A`, only the critical points
of `g₀` in `Q`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Theorem 7.3.1.
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963.
-/

public section

open Set Filter Function
open scoped Manifold Topology ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

omit [I.Boundaryless] in
/-- The modification inside one tube: a smooth `ν ≥ 0` on `M`, supported in `Φ '' S`, which reads
through `Φ` as a function `μ` at whose critical points in `S` the second derivative of
`g₀ ∘ Φ + μ` is positive on some vector. -/
private lemma exists_tube_bump {g₀ : M → ℝ} (hg₀ : ContMDiff I 𝓘(ℝ) ∞ g₀)
    (Φ : SmoothEmbedding (𝓘(ℝ).prod 𝓘(ℝ, V)) I ∞ (ℝ × V) M)
    (hdim : Module.finrank ℝ (ℝ × V) = Module.finrank ℝ E)
    (hS : IsClosed (Φ '' Ici (-1 : ℝ) ×ˢ Metric.closedBall (0 : V) 1))
    (hcrit : ∀ z ∈ Ici (-1 : ℝ) ×ˢ Metric.closedBall (0 : V) 1,
      Φ z ∈ criticalPoints I g₀ → z = 0) :
    ∃ (ν : M → ℝ) (μ : ℝ × V → ℝ), ContMDiff I 𝓘(ℝ) ∞ ν ∧ 0 ≤ ν ∧
      support ν ⊆ Φ '' Ici (-1 : ℝ) ×ˢ Metric.closedBall (0 : V) 1 ∧ (∀ z, ν (Φ z) = μ z) ∧
      ∀ z, fderiv ℝ (g₀ ∘ Φ + μ) z = 0 → z ∈ Ici (-1 : ℝ) ×ˢ Metric.closedBall (0 : V) 1 →
        ∃ v, 0 < fderiv ℝ (fderiv ℝ (g₀ ∘ Φ + μ)) z v v := by
  set S := Ici (-1 : ℝ) ×ˢ Metric.closedBall (0 : V) 1
  -- Read on `ℝ × V`, the product model is the model of the normed space `ℝ × V`.
  have hcd (f : ℝ × V → ℝ) : ContMDiff (𝓘(ℝ).prod 𝓘(ℝ, V)) 𝓘(ℝ) ∞ f ↔ ContDiff ℝ ∞ f :=
    contMDiff_prod_modelWithCornersSelf_iff.trans contMDiff_iff_contDiff
  have hf : ContDiff ℝ ∞ (g₀ ∘ Φ) := (hcd _).1 (hg₀.comp Φ.contMDiff)
  obtain ⟨μ, hμ, hμ0, hμS, hμcrit⟩ := SymplecticGeometry.exists_nonneg_halfCylinder_hessian_pos
    (hf.of_le (WithTop.coe_le_coe.2 le_top)) fun z hz h ↦ hcrit z hz
      (((Φ.mem_criticalPoints_iff_fderiv_comp_eq_zero_prod (by simp) hdim
        (hg₀.mdifferentiableAt (by simp))).2 h))
  have hμS' : support μ ⊆ S := (subset_tsupport μ).trans hμS
  refine ⟨(range Φ).indicator (μ ∘ invFunOn Φ univ), μ,
    Φ.contMDiff_indicator_range_comp_invFunOn hdim (by simp) ((hcd μ).2 hμ) hS hμS',
    indicator_nonneg fun _ _ ↦ hμ0 _,
    (Φ.support_indicator_range_comp_invFunOn_subset μ).trans (image_mono hμS'),
    Φ.indicator_range_comp_invFunOn_apply_self μ, hμcrit⟩

/-- **Raising a function inside locally finite tubes.** Let `M` be a boundaryless manifold of
dimension `dim V + 1`, `S = [-1, ∞) × closedBall 0 1 ⊆ ℝ × V`, and `Φ i : ℝ × V → M` smooth
embeddings for which the sets `Φ i '' S` are closed, pairwise disjoint and locally finite. If a
smooth `g₀ : M → ℝ` has no critical point in any `Φ i '' S` other than `Φ i 0`, then there is a
smooth `g₁ ≥ g₀` with `g₁ - g₀` supported in `⋃ i, Φ i '' S` such that at every critical point
of `g₁` in `⋃ i, Φ i '' S` the critical Hessian of `g₁` is positive on some tangent vector. -/
theorem exists_le_criticalHessian_pos_of_tubes (g₀ : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯) {ι : Type*}
    (Φ : ι → SmoothEmbedding (𝓘(ℝ).prod 𝓘(ℝ, V)) I ∞ (ℝ × V) M)
    (hV : Module.finrank ℝ V + 1 = Module.finrank ℝ E)
    (hS : ∀ i, IsClosed (Φ i '' Ici (-1 : ℝ) ×ˢ Metric.closedBall (0 : V) 1))
    (hlf : LocallyFinite fun i ↦ Φ i '' Ici (-1 : ℝ) ×ˢ Metric.closedBall (0 : V) 1)
    (hdisj : Pairwise (Disjoint on fun i ↦ Φ i '' Ici (-1 : ℝ) ×ˢ Metric.closedBall (0 : V) 1))
    (hcrit : ∀ i, ∀ z ∈ Ici (-1 : ℝ) ×ˢ Metric.closedBall (0 : V) 1,
      Φ i z ∈ criticalPoints I g₀ → z = 0) :
    ∃ g₁ : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯, (∀ x, g₀ x ≤ g₁ x) ∧
      tsupport (fun x ↦ g₁ x - g₀ x) ⊆ ⋃ i, Φ i '' Ici (-1 : ℝ) ×ˢ Metric.closedBall (0 : V) 1 ∧
      ∀ x ∈ ⋃ i, Φ i '' Ici (-1 : ℝ) ×ˢ Metric.closedBall (0 : V) 1,
        x ∈ criticalPoints I g₁ → ∃ v, 0 < criticalHessian I g₁ x v v := by
  set S := Ici (-1 : ℝ) ×ˢ Metric.closedBall (0 : V) 1
  have hdim : Module.finrank ℝ (ℝ × V) = Module.finrank ℝ E := by
    rw [Module.finrank_prod, Module.finrank_self, add_comm, hV]
  choose ν μ hν hν0 hνS hνμ hμ using fun i ↦
    exists_tube_bump g₀.contMDiff (Φ i) hdim (hS i) (hcrit i)
  set g₁ : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯ :=
    ⟨fun x ↦ g₀ x + ∑ᶠ i, ν i x, g₀.contMDiff.add (contMDiff_finsum hν (hlf.subset hνS))⟩
  have hg₁ (x : M) : g₁ x = g₀ x + ∑ᶠ i, ν i x := by rw [ContMDiffMap.coeFn_mk]
  refine ⟨g₁, fun x ↦ ?_, ?_, ?_⟩
  · rw [hg₁]
    exact le_add_of_nonneg_right (finsum_nonneg fun i ↦ hν0 i x)
  · rw [← (hlf.isClosed_iUnion hS).closure_eq]
    refine closure_mono fun x hx ↦ ?_
    rw [mem_support, hg₁, add_sub_cancel_left] at hx
    obtain ⟨i, hi⟩ : ∃ i, ν i x ≠ 0 := by
      by_contra! h
      exact hx (finsum_eq_zero_of_forall_eq_zero h)
    exact mem_iUnion.2 ⟨i, hνS i hi⟩
  · intro x hx hx₁
    obtain ⟨i, z, hz, rfl⟩ := mem_iUnion.1 hx
    -- Away from the other tubes, `g₁` is `g₀ + ν i`.
    have hW : IsClosed (⋃ j : {j // j ≠ i}, Φ j '' S) :=
      (hlf.comp_injective Subtype.val_injective).isClosed_iUnion fun j ↦ hS j
    have hzW : Φ i z ∉ ⋃ j : {j // j ≠ i}, Φ j '' S := by
      simp only [mem_iUnion, not_exists]
      exact fun j hj ↦ disjoint_left.1 (hdisj j.property) hj (mem_image_of_mem _ hz)
    have hloc : ⇑g₁ ∘ Φ i =ᶠ[𝓝 z] g₀ ∘ Φ i + μ i := by
      filter_upwards [(Φ i).contMDiff.continuous.continuousAt.preimage_mem_nhds
        (hW.isOpen_compl.mem_nhds hzW)] with w hw
      rw [comp_apply, hg₁, finsum_eq_single _ i fun j hj ↦ ?_, hνμ, Pi.add_apply, comp_apply]
      rw [mem_preimage, mem_compl_iff] at hw
      by_contra h
      exact hw (mem_iUnion.2 ⟨⟨j, hj⟩, hνS j h⟩)
    have hcrit₁ := ((Φ i).mem_criticalPoints_iff_fderiv_comp_eq_zero_prod (by simp) hdim
      (g₁.contMDiff.mdifferentiableAt (by simp))).1 hx₁
    rw [hloc.fderiv_eq] at hcrit₁
    obtain ⟨v, hv⟩ := hμ i z hcrit₁ hz
    refine ((Φ i).exists_criticalHessian_pos_iff_fderiv_fderiv_comp_prod
      (WithTop.coe_le_coe.2 le_top) hdim
      (g₁.contMDiff.of_le (WithTop.coe_le_coe.2 le_top)).contMDiffAt hx₁).2 ⟨v, ?_⟩
    rwa [hloc.fderiv.fderiv_eq]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [FiniteDimensional ℝ V] in
/-- The critical points of `g₀` in a tube of the family lie only at its centre. -/
private lemma eq_zero_of_mem_tube {g₀ : M → ℝ} {P Q : Set M}
    (hP : ∀ x ∈ criticalPoints I g₀, x ∉ Q → x ∈ P) {O : P → Set M}
    (hOdisj : Pairwise (Disjoint on O)) (hOQ : ∀ p, Disjoint (O p) Q) (hPO : ∀ p : P, ↑p ∈ O p)
    (Φ : SmoothEmbedding (𝓘(ℝ).prod 𝓘(ℝ, V)) I ∞ (ℝ × V) M) (p : P) (hΦ0 : Φ 0 = p)
    {s : Set (ℝ × V)} (hΦO : Φ '' s ⊆ O p) {z : ℝ × V} (hz : z ∈ s)
    (hc : Φ z ∈ criticalPoints I g₀) : z = 0 := by
  have hzO : Φ z ∈ O p := hΦO (mem_image_of_mem _ hz)
  have hzP := hP _ hc (disjoint_left.1 (hOQ p) hzO)
  have hq : (⟨Φ z, hzP⟩ : P) = p := by
    by_contra hne
    exact disjoint_left.1 (hOdisj hne) (hPO _) hzO
  refine Φ.isEmbedding.injective ?_
  rw [hΦ0, ← hq]

section Assembly

variable [T2Space M] [SigmaCompactSpace M]

/-- **Morse functions without critical points of top index.** On a boundaryless Hausdorff
σ-compact manifold of finite dimension `n ≠ 1` none of whose connected components is compact,
there is a proper Morse function, bounded below, all of whose critical points have Morse index
less than `n`. -/
theorem exists_isMorse_isProperMap_manifoldMorseIndex_lt
    (hE : Module.finrank ℝ E ≠ 1) (hM : ∀ x : M, ¬ IsCompact (connectedComponent x)) :
    ∃ g : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯, IsMorse I g ∧ IsProperMap g ∧ BddBelow (Set.range g) ∧
      ∀ x ∈ criticalPoints I g, manifoldMorseIndex I g x < Module.finrank ℝ E := by
  obtain ⟨g₀, hg₀m, hg₀p, hg₀b⟩ := exists_isMorse_isProperMap_bddBelow (I := I) (M := M)
  rcases Nat.lt_or_ge (Module.finrank ℝ E) 2 with h2 | h2
  · -- In dimension zero `M` is discrete, so it is empty.
    have : Subsingleton E := (Module.finrank_zero_iff (R := ℝ)).1 (by omega)
    have : DiscreteTopology M := I.discreteTopology M
    refine ⟨g₀, hg₀m, hg₀p, hg₀b, fun x _ ↦ absurd ?_ (hM x)⟩
    rw [connectedComponent_eq_singleton]
    exact isCompact_singleton
  have : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  have : SecondCountableTopology M := I.secondCountableTopology_of_sigmaCompact M
  set n := Module.finrank ℝ E
  -- Step 1: the critical points of `g₀`, split by whether they have the top index.
  set crit := criticalPoints I g₀
  have hcc : IsClosed crit := isClosed_criticalPoints (g₀.contMDiff.of_le (by simp))
  have hcd : IsDiscrete crit := IsDiscrete.of_nhdsWithin fun x _ t ht ↦
    mem_nhdsWithin_iff_eventually.2 <| (eventually_eq_of_mem_criticalPoints
      (g₀.contMDiff.contMDiffAt.of_le (by simp))
      hg₀m.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints).mono
        fun y hy hyc ↦ (hy hyc) ▸ ht
  set P := {x | x ∈ crit ∧ manifoldMorseIndex I g₀ x = n}
  set Q := {x | x ∈ crit ∧ manifoldMorseIndex I g₀ x ≠ n}
  have hPc : P ⊆ crit := fun _ h ↦ h.1
  have hQc : Q ⊆ crit := fun _ h ↦ h.1
  have hPQ : Disjoint P Q := disjoint_left.2 fun _ hP hQ ↦ hQ.2 hP.2
  have : DiscreteTopology P := isDiscrete_iff_discreteTopology.1 (hcd.mono hPc)
  have : DiscreteTopology Q := isDiscrete_iff_discreteTopology.1 (hcd.mono hQc)
  have hQcl : IsClosed Q := isClosed_of_subset_discrete_closed hQc hcd hcc
  -- Step 2: rays from `P` avoiding `Q`, and disjoint neighbourhoods of them.
  obtain ⟨γ, hγ0, hγt, hγlf, hγdisj, hγQ⟩ := SymplecticGeometry.exists_rays (I := I) h2 hM
    (isClosed_of_subset_discrete_closed hPc hcd hcc) hQcl hPQ
  obtain ⟨O, hOo, hRO, hOdisj, hOQ, hOlf⟩ :=
    hγlf.exists_isOpen_superset_pairwise_disjoint
      (fun p ↦ (hγt p).isClosed_image_Ici (γ p).contMDiff.continuous (-2))
      (fun i j hij ↦ (hγdisj hij).mono (image_subset_range _ _) (image_subset_range _ _))
      hQcl fun p ↦ (hγQ p).mono_left (image_subset_range _ _)
  have hPO (p : P) : ↑p ∈ O p := hRO p ⟨0, by norm_num, hγ0 p⟩
  have hPcrit : ∀ x ∈ crit, x ∉ Q → x ∈ P := fun x hx hxQ ↦ ⟨hx, not_not.1 fun h ↦ hxQ ⟨hx, h⟩⟩
  -- Step 3: tubes around the rays inside these neighbourhoods.
  let V := EuclideanSpace ℝ (Fin (n - 1))
  have hV : Module.finrank ℝ V + 1 = n := by simp [V, finrank_euclideanSpace]; omega
  choose Φ hΦo _ hΦγ hΦB hΦO using fun p ↦
    (γ p).exists_rayTube (V := V) hV (hγt p) isOpen_univ (subset_univ _) (hOo p) (hRO p)
  set S := Ici (-1 : ℝ) ×ˢ Metric.closedBall (0 : V) 1
  set B := Ici (-2 : ℝ) ×ˢ Metric.closedBall (0 : V) 2
  have hSB : S ⊆ B := Set.prod_mono (Ici_subset_Ici.2 (by norm_num))
    (Metric.closedBall_subset_closedBall (by norm_num))
  have h0S : (0 : ℝ × V) ∈ S := by simp [S]
  have hΦ0 (p : P) : Φ p 0 = p := (hΦγ p 0).trans (hγ0 p)
  have hSc (p : P) : IsClosed (Φ p '' S) := by
    refine closure_subset_iff_isClosed.1 fun x hx ↦ ?_
    obtain ⟨z, -, rfl⟩ := (hΦB p).closure_subset_iff.2 (image_mono hSB) hx
    refine mem_image_of_mem _ ?_
    rw [← (show IsClosed S from isClosed_Ici.prod Metric.isClosed_closedBall).closure_eq,
      (Φ p).isEmbedding.isInducing.closure_eq_preimage_closure_image]
    exact hx
  have hlfB : LocallyFinite fun p ↦ Φ p '' B := hOlf.subset hΦO
  have hdisjB : Pairwise (Disjoint on fun p ↦ Φ p '' B) :=
    fun i j hij ↦ (hOdisj hij).mono (hΦO i) (hΦO j)
  have hcritB (p : P) {z : ℝ × V} (hz : z ∈ B) (hc : Φ p z ∈ crit) : z = 0 :=
    eq_zero_of_mem_tube hPcrit hOdisj hOQ hPO (Φ p) p (hΦ0 p) (hΦO p) hz hc
  -- Step 4: raise `g₀` inside the tubes.
  obtain ⟨g₁, hg₀₁, hg₁s, hg₁pos⟩ := exists_le_criticalHessian_pos_of_tubes g₀ Φ hV hSc
    (hlfB.subset fun p ↦ image_mono hSB)
    (fun i j hij ↦ (hdisjB hij).mono (image_mono hSB) (image_mono hSB))
    fun p z hz hc ↦ hcritB p (hSB hz) hc
  set A := ⋃ p, Φ p '' S
  set A' := ⋃ p, Φ p '' B
  have hAA' : A ⊆ interior A' := by
    refine iUnion_subset fun p ↦ ?_
    have hopen : IsOpen (Φ p '' Ioi (-2 : ℝ) ×ˢ Metric.ball (0 : V) 2) :=
      (Topology.IsOpenEmbedding.mk (Φ p).isEmbedding (hΦo p)).isOpenMap _
        (isOpen_Ioi.prod Metric.isOpen_ball)
    refine (image_mono (Set.prod_mono (Ici_subset_Ioi.2 (by norm_num))
      (Metric.closedBall_subset_ball (by norm_num)))).trans (interior_maximal ?_ hopen)
    exact (image_mono (Set.prod_mono Ioi_subset_Ici_self Metric.ball_subset_closedBall)).trans
      (subset_iUnion (fun p ↦ Φ p '' B) p)
  have hg₁₀ {x : M} (hx : x ∉ A) : ⇑g₁ =ᶠ[𝓝 x] ⇑g₀ := by
    filter_upwards [notMem_tsupport_iff_eventuallyEq.1 fun h ↦ hx (hg₁s h)] with y hy
    exact sub_eq_zero.1 hy
  have hA'pos : ∀ x ∈ A', x ∈ criticalPoints I g₁ → ∃ v, 0 < criticalHessian I g₁ x v v := by
    intro x hx hxc
    by_cases hxA : x ∈ A
    · exact hg₁pos x hxA hxc
    obtain ⟨p, z, hz, rfl⟩ := mem_iUnion.1 hx
    have hz0 := hcritB p hz ((hg₁₀ hxA).mem_criticalPoints_iff.1 hxc)
    exact (hxA (mem_iUnion.2 ⟨p, mem_image_of_mem _ (by rw [hz0]; exact h0S)⟩)).elim
  -- Step 5: a Morse approximation keeping positive directions on `A'` and `g₁` off it.
  obtain ⟨c, -, hc⟩ := exists_strongCkControl_criticalHessian_pos (by simp) g₁
    (hlfB.isClosed_iUnion hΦB) hA'pos
  set C := (interior A')ᶜ
  have hCA : C ⊆ (tsupport fun x ↦ g₁ x - g₀ x)ᶜ :=
    compl_subset_compl.2 (hg₁s.trans hAA')
  have hg₁C : IsMorseOn I g₁ C :=
    (((isMorseOn_univ.2 hg₀m).mono (subset_univ _)).congr (isClosed_tsupport _).isOpen_compl
      fun x hx ↦ sub_eq_zero.1
        (image_eq_zero_of_notMem_tsupport (f := fun x ↦ g₁ x - g₀ x) hx)).mono hCA
  have hg₁p : IsProperMap g₁ := hg₀p.of_le hg₀b g₁.contMDiff.continuous hg₀₁
  obtain ⟨g, hgc, hgm, hgp, hg1, hgs⟩ :=
    g₁.exists_isMorse_isProperMap_mem_ball c hg₁p isOpen_interior.isClosed_compl hg₁C
  obtain ⟨m, hm⟩ := hg₀b
  refine ⟨g, hgm, hgp, ⟨m - 1, forall_mem_range.2 fun x ↦ ?_⟩, fun x hxc ↦ ?_⟩
  · have := (abs_lt.1 (hg1 x)).1
    linarith [hm (mem_range_self x), hg₀₁ x]
  refine manifoldMorseIndex_le_finrank.lt_of_ne fun hn ↦ ?_
  rw [manifoldMorseIndex_eq_finrank_iff] at hn
  by_cases hxA' : x ∈ A'
  · obtain ⟨v, hv⟩ := hc g hgc x hxA' hxc
    have hv0 : v ≠ 0 := by rintro rfl; simp at hv
    exact (hn v hv0).not_gt hv
  -- Off `A'`, `g` agrees with `g₀` near `x`, so `x` is a critical point of `g₀` not in `P`.
  have hxC : x ∈ C := fun h ↦ hxA' (interior_subset h)
  have hgg₀ : ⇑g =ᶠ[𝓝 x] ⇑g₀ := by
    have h₁ : ⇑g =ᶠ[𝓝 x] ⇑g₁ := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 fun h ↦ hgs h hxC] with y hy
      exact sub_eq_zero.1 hy
    exact h₁.trans (hg₁₀ fun h ↦ hxA' (interior_subset (hAA' h)))
  have hx₀ : x ∈ crit := hgg₀.mem_criticalPoints_iff.1 hxc
  have hxP : x ∉ P := fun h ↦ hxA' (mem_iUnion.2 ⟨⟨x, h⟩, 0, hSB h0S, hΦ0 _⟩)
  refine hxP ⟨hx₀, manifoldMorseIndex_eq_finrank_iff.2 ?_⟩
  rwa [← criticalHessian_congr_of_eventuallyEq hgg₀]

end Assembly

end TauCeti

end
