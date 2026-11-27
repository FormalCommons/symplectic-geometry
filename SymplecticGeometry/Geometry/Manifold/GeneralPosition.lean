/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothApprox.Basic
public import TauCeti.Geometry.Manifold.Instances.AddCircle
import TauCeti.Geometry.Manifold.Sard.Transversality
import SymplecticGeometry.Geometry.Manifold.PerturbationFamily

/-!
# General position of finitely many maps from a low-dimensional compact manifold

Let `N` be a compact Hausdorff manifold and `M` a Hausdorff manifold, both smooth, without
boundary and modelled on finite-dimensional real spaces, with `dim N < dim M`. This file shows
that finitely many continuous maps `f i : N → M` are homotopic to smooth maps `g i` with
`g i x ≠ g j x` for every `x` and all `i ≠ j`. For `N` a circle this is the case `dim M ≥ 2`.

## Main results

* `SymplecticGeometry.exists_contMDiff_homotopic_forall_ne`: the statement above.
* `SymplecticGeometry.exists_contMDiff_homotopic_forall_ne_addCircle`: its case for maps from
  `AddCircle p`, when `2 ≤ dim M`.

## Proof

Each `f i` is homotopic to a smooth map `g₀ i` by Tau Ceti's Whitney approximation theorem
`ContinuousMap.exists_contMDiff_homotopic_of_isCompact_closure_range`. The library's
`ContMDiff.exists_isRegularPoint_perturbation` gives each `g₀ i` a family of perturbations
`F i : N × V i → M` whose slices are submersions for parameters in a ball. On the open set `U` of
parameters `s` in the product of these balls, the map `(x, s) ↦ (F i (x, s i), F j (x, s j))`
into `M × M` is a submersion for `i ≠ j`, so it is transverse to the diagonal. By Tau Ceti's
parametric transversality theorem `ContMDiff.isNullSet_setOf_exists_not_transverse`, the
parameters whose slice is not transverse to the diagonal form a null set. Away from the finitely
many such null sets, every slice is transverse to the diagonal, and since
`dim N + dim M < 2 dim M` it misses the diagonal. The slice at such a parameter is homotopic to
`g₀ i` through the slices along the segment from `0`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Theorems 6.26 (Whitney approximation) and 6.35 (parametric transversality).
-/

public section

open Function Set Metric Module TauCeti
open scoped Manifold ContDiff

namespace SymplecticGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] 
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {EN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [FiniteDimensional ℝ EN]
  {HN : Type*} [TopologicalSpace HN] {J : ModelWithCorners ℝ EN HN}

/-- A map `γ : N → M × M` with `dim N < dim M` is not transverse to the diagonal at a point that
it sends to the diagonal: the images of the two tangent spaces do not span the tangent space
of `M × M`. -/
private theorem range_mfderiv_sup_ne_top [FiniteDimensional ℝ E] {N : Type*} [TopologicalSpace N] [ChartedSpace HN N]
    (hdim : finrank ℝ EN < finrank ℝ E) (γ : N → M × M) (x : N) (y : M) :
    (mfderiv J (I.prod I) γ x).range ⊔
      (((tangentSpaceCast (I.prod I) ((fun z : M ↦ (z, z)) y) (γ x)).toContinuousLinearMap).comp
        (mfderiv I (I.prod I) (fun z : M ↦ (z, z)) y)).range ≠ ⊤ := by
  intro h
  -- The tangent spaces are the model spaces by definition.
  have : FiniteDimensional ℝ (TangentSpace I y) := inferInstanceAs (FiniteDimensional ℝ E)
  have : FiniteDimensional ℝ (TangentSpace (I.prod I) (γ x)) :=
    inferInstanceAs (FiniteDimensional ℝ (E × E))
  have h1 := LinearMap.finrank_range_le (mfderiv J (I.prod I) γ x).toLinearMap
  have h2 := LinearMap.finrank_range_le
    (((tangentSpaceCast (I.prod I) ((fun z : M ↦ (z, z)) y) (γ x)).toContinuousLinearMap).comp
      (mfderiv I (I.prod I) (fun z : M ↦ (z, z)) y)).toLinearMap
  have h3 := Submodule.finrank_add_le_finrank_add_finrank
    (mfderiv J (I.prod I) γ x).range
    (((tangentSpaceCast (I.prod I) ((fun z : M ↦ (z, z)) y) (γ x)).toContinuousLinearMap).comp
      (mfderiv I (I.prod I) (fun z : M ↦ (z, z)) y)).range
  rw [h, finrank_top] at h3
  change finrank ℝ (E × E) ≤ _ at h3
  change _ ≤ finrank ℝ EN at h1
  change _ ≤ finrank ℝ E at h2
  rw [finrank_prod] at h3
  exact absurd (h3.trans (add_le_add h1 h2)) (by omega)

/-- A product of two maps is regular at a point where both maps are regular. -/
private theorem isRegularPoint_prodMap {EA EB : Type*} [NormedAddCommGroup EA] [NormedSpace ℝ EA]
    [NormedAddCommGroup EB] [NormedSpace ℝ EB] {f₁ : EA → M} {f₂ : EB → M} {a : EA} {b : EB}
    (h₁ : IsRegularPoint 𝓘(ℝ, EA) I f₁ a) (h₂ : IsRegularPoint 𝓘(ℝ, EB) I f₂ b)
    (hd₁ : MDifferentiableAt 𝓘(ℝ, EA) I f₁ a) (hd₂ : MDifferentiableAt 𝓘(ℝ, EB) I f₂ b) :
    IsRegularPoint (𝓘(ℝ, EA).prod 𝓘(ℝ, EB)) (I.prod I) (Prod.map f₁ f₂) (a, b) := by
  rw [isRegularPoint_iff, mfderiv_prodMap hd₁ hd₂]
  rintro ⟨v, w⟩
  obtain ⟨v', rfl⟩ := isRegularPoint_iff.1 h₁ v
  obtain ⟨w', rfl⟩ := isRegularPoint_iff.1 h₂ w
  exact ⟨(v', w'), rfl⟩

variable [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] [IsManifold I ∞ M] [J.Boundaryless] {N : Type*} [TopologicalSpace N] [ChartedSpace HN N] [CompactSpace N]
  [T2Space N] [IsManifold J ∞ N]

/-- **General position of finitely many maps.** Let `N` be a compact Hausdorff manifold and `M`
a Hausdorff manifold, both smooth, without boundary and modelled on finite-dimensional real
spaces, with `dim N < dim M`. Finitely many continuous maps `f i : N → M` are homotopic to smooth
maps `g i` such that `g i x ≠ g j x` for every `x : N` and all `i ≠ j`. -/
theorem exists_contMDiff_homotopic_forall_ne (hdim : finrank ℝ EN < finrank ℝ E) {ι : Type*}
    [Finite ι] (f : ι → C(N, M)) :
    ∃ g : ι → C(N, M), (∀ i, ContMDiff J I ∞ (g i) ∧ (f i).Homotopic (g i)) ∧
      ∀ i j, i ≠ j → ∀ x, g i x ≠ g j x := by
  classical
  have := Fintype.ofFinite ι
  have : IsManifold J 1 N := IsManifold.of_le (n := ∞) (by simp)
  -- Smooth approximations of the `f i`, and their families of perturbations.
  choose g₀ hg₀ hfg₀ using fun i ↦ (f i).exists_contMDiff_homotopic_of_isCompact_closure_range
    (I := J) (J := I) ⊤ (by
      rw [(isCompact_range (f i).continuous).isClosed.closure_eq]
      exact isCompact_range (f i).continuous)
  choose m F ε hε hF hF0 hFreg using fun i ↦
    (hg₀ i).exists_isRegularPoint_perturbation (n := ⊤) le_top
  -- The open set of parameters on which every family is submersive.
  let P := ∀ i, Fin (m i) → E
  let U : TopologicalSpace.Opens P := ⟨{s | ∀ i, s i ∈ ball 0 (ε i)}, by
    rw [ofPred_forall]
    exact isOpen_iInter_of_finite fun i ↦ isOpen_ball.preimage (continuous_apply i)⟩
  have h0U : (0 : P) ∈ U := fun i ↦ mem_ball_self (hε i)
  have : Nonempty U := ⟨⟨0, h0U⟩⟩
  have hproj (i : ι) : ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, Fin (m i) → E) ∞ fun s : P ↦ s i :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun i ↦ Fin (m i) → E) i).contMDiff
  -- For `i ≠ j`, the pair of perturbations, as a map to `M × M`.
  let Φ : ι → ι → N × U → M × M := fun i j q ↦ (F i (q.1, q.2.1 i), F j (q.1, q.2.1 j))
  have hΦ (i j : ι) : ContMDiff (J.prod 𝓘(ℝ, P)) (I.prod I) ∞ (Φ i j) := by
    refine ((hF i).comp (contMDiff_fst.prodMk ?_)).prodMk ((hF j).comp (contMDiff_fst.prodMk ?_))
    · exact (hproj i).comp (contMDiff_subtypeVal.comp contMDiff_snd)
    · exact (hproj j).comp (contMDiff_subtypeVal.comp contMDiff_snd)
  have hΦreg (i j : ι) (hij : i ≠ j) (q : N × U) :
      IsRegularPoint (J.prod 𝓘(ℝ, P)) (I.prod I) (Φ i j) q := by
    obtain ⟨x, s, hs⟩ := q
    have hd (k : ι) : MDifferentiableAt 𝓘(ℝ, Fin (m k) → E) I (fun t ↦ F k (x, t)) (s k) :=
      ((hF k).comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiableAt (by simp)
    -- The parameters of `i` and `j`, as a surjective linear map.
    let π : P →L[ℝ] (Fin (m i) → E) × (Fin (m j) → E) :=
      (ContinuousLinearMap.proj i).prod (ContinuousLinearMap.proj j)
    have hπ : IsRegularPoint 𝓘(ℝ, P) (𝓘(ℝ, Fin (m i) → E).prod 𝓘(ℝ, Fin (m j) → E)) π s := by
      rw [isRegularPoint_iff, ← modelWithCornersSelf_prod, chartedSpaceSelf_prod, π.mfderiv_eq]
      -- The tangent spaces of the model spaces are these spaces by definition.
      show Surjective (π : P → (Fin (m i) → E) × (Fin (m j) → E))
      rintro ⟨a, b⟩
      refine ⟨update (update 0 i a) j b, Prod.ext ?_ ?_⟩
      · exact (ContinuousLinearMap.proj_apply (R := ℝ) (φ := fun k ↦ Fin (m k) → E) i _).trans
          (by rw [update_of_ne hij, update_self])
      · exact (ContinuousLinearMap.proj_apply (R := ℝ) (φ := fun k ↦ Fin (m k) → E) j _).trans
          (update_self _ _ _)
    have hprod := isRegularPoint_prodMap (hFreg i x (s i) (hs i)).1 (hFreg j x (s j) (hs j)).1
      (hd i) (hd j)
    rw [show (s i, s j) = π s from rfl] at hprod
    have hψ := hprod.comp hπ
    have hslice := hψ.comp (isRegularPoint_subtype_val (I := 𝓘(ℝ, P)) ⟨s, hs⟩)
    exact IsRegularPoint.of_comp (g := fun t : U ↦ (x, t)) hslice
      ((hΦ i j _).mdifferentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0))
      ((contMDiff_const.prodMk contMDiff_id).mdifferentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0))
  -- The diagonal of `M`.
  have hδ : ContMDiff I (I.prod I) ∞ fun z : M ↦ (z, z) := contMDiff_id.prodMk contMDiff_id
  have hδe : Topology.IsEmbedding fun z : M ↦ (z, z) :=
    .of_comp (continuous_id.prodMk continuous_id) continuous_fst .id
  -- The parameters whose slice is not transverse to the diagonal form a null set.
  borelize P
  have hnull : IsNullSet 𝓘(ℝ, P) (⋃ p : {p : ι × ι // p.1 ≠ p.2}, {s : U | ∃ q : N × M,
      Φ p.1.1 p.1.2 (q.1, s) = (q.2, q.2) ∧
      (mfderiv J (I.prod I) (fun x ↦ Φ p.1.1 p.1.2 (x, s)) q.1).range ⊔
        (((tangentSpaceCast (I.prod I) ((fun z : M ↦ (z, z)) q.2)
          (Φ p.1.1 p.1.2 (q.1, s))).toContinuousLinearMap).comp
          (mfderiv I (I.prod I) (fun z : M ↦ (z, z)) q.2)).range ≠ ⊤}) :=
    IsNullSet.iUnion fun p ↦ (hΦ p.1.1 p.1.2).isNullSet_setOf_exists_not_transverse hδ hδe
      (WithTop.coe_le_coe.2 le_top) fun q _ ↦ by
        rw [LinearMap.range_eq_top.2 (isRegularPoint_iff.1 (hΦreg p.1.1 p.1.2 p.2 q.1)), top_sup_eq]
  obtain ⟨s, hs⟩ := hnull.dense_compl.nonempty
  simp only [mem_compl_iff, mem_iUnion, not_exists] at hs
  -- The slices at `s`.
  let g : ι → C(N, M) := fun i ↦
    ⟨fun x ↦ F i (x, s.1 i), (hF i).continuous.comp (continuous_id.prodMk continuous_const)⟩
  refine ⟨g, fun i ↦ ⟨(hF i).comp (contMDiff_id.prodMk contMDiff_const), (hfg₀ i).trans ?_⟩,
    fun i j hij x hx ↦ ?_⟩
  · -- The slices along the segment from `0` to `s i`.
    refine ⟨⟨⟨fun q ↦ F i (q.2, (q.1 : ℝ) • s.1 i), ?_⟩, fun x ↦ ?_, fun x ↦ ?_⟩⟩
    · exact (hF i).continuous.comp (continuous_snd.prodMk
        ((continuous_subtypeVal.comp continuous_fst).smul continuous_const))
    · simp [hF0]
    · simp [g]
  · exact range_mfderiv_sup_ne_top (I := I) hdim (fun x ↦ Φ i j (x, s)) x (g i x)
      (not_not.1 fun h ↦ hs ⟨(i, j), hij⟩ ⟨⟨x, g i x⟩, Prod.ext rfl hx.symm, h⟩)

/-- **General position of finitely many loops.** In a Hausdorff manifold `M` of dimension at
least two, smooth and without boundary, finitely many continuous loops `f i : AddCircle p → M`
are homotopic to smooth loops `g i` such that `g i t ≠ g j t` for every `t` and all `i ≠ j`. -/
theorem exists_contMDiff_homotopic_forall_ne_addCircle (hdim : 2 ≤ finrank ℝ E) {p : ℝ}
    [Fact (0 < p)] {ι : Type*} [Finite ι] (f : ι → C(AddCircle p, M)) :
    ∃ g : ι → C(AddCircle p, M), (∀ i, ContMDiff 𝓘(ℝ) I ∞ (g i) ∧ (f i).Homotopic (g i)) ∧
      ∀ i j, i ≠ j → ∀ t, g i t ≠ g j t :=
  exists_contMDiff_homotopic_forall_ne (by rw [finrank_self]; omega) f

end SymplecticGeometry

end
