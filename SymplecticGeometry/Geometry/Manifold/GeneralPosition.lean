/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothApprox.Basic
public import TauCeti.Geometry.Manifold.Instances.AddCircle
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.Sard.Transversality
import TauCeti.Geometry.Manifold.SmoothEmbedding.Diagonal
import SymplecticGeometry.Geometry.Manifold.PerturbationFamily
import SymplecticGeometry.Geometry.Manifold.RegularValue.Prod

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
* `SymplecticGeometry.range_mfderiv_sup_ne_top_of_finrank_lt`: if `dim N + dim Z < dim P`, the
  images of the tangent spaces of `N` and `Z` under maps into `P` never span a tangent space
  of `P`. Its proof is the dimension count of Tau Ceti's
  `TauCeti.isTransverseAt_iff_notMem_range`, there for maps into a normed space, here for maps into
  a manifold, in the form that `ContMDiff.isNullSet_setOf_exists_not_transverse` uses.

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

variable {EN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [FiniteDimensional ℝ EN]
  {HN : Type*} [TopologicalSpace HN] {J : ModelWithCorners ℝ EN HN}
  {N : Type*} [TopologicalSpace N] [ChartedSpace HN N]

/-- **Dimension count for transversality.** Let `γ : N → P` and `g : Z → P` be maps of manifolds
modelled on finite-dimensional real spaces, with `dim N + dim Z < dim P`. At any `x : N` and
`z : Z`, the images of the tangent spaces at `x` and `z` do not span the tangent space of `P`.
So `γ` can be transverse to `g` only where it misses the range of `g`. -/
theorem range_mfderiv_sup_ne_top_of_finrank_lt {EZ : Type*} [NormedAddCommGroup EZ]
    [NormedSpace ℝ EZ] [FiniteDimensional ℝ EZ] {HZ : Type*} [TopologicalSpace HZ]
    {IZ : ModelWithCorners ℝ EZ HZ} {Z : Type*} [TopologicalSpace Z] [ChartedSpace HZ Z]
    {EP : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
    {HP : Type*} [TopologicalSpace HP] {IP : ModelWithCorners ℝ EP HP} {P : Type*}
    [TopologicalSpace P] [ChartedSpace HP P]
    (hdim : finrank ℝ EN + finrank ℝ EZ < finrank ℝ EP) (γ : N → P) (g : Z → P) (x : N) (z : Z) :
    (mfderiv J IP γ x).range ⊔
      (((tangentSpaceCast IP (g z) (γ x)).toContinuousLinearMap).comp
        (mfderiv IZ IP g z)).range ≠ ⊤ := by
  have : FiniteDimensional ℝ EP := Module.finite_of_finrank_pos (by omega)
  intro h
  -- The tangent spaces are the model spaces by definition.
  have : FiniteDimensional ℝ (TangentSpace IZ z) := inferInstanceAs (FiniteDimensional ℝ EZ)
  have : FiniteDimensional ℝ (TangentSpace IP (γ x)) := inferInstanceAs (FiniteDimensional ℝ EP)
  have h1 := LinearMap.finrank_range_le (mfderiv J IP γ x).toLinearMap
  have h2 := LinearMap.finrank_range_le
    (((tangentSpaceCast IP (g z) (γ x)).toContinuousLinearMap).comp (mfderiv IZ IP g z)).toLinearMap
  have h3 := Submodule.finrank_add_le_finrank_add_finrank (mfderiv J IP γ x).range
    (((tangentSpaceCast IP (g z) (γ x)).toContinuousLinearMap).comp (mfderiv IZ IP g z)).range
  rw [h, finrank_top] at h3
  rw [finrank_tangentSpace] at h1 h2 h3
  omega

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] [IsManifold I ∞ M] [J.Boundaryless]
  [CompactSpace N] [T2Space N] [IsManifold J ∞ N]

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
  let Φ : ι → ι → N × U → M × M := fun i j q ↦ (F i (q.1, q.2.val i), F j (q.1, q.2.val j))
  have hΦ (i j : ι) : ContMDiff (J.prod 𝓘(ℝ, P)) (I.prod I) ∞ (Φ i j) := by
    refine ((hF i).comp (contMDiff_fst.prodMk ?_)).prodMk ((hF j).comp (contMDiff_fst.prodMk ?_))
    · exact (hproj i).comp (contMDiff_subtypeVal.comp contMDiff_snd)
    · exact (hproj j).comp (contMDiff_subtypeVal.comp contMDiff_snd)
  have hΦreg (i j : ι) (hij : i ≠ j) (q : N × U) :
      IsRegularPoint (J.prod 𝓘(ℝ, P)) (I.prod I) (Φ i j) q := by
    obtain ⟨x, s, hs⟩ := q
    have hd (k : ι) : MDifferentiableAt 𝓘(ℝ, Fin (m k) → E) I (fun t ↦ F k (x, t)) (s k) :=
      ((hF k).comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiableAt (by simp)
    have hψ := isRegularPoint_apply_prodMk_apply (f := fun k t ↦ F k (x, t)) hij
      (hFreg i x (s i) (hs i)).1 (hFreg j x (s j) (hs j)).1 (hd i) (hd j)
    have hslice := hψ.comp (isRegularPoint_subtype_val (I := 𝓘(ℝ, P)) ⟨s, hs⟩)
    exact IsRegularPoint.of_comp (g := fun t : U ↦ (x, t)) hslice
      ((hΦ i j _).mdifferentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0))
      ((contMDiff_const.prodMk contMDiff_id).mdifferentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0))
  -- The diagonal of `M`.
  have hδ : ContMDiff I (I.prod I) ∞ fun z : M ↦ (z, z) := contMDiff_id.prodMk contMDiff_id
  have hδe : Topology.IsEmbedding fun z : M ↦ (z, z) :=
    SmoothEmbedding.coe_diagonal (I := I) (M := M) ▸ SmoothEmbedding.isEmbedding _
  -- The parameters whose slice is not transverse to the diagonal form a null set.
  borelize P
  have hnull : IsNullSet 𝓘(ℝ, P) (⋃ p : {p : ι × ι // p.1 ≠ p.2}, {s : U | ∃ q : N × M,
      Φ p.val.1 p.val.2 (q.1, s) = (q.2, q.2) ∧
      (mfderiv J (I.prod I) (fun x ↦ Φ p.val.1 p.val.2 (x, s)) q.1).range ⊔
        (((tangentSpaceCast (I.prod I) ((fun z : M ↦ (z, z)) q.2)
          (Φ p.val.1 p.val.2 (q.1, s))).toContinuousLinearMap).comp
          (mfderiv I (I.prod I) (fun z : M ↦ (z, z)) q.2)).range ≠ ⊤}) :=
    IsNullSet.iUnion fun p ↦ (hΦ p.val.1 p.val.2).isNullSet_setOf_exists_not_transverse hδ hδe
      (WithTop.coe_le_coe.2 le_top) fun q _ ↦ by
        rw [LinearMap.range_eq_top.2 (isRegularPoint_iff.1 (hΦreg _ _ p.property q.1)), top_sup_eq]
  obtain ⟨s, hs⟩ := hnull.dense_compl.nonempty
  simp only [mem_compl_iff, mem_iUnion, not_exists] at hs
  -- The slices at `s`.
  let g : ι → C(N, M) := fun i ↦
    ⟨fun x ↦ F i (x, s.val i), (hF i).continuous.comp (continuous_id.prodMk continuous_const)⟩
  refine ⟨g, fun i ↦ ⟨(hF i).comp (contMDiff_id.prodMk contMDiff_const), (hfg₀ i).trans ?_⟩,
    fun i j hij x hx ↦ ?_⟩
  · -- The slices along the segment from `0` to `s i`.
    refine ⟨⟨⟨fun q ↦ F i (q.2, (q.1 : ℝ) • s.val i), ?_⟩, fun x ↦ ?_, fun x ↦ ?_⟩⟩
    · exact (hF i).continuous.comp (continuous_snd.prodMk
        ((continuous_subtypeVal.comp continuous_fst).smul continuous_const))
    · simp [hF0]
    · simp [g]
  · refine range_mfderiv_sup_ne_top_of_finrank_lt (IZ := I) (IP := I.prod I)
      (by rw [finrank_prod]; omega) (fun x ↦ Φ i j (x, s)) (fun z : M ↦ (z, z)) x (g i x)
      (not_not.1 fun h ↦ hs ⟨(i, j), hij⟩
        ⟨⟨x, g i x⟩, Prod.ext (by simp [Φ, g]) (by simpa [Φ, g] using hx.symm), h⟩)

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
