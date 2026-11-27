/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.RegularValue
import SymplecticGeometry.Data.List.Pi
import SymplecticGeometry.Geometry.Manifold.ContMDiff.Foldr
import SymplecticGeometry.Geometry.Manifold.RegularValue.Slice
import TauCeti.Geometry.Manifold.Diffeomorph.Extend
import TauCeti.Geometry.Manifold.Diffeomorph.Perturbation
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic

/-!
# Submersive families of perturbations of a map from a compact manifold

Let `g : N → M` be a `C^n` map, `1 ≤ n`, from a compact manifold `N` to a Hausdorff boundaryless
manifold `M`, both modelled on finite-dimensional real spaces, with `M` modelled on `E`. We build
a `C^n` family `F : N × (Fin m → E) → M` with `F (x, 0) = g x` such that, for every `x` and every
parameter `s` in a ball about `0`, the derivative of `s ↦ F (x, s)` at `s` is surjective
(`ContMDiff.exists_isRegularPoint_perturbation`); in particular `F` is a submersion there. This
is the input that the parametric transversality theorem `ContMDiff.dense_setOf_forall_transverse`
of Tau Ceti asks for.

Lee builds such a family from an embedding of `M` in Euclidean space and a tubular neighbourhood
(proof of Theorem 6.36). Here it is built from local motions in charts instead, which needs
neither. Near a point `y` of `M`, the compactly supported translations
`TauCeti.exists_diffeomorph_family_apply_eq_add` of the chart at `y`, extended to `M` by the
identity, give a family `d ↦ φ d` of maps of `M`, indexed by `d ∈ E`, with `φ 0 = id` and
`d ↦ φ d z` regular at `d = 0` for every `z` near `y` (`exists_contMDiff_family_isRegularPoint`).
This adapts the proof of Tau Ceti's `TauCeti.exists_contMDiff_family_apply_eq`. Finitely many
such families cover the compact image of `g`, and `F (x, s)` applies them in turn to `g x`, the
`i`-th with parameter `s i`. At `s = 0` the derivative is surjective, and the set where it is
surjective is open (`TauCeti.isOpen_setOfPred_isRegularPoint_slice`), so by compactness of `N` it
contains `N × B(0, ε)` for some `ε > 0`.

## Main results

* `SymplecticGeometry.exists_contMDiff_family_isRegularPoint`: a smooth family of maps of `M`,
  equal to the identity at the parameter `0`, which moves every point near a given one in all
  directions.
* `ContMDiff.exists_isRegularPoint_perturbation`: a submersive finite-dimensional family of
  perturbations of a smooth map from a compact manifold.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Theorems 6.35 and 6.36.
* J. W. Milnor, *Topology from the Differentiable Viewpoint* (1965), §4, Homogeneity Lemma (the
  local motions).
-/

public section

open Function Set Metric Topology
open scoped Manifold ContDiff

namespace SymplecticGeometry

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [BoundarylessManifold I M] {n : ℕ∞} [IsManifold I n M]

/-- **A family of local motions moving nearby points in all directions.** Every point `y` of a
Hausdorff boundaryless `C^n` manifold `M`, `1 ≤ n`, modelled on a finite-dimensional real space
`E`, has an open neighbourhood `U` with a family `φ d`, `d ∈ E`, of maps of `M`, depending
jointly `C^n`-smoothly on `d` and the point, such that `φ 0` is the identity and, for every
`z ∈ U`, the map `d ↦ φ d z` is regular at `d = 0`. -/
theorem exists_contMDiff_family_isRegularPoint (hn : 1 ≤ n) (y : M) :
    ∃ U : Set M, IsOpen U ∧ y ∈ U ∧ ∃ φ : E → M → M,
      ContMDiff (𝓘(ℝ, E).prod I) I n (fun q : E × M ↦ φ q.1 q.2) ∧ φ 0 = id ∧
        ∀ z ∈ U, IsRegularPoint 𝓘(ℝ, E) I (fun d ↦ φ d z) 0 := by
  set e := extChartAt I y with he
  have hy : e y ∈ interior e.target :=
    (I.isInteriorPoint_iff).1 BoundarylessManifold.isInteriorPoint
  -- A closed ball `K` about `e y` in the interior of the chart target.
  obtain ⟨r, hr, hrt⟩ := Metric.isOpen_iff.1 isOpen_interior _ hy
  set K := closedBall (e y) (r / 2)
  have hKc : IsCompact K := isCompact_closedBall _ _
  have hKt : K ⊆ interior e.target := (closedBall_subset_ball (by linarith)).trans hrt
  -- The compactly supported translations `τ d` of the model space, moving `e y` to `e y + d`.
  obtain ⟨δ, hδ, τ, hτs, hτK, hτ0, hτc⟩ :=
    exists_diffeomorph_family_apply_eq_add (e y) (by positivity : 0 < r / 2) hn
  have hτK' (d : E) : ∀ p ∉ K, τ d p = p := fun p hp ↦ hτK d p fun h ↦ hp (ball_subset_closedBall h)
  -- Their extensions through the chart.
  let S : E → M ≃ₘ^n⟮I, I⟯ M := fun d ↦ (τ d).chartExtend y hKc hKt (hτK' d)
  have hS : ContMDiff (𝓘(ℝ, E).prod I) I n (fun q : E × M ↦ S q.1 q.2) := by
    have hτs' := contMDiff_iff_contDiff.2 hτs
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at hτs'
    exact Diffeomorph.contMDiff_chartExtend hτs' hτK'
  have hS_apply (d : E) (hd : ‖d‖ < δ) : S d y = e.symm (e y + d) := by
    have h := Diffeomorph.chartExtend_extChartAt_symm (φ := τ d) (hK := hKc) (hKt := hKt)
      (hφ := hτK' d) (mem_extChartAt_target y)
    rwa [← he, e.left_inv (mem_extChartAt_source y), hτc d hd] at h
  have hS0 : (fun d ↦ ⇑(S d)) 0 = id := by
    ext z
    simp [S, hτ0, chartExtend_id]
  -- The motions of `y` are regular at `d = 0`: near `0` they read `e.symm (e y + d)`.
  have hreg : IsRegularPoint 𝓘(ℝ, E) I (fun d ↦ S d y) 0 := by
    have h1 : IsRegularPoint 𝓘(ℝ, E) I e.symm (e y + 0) := by
      rw [add_zero]
      exact (isLocalDiffeomorphAt_extChartAt_symm (n := n) hy).isRegularPoint
        (by exact_mod_cast (zero_lt_one.trans_le hn).ne')
    have h2 : IsRegularPoint 𝓘(ℝ, E) 𝓘(ℝ, E) (fun d : E ↦ e y + d) 0 := by
      rw [isRegularPoint_iff_surjective_fderiv, fderiv_const_add, fderiv_fun_id]
      exact surjective_id
    refine (h1.comp h2).congr_of_eventuallyEq ?_
    filter_upwards [ball_mem_nhds (0 : E) hδ] with d hd
    rw [comp_apply, hS_apply d (by simpa using hd)]
  -- Regularity of `d ↦ S d z` at `d = 0` is an open condition on `z`.
  have : IsManifold I 1 M := IsManifold.of_le (n := n) (by exact_mod_cast hn)
  have hS' : ContMDiff (I.prod 𝓘(ℝ, E)) I n (fun p : M × E ↦ S p.2 p.1) :=
    hS.comp (contMDiff_snd.prodMk contMDiff_fst)
  have hO := isOpen_setOfPred_isRegularPoint_slice hS' (by exact_mod_cast hn)
  refine ⟨(fun z : M ↦ (z, (0 : E))) ⁻¹' {p : M × E | IsRegularPoint 𝓘(ℝ, E) I
    (fun d ↦ S d p.1) p.2}, hO.preimage (continuous_id.prodMk continuous_const), hreg,
    fun d ↦ S d, hS, hS0, fun z hz ↦ hz⟩

variable {EN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [FiniteDimensional ℝ EN]
  {HN : Type*} [TopologicalSpace HN] {J : ModelWithCorners ℝ EN HN}
  {N : Type*} [TopologicalSpace N] [ChartedSpace HN N] [CompactSpace N] [IsManifold J 1 N]

/-- **A submersive family of perturbations.** Let `g : N → M` be a `C^n` map, `1 ≤ n`, from a
compact `C¹` manifold `N` to a Hausdorff boundaryless `C^n` manifold `M`, both modelled on
finite-dimensional real spaces, `M` on `E`. There are `m : ℕ`, `ε > 0` and a `C^n` map
`F : N × (Fin m → E) → M` with `F (x, 0) = g x` for every `x`, such that for every `x` and every
parameter `s` in the ball `B(0, ε)`, the map `s ↦ F (x, s)` is regular at `s`, and so `F` itself
is regular at `(x, s)`. -/
theorem _root_.ContMDiff.exists_isRegularPoint_perturbation {g : N → M} (hg : ContMDiff J I n g)
    (hn : 1 ≤ n) :
    ∃ (m : ℕ) (F : N × (Fin m → E) → M) (ε : ℝ), 0 < ε ∧
      ContMDiff (J.prod 𝓘(ℝ, Fin m → E)) I n F ∧ (∀ x, F (x, 0) = g x) ∧
      ∀ x, ∀ s ∈ ball (0 : Fin m → E) ε,
        IsRegularPoint 𝓘(ℝ, Fin m → E) I (fun s ↦ F (x, s)) s ∧
          IsRegularPoint (J.prod 𝓘(ℝ, Fin m → E)) I F (x, s) := by
  have : IsManifold I 1 M := IsManifold.of_le (n := n) (by exact_mod_cast hn)
  have hn' : (1 : WithTop ℕ∞) ≤ n := by exact_mod_cast hn
  have hn0 : (n : WithTop ℕ∞) ≠ 0 := (zero_lt_one.trans_le hn').ne'
  -- A family of local motions about each point, and finitely many covering the image of `g`.
  choose U hUo hyU φ hφ hφ0 hφreg using fun y : M ↦ exists_contMDiff_family_isRegularPoint (I := I)
    hn y
  obtain ⟨t, ht⟩ := (isCompact_range hg.continuous).elim_finite_subcover U hUo
    fun z _ ↦ mem_iUnion.2 ⟨z, hyU z⟩
  set m := t.card
  let ys : Fin m → M := fun i ↦ (t.equivFin.symm i : M)
  let ψ : Fin m → E → M → M := fun i ↦ φ (ys i)
  have hψ0 (i : Fin m) : ψ i 0 = id := hφ0 _
  let F : N × (Fin m → E) → M := fun p ↦ (List.finRange m).foldr (fun i w ↦ ψ i (p.2 i) w) (g p.1)
  have hF : ContMDiff (J.prod 𝓘(ℝ, Fin m → E)) I n F :=
    (List.contMDiff_foldr (fun i ↦ hφ (ys i)) _).comp (contMDiff_snd.prodMk (hg.comp contMDiff_fst))
  have hF0 (x : N) : F (x, 0) = g x := List.foldr_fixed' (fun i ↦ by simp [hψ0]) _
  -- At the parameter `0`, every slice is regular.
  have hreg0 (x : N) : IsRegularPoint 𝓘(ℝ, Fin m → E) I (fun s ↦ F (x, s)) 0 := by
    obtain ⟨y, hyt, hxy⟩ := mem_iUnion₂.1 (ht (mem_range_self x))
    set k := t.equivFin ⟨y, hyt⟩
    have hk : ys k = y := by simp [ys, k]
    have hcomp : (fun s ↦ F (x, s)) ∘ Pi.single k = fun d ↦ ψ k d (g x) := by
      ext d
      simp only [comp_apply, F]
      rw [List.foldr_pi_single_eq hψ0 k d (g x) (List.nodup_finRange m)]
      simp
    have hsingle : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, Fin m → E) n (Pi.single (M := fun _ ↦ E) k) :=
      (ContinuousLinearMap.single ℝ (fun _ : Fin m ↦ E) k).contMDiff
    have h := IsRegularPoint.of_comp (f := fun s ↦ F (x, s))
      (g := Pi.single (M := fun _ ↦ E) k) (p := 0)
      (by rw [hcomp]; simp only [ψ, hk]; exact hφreg y (g x) hxy)
      ((hF.comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiableAt hn0)
      ((hsingle 0).mdifferentiableAt hn0)
    rwa [Pi.single_zero] at h
  -- The regular slices form an open set containing `N × {0}`, hence `N × B(0, ε)`.
  obtain ⟨u, v, -, hv, hu, h0v, huv⟩ := generalized_tube_lemma isCompact_univ isCompact_singleton
    (t := {(0 : Fin m → E)}) (isOpen_setOfPred_isRegularPoint_slice hF hn') fun ⟨x, s⟩ hp ↦ by
      obtain ⟨-, rfl⟩ : x ∈ univ ∧ s = 0 := by simpa using hp
      exact hreg0 x
  obtain ⟨ε, hε, hεv⟩ := Metric.isOpen_iff.1 hv 0 (singleton_subset_iff.1 h0v)
  refine ⟨m, F, ε, hε, hF, hF0, fun x s hs ↦ ?_⟩
  have hslice : IsRegularPoint 𝓘(ℝ, Fin m → E) I (fun s ↦ F (x, s)) s :=
    huv (show (x, s) ∈ u ×ˢ v from ⟨hu (mem_univ x), hεv hs⟩)
  exact ⟨hslice, IsRegularPoint.of_comp (g := fun s : Fin m → E ↦ (x, s)) (p := s) hslice
    ((hF _).mdifferentiableAt hn0)
    ((contMDiff_const.prodMk contMDiff_id).mdifferentiableAt hn0)⟩

end SymplecticGeometry

end
