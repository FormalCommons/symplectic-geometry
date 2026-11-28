/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.HPrinciple.CubeCompression
public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Topology.MetricSpace.Thickening
import SymplecticGeometry.Geometry.Diffeomorphism.Diffeotopy.Slice
import TauCeti.Data.Set.Function

/-!
# Pushing the cube into a region of approximation

Let the core `E` be a finite-dimensional real normed space (such as `Fin m → ℝ`), `F` a real
normed space, and `D = E × F` with the max norm, so that `Q = closedBall 0 1` is the cube and
`closedBall 0 1 ×ˢ {0}` its core. Let `H` be a diffeotopy of `L × D` that keeps the parameter
`l ∈ L` and is the identity off `{p | ‖p.2.1‖ ≤ 1 - ε₀ ∧ ‖p.2‖ < 1}`, and let `V ⊆ L × D` be an
open set containing `H (1, (l, y))` for `l` in a compact `K` and `y` in the core, as holonomic
approximation gives it (`SymplecticGeometry.exists_holonomic_approximation_family`).

`SymplecticGeometry.exists_isotopy_mapsTo_of_diffeotopy` composes `H` with the compression of the
cube onto a thin tube around its core (`SymplecticGeometry.exists_cubeCompression`). It gives a
smooth family `e (l, s, ·)` of diffeomorphisms of `D`, over `L × [0, 1]`, starting at the identity,
preserving `Q`, the identity where `1 - ε₀ / 2 < ‖x.1‖`, and such that, for `l ∈ K`,
`e (l, 1, ·)` maps `Q` into the union of the slice of `V` over `l` and the slab
`1 - ε₀ < ‖x.1‖`. First a tube lemma, uniform over `K`, gives `δ' > 0` such that `H (1, ·)` maps
the points over `K` within `δ'` of the core into `V`; then the compression, with this `δ'`, maps
`Q` into that tube or into the slab, where `H` is the identity.

This is the isotopy of the handle-core lemma, proved for a core of any dimension by holonomic
approximation and compression (Eliashberg–Mishachev, §10.2) in place of McDuff–Salamon's
induction on the dimension of the core.

## Main results

* `SymplecticGeometry.exists_isotopy_mapsTo_of_diffeotopy`

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Lemma 7.3.2.
* [Y. Eliashberg and N. Mishachev, *Introduction to the h-principle*][EliashbergMishachev2002],
  §10.2.
-/

public section

open Set Metric TauCeti
open scoped ContDiff Manifold unitInterval

namespace SymplecticGeometry

variable {L E F : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **The isotopy that pushes the cube into a region of approximation.** Let `D = E × F`, `E`
finite-dimensional, with the max norm, and `0 < ε₀ < 1`. Let `H` be a diffeotopy of `L × D` that
keeps the parameter and, at all times, is the identity at the points `p` with
`1 - ε₀ < ‖p.2.1‖` or `1 ≤ ‖p.2‖`, and let `V ⊆ L × D` be open, containing `H (1, (l, y))` for
`l` in a compact `K` and `y` in the core `closedBall 0 1 ×ˢ {0}`. Then there is a smooth
`e : (L × [0, 1]) × D → D` such that

* each `e ((l, s), ·)` is a diffeomorphism of `D`, and `e ((l, 0), ·)` is the identity;
* each `e ((l, s), ·)` maps the cube `closedBall 0 1` into itself and is the identity where
  `1 - ε₀ / 2 < ‖x.1‖`;
* for `l ∈ K`, `e ((l, 1), ·)` maps the cube into the union of `{x | (l, x) ∈ V}` and the slab
  `1 - ε₀ < ‖x.1‖`. -/
theorem exists_isotopy_mapsTo_of_diffeotopy {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀₁ : ε₀ < 1)
    (H : Diffeotopy 𝓘(ℝ, L × E × F) ∞ (L × E × F)) (hH : ∀ t p, (H (t, p)).1 = p.1)
    (hHid : ∀ t p, 1 - ε₀ < ‖p.2.1‖ ∨ 1 ≤ ‖p.2‖ → H (t, p) = p)
    {K : Set L} (hK : IsCompact K) {V : Set (L × E × F)} (hV : IsOpen V)
    (hKV : ∀ l ∈ K, ∀ y ∈ closedBall (0 : E) 1 ×ˢ {(0 : F)}, H (1, (l, y)) ∈ V) :
    ∃ e : (L × I) × E × F → E × F,
      ContMDiff ((𝓘(ℝ, L).prod (𝓡∂ 1)).prod 𝓘(ℝ, E × F)) 𝓘(ℝ, E × F) ∞ e ∧
      (∀ p, ∃ φ : (E × F) ≃ₘ^∞⟮𝓘(ℝ, E × F), 𝓘(ℝ, E × F)⟯ (E × F), ⇑φ = fun x ↦ e (p, x)) ∧
      (∀ l x, e ((l, 0), x) = x) ∧
      (∀ p, MapsTo (fun x ↦ e (p, x)) (closedBall 0 1) (closedBall 0 1)) ∧
      (∀ p x, 1 - ε₀ / 2 < ‖x.1‖ → e (p, x) = x) ∧
      ∀ l ∈ K, MapsTo (fun x ↦ e ((l, 1), x)) (closedBall 0 1)
        ({x | (l, x) ∈ V} ∪ {x | 1 - ε₀ < ‖x.1‖}) := by
  -- the tube lemma: `H (1, ·)` maps the points over `K` near the core into `V`
  have hHc : Continuous fun p : L × E × F ↦ H (1, p) :=
    H.contMDiff.continuous.comp (continuous_const.prodMk continuous_id)
  obtain ⟨δ', hδ', hδ'V⟩ := (hK.prod ((isCompact_closedBall (0 : E) 1).prod
    isCompact_singleton)).exists_thickening_subset_open (hV.preimage hHc)
    fun q (hq : q ∈ K ×ˢ (closedBall (0 : E) 1 ×ˢ {(0 : F)})) ↦ hKV q.1 hq.1 q.2 hq.2
  -- the compression
  obtain ⟨ψ, hψ, hψpos, hψ0, hψA, hψQ, hψ1⟩ :=
    exists_cubeCompression (E := E) (F := F) hε₀ hε₀₁ hδ'
  set c : I → E × F → E × F := fun s ↦ prodFiberScaling fun u ↦ ψ ((s : ℝ), u) with hc
  have hψs (s : I) : ContDiff ℝ ∞ fun u : E ↦ ψ ((s : ℝ), u) :=
    hψ.comp (contDiff_const.prodMk contDiff_id)
  have hHmk (t : I) (l : L) (y : E × F) : (l, (H (t, (l, y))).2) = H (t, (l, y)) :=
    Prod.ext (hH t (l, y)).symm rfl
  -- every time slice of `H` maps the points with `‖p.2‖ ≤ 1` among themselves
  have hHQ (t : I) : MapsTo (fun p ↦ H (t, p)) {p : L × E × F | ‖p.2‖ ≤ 1}
      {p | ‖p.2‖ ≤ 1} := fun p hp ↦ by
    simpa only [Diffeotopy.timeSlice_apply] using
      (H.timeSlice t).injective.mapsTo_of_eq_self (f := H.timeSlice t)
        (K := {p : L × E × F | ‖p.2‖ ≤ 1})
        (fun q hq ↦ (H.timeSlice_apply t q).trans (hHid t q (Or.inr (not_le.1 hq).le))) hp
  -- `H` for the product model, so that it has slices over `L`
  have hH' (t : I) (p : L × E × F) : (H.toProdModel (t, p)).1 = p.1 := by
    rw [Diffeotopy.toProdModel_apply, hH]
  refine ⟨fun q ↦ (H (q.1.2, (q.1.1, c q.1.2 q.2))).2, ?_, fun p ↦ ?_, fun l x ↦ ?_,
    fun p x hx ↦ ?_, fun p x hx ↦ ?_, fun l hl x hx ↦ ?_⟩
  · have hcs : ContMDiff ((𝓘(ℝ, L).prod (𝓡∂ 1)).prod 𝓘(ℝ, E × F)) 𝓘(ℝ, E × F) ∞
        fun q : (L × I) × E × F ↦ c q.1.2 q.2 :=
      contMDiff_prodFiberScaling_family (ψ := fun q : (L × I) × E ↦ ψ ((q.1.2 : ℝ), q.2))
        (hψ.contMDiff.comp
          ((contMDiff_subtypeVal_Icc.comp (contMDiff_snd.comp contMDiff_fst)).prodMk_space
            contMDiff_snd))
    have he := (H.toProdModel.contMDiff_slice hH').comp (contMDiff_fst.prodMk hcs)
    simp only [Function.comp_def, Diffeotopy.slice_apply, Diffeotopy.toProdModel_apply] at he
    exact he
  · refine ⟨(prodFiberScalingDiffeomorph (hψs p.2) fun u ↦ (hψpos _).1.ne').trans
      (H.toProdModel.slice hH' p.1 p.2), ?_⟩
    funext x
    rw [Diffeomorph.coe_trans, Function.comp_apply, coe_prodFiberScalingDiffeomorph,
      Diffeotopy.slice_apply, Diffeotopy.toProdModel_apply]
  · have hc0 : c 0 x = x := by simpa only [hc, Set.Icc.coe_zero] using hψ0 x
    exact (congrArg (fun y ↦ (H (0, (l, y))).2) hc0).trans (congrArg Prod.snd (H.apply_zero _))
  · have hy : (p.1, c p.2 x) ∈ {q : L × E × F | ‖q.2‖ ≤ 1} :=
      mem_closedBall_zero_iff.1 (hψQ _ hx)
    exact mem_closedBall_zero_iff.2 (hHQ p.2 hy)
  · have hcx : c p.2 x = x := hψA _ x hx
    exact (congrArg (fun y ↦ (H (p.2, (p.1, y))).2) hcx).trans
      (congrArg Prod.snd (hHid _ _ (Or.inl (by linarith))))
  · -- `c 1` maps `x` into the tube, where `H (1, ·)` lands in `V`, or into the slab
    have hy : c 1 x ∈ closedBall 0 1 := hψQ _ hx
    rcases (by simpa only [hc, Set.Icc.coe_one] using hψ1 hx :
        c 1 x ∈ {y : E × F | ‖y.2‖ < δ'} ∪ {y | 1 - ε₀ < ‖y.1‖}) with h | h
    · left
      have hmem : (l, c 1 x) ∈ thickening δ' (K ×ˢ (closedBall (0 : E) 1 ×ˢ {(0 : F)})) := by
        refine mem_thickening_iff.2 ⟨(l, ((c 1 x).1, 0)), ⟨hl, ?_, rfl⟩, ?_⟩
        · exact mem_closedBall_zero_iff.2
            ((norm_fst_le (c 1 x)).trans (mem_closedBall_zero_iff.1 hy))
        · simpa [Prod.dist_eq, dist_zero_right, max_eq_right (norm_nonneg _)] using h
      have hV1 : H (1, (l, c 1 x)) ∈ V := hδ'V hmem
      rw [← hHmk] at hV1
      exact hV1
    · right
      have he : (H (1, (l, c 1 x))).2 = c 1 x := congrArg Prod.snd (hHid 1 _ (Or.inl h))
      exact (congrArg (fun y : E × F ↦ 1 - ε₀ < ‖y.1‖) he).mpr h

end SymplecticGeometry

end
