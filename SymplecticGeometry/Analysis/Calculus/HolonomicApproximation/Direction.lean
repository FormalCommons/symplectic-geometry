/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Basic
import SymplecticGeometry.Geometry.Diffeomorphism.Diffeotopy.Translate
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Geometry.Manifold.PartitionOfUnity
import SymplecticGeometry.Analysis.Calculus.ContDiff.Pi
import SymplecticGeometry.Analysis.Calculus.FDeriv.AddSmulSub
import SymplecticGeometry.Analysis.Calculus.HolonomicApproximation.Basic
import SymplecticGeometry.Analysis.Calculus.HolonomicApproximation.ZigZag
import SymplecticGeometry.Topology.MetricSpace.Thickening

/-!
# Holonomic approximation in one direction of a cube

In the coordinates of `SymplecticGeometry.Analysis.Calculus.HolonomicApproximation.Basic`, on
`D = (Fin m → ℝ) × (Fin k → ℝ)` with sup norms and `0 < k`, let `Q = closedBall 0 1 ×ˢ {0}` be
the core cube. This file proves the step of the induction of [EliashbergMishachev2002], Chapter 3,
that adds one core direction `i₀` to a set `J'` of directions in which a formal section `(f, G)`
is already holonomic on `Q`.

Let `B` be a closed set of core points, containing the faces of the cube in the directions
`insert i₀ J'`, such that `(f, G)` is holonomic on an open set `U ⊇ B ×ˢ {0}`. Then there are a
`δ`-small diffeotopy `h` of `D` that keeps every core coordinate, is the identity near
`B ×ˢ {0}` and off a compact subset `C` of the `δ`-neighbourhood of `Q`, and a smooth `f'` equal
to `f` off `C` and near `B ×ˢ {0}`, that is `ε`-close to `(f, G)` in the directions
`insert i₀ J'` on an open set containing the image of `Q` under `h 1`.

The proof glues three earlier results.
* `SymplecticGeometry.exists_holonomic_approximation_zigzag` gives, at a height `r` below a bound
  fixed in advance, a map `f₀` approximating `(f, G)` in the directions `insert i₀ J'` near the
  zig-zag `u ↦ (u, r g₀ (u i₀) eⱼ)`.
* A smooth cutoff `ψ` of the core point, `0` near `B` and `1` on the cube away from `B`, turns
  the profile into `u ↦ ψ u * g₀ (u i₀)`, and `SymplecticGeometry.exists_wiggling_diffeotopy`
  pushes the cube along `eⱼ` by this profile: away from `B` it moves the cube onto the zig-zag,
  and near `B` it is the identity.
* A second smooth cutoff `χ` on `D`, `0` near the points over a neighbourhood of `B` and away
  from the cube, and `1` near the points of the cube away from `B` up to the fixed height,
  glues: `f' := f + χ • (f₀ - f)`. Its derivative is bounded before the accuracy asked of `f₀` is
  chosen, so that the gluing error `‖D χ‖ ‖f₀ - f‖` is small where `χ` varies; there the
  displaced cube lies in `U`, where `f` itself is holonomic.

Both cutoffs come from Mathlib's smooth Urysohn lemma
`exists_contMDiffMap_zero_one_nhds_of_isClosed`.

## Main results

* `SymplecticGeometry.exists_holonomic_approximation_direction`: holonomic approximation in one
  more direction of the cube, relative to `B`.

## References

* [Y. Eliashberg and N. Mishachev, *Introduction to the h-Principle*][EliashbergMishachev2002]
-/

public section

open Set Metric
open scoped Manifold ContDiff Topology

namespace SymplecticGeometry

/-- The gluing cutoff of `exists_holonomic_approximation_direction`: a smooth `χ` on `D` with
values in `[0, 1]`, `0` near the points over `B` and over the closed `ρ / 4`-neighbourhood of the
part of `B` in the cube, `1` near the points of the cube off the `ρ / 2`-neighbourhood of that
part up to height `r₀`, `0` off a compact neighbourhood of the cube of height `2 r₀`, and with
bounded derivative. -/
private theorem exists_gluing_cutoff {m k : ℕ} {B : Set (Fin m → ℝ)} (hB : IsClosed B)
    {ρ δ r₀ : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ) (hr₀ : 0 < r₀) :
    ∃ χ : (Fin m → ℝ) × (Fin k → ℝ) → ℝ, ContDiff ℝ ∞ χ ∧ (∀ x, χ x ∈ Icc (0 : ℝ) 1) ∧
      (∀ᶠ x in 𝓝ˢ ((B ∪ cthickening (ρ / 4) (B ∩ closedBall 0 1)) ×ˢ univ), χ x = 0) ∧
      (∀ᶠ x in 𝓝ˢ ((closedBall 0 1 \ thickening (ρ / 2) (B ∩ closedBall 0 1)) ×ˢ
        closedBall 0 r₀), χ x = 1) ∧
      (∀ x ∉ cthickening (δ / 4) (closedBall (0 : Fin m → ℝ) 1) ×ˢ closedBall 0 (2 * r₀),
        χ x = 0) ∧
      ∃ L, ∀ x, ‖fderiv ℝ χ x‖ ≤ L := by
  set Q₁ : Set (Fin m → ℝ) := closedBall 0 1
  set B₁ := B ∩ Q₁
  set A : Set ((Fin m → ℝ) × (Fin k → ℝ)) :=
    (B ∪ cthickening (ρ / 4) B₁) ×ˢ univ ∪ (thickening (δ / 4) Q₁ ×ˢ ball 0 (2 * r₀))ᶜ
  set E : Set ((Fin m → ℝ) × (Fin k → ℝ)) := (Q₁ \ thickening (ρ / 2) B₁) ×ˢ closedBall 0 r₀
  have hA : IsClosed A := ((hB.union isClosed_cthickening).prod isClosed_univ).union
    (isOpen_thickening.prod isOpen_ball).isClosed_compl
  have hE : IsClosed E := (isClosed_closedBall.sdiff isOpen_thickening).prod isClosed_closedBall
  have hAE : Disjoint A E := by
    refine disjoint_left.2 fun x hxA hxE ↦ ?_
    obtain ⟨⟨hu, hu₂⟩, hv⟩ := hxE
    rcases hxA with ⟨huB | huB, -⟩ | hx
    · exact hu₂ (self_subset_thickening (by positivity) _ ⟨huB, hu⟩)
    · exact hu₂ (cthickening_subset_thickening' (by positivity) (by linarith) _ huB)
    · refine hx ⟨self_subset_thickening (by positivity) _ hu, ?_⟩
      rw [mem_ball_zero_iff]
      exact (mem_closedBall_zero_iff.1 hv).trans_lt (by linarith)
  obtain ⟨χ, hχ0, hχ1, hχI⟩ :=
    exists_contMDiffMap_zero_one_nhds_of_isClosed 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ)) (n := (⊤ : ℕ∞))
      hA hE hAE
  have hχ : ContDiff ℝ ∞ χ := contMDiff_iff_contDiff.1 χ.contMDiff
  have hχC : ∀ x ∉ cthickening (δ / 4) Q₁ ×ˢ closedBall 0 (2 * r₀), χ x = 0 :=
    fun x hx ↦ hχ0.self_of_nhdsSet x (Or.inr fun hx' ↦ hx
      ⟨thickening_subset_cthickening _ _ hx'.1, ball_subset_closedBall hx'.2⟩)
  have hχs : HasCompactSupport (fderiv ℝ χ) :=
    (HasCompactSupport.intro ((isCompact_closedBall _ _).cthickening.prod
      (isCompact_closedBall _ _)) hχC).fderiv ℝ
  obtain ⟨L, hL⟩ := (hχ.continuous_fderiv (by simp)).bounded_above_of_compact_support hχs
  exact ⟨χ, hχ, hχI, hχ0.filter_mono (nhdsSet_mono subset_union_left), hχ1, hχC, L, hL⟩

/-- The estimate of `exists_holonomic_approximation_direction` on `V`: the glued map
`f + χ • (f₀ - f)` is `ε`-close to `(f, G)`, on the vectors `w` with `P w`, at the points where
`f₀` is `ε₀`-close to `(f, G)` and either `f` is holonomic or `χ = 1` nearby, and at the points
where `f` is holonomic and `χ = 0` nearby. -/
private theorem glue_estimate {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f f₀ : E → F} {G : E → E →L[ℝ] F} {χ : E → ℝ}
    {U V₀ : Set E} {P : E → Prop} {ε ε₀ L : ℝ} (hf : Differentiable ℝ f)
    (hf₀ : Differentiable ℝ f₀) (hχ : Differentiable ℝ χ) (hχI : ∀ x, χ x ∈ Icc (0 : ℝ) 1)
    (hL : ∀ x, ‖fderiv ℝ χ x‖ ≤ L) (hUf : ∀ x ∈ U, fderiv ℝ f x = G x)
    (hf₀V₀ : ∀ x ∈ V₀, ‖f₀ x - f x‖ < ε₀ ∧ ∀ w, P w → ‖(fderiv ℝ f₀ x - G x) w‖ ≤ ε₀ * ‖w‖)
    (hε : 0 < ε) (hε₀ε : ε₀ ≤ ε) (hε₀L : (1 + L) * ε₀ ≤ ε) {x : E}
    (hx : x ∈ V₀ ∩ U ∪ V₀ ∩ interior {x | χ x = 1} ∪ U ∩ interior {x | χ x = 0}) :
    ‖f x + χ x • (f₀ x - f x) - f x‖ < ε ∧ ∀ w, P w →
      ‖(fderiv ℝ (fun y ↦ f y + χ y • (f₀ y - f y)) x - G x) w‖ ≤ ε * ‖w‖ := by
  rcases hx with (⟨hx₀, hxU⟩ | ⟨hx₀, hx₁⟩) | ⟨hxU, hx₀⟩
  · -- Where `χ` varies, `f` is holonomic and `f₀` close to it.
    obtain ⟨hf₀x, hf₀w⟩ := hf₀V₀ x hx₀
    obtain ⟨hχ₀, hχ₁⟩ := hχI x
    refine ⟨?_, fun w hw ↦ ?_⟩
    · rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hχ₀]
      exact (mul_le_of_le_one_left (norm_nonneg _) hχ₁).trans_lt (hf₀x.trans_le hε₀ε)
    · refine (norm_fderiv_add_smul_sub_sub_apply_le (G x) (hf x) (hf₀ x) (hχ x) hχ₀ hχ₁ (hL x)
        w).trans ?_
      rw [hUf x hxU, sub_self, zero_apply, norm_zero,
        max_eq_right (norm_nonneg _)]
      have hL₀ : 0 ≤ L := (norm_nonneg _).trans (hL x)
      calc ‖(fderiv ℝ f₀ x - G x) w‖ + L * ‖w‖ * ‖f₀ x - f x‖
          ≤ ε₀ * ‖w‖ + L * ‖w‖ * ε₀ := by gcongr; exact hf₀w w hw
        _ = (1 + L) * ε₀ * ‖w‖ := by ring
        _ ≤ ε * ‖w‖ := by gcongr
  · -- Where `χ = 1` nearby, the glued map is `f₀` nearby.
    have heq : (fun y ↦ f y + χ y • (f₀ y - f y)) =ᶠ[𝓝 x] f₀ :=
      Filter.mem_of_superset (mem_interior_iff_mem_nhds.1 hx₁) fun y hy ↦ by simp [hy.out]
    have hx₁' : χ x = 1 := interior_subset hx₁
    obtain ⟨hf₀x, hf₀w⟩ := hf₀V₀ x hx₀
    refine ⟨by simpa [hx₁'] using hf₀x.trans_le hε₀ε, fun w hw ↦ ?_⟩
    rw [heq.fderiv_eq]
    exact (hf₀w w hw).trans (by gcongr)
  · -- Where `χ = 0` nearby, the glued map is `f` nearby, and `f` is holonomic.
    have heq : (fun y ↦ f y + χ y • (f₀ y - f y)) =ᶠ[𝓝 x] f :=
      Filter.mem_of_superset (mem_interior_iff_mem_nhds.1 hx₀) fun y hy ↦ by simp [hy.out]
    have hx₀' : χ x = 0 := interior_subset hx₀
    refine ⟨by simpa [hx₀'] using hε, fun w _ ↦ ?_⟩
    rw [heq.fderiv_eq, hUf x hxU, sub_self, zero_apply, norm_zero]
    positivity

/-- **Holonomic approximation in one direction of a cube.** On `D = (Fin m → ℝ) × (Fin k → ℝ)`
with sup norms and `0 < k`, let `Q = closedBall 0 1 ×ˢ {0}` be the core cube, `i₀` a core
direction and `J'` a set of core directions. Let `(f, G)` be a smooth formal section such that:
* on `Q`, `D f` agrees with `G` on the core vectors in the directions `J'`;
* `(f, G)` is holonomic (`D f = G`) on an open set `U` containing `B ×ˢ {0}`, where `B` is a
  closed set of core points that contains the points of the cube with `|u i| = 1` for some `i`
  in `insert i₀ J'`.

Let `ε, δ > 0`. There are a diffeotopy `h` of `D`, a smooth map `f'` and an open set `V` such
that:
* `h` is the identity and `f'` equals `f` off a compact subset of the `δ`-neighbourhood of `Q`;
* `h` moves every point by less than `δ`, keeps the core coordinates of every point, and is the
  identity at all times near `B ×ˢ {0}`;
* `V` contains the image of `Q` under `h 1`, and on `V` the map `f'` is `ε`-close to `f`, and
  `(D f' - G) w` has norm at most `ε ‖w‖` for every vector `w` whose core part lies in the
  directions `insert i₀ J'`;
* `f'` equals `f` near `B ×ˢ {0}`. -/
theorem exists_holonomic_approximation_direction {m k : ℕ} (hk : 0 < k)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (i₀ : Fin m) {J' : Finset (Fin m)}
    {f : (Fin m → ℝ) × (Fin k → ℝ) → F}
    {G : (Fin m → ℝ) × (Fin k → ℝ) → (Fin m → ℝ) × (Fin k → ℝ) →L[ℝ] F}
    (hf : ContDiff ℝ ∞ f) (hG : ContDiff ℝ ∞ G)
    (hJ' : ∀ u ∈ closedBall (0 : Fin m → ℝ) 1, ∀ v : Fin m → ℝ, (∀ i ∉ J', v i = 0) →
      fderiv ℝ f (u, 0) (v, 0) = G (u, 0) (v, 0))
    {B : Set (Fin m → ℝ)} (hB : IsClosed B)
    (hJB : ∀ u ∈ closedBall (0 : Fin m → ℝ) 1, (∃ i ∈ insert i₀ J', |u i| = 1) → u ∈ B)
    {U : Set ((Fin m → ℝ) × (Fin k → ℝ))} (hU : IsOpen U) (hBU : B ×ˢ {0} ⊆ U)
    (hUf : ∀ x ∈ U, fderiv ℝ f x = G x) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ (h : TauCeti.Diffeotopy 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ)) ∞ ((Fin m → ℝ) × (Fin k → ℝ)))
      (f' : (Fin m → ℝ) × (Fin k → ℝ) → F) (V : Set ((Fin m → ℝ) × (Fin k → ℝ))),
      (∃ C, IsCompact C ∧ C ⊆ thickening δ (closedBall 0 1 ×ˢ {0}) ∧
        (∀ t, ∀ x ∉ C, h (t, x) = x) ∧ ∀ x ∉ C, f' x = f x) ∧
      (∀ t x, dist (h (t, x)) x < δ) ∧
      (∀ t x, (h (t, x)).1 = x.1) ∧
      (∃ W ∈ 𝓝ˢ (B ×ˢ {0}), ∀ t, ∀ x ∈ W, h (t, x) = x) ∧
      IsOpen V ∧ (fun x ↦ h (1, x)) '' (closedBall 0 1 ×ˢ {0}) ⊆ V ∧ ContDiff ℝ ∞ f' ∧
      (∀ x ∈ V, ‖f' x - f x‖ < ε ∧ ∀ w : (Fin m → ℝ) × (Fin k → ℝ),
        (∀ i ∉ insert i₀ J', w.1 i = 0) → ‖(fderiv ℝ f' x - G x) w‖ ≤ ε * ‖w‖) ∧
      ∃ U' ∈ 𝓝ˢ (B ×ˢ {0}), EqOn f' f U' := by
  set j : Fin k := ⟨0, hk⟩
  set Q₁ : Set (Fin m → ℝ) := closedBall 0 1
  set Q : Set ((Fin m → ℝ) × (Fin k → ℝ)) := Q₁ ×ˢ {0} with hQ
  -- Near the compact part `B₁` of `B` in the cube, `U` contains a uniform product neighbourhood.
  set B₁ := B ∩ Q₁
  have hB₁ : IsCompact B₁ := (isCompact_closedBall _ _).inter_left hB
  obtain ⟨r₁, hr₁, hr₁U⟩ := IsCompact.exists_thickening_subset_open
    (hB₁.prod (isCompact_singleton (x := (0 : Fin k → ℝ)))) hU
    ((prod_mono inter_subset_left subset_rfl).trans hBU)
  rw [thickening_prod, thickening_singleton] at hr₁U
  have hNU : ∀ u v, u ∈ thickening (r₁ / 2) B₁ → ‖v‖ < r₁ / 2 → (u, v) ∈ U := fun u v hu hv ↦
    hr₁U ⟨thickening_mono (half_le_self hr₁.le) _ hu,
      mem_ball_zero_iff.2 (hv.trans (half_lt_self hr₁))⟩
  -- The cutoff `ψ` of the core point: `0` near `B`, `1` on the cube off `N₁`.
  set N₁ := thickening (r₁ / 4) B₁
  set N₂ := thickening (r₁ / 2) B₁
  obtain ⟨ψ', hψ0, hψ1, hψI⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    𝓘(ℝ, Fin m → ℝ) (n := (⊤ : ℕ∞)) hB (isClosed_closedBall.sdiff (isOpen_thickening (E := B₁)))
    (s := B) (t := Q₁ \ N₁) (disjoint_left.2 fun u huB hu ↦
      hu.2 (self_subset_thickening (by positivity) _ ⟨huB, hu.1⟩))
  set ψ : (Fin m → ℝ) → ℝ := ⇑ψ'
  have hψ : ContDiff ℝ ∞ ψ := contMDiff_iff_contDiff.1 ψ'.contMDiff
  -- The height bound `r₀`, and the gluing cutoff `χ` on `D`.
  set r₀ := min (r₁ / 4) (δ / 8)
  have hr₀ : 0 < r₀ := lt_min (by positivity) (by positivity)
  obtain ⟨χ, hχ, hχI, hχ0, hχ1, hχC₂, L, hL⟩ :=
    exists_gluing_cutoff (k := k) hB hr₁ hδ hr₀
  set C₂ : Set ((Fin m → ℝ) × (Fin k → ℝ)) := cthickening (δ / 4) Q₁ ×ˢ closedBall 0 (2 * r₀)
  have hC₂ : IsCompact C₂ := (isCompact_closedBall _ _).cthickening.prod (isCompact_closedBall _ _)
  -- The accuracy asked of the zig-zag approximation, chosen after `χ`.
  set L' := max L 0 + 1
  have hL' : 1 ≤ L' := le_add_of_nonneg_left (le_max_right _ _)
  set ε₀ := ε / (2 * L')
  have hε₀ : 0 < ε₀ := by positivity
  have hε₀ε : ε₀ ≤ ε := div_le_self hε.le (by linarith)
  have hε₀L : (1 + L) * ε₀ ≤ ε := by
    calc (1 + L) * ε₀ ≤ (2 * L') * ε₀ := by
          gcongr; linarith [le_max_left L 0]
      _ = ε := mul_div_cancel₀ _ (by positivity)
  -- The zig-zag approximation.
  have hupd : ContDiff ℝ ∞ fun p : (Fin m → ℝ) × ℝ ↦ Function.update p.1 i₀ p.2 :=
    contDiff_fst.update i₀ contDiff_snd
  have hGu : ContDiff ℝ ∞ (Function.uncurry fun (q : (Fin m → ℝ) × ℝ) (u : Fin m → ℝ) ↦
      G (Function.update u i₀ q.2, 0)) :=
    hG.comp ((hupd.comp (contDiff_snd.prodMk (contDiff_snd.comp contDiff_fst))).prodMk
      contDiff_const)
  obtain ⟨r, g₀, f₀, V₀, hr, hrr₀, hg₀, hg₀1, -, hV₀, hXV₀, hf₀, hf₀V₀, -⟩ :=
    exists_holonomic_approximation_zigzag i₀ j (J' := J') hf hG.continuous
      (fun s ↦ hG.comp ((hupd.comp (contDiff_id.prodMk contDiff_const)).prodMk contDiff_const))
      ((hGu.fderiv (n := 0) contDiff_fst (by simp)).continuous)
      hJ' hU hUf (fun x ⟨⟨hu, hi⟩, hv⟩ ↦ hBU ⟨hJB _ hu ⟨i₀, Finset.mem_insert_self _ _, hi⟩, hv⟩)
      hε₀ hr₀
  -- The diffeotopy pushes the closed `δ / 2`-neighbourhood of the cube by the profile `φ`.
  set φ : (Fin m → ℝ) → ℝ := fun u ↦ ψ u * g₀ (u i₀)
  have hφ : ContDiff ℝ ∞ φ := hψ.mul (hg₀.comp (contDiff_apply ℝ (fun _ : Fin m ↦ ℝ) i₀))
  have hφ1 : ∀ u, |φ u| ≤ 1 := fun u ↦ by
    rw [abs_mul, abs_of_nonneg (hψI u).1]
    simpa using mul_le_mul (hψI u).2 (hg₀1 _) (abs_nonneg _) zero_le_one
  have hrδ : r < δ / 2 := hrr₀.trans_le ((min_le_right _ _).trans (by linarith))
  have hK : IsCompact (cthickening (δ / 2) Q) :=
    ((isCompact_closedBall _ _).prod isCompact_singleton).cthickening
  obtain ⟨h, ⟨C₁, hC₁, hC₁K, hC₁h⟩, hsmall, hKh, hfst, hfix⟩ :=
    exists_wiggling_diffeotopy hK j hr.le hrδ hφ hφ1
  set f' : (Fin m → ℝ) × (Fin k → ℝ) → F := fun x ↦ f x + χ x • (f₀ x - f x)
  set V := V₀ ∩ U ∪ V₀ ∩ interior {x | χ x = 1} ∪ U ∩ interior {x | χ x = 0}
  have hf' : ContDiff ℝ ∞ f' := hf.add (hχ.smul (hf₀.sub hf))
  refine ⟨h, f', V, ⟨C₁ ∪ C₂, hC₁.union hC₂, union_subset ?_ ?_,
    fun t x hx ↦ hC₁h t x fun h ↦ hx (Or.inl h),
    fun x hx ↦ by simp [f', hχC₂ x fun h ↦ hx (Or.inr h)]⟩,
    fun t x ↦ (hsmall t x).trans (half_lt_self hδ), hfst, ?_,
    (((hV₀.inter hU).union (hV₀.inter isOpen_interior)).union (hU.inter isOpen_interior)), ?_,
    hf', fun x hx ↦ ?_, ⟨{x | χ x = 0}, nhdsSet_mono ?_ hχ0, fun x hx ↦ by simp [f', hx.out]⟩⟩
  · calc C₁ ⊆ thickening (δ / 2) (cthickening (δ / 2) Q) := hC₁K
      _ ⊆ thickening (δ / 2 + δ / 2) Q := thickening_cthickening_subset _ (by positivity) _
      _ = thickening δ Q := by rw [add_halves]
  · rw [hQ, thickening_prod, thickening_singleton]
    exact prod_mono (cthickening_subset_thickening' hδ (by linarith) _)
      (closedBall_subset_ball (by linarith [min_le_right (r₁ / 4) (δ / 8)]))
  · -- Near `B` the cutoff `ψ`, hence the profile, vanishes, so the diffeotopy is the identity.
    obtain ⟨O, hO, hBO, hOψ⟩ := eventually_nhdsSet_iff_exists.1 hψ0
    refine ⟨Prod.fst ⁻¹' O, (hO.preimage continuous_fst).mem_nhdsSet.2 fun x hx ↦ hBO hx.1,
      fun t x hx ↦ hfix t x ?_⟩
    simp [φ, ψ, hOψ _ hx]
  · rintro _ ⟨⟨u, v⟩, ⟨hu, hv⟩, rfl⟩
    rw [mem_singleton_iff] at hv
    subst hv
    rw [hKh 1 _ (self_subset_cthickening _ ⟨hu, rfl⟩)]
    simp only [Set.Icc.coe_one, one_mul, zero_add]
    have hv : ‖(Pi.single j (r * φ u) : Fin k → ℝ)‖ < r₁ / 2 := by
      rw [Pi.norm_single, Real.norm_eq_abs, abs_mul, abs_of_pos hr]
      calc r * |φ u| ≤ r * 1 := by gcongr; exact hφ1 u
        _ < r₁ / 2 := by linarith [min_le_left (r₁ / 4) (δ / 8)]
    by_cases hu₁ : u ∈ N₁
    · refine Or.inr ⟨hNU _ _ (thickening_mono (by linarith) _ hu₁) hv,
        mem_interior_iff_mem_nhds.2 (eventually_nhdsSet_iff_forall.1 hχ0 _ ?_)⟩
      exact ⟨Or.inr (thickening_subset_cthickening _ _ hu₁), trivial⟩
    have hψu : ψ u = 1 := hψ1.self_of_nhdsSet u ⟨hu, hu₁⟩
    have hV₀u : (u, (Pi.single j (r * φ u) : Fin k → ℝ)) ∈ V₀ := by
      simpa [φ, hψu] using hXV₀ u hu
    by_cases hu₂ : u ∈ N₂
    · exact Or.inl (Or.inl ⟨hV₀u, hNU _ _ hu₂ hv⟩)
    · refine Or.inl (Or.inr ⟨hV₀u,
        mem_interior_iff_mem_nhds.2 (eventually_nhdsSet_iff_forall.1 hχ1 _ ⟨⟨hu, hu₂⟩, ?_⟩)⟩)
      rw [mem_closedBall_zero_iff]
      rw [Pi.norm_single]
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos hr]
      calc r * |φ u| ≤ r * 1 := by gcongr; exact hφ1 u
        _ ≤ r₀ := by linarith
  · exact glue_estimate (hf.differentiable (by simp)) (hf₀.differentiable (by simp))
      (hχ.differentiable (by simp)) hχI hL hUf hf₀V₀ hε hε₀ε hε₀L hx
  · exact fun x hx ↦ ⟨Or.inl hx.1, trivial⟩

end SymplecticGeometry

end
