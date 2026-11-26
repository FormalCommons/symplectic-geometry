/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Complex.Basic
public import SymplecticGeometry.Topology.VectorBundle.FiniteRank.Clutching
import SymplecticGeometry.Topology.VectorBundle.FiniteRank.NearbyClutching
import SymplecticGeometry.Topology.VectorBundle.FiniteRank.Basic

/-!
# Linear clutching functions with an invertible leading coefficient

Let `X` be compact Hausdorff, `E` a finite-rank complex core over `X`, and `a b : E ⟶ E`. A linear
clutching function is an automorphism `g` of the pullback of `E` to `X × Circle` with fibre map
`u • a(x) + b(x)` at `(x, u)`. Its leading coefficient `a` need not be invertible. Following
[Hatcher2017, §2.1], the clutching by `g` does not change, up to isomorphism, when `g` is replaced
by the linear clutching function `u • (a + t b) + (t a + b)`, for a real `t ∈ [0, 1)`, and `t` can
be chosen so that `a + t b` is invertible on every fibre.

The substitution behind this is the Möbius map `m_s(u) = (u + s) / (1 + s u)`, which for a real
`s ∈ [0, 1)` maps the unit circle to itself (by `Complex.norm_one_sub_conj_mul`). It gives
`(u + s) a + (s u + 1) b = (1 + s u) (m_s(u) a + b)`, so the family
`p_s(x, u) = u (a + s b) + (s a + b)` is invertible for every `s ∈ [0, 1)`, and `s ↦ p_{s t}`,
`s ∈ I`, is a homotopy through automorphisms from `g` to the new clutching function, to which
`TauCeti.FiniteRankBundleCore.nonempty_iso_clutching_of_homotopic` applies.

The leading coefficient of `p_1` is `a + b`, the fibre map of `g` at `u = 1`, which is invertible.
Invertibility of morphisms is open under small perturbations over a compact base
(`TauCeti.FiniteRankBundleCore.exists_isIso_add_smul`), so `a + t b` is invertible for `t` close
to `1`. The estimate is made in finitely many charts: the fibre maps of a morphism over a compact
base are bounded after a change of coordinates at each point
(`TauCeti.FiniteRankBundleCore.exists_norm_conj_fiberMap_le`), and
`TauCeti.FiniteRankBundleCore.isIso_of_norm_conj_lt_one` brings the estimate back to the chart at
each point. A small `t` would not do in general: for the trivial line over the closed disc of
radius `1/2`, with `a(x) = -x` and `b = 1`, the map `1 - u x` never vanishes, but the
coefficient `a + t b = t - x` vanishes at `x = t` for every `t ≤ 1/2`.

## Main result

* `TauCeti.FiniteRankBundleCore.exists_isIso_nonempty_iso_clutching_linear`: a linear clutching
  function `u • a + b` gives the same clutching as `u • (a + t b) + (t a + b)` for some
  `t ∈ [0, 1)` with `a + t b` an isomorphism.

## References

* [A. Hatcher, *Vector Bundles and K-Theory*][Hatcher2017], §2.1 (linear clutching functions).
-/

public section

noncomputable section

open CategoryTheory

open scoped unitInterval

namespace TauCeti.FiniteRankBundleCore

variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace X]

variable {E : FiniteRankBundleCore ℂ X}

/-- The pullback of `E` to `X × Circle`, on which the clutching functions live. -/
local notation "Q" E => (FiniteRankBundleCore.pullback E (ContinuousMap.fst : C(X × Circle, X)))

/-- The Möbius substitution: if `u • a + b` is invertible on every fibre over `X × Circle`, then so
is `(u + s) a + (s u + 1) b`, for every real `s ∈ [0, 1)`, as `(1 + s u)` times its value at the
point `(u + s) / (1 + s u)` of the circle. -/
private theorem bijective_moebius {a b : E ⟶ E} {g : (Q E) ≅ (Q E)}
    (hg : ∀ w : X × Circle, g.hom.fiberMap w = (w.2 : ℂ) • a.fiberMap w.1 + b.fiberMap w.1)
    {s : ℝ} (hs₀ : 0 ≤ s) (hs₁ : s < 1) (x : X) (u : Circle) :
    Function.Bijective (((u : ℂ) + s) • a.fiberMap x + ((s : ℂ) * u + 1) • b.fiberMap x) := by
  have hd : 1 + (s : ℂ) * u ≠ 0 := by
    intro h
    have h' : ‖(s : ℂ) * u‖ = ‖(-1 : ℂ)‖ := by rw [eq_neg_of_add_eq_zero_right h]
    rw [norm_mul, Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_of_nonneg hs₀,
      norm_neg, norm_one] at h'
    exact hs₁.ne h'
  let m : Circle :=
    { val := ((u : ℂ) + s) / (1 + s * u)
      property := mem_sphere_zero_iff_norm.2 <| by
        have h := Complex.norm_one_sub_conj_mul (z := -(s : ℂ)) (Circle.norm_coe u)
        rw [Complex.norm_one_sub_conj_mul_comm] at h
        rw [norm_div, show ‖(u : ℂ) + s‖ = ‖1 + s * (u : ℂ)‖ by
          simpa [norm_sub_rev, add_comm] using h.symm, div_self (norm_ne_zero_iff.2 hd)] }
  have he : ((u : ℂ) + s) • a.fiberMap x + ((s : ℂ) * u + 1) • b.fiberMap x =
      (1 + (s : ℂ) * u) • g.hom.fiberMap (x, m) := by
    rw [hg, smul_add, smul_smul, add_comm ((s : ℂ) * u) 1]
    congr 2
    exact (mul_div_cancel₀ _ hd).symm
  rw [he, FunLike.coe_smul, ← toContinuousLinearMap_isoFiberEquiv,
    ContinuousLinearEquiv.coe_coe]
  exact (MulAction.bijective₀ hd).comp (isoFiberEquiv g _).bijective

/-- **Linear clutching functions with an invertible leading coefficient.** Let `X` be compact
Hausdorff, `E` a finite-rank complex core over `X`, `a b : E ⟶ E`, and `g` an automorphism of the
pullback of `E` to `X × Circle` with fibre map `u • a(x) + b(x)` at `(x, u)`. Then there is a real
`t` with `0 ≤ t < 1` such that `a + t b` is an isomorphism, and an automorphism `g'` of the same
pullback with fibre map `u • (a + t b)(x) + (t a + b)(x)` at `(x, u)` whose clutching is
isomorphic to that of `g`. -/
theorem exists_isIso_nonempty_iso_clutching_linear [CompactSpace X] [T2Space X] {a b : E ⟶ E}
    {g : (Q E) ≅ (Q E)}
    (hg : ∀ w : X × Circle, g.hom.fiberMap w = (w.2 : ℂ) • a.fiberMap w.1 + b.fiberMap w.1) :
    ∃ t : ℝ, 0 ≤ t ∧ t < 1 ∧ IsIso (a + ContinuousMap.const X (t : ℂ) • b) ∧
      ∃ g' : (Q E) ≅ (Q E),
        (∀ w : X × Circle, g'.hom.fiberMap w = (w.2 : ℂ) •
          (a + ContinuousMap.const X (t : ℂ) • b).fiberMap w.1 +
            (ContinuousMap.const X (t : ℂ) • a + b).fiberMap w.1) ∧
        Nonempty (E.clutching g ≅ E.clutching g') := by
  -- At `u = 1` the fibre map of `g` is `a + b`, so `a + b` is an isomorphism, and so is
  -- `a + t b = (a + b) - (1 - t) b` for `t` close to `1`.
  have hab : IsIso (a + b) := (isIso_iff_bijective _).2 fun x ↦ by
    have h := (isoFiberEquiv g (x, 1)).bijective
    rwa [← ContinuousLinearEquiv.coe_coe, toContinuousLinearMap_isoFiberEquiv, hg, Circle.coe_one,
      one_smul, ← fiberMap_add] at h
  obtain ⟨ε, hε, hiso⟩ := exists_isIso_add_smul (a + b) b
  obtain ⟨δ, hδ, hδε, hδ₁⟩ : ∃ δ : ℝ, 0 < δ ∧ δ < ε ∧ δ ≤ 1 :=
    ⟨min (ε / 2) 1, lt_min (half_pos hε) one_pos,
      (min_le_left _ _).trans_lt (half_lt_self hε), min_le_right _ _⟩
  set t : ℝ := 1 - δ
  have ht₀ : 0 ≤ t := sub_nonneg.2 hδ₁
  have ht₁ : t < 1 := sub_lt_self 1 hδ
  refine ⟨t, ht₀, ht₁, ?_, ?_⟩
  · have h := hiso (-(δ : ℂ)) (by rwa [norm_neg, Complex.norm_real, Real.norm_of_nonneg hδ.le])
    convert h using 1
    ext x : 1
    simp only [t, fiberMap_add, fiberMap_smul, ContinuousMap.const_apply]
    push_cast
    module
  -- The linear clutching function `u • (a + t b) + (t a + b)`.
  let G : (Q E) ⟶ (Q E) :=
    (⟨fun w ↦ (w.2 : ℂ), by fun_prop⟩ : C(X × Circle, ℂ)) •
        pullbackMap (a + ContinuousMap.const X (t : ℂ) • b) ContinuousMap.fst +
      pullbackMap (ContinuousMap.const X (t : ℂ) • a + b) ContinuousMap.fst
  have hG (w : X × Circle) : G.fiberMap w = (w.2 : ℂ) •
      (a + ContinuousMap.const X (t : ℂ) • b).fiberMap w.1 +
        (ContinuousMap.const X (t : ℂ) • a + b).fiberMap w.1 := by
    simp only [G, fiberMap_add, fiberMap_smul, fiberMap_pullbackMap, ContinuousMap.coe_mk,
      ContinuousMap.fst_apply]
  have hGm (w : X × Circle) : G.fiberMap w =
      ((w.2 : ℂ) + t) • a.fiberMap w.1 + ((t : ℂ) * w.2 + 1) • b.fiberMap w.1 := by
    rw [hG]
    simp only [fiberMap_add, fiberMap_smul, ContinuousMap.const_apply]
    module
  have : IsIso G := (isIso_iff_bijective _).2 fun w ↦ by
    rw [hGm]
    exact bijective_moebius hg ht₀ ht₁ w.1 w.2
  refine ⟨asIso G, hG, ?_⟩
  -- The homotopy `s ↦ p_{s t}`, with fibre map `(u + s t) a + (s t u + 1) b` at `((x, s), u)`.
  let H := (⟨fun w ↦ (w.2 : ℂ) + (t * w.1.2 : ℝ), by fun_prop⟩ :
        C((X × I) × Circle, ℂ)) • pullbackForgetTime (pullbackMap a ContinuousMap.fst) +
      (⟨fun w ↦ ((t * w.1.2 : ℝ) : ℂ) * w.2 + 1, by fun_prop⟩ : C((X × I) × Circle, ℂ)) •
        pullbackForgetTime (pullbackMap b ContinuousMap.fst)
  have hH (w : (X × I) × Circle) : H.fiberMap w = ((w.2 : ℂ) + (t * w.1.2 : ℝ)) •
      a.fiberMap w.1.1 + (((t * w.1.2 : ℝ) : ℂ) * w.2 + 1) • b.fiberMap w.1.1 := by
    simp only [H, fiberMap_add, fiberMap_smul, fiberMap_pullbackForgetTime, fiberMap_pullbackMap,
      ContinuousMap.coe_mk, ContinuousMap.fst_apply]
  have : IsIso H := (isIso_iff_bijective _).2 fun w ↦ by
    rw [hH]
    exact bijective_moebius hg (mul_nonneg ht₀ w.1.2.property.1)
      ((mul_le_of_le_one_right ht₀ w.1.2.property.2).trans_lt ht₁) w.1.1 w.2
  refine E.nonempty_iso_clutching_of_homotopic (asIso H) (fun w ↦ ?_) fun w ↦ ?_
  · rw [asIso_hom, hH, hg]
    simp
  · rw [asIso_hom, asIso_hom, hH, hGm]
    simp

end TauCeti.FiniteRankBundleCore

end
