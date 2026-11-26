/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Topology.VectorBundle.Core.Basic
public import SymplecticGeometry.Topology.VectorBundle.FiniteRank.CompactCharts
public import SymplecticGeometry.Topology.VectorBundle.FiniteRank.NearbyClutching

/-!
# Linear clutching functions with an invertible leading coefficient

Let `X` be compact Hausdorff, `E` a finite-rank complex core over `X`, and `a b : E ⟶ E`. A linear
clutching function is an automorphism `g` of the pullback of `E` to `X × Circle` with fibre map
`u • a(x) + b(x)` at `(x, u)`. Its leading coefficient `a` need not be invertible. Following
[Hatcher2017, §2.1], the clutching by `g` does not change, up to isomorphism, when `g` is replaced
by the linear clutching function `u • (a + t b) + (t a + b)`, for a real `t ∈ [0, 1)`, and `t` can
be chosen so that `a + t b` is invertible on every fibre.

The substitution behind this is the Möbius map `m_s(u) = (u + s) / (1 + s u)`, which for a real
`s ∈ [0, 1)` maps the unit circle to itself (`Circle.norm_coe_add_ofReal`). It gives
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
each point. A small `t` would not do in general: for the trivial line over the unit disc with
`a(x) = -x` and `b = 1`, the coefficient `a + t b` vanishes at `x = t`.

## Main results

* `Circle.norm_coe_add_ofReal`: `‖u + s‖ = ‖1 + s u‖` for `u` on the unit circle and real `s`;
* `TauCeti.FiniteRankBundleCore.exists_norm_conj_fiberMap_le`: over a compact Hausdorff base, the
  fibre maps of an endomorphism are bounded after a change of coordinates at each point;
* `TauCeti.FiniteRankBundleCore.exists_isIso_add_smul`: over a compact Hausdorff base, `a + c b` is
  an isomorphism for an isomorphism `a` and all small enough scalars `c`;
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

/-- For `u` on the unit circle and a real `s`, `‖u + s‖ = ‖1 + s u‖`: the Möbius map
`u ↦ (u + s) / (1 + s u)` preserves the unit circle where it is defined. -/
theorem Circle.norm_coe_add_ofReal (u : Circle) (s : ℝ) : ‖(u : ℂ) + s‖ = ‖1 + s * (u : ℂ)‖ := by
  have h : 1 + s * (u : ℂ) = u * (starRingEnd ℂ (u : ℂ) + s) := by
    rw [mul_add, Complex.mul_conj, Complex.normSq_eq_norm_sq, Circle.norm_coe]
    push_cast
    ring
  rw [h, norm_mul, Circle.norm_coe, one_mul, ← Complex.norm_conj, map_add,
    Complex.conj_ofReal]

namespace TauCeti.FiniteRankBundleCore

variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace X]

/-- Over a compact Hausdorff base, the fibre maps of an endomorphism `n` of a finite-rank core are
bounded after a change of coordinates: there is a `C` such that at every point `x` some unit `U`
of the endomorphisms of the model fibre has `‖U⁻¹ ∘ n(x) ∘ U‖ ≤ C`. -/
theorem exists_norm_conj_fiberMap_le [CompactSpace X] [T2Space X]
    {A : FiniteRankBundleCore 𝕜 X} (n : A ⟶ A) :
    ∃ C, ∀ x, ∃ U : ((Fin A.rank → 𝕜) →L[𝕜] (Fin A.rank → 𝕜))ˣ,
      ‖↑U⁻¹ * n.fiberMap x * ↑U‖ ≤ C := by
  obtain ⟨t, ρ, -, hρs, -, -⟩ := A.exists_partitionOfUnity_isSubordinate_baseSet
  obtain ⟨C, hC⟩ := exists_norm_inChartCoordinates_le n (fun k : t ↦ (k : X)) (fun k ↦ k)
    (K := fun k ↦ tsupport (ρ k)) (fun k ↦ (isClosed_tsupport _).isCompact)
    fun k _ hx ↦ ⟨hρs k hx, hρs k hx⟩
  refine ⟨C, fun x ↦ ?_⟩
  obtain ⟨j, hj⟩ := ρ.exists_pos (Set.mem_univ x)
  have hxj : x ∈ tsupport (ρ j) := subset_tsupport _ hj.ne'
  obtain ⟨U, hU⟩ := A.core.exists_units_inv_mul_mul_eq_inChartCoordinates (hρs j hxj)
  exact ⟨U, (hU _).symm ▸ hC j x hxj⟩

/-- **Invertibility is open over a compact base.** Over a compact Hausdorff base, for an
isomorphism `a` and any morphism `b` of finite-rank cores, `a + c b` is an isomorphism for every
scalar `c` small enough. -/
theorem exists_isIso_add_smul [CompleteSpace 𝕜] [CompactSpace X] [T2Space X]
    {A D : FiniteRankBundleCore 𝕜 X} (a : A ⟶ D) [IsIso a] (b : A ⟶ D) :
    ∃ ε > 0, ∀ c : 𝕜, ‖c‖ < ε → IsIso (a + ContinuousMap.const X c • b) := by
  obtain ⟨C, hC⟩ := exists_norm_conj_fiberMap_le (b ≫ inv a)
  set C' := max C 1
  have hC' : 0 < C' := lt_max_of_lt_right one_pos
  refine ⟨1 / C', by positivity, fun c hc ↦ ?_⟩
  refine isIso_of_norm_conj_lt_one (asIso a) _ fun x ↦ ?_
  obtain ⟨U, hU⟩ := hC x
  refine ⟨U, ?_⟩
  -- After `a⁻¹`, the morphism `a + c b` is `1 + c (a⁻¹ ∘ b)`, in any coordinates.
  have he : ↑U⁻¹ * (((asIso a).inv.fiberMap x).comp
      ((a + ContinuousMap.const X c • b).fiberMap x)) * ↑U - 1 =
        c • (↑U⁻¹ * (b ≫ inv a).fiberMap x * ↑U) := by
    rw [asIso_inv, fiberMap_add, fiberMap_smul, ContinuousMap.const_apply,
      ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_smul, ← fiberMap_comp,
      ← fiberMap_comp, IsIso.hom_inv_id, fiberMap_id, ← ContinuousLinearMap.one_def, mul_add,
      add_mul, mul_one, Units.inv_mul, add_sub_cancel_left, mul_smul_comm, smul_mul_assoc]
  rw [he, norm_smul]
  calc ‖c‖ * ‖↑U⁻¹ * (b ≫ inv a).fiberMap x * ↑U‖ ≤ ‖c‖ * C' :=
        mul_le_mul_of_nonneg_left (hU.trans (le_max_left _ _)) (norm_nonneg _)
    _ < 1 / C' * C' := mul_lt_mul_of_pos_right hc hC'
    _ = 1 := by field_simp

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
        rw [norm_div, Circle.norm_coe_add_ofReal, div_self (norm_ne_zero_iff.2 hd)] }
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
