/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Topology.VectorBundle.Core.Basic
public import SymplecticGeometry.Topology.VectorBundle.FiniteRank.CompactCharts
public import SymplecticGeometry.Topology.ContinuousMap.LaurentApproximation
public import SymplecticGeometry.Topology.VectorBundle.FiniteRank.ChartHom
public import SymplecticGeometry.Topology.VectorBundle.FiniteRank.LaurentClutching
public import SymplecticGeometry.Topology.VectorBundle.FiniteRank.NearbyClutching

/-!
# Laurent approximation of clutching functions

Let `X` be compact Hausdorff and `E` a finite-rank complex core over `X`. Every automorphism `f`
of the pullback of `E` to `X × Circle` is close to a Laurent family
`laurentHom N a = ∑_{|i| ≤ N} a_i(x) u^i` of endomorphisms `a i : E ⟶ E`: close enough that the
Laurent family is an automorphism and the clutchings of `E` by `f` and by it are isomorphic.

The proof follows [Hatcher2017, §2.1]. Cover `X` by finitely many charts of `E` and take a
partition of unity `ρ` subordinate to them, with cutoffs `σ_k` equal to `1` on the support of
`ρ_k` and supported in the chart `k`
(`TauCeti.FiniteRankBundleCore.exists_partitionOfUnity_isSubordinate_baseSet`). In the chart `k`,
the cut-off fibre map `σ_k f` is a continuous map `X × Circle → End(ℂⁿ)`, which
`ContinuousMap.exists_norm_sub_laurent_lt` approximates uniformly by a Laurent polynomial with
continuous coefficients `c_{k,i}`. The coefficient fields `ρ_k c_{k,i}` are supported in the
chart `k`, so `VectorBundleCore.CoordinateHom.ofChart` makes them endomorphisms of `E`, and
`a_i = ∑_k ofChart (ρ_k c_{k,i})`.

The fibre maps of a morphism are read in the chart of `E` at each point, and the transitions to
those charts need not be bounded. The estimate is therefore made in the chart `j` of the finite
cover with `ρ_j(x) ≠ 0`, where the transitions between the finitely many charts are bounded on
the compact supports of the `ρ_k` (`VectorBundleCore.exists_norm_coordChange_le`), and so is `f⁻¹`
(`TauCeti.FiniteRankBundleCore.exists_norm_inChartCoordinates_le`). It is brought back to the
point's own chart by `TauCeti.FiniteRankBundleCore.isIso_of_norm_conj_lt_one` and
`TauCeti.FiniteRankBundleCore.nonempty_iso_clutching_of_norm_conj_lt_one`.

## Main results

* `TauCeti.FiniteRankBundleCore.exists_norm_conj_laurentHom_lt_one`: for every automorphism `f`
  of the pullback of `E` to `X × Circle` there is a Laurent family `g` such that, at every point,
  some change of coordinates brings `f⁻¹ g` within distance less than `1` of the identity;
* `TauCeti.FiniteRankBundleCore.exists_iso_clutching_laurentHom`: the Laurent family is then an
  automorphism, and the clutchings of `E` by `f` and by it are isomorphic.

## References

* [A. Hatcher, *Vector Bundles and K-Theory*][Hatcher2017], §2.1 (Laurent clutching functions).
-/

public section

noncomputable section

open CategoryTheory Finset

namespace TauCeti.FiniteRankBundleCore

variable {X : Type*} [TopologicalSpace X] {E : FiniteRankBundleCore ℂ X}

/-- The pullback of `E` to `X × Circle`, on which the clutching functions live. -/
local notation "Q" E => (FiniteRankBundleCore.pullback E (ContinuousMap.fst : C(X × Circle, X)))

/-- A point of `X × Circle` over the domain of the chart `k` of `E` lies in the domain of the
chart `(k, 1)` of the pullback of `E`. -/
private theorem mem_baseSet_pullback_fst {k : X} {w : X × Circle}
    (h : w.1 ∈ E.core.baseSet k) : w ∈ (Q E).core.baseSet (k, 1) := by
  rw [VectorBundleCore.baseSet_at, localTriv_baseSet_pullback, Set.mem_preimage,
    ← VectorBundleCore.baseSet_at]
  simpa only [ContinuousMap.fst_apply] using h

/-- Let `a i = ∑ k, ofChart k k (ρ k • c i · k)` be patched from the coefficient fields `c i` in
the charts `k`, which `ρ k` cuts off. Read in a chart `j` of `E` at a point `(x, u)` with `x` in
its domain, the Laurent family `laurentHom N a` is `∑ k, ρ k x • T(k → j) ∘ L k ∘ T(j → k)`, for
the Laurent polynomials `L k = ∑_{|i| ≤ N} u ^ i • c i x k`. -/
private theorem inChartCoordinates_laurentHom_ofChart {t : Finset X} (ρ : t → C(X, ℝ))
    (hρ : ∀ k, tsupport (ρ k) ⊆ E.core.baseSet k) (N : ℕ)
    (c : ℤ → C(X, t → (Fin E.rank → ℂ) →L[ℂ] (Fin E.rank → ℂ))) {j : X} {w : X × Circle}
    (hw : w.1 ∈ E.core.baseSet j) :
    (Q E).core.inChartCoordinates (Q E).core (j, 1) (j, 1) w
        ((laurentHom N fun i ↦ ∑ k : t,
          (VectorBundleCore.CoordinateHom.ofChart (k : X) (k : X) (fun x ↦ ρ k x • c i x k)
            ((ρ k).continuous.smul ((continuous_apply k).comp (c i).continuous))
            ((tsupport_smul_subset_left _ _).trans fun _ hx ↦ ⟨hρ k hx, hρ k hx⟩) :
              E ⟶ E)).fiberMap w) =
      ∑ k : t, ρ k w.1 • (E.core.coordChange k j w.1).comp
        ((∑ i ∈ Icc (-(N : ℤ)) N, (w.2 : ℂ) ^ i • c i w.1 k).comp
          (E.core.coordChange j k w.1)) := by
  rw [inChartCoordinates_pullback,
    fiberMap_laurentHom, VectorBundleCore.inChartCoordinates_sum]
  simp_rw [VectorBundleCore.inChartCoordinates_smul, fiberMap_sum,
    VectorBundleCore.inChartCoordinates_sum, ContinuousMap.fst_apply]
  have hk (i : ℤ) (k : t) := (VectorBundleCore.CoordinateHom.operator_eq _ j j
    ⟨w.1, hw, hw⟩).symm.trans (VectorBundleCore.CoordinateHom.operator_ofChart
      (g := fun x ↦ ρ k x • c i x k) (hg := (ρ k).continuous.smul
        ((continuous_apply k).comp (c i).continuous))
      (hgs := (tsupport_smul_subset_left _ _).trans fun _ hx ↦ ⟨hρ k hx, hρ k hx⟩) j j
      ⟨w.1, hw, hw⟩)
  simp only [hk]
  ext v : 1
  simp only [sum_apply, smul_apply, ContinuousLinearMap.comp_apply, map_sum, map_smul,
    smul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun k _ ↦ sum_congr rfl fun i _ ↦ ?_
  rw [ContinuousLinearMap.map_smul_of_tower, smul_comm]

/-- A morphism `h` of the pullback of `E` to `X × Circle`, read in the chart `k` of `E` and cut
off by a function `σ` supported in the domain of that chart, is continuous on `X × Circle`. -/
private theorem continuous_smul_inChartCoordinates_fiberMap (h : (Q E) ⟶ (Q E)) {k : X}
    {σ : C(X, ℝ)} (hσ : tsupport σ ⊆ E.core.baseSet k) :
    Continuous fun w : X × Circle ↦
      σ w.1 • (E.core.inChartCoordinates E.core k k w.1 (h.fiberMap w) :
        (Fin E.rank → ℂ) →L[ℂ] (Fin E.rank → ℂ)) := by
  have hs : (tsupport fun w : X × Circle ↦ σ w.1 •
      (E.core.inChartCoordinates E.core k k w.1 (h.fiberMap w) :
        (Fin E.rank → ℂ) →L[ℂ] (Fin E.rank → ℂ))) ⊆ (Q E).core.baseSet (k, 1) := by
    refine (tsupport_smul_subset_left (fun w : X × Circle ↦ σ w.1) _).trans ?_
    exact (tsupport_comp_subset_preimage σ continuous_fst).trans fun w hw ↦
      mem_baseSet_pullback_fst (hσ hw)
  refine ContinuousOn.continuous_of_tsupport_subset ?_
    (((Q E).core.isOpen_baseSet _).inter ((Q E).core.isOpen_baseSet _)) (Set.subset_inter hs hs)
  refine ((σ.continuous.comp continuous_fst).continuousOn.smul
    (VectorBundleCore.continuousOn_inChartCoordinates
      (VectorBundleCore.CoordinateHom.continuous_fiberMap h).continuousOn)).congr fun w _ ↦ ?_
  simp only [inChartCoordinates_pullback, ContinuousMap.fst_apply, Function.comp_apply,
    Pi.smul_apply']

/-- The estimate in the chart `j`: let `ρ` be a partition of unity subordinate to charts `k` of
`E`, with cutoffs `σ k` equal to `1` on the support of `ρ k`, and let the Laurent polynomials
`L k = ∑_{|i| ≤ N} u ^ i • c i x k` be within `ε` of `σ k • h` read in the chart `k` at a point
`w = (x, u)`, with `x` in the support of `ρ j`. If the transitions between the chart `j` and the
charts `k` with `x` in the support of `ρ k` are bounded by `D` at `x`, then the Laurent family
patched from the `c i` and `h` differ, read in the chart `j`, by at most `D ^ 2 * ε` at `w`. -/
private theorem norm_inChartCoordinates_laurentHom_ofChart_sub_le {t : Finset X}
    (ρ : PartitionOfUnity t X) (hρ : ∀ k, tsupport (ρ k) ⊆ E.core.baseSet k)
    {σ : t → C(X, ℝ)} (hσ : ∀ k, Set.EqOn (σ k) 1 (tsupport (ρ k))) (N : ℕ)
    (c : ℤ → C(X, t → (Fin E.rank → ℂ) →L[ℂ] (Fin E.rank → ℂ))) (h : (Q E) ⟶ (Q E)) {D ε : ℝ}
    {j : t} {w : X × Circle} (hj : w.1 ∈ tsupport (ρ j))
    (hD : ∀ k, w.1 ∈ tsupport (ρ k) →
      ‖E.core.coordChange k j w.1‖ ≤ D ∧ ‖E.core.coordChange j k w.1‖ ≤ D)
    (hc : ∀ k, ‖σ k w.1 • E.core.inChartCoordinates E.core k k w.1 (h.fiberMap w) -
      ∑ i ∈ Icc (-(N : ℤ)) N, (w.2 : ℂ) ^ i • c i w.1 k‖ < ε) :
    ‖(Q E).core.inChartCoordinates (Q E).core ((j : X), 1) ((j : X), 1) w
        ((laurentHom N fun i ↦ ∑ k : t,
          (VectorBundleCore.CoordinateHom.ofChart (k : X) (k : X) (fun x ↦ ρ k x • c i x k)
            ((ρ k).continuous.smul ((continuous_apply k).comp (c i).continuous))
            ((tsupport_smul_subset_left _ _).trans fun _ hx ↦ ⟨hρ k hx, hρ k hx⟩) :
              E ⟶ E)).fiberMap w) -
      (Q E).core.inChartCoordinates (Q E).core ((j : X), 1) ((j : X), 1) w (h.fiberMap w)‖ ≤
        D ^ 2 * ε := by
  have hρ1 : ∑ k, ρ k w.1 = 1 := by
    rw [← finsum_eq_sum_of_fintype]
    exact ρ.sum_eq_one (Set.mem_univ _)
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD j hj).1
  have hwj : w ∈ (Q E).core.baseSet ((j : X), 1) := mem_baseSet_pullback_fst (hρ j hj)
  -- Split `h` along the partition of unity, and compare it with the Laurent family term by term.
  have hsplit (M : (Fin (Q E).rank → ℂ) →L[ℂ] (Fin (Q E).rank → ℂ)) : M = ∑ k, ρ k w.1 • M := by
    rw [← sum_smul, hρ1, one_smul]
  rw [inChartCoordinates_laurentHom_ofChart ρ hρ N c (hρ j hj),
    hsplit ((Q E).core.inChartCoordinates _ _ _ w (h.fiberMap w)), ← sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  calc _ ≤ ∑ k : t, ρ k w.1 * (D ^ 2 * ε) := sum_le_sum fun k _ ↦ ?_
    _ = D ^ 2 * ε := by rw [← sum_mul, hρ1, one_mul]
  rw [← smul_sub, norm_smul, Real.norm_of_nonneg (ρ.nonneg k w.1)]
  by_cases hk : ρ k w.1 = 0
  · simp [hk]
  refine mul_le_mul_of_nonneg_left ?_ (ρ.nonneg k w.1)
  have hxk : w.1 ∈ tsupport (ρ k) := subset_tsupport _ hk
  have hwk : w ∈ (Q E).core.baseSet ((k : X), 1) := mem_baseSet_pullback_fst (hρ k hxk)
  have hck := hc k
  generalize (∑ i ∈ Icc (-(N : ℤ)) N, (w.2 : ℂ) ^ i • c i w.1 k) = L at hck ⊢
  -- Read `h` in the chart `k`, where the Laurent polynomial `L` approximates it.
  rw [VectorBundleCore.inChartCoordinates_eq_coordChange_comp _ hwk hwj hwk hwj,
    inChartCoordinates_pullback, coordChange_pullback, coordChange_pullback]
  simp only [ContinuousMap.fst_apply]
  have hσk : σ k w.1 = 1 := hσ k hxk
  rw [← one_smul ℝ (E.core.inChartCoordinates E.core k k w.1 (h.fiberMap w)), ← hσk,
    ← ContinuousLinearMap.comp_sub, ← ContinuousLinearMap.sub_comp]
  calc _ ≤ ‖E.core.coordChange k j w.1‖ *
        (‖L - σ k w.1 • E.core.inChartCoordinates E.core k k w.1 (h.fiberMap w)‖ *
          ‖E.core.coordChange j k w.1‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ D * (ε * D) :=
        mul_le_mul (hD k hxk).1 (mul_le_mul (by rw [norm_sub_rev]; exact hck.le) (hD k hxk).2
          (norm_nonneg _) ((norm_nonneg _).trans hck.le)) (by positivity) hD0
    _ = D ^ 2 * ε := by ring

variable [CompactSpace X] [T2Space X]

/-- **Laurent approximation of clutching functions.** For `X` compact Hausdorff, every
automorphism `f` of the pullback of `E` to `X × Circle` is close to a Laurent family
`laurentHom N a`: at every point `w`, some change of coordinates `U` brings the fibre map of
`f⁻¹ ∘ laurentHom N a` within distance less than `1` of the identity. -/
theorem exists_norm_conj_laurentHom_lt_one (f : (Q E) ≅ (Q E)) :
    ∃ (N : ℕ) (a : ℤ → (E ⟶ E)), ∀ w,
      ∃ U : ((Fin (Q E).rank → ℂ) →L[ℂ] (Fin (Q E).rank → ℂ))ˣ,
        ‖↑U⁻¹ * ((f.inv.fiberMap w).comp ((laurentHom N a).fiberMap w)) * ↑U - 1‖ < 1 := by
  obtain ⟨t, ρ, σ, hρs, hσs, hσ1⟩ := E.exists_partitionOfUnity_isSubordinate_baseSet
  have hK (k : t) : IsCompact (tsupport (ρ k)) := (isClosed_tsupport _).isCompact
  -- Bounds for the transitions between the charts of the cover, and for `f⁻¹` in them.
  obtain ⟨C₁, hC₁⟩ := E.core.exists_norm_coordChange_le (fun k : t ↦ (k : X)) hK hρs
  obtain ⟨C₂, hC₂⟩ := exists_norm_inChartCoordinates_le f.inv (fun k : t ↦ ((k : X), 1))
    (fun k ↦ ((k : X), 1)) (K := fun k ↦ tsupport (ρ k) ×ˢ Set.univ)
    (fun k ↦ (hK k).prod isCompact_univ) fun k w hw ↦
      ⟨mem_baseSet_pullback_fst (hρs k hw.1), mem_baseSet_pullback_fst (hρs k hw.1)⟩
  set D₁ := max C₁ 1
  set D₂ := max C₂ 1
  have hD₁ : 0 < D₁ := lt_max_of_lt_right one_pos
  have hD₂ : 0 < D₂ := lt_max_of_lt_right one_pos
  set ε : ℝ := 1 / (2 * (D₂ * D₁ ^ 2)) with hε_def
  -- Approximate the fibre maps of `f` in the charts of the cover, cut off by `σ`, uniformly by
  -- Laurent polynomials.
  let ψ : C(X × Circle, t → (Fin E.rank → ℂ) →L[ℂ] (Fin E.rank → ℂ)) :=
    ⟨fun w k ↦ σ k w.1 • E.core.inChartCoordinates E.core k k w.1 (f.hom.fiberMap w),
      continuous_pi fun k ↦ continuous_smul_inChartCoordinates_fiberMap f.hom (hσs k)⟩
  obtain ⟨N, c, hc⟩ := ContinuousMap.exists_norm_sub_laurent_lt ψ (by positivity : 0 < ε)
  have hck (w : X × Circle) (k : t) :
      ‖σ k w.1 • E.core.inChartCoordinates E.core k k w.1 (f.hom.fiberMap w) -
        ∑ i ∈ Icc (-(N : ℤ)) N, (w.2 : ℂ) ^ i • c i w.1 k‖ < ε := by
    simpa [ψ, Finset.sum_apply] using (norm_le_pi_norm _ k).trans_lt (hc w)
  -- The Laurent coefficients, patched from the charts.
  obtain ⟨a, ha⟩ : ∃ a : ℤ → (E ⟶ E), a = fun i ↦ ∑ k : t,
    (VectorBundleCore.CoordinateHom.ofChart (k : X) (k : X) (fun x ↦ ρ k x • c i x k)
      ((ρ k).continuous.smul ((continuous_apply k).comp (c i).continuous))
      ((tsupport_smul_subset_left _ _).trans fun _ hx ↦ ⟨hρs k hx, hρs k hx⟩) : E ⟶ E) :=
    ⟨_, rfl⟩
  refine ⟨N, a, fun w ↦ ?_⟩
  -- The estimate is made in a chart `j` of the cover at the base point of `w`.
  obtain ⟨j, hj⟩ := ρ.exists_pos (Set.mem_univ w.1)
  have hxj : w.1 ∈ tsupport (ρ j) := subset_tsupport _ hj.ne'
  obtain ⟨U, hU⟩ := (Q E).core.exists_units_inv_mul_mul_eq_inChartCoordinates
    (mem_baseSet_pullback_fst (hρs j hxj))
  refine ⟨U, ?_⟩
  set Φ := (Q E).core.inChartCoordinates (Q E).core ((j : X), 1) ((j : X), 1) w
  -- Conjugation by `U` reads `f⁻¹ ∘ g - 1` in the chart `j`, as `f⁻¹ ∘ (g - f)`.
  have hinv (M : (Fin (Q E).rank → ℂ) →L[ℂ] (Fin (Q E).rank → ℂ)) :
      f.inv.fiberMap w * (f.hom.fiberMap w * M) = M := by
    rw [← mul_assoc, ContinuousLinearMap.mul_def (f.inv.fiberMap w), fiberMap_hom_inv_id,
      ← ContinuousLinearMap.one_def, one_mul]
  have hfac : ↑U⁻¹ * ((f.inv.fiberMap w).comp ((laurentHom N a).fiberMap w)) * ↑U - 1 =
      Φ (f.inv.fiberMap w) * (Φ ((laurentHom N a).fiberMap w) - Φ (f.hom.fiberMap w)) := by
    rw [← hU, ← hU, ← hU, ← ContinuousLinearMap.mul_def]
    simp only [mul_sub, mul_assoc, Units.mul_inv_cancel_left, hinv, Units.inv_mul]
  have hdiff : ‖Φ ((laurentHom N a).fiberMap w) - Φ (f.hom.fiberMap w)‖ ≤ D₁ ^ 2 * ε := by
    rw [ha]
    exact norm_inChartCoordinates_laurentHom_ofChart_sub_le ρ hρs hσ1 N c f.hom hxj
      (fun k hk ↦ ⟨(hC₁ j k w.1 ⟨hxj, hk⟩).trans (le_max_left _ _),
        (hC₁ k j w.1 ⟨hk, hxj⟩).trans (le_max_left _ _)⟩) (hck w)
  have hfi : ‖Φ (f.inv.fiberMap w)‖ ≤ D₂ :=
    (hC₂ j w ⟨hxj, Set.mem_univ _⟩).trans (le_max_left _ _)
  rw [hfac]
  calc _ ≤ _ := norm_mul_le _ _
    _ ≤ D₂ * (D₁ ^ 2 * ε) := mul_le_mul hfi hdiff (norm_nonneg _) hD₂.le
    _ = 1 / 2 := by
        rw [hε_def]
        field_simp
    _ < 1 := by norm_num

/-- **Laurent clutching functions.** For `X` compact Hausdorff, every automorphism `f` of the
pullback of `E` to `X × Circle` gives the same clutching, up to isomorphism, as an automorphism
`g` whose underlying morphism is a Laurent family `laurentHom N a`, with fibre map
`∑_{|i| ≤ N} u ^ i • (a i).fiberMap x` at `(x, u)`. -/
theorem exists_iso_clutching_laurentHom (f : (Q E) ≅ (Q E)) :
    ∃ (N : ℕ) (a : ℤ → (E ⟶ E)) (g : (Q E) ≅ (Q E)), g.hom = laurentHom N a ∧
      Nonempty (E.clutching f ≅ E.clutching g) := by
  obtain ⟨N, a, h⟩ := exists_norm_conj_laurentHom_lt_one f
  have := isIso_of_norm_conj_lt_one f (laurentHom N a) h
  exact ⟨N, a, asIso (laurentHom N a), rfl, nonempty_iso_clutching_of_norm_conj_lt_one h⟩

end TauCeti.FiniteRankBundleCore

end
