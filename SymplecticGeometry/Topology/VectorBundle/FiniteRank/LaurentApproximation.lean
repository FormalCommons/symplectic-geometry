/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Data.Fintype.Order
public import Mathlib.Topology.PartitionOfUnity
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
`ρ_k` and supported in the chart `k`. In the chart `k`, the cut-off fibre map `σ_k f` is a
continuous map `X × Circle → End(ℂⁿ)`, which `ContinuousMap.exists_norm_sub_laurent_lt`
approximates uniformly by a Laurent polynomial with continuous coefficients `c_{k,i}`. The
coefficient fields `ρ_k c_{k,i}` are supported in the chart `k`, so
`VectorBundleCore.CoordinateHom.ofChart` makes them endomorphisms of `E`, and
`a_i = ∑_k ofChart (ρ_k c_{k,i})`.

The fibre maps of a morphism are read in the chart of `E` at each point, and the transitions to
those charts need not be bounded. The estimate is therefore made in the chart `j` of the finite
cover with `ρ_j(x) ≠ 0`, where the transitions between the finitely many charts are bounded on
the compact supports of the `ρ_k`, and it is brought back to the point's own chart by
`nonempty_iso_clutching_of_norm_conj_lt_one`.

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

/-- The fibre map at `w` of a morphism `h` of the pullback of `E` to `X × Circle`, read in the
chart of `E` at `k`. -/
private def chartFiber (h : (Q E) ⟶ (Q E)) (k : X) (w : X × Circle) :
    (Fin (Q E).rank → ℂ) →L[ℂ] (Fin (Q E).rank → ℂ) :=
  (Q E).core.coordChange w (k, 1) w * (h.fiberMap w * (Q E).core.coordChange (k, 1) w w)

/-- The fibre maps of a morphism, read in a fixed chart `k` of `E`, are continuous over the
chart. -/
private theorem continuousOn_chartFiber (h : (Q E) ⟶ (Q E)) (k : X) :
    ContinuousOn (chartFiber h k) ((Q E).core.baseSet (k, 1)) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hc := (h.operator (k, 1) (k, 1)).continuous.comp
    (f := fun w : ((Q E).core.baseSet (k, 1)) ↦
      (⟨w.1, w.2, w.2⟩ : ↥((Q E).core.baseSet (k, 1) ∩ (Q E).core.baseSet (k, 1))))
    (by fun_prop)
  refine hc.congr fun w ↦ ?_
  simp only [Function.comp_apply, Set.domRestrict_apply, VectorBundleCore.CoordinateHom.operator_eq,
    inChartCoordinates_core, chartFiber, ContinuousLinearMap.mul_def]

variable (E) in
/-- A finite partition of unity `ρ` on a compact Hausdorff base subordinate to charts of `E`,
with cutoffs `σ k` supported in the chart `k` and equal to `1` on the support of `ρ k`. -/
private theorem exists_chartPartition [CompactSpace X] [T2Space X] :
    ∃ (t : Finset X) (ρ σ : t → C(X, ℝ)), (∀ k x, 0 ≤ ρ k x) ∧ (∀ x, ∑ k, ρ k x = 1) ∧
      (∀ k, tsupport (ρ k) ⊆ E.core.baseSet k) ∧ (∀ k, tsupport (σ k) ⊆ E.core.baseSet k) ∧
      (∀ k, ∀ x ∈ tsupport (ρ k), σ k x = 1) := by
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : X ↦ E.core.baseSet x)
    (fun x ↦ E.core.isOpen_baseSet x)
    fun x _ ↦ Set.mem_iUnion.2 ⟨x, E.mem_baseSet_self x⟩
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ
    (fun k : t ↦ E.core.baseSet k) (fun k ↦ E.core.isOpen_baseSet k) fun x _ ↦ by
      obtain ⟨k, hk, hx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
      exact Set.mem_iUnion.2 ⟨⟨k, hk⟩, hx⟩
  have hσ (k : t) : ∃ σ : C(X, ℝ), tsupport σ ⊆ E.core.baseSet k ∧
      ∀ x ∈ tsupport (ρ k), σ x = 1 := by
    have hK : IsCompact (tsupport (ρ k)) := (isClosed_tsupport _).isCompact
    obtain ⟨L, -, hLc, hKL, hL⟩ :=
      exists_compact_closed_between hK (E.core.isOpen_baseSet k) (hρ k)
    obtain ⟨σ, hσ1, hσ0, -, -⟩ := exists_continuous_one_zero_of_isCompact hK
      isOpen_interior.isClosed_compl (Set.disjoint_compl_right_iff_subset.2 hKL)
    refine ⟨σ, (closure_minimal (fun x hx ↦ ?_) hLc).trans hL, fun x hx ↦ hσ1 hx⟩
    by_contra hxL
    exact hx (hσ0 fun h ↦ hxL (interior_subset h))
  choose σ hσs hσ1 using hσ
  refine ⟨t, fun k ↦ ρ k, σ, fun k x ↦ ρ.nonneg k x, fun x ↦ ?_, hρ, hσs, hσ1⟩
  rw [← finsum_eq_sum_of_fintype]
  exact ρ.sum_eq_one (Set.mem_univ x)

/-- In a ring, if `q` is inverse to `p` and `a c = 1`, then `q (a b) p - 1` factors as
`(q a p) (q b p - q c p)`. -/
private theorem conj_mul_sub_one {R : Type*} [Ring R] {p q a b c : R} (hpq : p * q = 1)
    (hqp : q * p = 1) (hac : a * c = 1) :
    q * (a * b) * p - 1 = q * a * p * (q * b * p - q * c * p) := by
  have h (d : R) : q * a * p * (q * d * p) = q * (a * d) * p := by
    simp only [mul_assoc]
    rw [← mul_assoc p q, hpq, one_mul]
  rw [mul_sub, h, h, hac, mul_one, hqp]

variable [CompactSpace X] [T2Space X]

/-- **Laurent approximation of clutching functions.** For `X` compact Hausdorff, every
automorphism `f` of the pullback of `E` to `X × Circle` is close to a Laurent family
`laurentHom N a`: at every point `w`, some change of coordinates `U` brings the fibre map of
`f⁻¹ ∘ laurentHom N a` within distance less than `1` of the identity. -/
theorem exists_norm_conj_laurentHom_lt_one (f : (Q E) ≅ (Q E)) :
    ∃ (N : ℕ) (a : ℤ → (E ⟶ E)), ∀ w,
      ∃ U : ((Fin (Q E).rank → ℂ) →L[ℂ] (Fin (Q E).rank → ℂ))ˣ,
        ‖↑U⁻¹ * ((f.inv.fiberMap w).comp ((laurentHom N a).fiberMap w)) * ↑U - 1‖ < 1 := by
  obtain ⟨t, ρ, σ, hρ0, hρ1, hρs, hσs, hσ1⟩ := exists_chartPartition E
  -- Bounds for the transitions between the charts of the cover, and for `f⁻¹` in them.
  obtain ⟨C₁, hC₁, hC₁b⟩ : ∃ C, 0 < C ∧ ∀ (j k : t) (w : X × Circle), w.1 ∈ tsupport (ρ j) →
      w.1 ∈ tsupport (ρ k) → ‖(Q E).core.coordChange (k, 1) (j, 1) w‖ ≤ C := by
    have h (j k : t) : ∃ C, ∀ x ∈ tsupport (ρ j) ∩ tsupport (ρ k),
        ‖E.core.coordChange k j x‖ ≤ C :=
      ((isClosed_tsupport _).inter (isClosed_tsupport _)).isCompact.exists_bound_of_continuousOn
        ((E.core.continuousOn_coordChange k j).mono fun x hx ↦ ⟨hρs k hx.2, hρs j hx.1⟩)
    choose B hB using h
    obtain ⟨C, hC⟩ := Finite.exists_le fun p : t × t ↦ B p.1 p.2
    exact ⟨max C 1, by positivity, fun j k w hj hk ↦
      (hB j k w.1 ⟨hj, hk⟩).trans ((hC (j, k)).trans (le_max_left _ _))⟩
  obtain ⟨C₂, hC₂, hC₂b⟩ : ∃ C, 0 < C ∧ ∀ (j : t) (w : X × Circle), w.1 ∈ tsupport (ρ j) →
      ‖chartFiber f.inv j w‖ ≤ C := by
    have h (j : t) : ∃ C, ∀ w ∈ tsupport (ρ j) ×ˢ (Set.univ : Set Circle),
        ‖chartFiber f.inv j w‖ ≤ C :=
      ((isClosed_tsupport _).isCompact.prod isCompact_univ).exists_bound_of_continuousOn
        ((continuousOn_chartFiber f.inv j).mono fun w hw ↦ hρs j hw.1)
    choose B hB using h
    obtain ⟨C, hC⟩ := Finite.exists_le B
    exact ⟨max C 1, by positivity, fun j w hj ↦
      (hB j w ⟨hj, Set.mem_univ _⟩).trans ((hC j).trans (le_max_left _ _))⟩
  set ε : ℝ := 1 / (2 * (C₂ * C₁ ^ 2)) with hε_def
  have hε : 0 < ε := by positivity
  -- The fibre maps of `f` in the charts of the cover, cut off by `σ`.
  have hψ (k : t) : Continuous fun w : X × Circle ↦ σ k w.1 • chartFiber f.hom k w := by
    refine continuous_iff_continuousAt.2 fun w ↦ ?_
    by_cases hw : w.1 ∈ tsupport (σ k)
    · exact ((σ k).continuous.comp continuous_fst).continuousAt.smul
        ((continuousOn_chartFiber f.hom k).continuousAt
          (((E.core.isOpen_baseSet k).preimage continuous_fst).mem_nhds (hσs k hw)))
    · refine (continuousAt_const (y := 0)).congr ?_
      filter_upwards [((isClosed_tsupport (σ k)).isOpen_compl.preimage continuous_fst).mem_nhds hw]
        with v hv
      rw [image_eq_zero_of_notMem_tsupport (f := σ k) hv]
      exact (zero_smul ℝ (chartFiber f.hom k v)).symm
  let ψ : C(X × Circle, t → (Fin (Q E).rank → ℂ) →L[ℂ] (Fin (Q E).rank → ℂ)) :=
    ⟨fun w k ↦ σ k w.1 • chartFiber f.hom k w, continuous_pi hψ⟩
  obtain ⟨N, c, hc⟩ := ContinuousMap.exists_norm_sub_laurent_lt ψ hε
  have hck (w : X × Circle) (k : t) : ‖σ k w.1 • chartFiber f.hom k w -
      ∑ i ∈ Icc (-(N : ℤ)) N, (w.2 : ℂ) ^ i • c i w.1 k‖ < ε := by
    have := (norm_le_pi_norm _ k).trans_lt (hc w)
    simpa [ψ, Finset.sum_apply] using this
  -- The Laurent coefficients, patched from the charts.
  let a : ℤ → (E ⟶ E) := fun i ↦ ∑ k : t,
    (VectorBundleCore.CoordinateHom.ofChart (k : X) (k : X) (fun x ↦ ρ k x • c i x k)
      ((ρ k).continuous.smul ((continuous_apply k).comp (c i).continuous))
      ((tsupport_smul_subset_left _ _).trans fun x hx ↦ ⟨hρs k hx, hρs k hx⟩) : E ⟶ E)
  refine ⟨N, a, fun w ↦ ?_⟩
  -- A chart of the cover at the base point of `w`, in which the estimate is made.
  obtain ⟨j, hj⟩ : ∃ j : t, ρ j w.1 ≠ 0 := by
    by_contra! h
    have := hρ1 w.1
    simp [h] at this
  have hxj : w.1 ∈ tsupport (ρ j) := subset_tsupport _ hj
  have hwj : w ∈ (Q E).core.baseSet (j, 1) := hρs j hxj
  have hww : w ∈ (Q E).core.baseSet w := (Q E).mem_baseSet_self w
  set T := (Q E).core.coordChange with hT
  have hTT {i k : X × Circle} (hi : w ∈ (Q E).core.baseSet i) (hk : w ∈ (Q E).core.baseSet k) :
      T i k w * T k i w = 1 :=
    (ContinuousLinearMap.mul_def _ _).trans
      (((Q E).core.coordChange_comp_coordChange_eq_id hk hi).trans
        ContinuousLinearMap.one_def.symm)
  have hTc {i k l : X × Circle} (hi : w ∈ (Q E).core.baseSet i)
      (hk : w ∈ (Q E).core.baseSet k) (hl : w ∈ (Q E).core.baseSet l) :
      T k l w * T i k w = T i l w :=
    (ContinuousLinearMap.mul_def _ _).trans
      ((Q E).core.coordChange_linear_comp i k l w ⟨⟨hi, hk⟩, hl⟩)
  let U : ((Fin (Q E).rank → ℂ) →L[ℂ] (Fin (Q E).rank → ℂ))ˣ :=
    ⟨T (j, 1) w w, T w (j, 1) w, hTT hwj hww, hTT hww hwj⟩
  refine ⟨U, ?_⟩
  have hinv : f.inv.fiberMap w * f.hom.fiberMap w = 1 := by
    rw [ContinuousLinearMap.mul_def, ← fiberMap_comp, f.hom_inv_id, fiberMap_id,
      ContinuousLinearMap.one_def]
  rw [← ContinuousLinearMap.mul_def, conj_mul_sub_one U.mul_inv U.inv_mul hinv]
  have hU : (↑U : (Fin (Q E).rank → ℂ) →L[ℂ] (Fin (Q E).rank → ℂ)) = T (j, 1) w w := rfl
  have hU' : (↑U⁻¹ : (Fin (Q E).rank → ℂ) →L[ℂ] (Fin (Q E).rank → ℂ)) = T w (j, 1) w := rfl
  rw [hU, hU']
  -- The Laurent family, at `w`, is the sum over the charts of its local pieces.
  set L : t → (Fin (Q E).rank → ℂ) →L[ℂ] (Fin (Q E).rank → ℂ) :=
    fun k ↦ ∑ i ∈ Icc (-(N : ℤ)) N, (w.2 : ℂ) ^ i • c i w.1 k with hL
  have hb0 : (laurentHom N a).fiberMap w =
      ∑ k : t, ρ k w.1 • (T (k, 1) w w * (L k * T w (k, 1) w)) := by
    ext v
    simp only [fiberMap_laurentHom, a, fiberMap_sum, fiberMap_ofChart, hL, hT,
      coordChange_pullback, FunLike.coe_sum, FunLike.coe_smul,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_def, map_sum, map_smul,
      Finset.sum_apply, Pi.smul_apply]
    simp only [ContinuousMap.fst_apply, ContinuousLinearMap.map_smul_of_tower, Finset.smul_sum,
      Pi.smul_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
    exact smul_comm _ _ _
  have hwk {k : t} (hk : ρ k w.1 ≠ 0) : w ∈ (Q E).core.baseSet (k, 1) :=
    hρs k (subset_tsupport _ hk)
  -- In the chart `j`, the Laurent family and `f` are sums of their pieces in the charts `k`.
  have hb : T w (j, 1) w * (laurentHom N a).fiberMap w * T (j, 1) w w =
      ∑ k : t, ρ k w.1 • (T (k, 1) (j, 1) w * (L k * T (j, 1) (k, 1) w)) := by
    rw [hb0, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    by_cases hk : ρ k w.1 = 0
    · simp [hk]
    rw [mul_smul_comm, smul_mul_assoc]
    congr 1
    calc T w (j, 1) w * (T (k, 1) w w * (L k * T w (k, 1) w)) * T (j, 1) w w
        = (T w (j, 1) w * T (k, 1) w w) * (L k * (T w (k, 1) w * T (j, 1) w w)) := by
          simp only [mul_assoc]
      _ = _ := by rw [hTc (hwk hk) hww hwj, hTc hwj hww (hwk hk)]
  have hf : T w (j, 1) w * f.hom.fiberMap w * T (j, 1) w w =
      ∑ k : t, ρ k w.1 • (T (k, 1) (j, 1) w *
        ((σ k w.1 • chartFiber f.hom k w) * T (j, 1) (k, 1) w)) := by
    rw [← one_smul ℝ (T w (j, 1) w * f.hom.fiberMap w * T (j, 1) w w), ← hρ1 w.1,
      Finset.sum_smul]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    by_cases hk : ρ k w.1 = 0
    · simp [hk]
    congr 1
    rw [hσ1 k w.1 (subset_tsupport _ hk), one_smul, chartFiber]
    calc T w (j, 1) w * f.hom.fiberMap w * T (j, 1) w w
        = (T (k, 1) (j, 1) w * T w (k, 1) w) * (f.hom.fiberMap w *
            (T (k, 1) w w * T (j, 1) (k, 1) w)) := by
          rw [hTc hww (hwk hk) hwj, hTc hwj (hwk hk) hww, mul_assoc]
      _ = _ := by simp only [mul_assoc, hT]
  have hdiff : ‖T w (j, 1) w * (laurentHom N a).fiberMap w * T (j, 1) w w -
      T w (j, 1) w * f.hom.fiberMap w * T (j, 1) w w‖ ≤ C₁ ^ 2 * ε := by
    rw [hb, hf, ← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ k : t, ‖ρ k w.1 • (T (k, 1) (j, 1) w * (L k * T (j, 1) (k, 1) w)) -
          ρ k w.1 • (T (k, 1) (j, 1) w *
            ((σ k w.1 • chartFiber f.hom k w) * T (j, 1) (k, 1) w))‖
        ≤ ∑ k : t, ρ k w.1 * (C₁ ^ 2 * ε) := Finset.sum_le_sum fun k _ ↦ ?_
      _ = C₁ ^ 2 * ε := by rw [← Finset.sum_mul, hρ1, one_mul]
    rw [← smul_sub, norm_smul, Real.norm_of_nonneg (hρ0 k w.1)]
    by_cases hk : ρ k w.1 = 0
    · simp [hk]
    refine mul_le_mul_of_nonneg_left ?_ (hρ0 k w.1)
    have hxk : w.1 ∈ tsupport (ρ k) := subset_tsupport _ hk
    rw [← mul_sub, ← sub_mul]
    calc ‖T (k, 1) (j, 1) w * ((L k - σ k w.1 • chartFiber f.hom k w) * T (j, 1) (k, 1) w)‖
        ≤ ‖T (k, 1) (j, 1) w‖ * (‖L k - σ k w.1 • chartFiber f.hom k w‖ *
            ‖T (j, 1) (k, 1) w‖) :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ C₁ * (ε * C₁) :=
          mul_le_mul (hC₁b j k w hxj hxk)
            (mul_le_mul (by rw [norm_sub_rev]; exact (hck w k).le) (hC₁b k j w hxk hxj)
              (norm_nonneg _) hε.le) (by positivity) hC₁.le
      _ = C₁ ^ 2 * ε := by ring
  have hfinv : T w (j, 1) w * f.inv.fiberMap w * T (j, 1) w w = chartFiber f.inv j w := by
    rw [chartFiber, mul_assoc]
  have hlt : C₂ * (C₁ ^ 2 * ε) < 1 := by
    have : C₂ * (C₁ ^ 2 * ε) = 1 / 2 := by
      rw [hε_def]
      field_simp
    rw [this]
    norm_num
  calc _ ≤ _ := norm_mul_le _ _
    _ ≤ C₂ * (C₁ ^ 2 * ε) :=
        mul_le_mul (hfinv ▸ hC₂b j w hxj) hdiff (norm_nonneg _) hC₂.le
    _ < 1 := hlt

end TauCeti.FiniteRankBundleCore

end
