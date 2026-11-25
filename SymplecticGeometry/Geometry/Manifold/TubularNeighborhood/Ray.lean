/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Immersion.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Diffeomorph
public import TauCeti.Geometry.Manifold.TubularNeighborhood.Existence
public import TauCeti.Geometry.Manifold.VectorBundle.Scalar
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Real
public import TauCeti.Geometry.Manifold.ContMDiffMap.Radius

/-!
# Tubes around proper rays

Let `γ : ℝ → M` be a smooth embedding into a manifold of dimension `finrank ℝ V + 1` that tends
to infinity as `t → ∞`. Then `γ` extends to a smooth embedding `Φ : ℝ × V → M` with open image
inside any prescribed open neighbourhood of `range γ`, with `Φ (t, 0) = γ t`, such that the part
`Φ '' (Ici (-2) ×ˢ closedBall 0 2)` of the tube over `[-2, ∞)` is closed and lies in any
prescribed open neighbourhood of `γ '' Ici (-2)` (`TauCeti.SmoothEmbedding.exists_rayTube`).

The proof composes three maps. Tau Ceti's tubular neighbourhood theorem
`TauCeti.SmoothEmbedding.exists_diffeomorph_normalBundle_subset` identifies the total space of
the normal bundle of `γ` with an open neighbourhood of `range γ`. Since the base is `ℝ`, the
normal bundle is trivial (`Bundle.exists_diffeomorph_prod_of_real`), which turns this into a
diffeomorphism `Ψ` from `ℝ × V` onto that neighbourhood. Finally the fibres are shrunk by a
smooth positive function `r` of the base point (`vectorBundleScalarDiffeomorph`). The function `r`
comes from `Continuous.exists_contDiff_pos_isClosed_image_subset`: for a continuous map
`Ψ : ℝ × V → M` whose restriction to `ℝ × {0}` is proper towards `+∞`, the image of
`{(t, y) | a ≤ t, ‖y‖ ≤ r t}` is closed and inside a given open neighbourhood of
`Ψ '' (Ici a ×ˢ {0})` once `r` decreases fast enough. Such an `r` is a smooth radius of
balls inside a neighbourhood of `ℝ × {0}`, which Tau Ceti's
`TauCeti.exists_contMDiffMap_closedBall_subset` provides.

## Main results

* `Continuous.exists_contDiff_pos_isClosed_image_subset`: shrinking the fibres of a map
  `ℝ × V → M` along a proper ray makes the image of the half tube closed and small.
* `TauCeti.SmoothEmbedding.exists_rayTube`: a tube around a proper ray.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Theorem 7.3.1.
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963.
-/

public section

open Bundle Filter Manifold Set Topology
open scoped ContDiff Manifold

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {M : Type*} [TopologicalSpace M] [T2Space M]

/-- Let `Ψ : ℝ × V → M` be continuous, with `Ψ (t, 0)` tending to infinity as `t → ∞`, and let
`O'` be an open set containing `Ψ (t, 0)` for all `t ≥ a`. Then there is a smooth positive
function `r : ℝ → ℝ` such that the image under `Ψ` of `{(t, y) | a ≤ t ∧ ‖y‖ ≤ r t}` is closed
and contained in `O'`. -/
theorem Continuous.exists_contDiff_pos_isClosed_image_subset [WeaklyLocallyCompactSpace M]
    [SigmaCompactSpace M] {Ψ : ℝ × V → M} (hΨ : Continuous Ψ)
    (hγ : Tendsto (fun t ↦ Ψ (t, 0)) atTop (cocompact M)) {a : ℝ} {O' : Set M}
    (hO' : IsOpen O') (hγO' : ∀ t, a ≤ t → Ψ (t, 0) ∈ O') :
    ∃ r : ℝ → ℝ, ContDiff ℝ ∞ r ∧ (∀ t, 0 < r t) ∧
      IsClosed (Ψ '' {p | a ≤ p.1 ∧ ‖p.2‖ ≤ r p.1}) ∧
      Ψ '' {p | a ≤ p.1 ∧ ‖p.2‖ ≤ r p.1} ⊆ O' := by
  let K := CompactExhaustion.choice M
  -- `Ψ (t, 0)` lies outside `K n` for `t ≥ T n`.
  have hT (n : ℕ) : ∃ T : ℝ, ∀ t, T ≤ t → Ψ (t, 0) ∉ K n :=
    eventually_atTop.1 (hγ (K.isCompact n).compl_mem_cocompact)
  choose T hT using hT
  -- The points `p` over which the image stays in `O'` if `a ≤ p.1`, and outside `K n` whenever
  -- `T n ≤ p.1`.
  let U : Set (ℝ × V) := {p | (a ≤ p.1 → Ψ p ∈ O') ∧ ∀ n, T n ≤ p.1 → Ψ p ∉ K n}
  -- A condition `b ≤ p.1 → Ψ p ∈ W` that holds at `(s₀, 0)` holds near `(s₀, 0)`: if
  -- `b ≤ s₀` by continuity, and otherwise because its premise fails nearby.
  have hev {W : Set M} (hW : IsOpen W) {b s₀ : ℝ} (h : b ≤ s₀ → Ψ (s₀, 0) ∈ W) :
      ∀ᶠ p in 𝓝 (s₀, (0 : V)), b ≤ p.1 → Ψ p ∈ W := by
    by_cases hb : b ≤ s₀
    · filter_upwards [(hW.preimage hΨ).mem_nhds (h hb)] with p hp _ using hp
    · filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds (Iio_mem_nhds (not_le.1 hb))]
        with p hp hbp using absurd (hbp.trans_lt hp) (lt_irrefl b)
  have hU (s₀ : ℝ) : U ∈ 𝓝 (s₀, (0 : V)) := by
    obtain ⟨m, hm⟩ := K.exists_superset_of_isCompact
      ((isCompact_Icc (a := s₀ - 1) (b := s₀ + 1)).image (hΨ.comp (Continuous.prodMk_left 0)))
    have hbig : ∀ᶠ p in 𝓝 (s₀, (0 : V)), ∀ n, m ≤ n → T n ≤ p.1 → Ψ p ∉ K n := by
      filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds
        (Ioo_mem_nhds (show s₀ - 1 < s₀ by linarith) (show s₀ < s₀ + 1 by linarith))]
        with p hp n hn hTn _
      exact hT n p.1 hTn (K.subset hn (hm ⟨p.1, Ioo_subset_Icc_self hp, rfl⟩))
    have hsmall : ∀ᶠ p in 𝓝 (s₀, (0 : V)), ∀ n ∈ Iio m, T n ≤ p.1 → Ψ p ∉ K n :=
      (eventually_all_finite (finite_Iio m)).2 fun n _ ↦
        hev (K.isCompact n).isClosed.isOpen_compl (hT n s₀)
    filter_upwards [hev hO' (hγO' s₀), hbig, hsmall] with p hpO hpm hpn
    exact ⟨hpO, fun n ↦ (lt_or_ge n m).elim (hpn n) (hpm n)⟩
  obtain ⟨r, hr0, hr1, hr⟩ := TauCeti.exists_contMDiffMap_closedBall_subset (I := 𝓘(ℝ))
    (v₀ := (0 : V)) hU lowerSemicontinuous_const fun _ ↦ one_pos
  let A : Set (ℝ × V) := {p | a ≤ p.1 ∧ ‖p.2‖ ≤ r p.1}
  have hrc : Continuous r := r.contMDiff.continuous
  have hrU {p : ℝ × V} (hp : p ∈ A) : p ∈ U := hr p.1 p.2 (mem_closedBall_zero_iff.2 hp.2)
  refine ⟨r, contMDiff_iff_contDiff.1 r.contMDiff, hr0, ?_,
    image_subset_iff.2 fun p hp ↦ (hrU hp).1 hp.1⟩
  refine closure_subset_iff_isClosed.1 fun x hx ↦ ?_
  obtain ⟨n, hn⟩ := K.exists_mem_nhds x
  -- Near `x`, the image of `A` is the image of a compact part of `A`.
  let B : Set (ℝ × V) := A ∩ Icc a (T n) ×ˢ Metric.closedBall 0 1
  have hA : IsClosed A :=
    (isClosed_le continuous_const continuous_fst).inter
      (isClosed_le continuous_snd.norm (hrc.comp continuous_fst))
  have hB : IsCompact (Ψ '' B) :=
    ((isCompact_Icc.prod (isCompact_closedBall 0 1)).of_isClosed_subset
      (hA.inter (isClosed_Icc.prod Metric.isClosed_closedBall)) inter_subset_right).image hΨ
  have hAK : Ψ '' A ∩ K n ⊆ Ψ '' B := by
    rintro _ ⟨⟨p, hp, rfl⟩, hpK⟩
    refine ⟨p, ⟨hp, ⟨hp.1, ?_⟩, ?_⟩, rfl⟩
    · by_contra h
      exact (hrU hp).2 n (not_le.1 h).le hpK
    · exact mem_closedBall_zero_iff.2 (hp.2.trans (hr1 p.1).le)
  refine image_mono inter_subset_left (hB.isClosed.closure_subset ?_)
  refine mem_closure_iff_nhds.2 fun U hU ↦ ?_
  obtain ⟨z, hzU, hz⟩ := mem_closure_iff_nhds.1 hx (U ∩ K n) (inter_mem hU hn)
  exact ⟨z, hzU.1, hAK ⟨hz, hzU.2⟩⟩

namespace TauCeti.SmoothEmbedding

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [ChartedSpace H M] [IsManifold I ∞ M] [SecondCountableTopology M]

/-- **Tubes around proper rays.** Let `γ : ℝ → M` be a smooth embedding into a boundaryless
manifold of dimension `finrank ℝ V + 1` with `γ t → ∞` as `t → ∞`, let `O` be an open
neighbourhood of `range γ` and `O'` an open neighbourhood of `γ '' Ici (-2)`. Then there is a
smooth embedding `Φ : ℝ × V → M` with open image inside `O`, equal to `γ` on `ℝ × {0}`, such that
`Φ '' (Ici (-2) ×ˢ closedBall 0 2)` is closed and contained in `O'`. -/
theorem exists_rayTube (γ : SmoothEmbedding 𝓘(ℝ) I ∞ ℝ M)
    (hV : Module.finrank ℝ V + 1 = Module.finrank ℝ E)
    (hγ : Tendsto γ atTop (cocompact M)) {O O' : Set M} (hO : IsOpen O) (hγO : range γ ⊆ O)
    (hO' : IsOpen O') (hγO' : γ '' Ici (-2) ⊆ O') :
    ∃ Φ : SmoothEmbedding (𝓘(ℝ).prod 𝓘(ℝ, V)) I ∞ (ℝ × V) M,
      IsOpen (range Φ) ∧ range Φ ⊆ O ∧ (∀ t, Φ (t, 0) = γ t) ∧
      IsClosed (Φ '' (Ici (-2) ×ˢ Metric.closedBall 0 2)) ∧
      Φ '' (Ici (-2) ×ˢ Metric.closedBall 0 2) ⊆ O' := by
  have hdim : Module.finrank ℝ V = Module.finrank ℝ E - Module.finrank ℝ ℝ := by
    rw [Module.finrank_self]; omega
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  let := γ.normalSpaceFiberBundle hn hdim
  let := γ.normalSpaceVectorBundle hn hdim
  have : IsManifold 𝓘(ℝ) ((∞ : ℕ∞ω) + 1) ℝ := IsManifold.of_le (n := ∞) (by simp)
  have : IsManifold I ((∞ : ℕ∞ω) + 1) M := IsManifold.of_le (n := ∞) (by simp)
  have := γ.normalSpaceContMDiffVectorBundle (m := ∞) hn (by simp) hdim
  obtain ⟨W, hWO, Φ₀, hΦ₀⟩ := γ.exists_diffeomorph_normalBundle_subset hdim hO hγO
  obtain ⟨h, L, hL⟩ :=
    Bundle.exists_diffeomorph_prod_of_real (F := V) (T := fun x ↦ γ.NormalSpace x hn)
  -- `h` covers the identity of `ℝ` and is linear on the fibres.
  have hh_symm (q : ℝ × V) : h.symm q = ⟨q.1, (L q.1).symm q.2⟩ := by
    conv_rhs => rw [← h.symm_apply_apply ⟨q.1, (L q.1).symm q.2⟩, hL,
      ContinuousLinearEquiv.apply_symm_apply]
  let Ψ : ℝ × V → M := fun q ↦ Φ₀ (h.symm q)
  have hΨ : Continuous Ψ := continuous_subtypeVal.comp (Φ₀.continuous.comp h.symm.continuous)
  have hΨ0 (t : ℝ) : Ψ (t, 0) = γ t := by
    simp only [Ψ, hh_symm, map_zero]
    exact hΦ₀ t
  obtain ⟨r, hr, hr0, hclosed, hsub⟩ := hΨ.exists_contDiff_pos_isClosed_image_subset
    (by simpa only [hΨ0] using hγ) hO' (a := -2) fun t ht ↦ hΨ0 t ▸ hγO' ⟨t, ht, rfl⟩
  have hr2 : ContMDiff 𝓘(ℝ) 𝓘(ℝ, ℝ) ∞ fun t ↦ r t / 2 :=
    contMDiff_iff_contDiff.2 (hr.div_const 2)
  let S := vectorBundleScalarDiffeomorph (F := V) (V := fun x ↦ γ.NormalSpace x hn)
    (fun t ↦ r t / 2) hr2 fun t ↦ (half_pos (hr0 t)).ne'
  let e := h.symm.trans (S.trans Φ₀)
  have he (q : ℝ × V) : (e q : M) = Ψ (q.1, (r q.1 / 2) • q.2) := by
    simp only [e, Ψ, Diffeomorph.coe_trans, Function.comp_apply, hh_symm, S,
      vectorBundleScalarDiffeomorph_apply, map_smul]
  have hemb : IsSmoothEmbedding (𝓘(ℝ).prod 𝓘(ℝ, V)) I ∞ (Subtype.val ∘ e) :=
    isSmoothEmbedding_subtypeVal_comp_iff.2 (e.isSmoothEmbedding_comp (by simp) .id)
  let Φ := SmoothEmbedding.ofIsSmoothEmbedding _ hemb
  have hΦ (q : ℝ × V) : Φ q = Ψ (q.1, (r q.1 / 2) • q.2) :=
    (SmoothEmbedding.ofIsSmoothEmbedding_apply _ hemb q).trans (he q)
  have hrange : range Φ = W := by
    have : range e = univ := range_eq_univ.2 e.surjective
    rw [SmoothEmbedding.coe_ofIsSmoothEmbedding, range_comp, this, image_univ, Subtype.range_coe]
  have himage : Φ '' (Ici (-2) ×ˢ Metric.closedBall 0 2) =
      Ψ '' {p | -2 ≤ p.1 ∧ ‖p.2‖ ≤ r p.1} := by
    ext x
    simp only [mem_image, mem_prod, mem_Ici, mem_closedBall_zero_iff, mem_ofPred_eq, hΦ]
    constructor
    · rintro ⟨q, ⟨hq1, hq2⟩, rfl⟩
      refine ⟨(q.1, (r q.1 / 2) • q.2), ⟨hq1, ?_⟩, rfl⟩
      rw [norm_smul, Real.norm_of_nonneg (half_pos (hr0 q.1)).le]
      nlinarith [hr0 q.1]
    · rintro ⟨p, ⟨hp1, hp2⟩, rfl⟩
      have hrp := hr0 p.1
      refine ⟨(p.1, (r p.1 / 2)⁻¹ • p.2), ⟨hp1, ?_⟩, ?_⟩
      · rw [norm_smul, Real.norm_of_nonneg (inv_pos.2 (half_pos hrp)).le, inv_div,
          div_mul_eq_mul_div, div_le_iff₀ hrp]
        linarith
      · rw [smul_smul, mul_inv_cancel₀ (half_pos hrp).ne', one_smul]
  refine ⟨Φ, hrange ▸ W.isOpen, hrange ▸ hWO, fun t ↦ ?_, himage ▸ hclosed, himage ▸ hsub⟩
  rw [hΦ, smul_zero, hΨ0]

end TauCeti.SmoothEmbedding
