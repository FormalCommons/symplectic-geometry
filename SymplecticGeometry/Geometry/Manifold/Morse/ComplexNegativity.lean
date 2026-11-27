/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Topology
public import TauCeti.Geometry.Manifold.Morse.Hessian
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Basic
import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Seminorm
import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Chart

/-!
# Complex negativity of critical Hessians is an open condition

Let `J` be a smooth almost complex structure on a boundaryless finite-dimensional manifold `M`,
`K ⊆ M` compact, and `f : M → ℝ` smooth. Say that `f` is *complex negative* at a critical point
`x` if `Hess f(v, v) + Hess f(Jv, Jv) < 0` for every nonzero tangent vector `v` at `x`. If `f` is
complex negative at each of its critical points in `K`, then so is every `g` close enough to `f`
in the weak Whitney topology, at each of the critical points of `g` in `K`
(`TauCeti.SmoothAlmostComplexStructure.eventually_criticalHessian_add_neg`). By
`TauCeti.AlmostComplexStructure.complexFinrank_le_manifoldMorseIndex_of_criticalHessian_add_neg`
the Morse index at such a critical point is at least the complex dimension, so a small
perturbation, such as the one of `ContMDiffMap.exists_isMorseOn_hasCompactSupport_sub_compl`,
keeps this lower bound on `K`.

The condition is read in coordinates. In the extended chart at `a`, at a critical point, the
critical Hessian is the second derivative of the coordinate expression of `f`, composed with
the chart derivative, and that derivative carries `J` to `J.inChart a`. So the condition holds at
the point of `M` over `z` exactly when the triple formed by the first and second coordinate
derivatives of `f` at `z` and `J.inChart a z` lies in a set of triples `(D¹, D², A)` which is open:
either `D¹ ≠ 0`, or `D²(w, w) + D²(Aw, Aw) < 0` on the unit sphere, which is compact.

## Implementation notes

The proof follows the library's `TauCeti.exists_strongCkControl_criticalHessian_pos`, itself
modelled on Tau Ceti's `TauCeti.exists_strongCkControl_isManifoldStronglyPseudoconvexAt`: a cover
by compact sets in chart targets, here finite since `K` is compact, and on each of them a
tolerance from compactness keeping the coordinate jets in the open set. The tolerances give
compact chart `C²` balls, which are weak Whitney neighbourhoods
(`ContMDiffMap.ball_chartCkSeminorm_mem_nhds`).

## References

* [D. Auroux, *Asymptotically holomorphic families of symplectic submanifolds*][Auroux1997]
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §2, for the Hessian at a critical point.
* M. Hirsch, *Differential Topology*, Graduate Texts in Mathematics 33, Springer, 1976,
  Chapter 2, §1, for the weak topology.
-/

public section

open Set Filter Topology ContMDiffMap
open scoped Manifold ContDiff TauCeti.ManifoldWeakWhitney

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The triples `(D¹, D², A)` of a first and a second derivative of a real function on `E` and an
endomorphism of `E` such that either `D¹ ≠ 0` or `D²(w, w) + D²(Aw, Aw) < 0` for every `w ≠ 0`. -/
private def NegJets (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Set ((E [×1]→L[ℝ] ℝ) × (E [×2]→L[ℝ] ℝ) × (E →L[ℝ] E)) :=
  {p | p.1 ≠ 0 ∨ ∀ w : E, w ≠ 0 → p.2.1 ![w, w] + p.2.1 ![p.2.2 w, p.2.2 w] < 0}

private theorem isOpen_negJets [FiniteDimensional ℝ E] : IsOpen (NegJets E) := by
  let Q (p : (E [×1]→L[ℝ] ℝ) × (E [×2]→L[ℝ] ℝ) × (E →L[ℝ] E)) (w : E) : ℝ :=
    p.2.1 ![w, w] + p.2.1 ![p.2.2 w, p.2.2 w]
  have hvec : Continuous fun w : E ↦ (![w, w] : Fin 2 → E) :=
    continuous_pi fun i ↦ by fin_cases i <;> exact continuous_id
  have hQ : Continuous fun q : ((E [×1]→L[ℝ] ℝ) × (E [×2]→L[ℝ] ℝ) × (E →L[ℝ] E)) × E ↦
      Q q.1 q.2 := by
    have hA : Continuous fun q : ((E [×1]→L[ℝ] ℝ) × (E [×2]→L[ℝ] ℝ) × (E →L[ℝ] E)) × E ↦
        q.1.2.2 q.2 := by fun_prop
    exact (continuous_eval.comp ((continuous_fst.comp (continuous_snd.comp continuous_fst)).prodMk
      (hvec.comp continuous_snd))).add
      (continuous_eval.comp ((continuous_fst.comp (continuous_snd.comp continuous_fst)).prodMk
        (hvec.comp hA)))
  -- `Q p` is homogeneous of degree two, so it is enough to test it on the unit sphere.
  have hsmul (p : (E [×1]→L[ℝ] ℝ) × (E [×2]→L[ℝ] ℝ) × (E →L[ℝ] E)) (c : ℝ) (u : E) :
      Q p (c • u) = c ^ 2 * Q p u := by
    have h (y : E) : (![c • y, c • y] : Fin 2 → E) = fun i ↦ c • ![y, y] i := by
      ext i; fin_cases i <;> rfl
    simp only [Q, map_smul, h, ContinuousMultilinearMap.map_smul_univ, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_add]
  have hset : NegJets E = {p | p.1 ≠ 0} ∪ {p | ∀ w ∈ Metric.sphere (0 : E) 1, Q p w < 0} := by
    ext p
    refine or_congr Iff.rfl ⟨fun h w hw ↦ h w (ne_zero_of_mem_unit_sphere ⟨w, hw⟩), fun h w hw ↦ ?_⟩
    have hw' : 0 < ‖w‖ := norm_pos_iff.mpr hw
    have hu : ‖w‖⁻¹ • w ∈ Metric.sphere (0 : E) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hw'.ne']
    have key := hsmul p ‖w‖ (‖w‖⁻¹ • w)
    rw [smul_smul, mul_inv_cancel₀ hw'.ne', one_smul] at key
    -- `Q p w` is the left side of the condition defining `NegJets`.
    change Q p w < 0
    rw [key]
    exact mul_neg_of_pos_of_neg (by positivity) (h _ hu)
  rw [hset]
  refine (isOpen_compl_singleton.preimage continuous_fst).union (isOpen_iff_mem_nhds.mpr ?_)
  intro p hp
  exact (isCompact_sphere (0 : E) 1).eventually_forall_of_forall_eventually fun w hw ↦
    hQ.continuousAt.eventually (Iio_mem_nhds (hp w hw))

/-- The test of `NegJets` on the first two chart derivatives of `g` and on `J` read in the chart,
at a point `z` of a chart target, is complex negativity of `g` at the point of `M` over `z`, if
that point is critical. -/
private theorem mem_negJets_iff (J : SmoothAlmostComplexStructure I M) (g : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯)
    (a : M) (z : (extChartAt I a).target) {x : M} (hzx : (extChartAt I a).symm z = x) :
    (chartIteratedFDeriv g a 1 ENat.LEInfty.out z, chartIteratedFDeriv g a 2 ENat.LEInfty.out z,
        J.inChart a z) ∈ NegJets E ↔
      (x ∈ criticalPoints I g → ∀ v : TangentSpace I x, v ≠ 0 →
        criticalHessian I g x v v + criticalHessian I g x (J x v) (J x v) < 0) := by
  subst hzx
  set x := (extChartAt I a).symm z
  have hz : (z : E) ∈ (extChartAt I a).target := z.property
  have hxs : x ∈ (chartAt H a).source := by
    rw [← extChartAt_source (I := I)]; exact (extChartAt I a).map_target hz
  have hzx : (chartAt H a).extend I x = z := by
    rw [← extChartAt.eq_1]; exact (extChartAt I a).right_inv hz
  have hopen := isOpen_extChartAt_target (I := I) a
  have he : chartAt H a ∈ IsManifold.maximalAtlas I 2 M :=
    IsManifold.maximalAtlas_subset_of_le ENat.LEInfty.out (IsManifold.chart_mem_maximalAtlas a)
  have hcrit : x ∈ criticalPoints I g ↔ chartIteratedFDeriv g a 1 ENat.LEInfty.out z = 0 := by
    rw [mem_criticalPoints, mvfderiv_eq_zero_iff_fderiv_comp_extend_symm_eq_zero
      (IsManifold.maximalAtlas_subset_of_le (by norm_num) he) hxs, hzx,
      chartIteratedFDeriv_self_target_apply, iteratedFDerivWithin_of_isOpen 1 hopen hz,
      ← norm_eq_zero, ← norm_eq_zero (a := iteratedFDeriv _ _ _ _), norm_iteratedFDeriv_one,
      ← extChartAt.eq_1]
  have hD2 (w₁ w₂ : E) : chartIteratedFDeriv g a 2 ENat.LEInfty.out z ![w₁, w₂] =
      fderiv ℝ (fderiv ℝ (g ∘ (extChartAt I a).symm)) z w₁ w₂ := by
    rw [chartIteratedFDeriv_self_target_apply, iteratedFDerivWithin_of_isOpen 2 hopen hz,
      iteratedFDeriv_two_apply]
    simp
  have hhess : x ∈ criticalPoints I g →
      ((∀ v : TangentSpace I x, v ≠ 0 →
        criticalHessian I g x v v + criticalHessian I g x (J x v) (J x v) < 0) ↔
      ∀ w : E, w ≠ 0 → chartIteratedFDeriv g a 2 ENat.LEInfty.out z ![w, w] +
        chartIteratedFDeriv g a 2 ENat.LEInfty.out z ![J.inChart a z w, J.inChart a z w] < 0) :=
      fun hx ↦ by
    obtain ⟨T, hT⟩ :=
      isInvertible_mvfderiv_extend (IsManifold.maximalAtlas_subset_of_le (by norm_num) he) hxs
    have hHess (v w : TangentSpace I x) :
        criticalHessian I g x v w = chartIteratedFDeriv g a 2 ENat.LEInfty.out z ![T v, T w] := by
      rw [criticalHessian_apply_eq_of_mem_maximalAtlas he hxs
        ((g.contMDiff.of_le ENat.LEInfty.out).contMDiffAt) (mem_criticalPoints.mp hx), hzx, hD2,
        ← hT]
      -- The two sides differ only by the coercion of `T` to a continuous linear map.
      rfl
    have hJT (v : TangentSpace I x) : T (J x v) = J.inChart a z (T v) := by
      have hT' (u : TangentSpace I x) : T u = mfderiv I 𝓘(ℝ, E) (extChartAt I a) x u := by
        rw [← extChartAt.eq_1] at hT
        rw [← ContinuousLinearEquiv.coe_coe, hT]
        -- `mvfderiv` is `mfderiv` followed by the identification of the tangent space of `E`.
        rfl
      rw [hT', hT']
      refine Eq.symm ((J.inChart_apply_eq_mfderiv a hz _).trans ?_)
      congr 2
      exact congr($(mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt hz) v)
    simp only [hHess, hJT]
    refine ⟨fun h w hw ↦ ?_, fun h v hv ↦ h (T v) (by simpa using hv)⟩
    simpa using h (T.symm w) (by simpa using hw)
  simp only [NegJets, mem_ofPred_eq, ne_eq, hcrit]
  by_cases h0 : chartIteratedFDeriv g a 1 ENat.LEInfty.out z = 0
  · simp only [h0, not_true_eq_false, false_or, true_implies]
    exact (hhess (hcrit.mpr h0)).symm
  · exact iff_of_true (Or.inl h0) fun h ↦ absurd h h0

variable [FiniteDimensional ℝ E] [T2Space M]

/-- Let `J` be a smooth almost complex structure on a Hausdorff boundaryless manifold with a
finite-dimensional model, `K` a compact set, and `f` a smooth function such that at every critical
point `x ∈ K` of `f`, `Hess f(v, v) + Hess f(Jv, Jv) < 0` for every nonzero tangent vector `v`
at `x`. Then every `g` close enough to `f` in the weak Whitney topology has the same property at
each of its critical points in `K`. -/
theorem SmoothAlmostComplexStructure.eventually_criticalHessian_add_neg
    (J : SmoothAlmostComplexStructure I M) {K : Set M} (hK : IsCompact K)
    {f : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯}
    (hf : ∀ x ∈ K, x ∈ criticalPoints I f → ∀ v : TangentSpace I x, v ≠ 0 →
      criticalHessian I f x v v + criticalHessian I f x (J x v) (J x v) < 0) :
    ∀ᶠ g : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯ in 𝓝 f, ∀ x ∈ K, x ∈ criticalPoints I g →
      ∀ v : TangentSpace I x, v ≠ 0 →
        criticalHessian I g x v v + criticalHessian I g x (J x v) (J x v) < 0 := by
  have : LocallyCompactSpace H := I.locallyCompactSpace
  obtain ⟨N, -, a, u, b, hab, hKu⟩ := exists_finite_precompact_chart_cover_of_isOpen_cover
    (I := I) hK (V := fun _ : Unit ↦ univ) (fun _ ↦ isOpen_univ)
    fun _ _ ↦ mem_iUnion.mpr ⟨(), mem_univ _⟩
  -- The compact pieces of the chart targets, and the parts of them lying over `K`.
  let L (i : Fin N) : TopologicalSpace.Compacts (extChartAt I (a i)).target :=
    ⟨Subtype.val ⁻¹' b i, by
      rw [Subtype.isCompact_iff, Subtype.image_preimage_coe,
        inter_eq_right.mpr (hab i).2.2.2.2.2.1]
      exact (hab i).2.2.2.2.1⟩
  let S (i : Fin N) : Set (extChartAt I (a i)).target :=
    (L i : Set _) ∩ {z | (extChartAt I (a i)).symm z ∈ K}
  have hS (i : Fin N) : IsCompact (S i) :=
    (L i).isCompact.inter_right (hK.isClosed.preimage
      ((continuousOn_extChartAt_symm (a i)).domRestrict))
  let jet (g : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯) (i : Fin N) (z : (extChartAt I (a i)).target) :=
    (chartIteratedFDeriv g (a i) 1 ENat.LEInfty.out z,
      chartIteratedFDeriv g (a i) 2 ENat.LEInfty.out z,
      J.inChart (a i) z)
  have hjet (i : Fin N) : Continuous (jet f i) :=
    (chartIteratedFDeriv f (a i) 1 ENat.LEInfty.out).continuous.prodMk
      ((chartIteratedFDeriv f (a i) 2 ENat.LEInfty.out).continuous.prodMk
        (J.contDiffOn_inChart (a i)).continuousOn.domRestrict)
  have hmaps (i : Fin N) : MapsTo (jet f i) (S i) (NegJets E) :=
    fun z hz ↦ (mem_negJets_iff J f (a i) z rfl).mpr (hf _ hz.2)
  -- Compactness gives a tolerance on each piece keeping the jets in the open set.
  have htol (i : Fin N) : ∃ ε, 0 < ε ∧ Metric.thickening ε (jet f i '' S i) ⊆ NegJets E :=
    ((hS i).image (hjet i)).exists_thickening_subset_open isOpen_negJets
      (hmaps i).image_subset
  choose ε hε hsub using htol
  have hball : ⋂ i, (chartCkSeminorm (a i) (L i) 2 ENat.LEInfty.out).ball f (ε i) ∈ 𝓝 f :=
    iInter_mem.mpr fun i ↦ ball_chartCkSeminorm_mem_nhds _ _ _ _ _ (hε i)
  filter_upwards [hball] with g hg x hxK
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hKu hxK)
  have hxs : x ∈ (extChartAt I (a i)).source := (hab i).2.2.2.1 hi
  let z : (extChartAt I (a i)).target := ⟨extChartAt I (a i) x, (extChartAt I (a i)).map_source hxs⟩
  have hzx : (extChartAt I (a i)).symm z = x := (extChartAt I (a i)).left_inv hxs
  have hzS : z ∈ S i := ⟨(hab i).2.2.2.2.2.2.2 (mem_image_of_mem _ hi), by
    simpa only [mem_ofPred_eq, hzx] using hxK⟩
  have hgi := (mem_ball_chartCkSeminorm_iff _ _ _ _ f g (hε i)).mp (mem_iInter.mp hg i)
  refine (mem_negJets_iff J g (a i) z hzx).mp (hsub i (Metric.mem_thickening_iff.mpr
    ⟨jet f i z, mem_image_of_mem _ hzS, ?_⟩))
  rw [Prod.dist_eq, Prod.dist_eq, dist_self, max_lt_iff, max_lt_iff, dist_eq_norm, dist_eq_norm]
  exact ⟨hgi 1 (by norm_num) z hzS.1, hgi 2 le_rfl z hzS.1, hε i⟩

end TauCeti

end
