/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Topology
public import TauCeti.Geometry.Manifold.Morse.Hessian
public import TauCeti.Geometry.Manifold.Morse.Index
public import TauCeti.Geometry.Symplectic.Finrank
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Basic
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Restriction
import SymplecticGeometry.Geometry.Manifold.ContMDiffMap.Chart.Jet
import SymplecticGeometry.Geometry.Manifold.Morse.ComplexIndex
import SymplecticGeometry.Geometry.Manifold.Morse.CriticalPoints
import SymplecticGeometry.Geometry.Manifold.Morse.Generic.Sublevel
import SymplecticGeometry.Topology.Compactness.Compact
import TauCeti.Geometry.Manifold.Morse.Generic.Relative
import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Chart

/-!
# Complex negativity of critical Hessians: openness and pull-back

Let `J` be a smooth almost complex structure on a boundaryless finite-dimensional manifold `M`,
`K ⊆ M` compact, and `f : M → ℝ` smooth. Say that `f` is *complex negative* at `x`
(`TauCeti.SmoothAlmostComplexStructure.IsComplexNegativeAt`) if
`Hess f(v, v) + Hess f(Jv, Jv) < 0` for every nonzero tangent vector `v` at `x`. If `f` is
complex negative at each of its critical points in `K`, then so is every `g` close enough to `f`
in the weak Whitney topology, at each of the critical points of `g` in `K`
(`TauCeti.SmoothAlmostComplexStructure.eventually_isComplexNegativeAt`). By
`TauCeti.AlmostComplexStructure.complexFinrank_le_manifoldMorseIndex_of_criticalHessian_add_neg`
the Morse index at such a critical point is at least the complex dimension
(`TauCeti.SmoothAlmostComplexStructure.IsComplexNegativeAt.complexFinrank_le_manifoldMorseIndex`),
that is half the real dimension
(`TauCeti.SmoothAlmostComplexStructure.IsComplexNegativeAt.finrank_div_two_le_manifoldMorseIndex`),
so a small perturbation, such as the one of
`ContMDiffMap.exists_isMorseOn_hasCompactSupport_sub_compl`,
keeps this lower bound on `K`. Thus `f` can be made Morse on `K` by a compactly supported change
that vanishes near a closed set `C` on which it is already Morse, keeping complex negativity
(`TauCeti.SmoothAlmostComplexStructure.exists_isMorseOn_isComplexNegativeAt`), and hence with
Morse index at least half the real dimension at each critical point in `K`
(`TauCeti.SmoothAlmostComplexStructure.exists_isMorseOn_finrank_div_two_le_manifoldMorseIndex`).

If moreover `f⁻¹[c, ∞)` is compact and all critical values of `f` exceed `c`, the library's
`ContMDiffMap.exists_isMorse_eqOn_preimage_Iic` gives, in any weak Whitney neighbourhood, a Morse
function that agrees with `f` on `{f ≤ c}`, has `c` as a regular value, a compact superlevel set
above `c` and a regular value above it, and all of whose critical points lie in `f⁻¹[c, ∞)`.
Taking it inside the neighbourhood of
`TauCeti.SmoothAlmostComplexStructure.eventually_criticalHessian_add_neg` for that compact set
adds the bound on the Morse index at every critical point
(`TauCeti.SmoothAlmostComplexStructure.exists_isMorse_eqOn_preimage_Iic`).

The condition is read in coordinates. In the extended chart at `a`, at a critical point, the
critical Hessian is the second derivative of the coordinate expression of `f`, composed with
the chart derivative, and that derivative carries `J` to `J.inChart a`. So the condition holds at
the point of `M` over `z` exactly when the triple formed by the first and second coordinate
derivatives of `f` at `z` and `J.inChart a z` lies in a set of triples `(D¹, D², A)` which is open:
either `D¹ ≠ 0`, or `D²(w, w) + D²(Aw, Aw) < 0` on the unit sphere, which is compact.

Complex negativity also pulls back: if `φ : M' → M` is `C²` and pseudoholomorphic at `y` for
`J'` and `J`, with injective derivative there, and `f` is complex negative at the critical point
`φ y`, then `f ∘ φ` is complex negative at `y` for `J'`
(`TauCeti.IsPseudoholomorphicAt.isComplexNegativeAt_comp`). By the second-order chain rule
at a critical point, Tau Ceti's `TauCeti.criticalHessian_comp_apply`, the critical Hessian of
`f ∘ φ` is that of `f` on the images under `dφ`, and `dφ` carries `J'` to `J`. The inclusion of
an open submanifold `U` is such a map for `J.restrictOpen U`
(`TauCeti.SmoothAlmostComplexStructure.IsComplexNegativeAt.comp_subtypeVal`).

## Implementation notes

The proof follows the library's `TauCeti.exists_strongCkControl_criticalHessian_pos`, itself
modelled on Tau Ceti's `TauCeti.exists_strongCkControl_isManifoldStronglyPseudoconvexAt`, in
using a cover by compact sets in chart targets, here finite since `K` is compact. In the weak
Whitney topology no explicit tolerance is needed: the coordinate jets vary continuously with the
function (`ContMDiffMap.continuous_chartIteratedFDeriv`), so on each piece the condition that
they lie in the open set is open in the compact-open topology.

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

namespace SmoothAlmostComplexStructure

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {J : SmoothAlmostComplexStructure I M} {f : M → ℝ} {x : M}

/-- A function `f : M → ℝ` is *complex negative* at `x` for the smooth almost complex structure
`J` if its critical Hessian satisfies `Hess f(v, v) + Hess f(Jv, Jv) < 0` for every nonzero
tangent vector `v` at `x`. The predicate does not ask that `x` be a critical point of `f`: the
results that need this assume it separately. -/
def IsComplexNegativeAt (J : SmoothAlmostComplexStructure I M) (f : M → ℝ) (x : M) : Prop :=
  ∀ v : TangentSpace I x, v ≠ 0 →
    criticalHessian I f x v v + criticalHessian I f x (J x v) (J x v) < 0

theorem isComplexNegativeAt_def :
    J.IsComplexNegativeAt f x ↔ ∀ v : TangentSpace I x, v ≠ 0 →
      criticalHessian I f x v v + criticalHessian I f x (J x v) (J x v) < 0 :=
  Iff.rfl

/-- If `f` is complex negative at `x` for `J`, then the Morse index of `f` at `x` is at least the
complex dimension of the model space for the linear almost complex structure that `J` induces
on it at `x`. -/
theorem IsComplexNegativeAt.complexFinrank_le_manifoldMorseIndex
    (h : J.IsComplexNegativeAt f x) :
    (J.almostComplexStructureAt x).complexFinrank ≤ manifoldMorseIndex I f x :=
  AlmostComplexStructure.complexFinrank_le_manifoldMorseIndex_of_criticalHessian_add_neg
    (J.almostComplexStructureAt x) (I := I) f x fun v hv ↦ by
      rw [almostComplexStructureAt_toLinearMap]
      exact isComplexNegativeAt_def.1 h v hv

/-- If `f` is complex negative at `x` for a smooth almost complex structure `J`, then the Morse
index of `f` at `x` is at least half the dimension of the model space. -/
theorem IsComplexNegativeAt.finrank_div_two_le_manifoldMorseIndex
    (h : J.IsComplexNegativeAt f x) :
    Module.finrank ℝ E / 2 ≤ manifoldMorseIndex I f x := by
  have hE : Module.finrank ℝ E = 2 * (J.almostComplexStructureAt x).complexFinrank :=
    (J.almostComplexStructureAt x).finrank_real_eq_two_mul_complexFinrank
  rw [hE, Nat.mul_div_cancel_left _ two_pos]
  exact h.complexFinrank_le_manifoldMorseIndex

end SmoothAlmostComplexStructure

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
  exact (isOpen_compl_singleton.preimage continuous_fst).union
    ((isCompact_sphere (0 : E) 1).isOpen_setOfPred_forall_prodMk_mem
      (isOpen_lt hQ continuous_const))

/-- The test of `NegJets` on the first two chart derivatives of `g` and on `J` read in the chart,
at a point `z` of a chart target, is complex negativity of `g` at the point of `M` over `z`, if
that point is critical. -/
private theorem mem_negJets_iff (J : SmoothAlmostComplexStructure I M) (g : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯)
    (a : M) (z : (extChartAt I a).target) {x : M} (hzx : (extChartAt I a).symm z = x) :
    (chartIteratedFDeriv g a 1 ENat.LEInfty.out z, chartIteratedFDeriv g a 2 ENat.LEInfty.out z,
        J.inChart a z) ∈ NegJets E ↔
      (x ∈ criticalPoints I g → J.IsComplexNegativeAt g x) := by
  subst hzx
  set x := (extChartAt I a).symm z
  have hz : (z : E) ∈ (extChartAt I a).target := z.property
  have hxs : x ∈ (chartAt H a).source := extChartAt_symm_mem_chart_source hz
  have hzx : (chartAt H a).extend I x = z := by
    rw [← extChartAt.eq_1]; exact (extChartAt I a).right_inv hz
  have he : chartAt H a ∈ IsManifold.maximalAtlas I 2 M :=
    IsManifold.maximalAtlas_subset_of_le ENat.LEInfty.out (IsManifold.chart_mem_maximalAtlas a)
  have hcrit := extChartAt_symm_mem_criticalPoints_iff ENat.LEInfty.out g a z
  have hhess : x ∈ criticalPoints I g →
      (J.IsComplexNegativeAt g x ↔
      ∀ w : E, w ≠ 0 → chartIteratedFDeriv g a 2 ENat.LEInfty.out z ![w, w] +
        chartIteratedFDeriv g a 2 ENat.LEInfty.out z ![J.inChart a z w, J.inChart a z w] < 0) :=
      fun hx ↦ by
    obtain ⟨T, hT⟩ :=
      isInvertible_mvfderiv_extend (IsManifold.maximalAtlas_subset_of_le (by norm_num) he) hxs
    have hHess (v w : TangentSpace I x) :
        criticalHessian I g x v w = chartIteratedFDeriv g a 2 ENat.LEInfty.out z ![T v, T w] := by
      rw [criticalHessian_apply_eq_of_mem_maximalAtlas he hxs
        ((g.contMDiff.of_le ENat.LEInfty.out).contMDiffAt) (mem_criticalPoints.mp hx), hzx,
        chartIteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, ← hT, ContinuousLinearEquiv.coe_coe, ← extChartAt.eq_1]
    have hJT (v : TangentSpace I x) : T (J x v) = J.inChart a z (T v) := by
      have hT' (u : TangentSpace I x) : T u = mfderiv I 𝓘(ℝ, E) (extChartAt I a) x u := by
        rw [← extChartAt.eq_1] at hT
        rw [← ContinuousLinearEquiv.coe_coe, hT]
        exact mvfderiv_apply_eq_mfderiv_apply _ _ _
      rw [hT', hT']
      refine Eq.symm ((J.inChart_apply_eq_mfderiv a hz _).trans ?_)
      congr 2
      exact congr($(mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt hz) v)
    simp only [SmoothAlmostComplexStructure.isComplexNegativeAt_def, hHess, hJT]
    refine ⟨fun h w hw ↦ ?_, fun h v hv ↦ h (T v) (by simpa using hv)⟩
    simpa using h (T.symm w) (by simpa using hw)
  simp only [NegJets, mem_ofPred_eq, ne_eq, ← imp_iff_not_or, ← hcrit]
  exact imp_congr_right fun hx ↦ (hhess hx).symm

section Pullback

variable {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless] [TopologicalSpace M'] [ChartedSpace H' M']
  [IsManifold I' ∞ M'] {J' : SmoothAlmostComplexStructure I' M'}
  {J : SmoothAlmostComplexStructure I M} {φ : M' → M} {y : M'} {f : M → ℝ}

/-- **Complex negativity pulls back along pseudoholomorphic immersions.** Let `φ : M' → M` be
`C²` at `y`, pseudoholomorphic at `y` for `J'` and `J`, with injective derivative there, and let
`f` be `C²` at the critical point `φ y` and complex negative there for `J`. Then `f ∘ φ` is
complex negative at `y` for `J'`. The point `y` is a critical point of `f ∘ φ` by
`TauCeti.mem_criticalPoints_comp`. -/
theorem IsPseudoholomorphicAt.isComplexNegativeAt_comp (hJ : IsPseudoholomorphicAt J' J φ y)
    (hφ : ContMDiffAt I' I 2 φ y) (hinj : Function.Injective (mfderiv I' I φ y))
    (hf : ContMDiffAt I 𝓘(ℝ) 2 f (φ y)) (hcrit : φ y ∈ criticalPoints I f)
    (hneg : J.IsComplexNegativeAt f (φ y)) : J'.IsComplexNegativeAt (f ∘ φ) y := by
  refine SmoothAlmostComplexStructure.isComplexNegativeAt_def.2 fun v hv ↦ ?_
  rw [criticalHessian_comp_apply rfl hf hφ hcrit, criticalHessian_comp_apply rfl hf hφ hcrit,
    hJ.mfderiv_apply_commute]
  exact SmoothAlmostComplexStructure.isComplexNegativeAt_def.1 hneg _ fun h ↦
    hv (hinj (h.trans (map_zero _).symm))

/-- **Complex negativity restricts to open submanifolds.** If `x ∈ U` is a critical point of a
function `f` that is `C²` there, and `f` is complex negative at `x` for `J`, then the restriction
of `f` to `U` is complex negative at `x` for the restricted structure `J.restrictOpen U`. The
point `x` is a critical point of the restriction by `TauCeti.mem_criticalPoints_comp_subtypeVal`.
-/
theorem SmoothAlmostComplexStructure.IsComplexNegativeAt.comp_subtypeVal
    {U : TopologicalSpace.Opens M} {x : U} (hneg : J.IsComplexNegativeAt f x)
    (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) (hcrit : (x : M) ∈ criticalPoints I f) :
    (J.restrictOpen U).IsComplexNegativeAt (f ∘ Subtype.val) x :=
  ((J.isPseudoholomorphic_subtype_val U).isPseudoholomorphicAt x).isComplexNegativeAt_comp
    contMDiff_subtypeVal.contMDiffAt (Manifold.mfderiv_subtype_val_injective x) hf hcrit hneg

end Pullback

variable [FiniteDimensional ℝ E] [T2Space M]

/-- Let `J` be a smooth almost complex structure on a Hausdorff boundaryless manifold with a
finite-dimensional model, `K` a compact set, and `f` a smooth function such that at every critical
point `x ∈ K` of `f`, `f` is complex negative at `x` for `J`. Then every `g` close enough to `f`
in the weak Whitney topology is complex negative at each of its critical points in `K`. -/
theorem SmoothAlmostComplexStructure.eventually_isComplexNegativeAt
    (J : SmoothAlmostComplexStructure I M) {K : Set M} (hK : IsCompact K)
    {f : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯}
    (hf : ∀ x ∈ K, x ∈ criticalPoints I f → J.IsComplexNegativeAt f x) :
    ∀ᶠ g : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯ in 𝓝 f, ∀ x ∈ K, x ∈ criticalPoints I g →
      J.IsComplexNegativeAt g x := by
  have : LocallyCompactSpace H := I.locallyCompactSpace
  obtain ⟨N, -, a, u, b, hab, hKu⟩ := exists_finite_precompact_chart_cover_of_isOpen_cover
    (I := I) hK (V := fun _ : Unit ↦ univ) (fun _ ↦ isOpen_univ)
    fun _ _ ↦ mem_iUnion.mpr ⟨(), mem_univ _⟩
  -- The parts of the compact pieces of the chart targets lying over `K`.
  let S (i : Fin N) : Set (extChartAt I (a i)).target :=
    Subtype.val ⁻¹' b i ∩ {z | (extChartAt I (a i)).symm z ∈ K}
  have hS (i : Fin N) : IsCompact (S i) := by
    refine IsCompact.inter_right ?_ (hK.isClosed.preimage
      ((continuousOn_extChartAt_symm (a i)).domRestrict))
    rw [Subtype.isCompact_iff, Subtype.image_preimage_coe,
      inter_eq_right.mpr (hab i).2.2.2.2.2.1]
    exact (hab i).2.2.2.2.1
  -- The coordinate jets, as continuous maps on the chart targets.
  let Jc (i : Fin N) : C((extChartAt I (a i)).target, E →L[ℝ] E) :=
    ⟨fun z ↦ J.inChart (a i) z, (J.contDiffOn_inChart (a i)).continuousOn.domRestrict⟩
  let jet (g : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯) (i : Fin N) :
      C((extChartAt I (a i)).target, (E [×1]→L[ℝ] ℝ) × (E [×2]→L[ℝ] ℝ) × (E →L[ℝ] E)) :=
    (chartIteratedFDeriv g (a i) 1 ENat.LEInfty.out).prodMk
      ((chartIteratedFDeriv g (a i) 2 ENat.LEInfty.out).prodMk (Jc i))
  have hjet (i : Fin N) : Continuous fun g ↦ jet g i :=
    ContinuousMap.continuous_prodMk.comp ((continuous_chartIteratedFDeriv _ _ _).prodMk
      (ContinuousMap.continuous_prodMk.comp
        ((continuous_chartIteratedFDeriv _ _ _).prodMk continuous_const)))
  have hmaps (i : Fin N) : MapsTo (jet f i) (S i) (NegJets E) :=
    fun z hz ↦ (mem_negJets_iff J f (a i) z rfl).mpr (hf _ hz.2)
  have hnhds : ⋂ i, {g | MapsTo (jet g i) (S i) (NegJets E)} ∈ 𝓝 f :=
    iInter_mem.mpr fun i ↦ ((ContinuousMap.isOpen_setOfPred_mapsTo (hS i)
      isOpen_negJets).preimage (hjet i)).mem_nhds (hmaps i)
  filter_upwards [hnhds] with g hg x hxK
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hKu hxK)
  have hxs : x ∈ (extChartAt I (a i)).source := (hab i).2.2.2.1 hi
  let z : (extChartAt I (a i)).target := ⟨extChartAt I (a i) x, (extChartAt I (a i)).map_source hxs⟩
  have hzx : (extChartAt I (a i)).symm z = x := (extChartAt I (a i)).left_inv hxs
  have hzS : z ∈ S i := ⟨(hab i).2.2.2.2.2.2.2 (mem_image_of_mem _ hi), by
    simpa only [mem_ofPred_eq, hzx] using hxK⟩
  exact (mem_negJets_iff J g (a i) z hzx).mp (mem_iInter.mp hg i hzS)

/-- **Relative Morse perturbation keeping complex negativity.** In the setting of
`TauCeti.SmoothAlmostComplexStructure.eventually_isComplexNegativeAt`, let `C` be a closed set
such that `f` is Morse on `K ∩ C`. Then every neighbourhood of `f` in the weak Whitney topology
contains a function `g` which is Morse on `K`, such that `g - f` has compact support disjoint from
`C`, and which is complex negative for `J` at each of its critical points in `K`. -/
theorem SmoothAlmostComplexStructure.exists_isMorseOn_isComplexNegativeAt
    (J : SmoothAlmostComplexStructure I M) {K C : Set M} (hK : IsCompact K) (hC : IsClosed C)
    {f : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯} (hfKC : IsMorseOn I f (K ∩ C))
    (hf : ∀ x ∈ K, x ∈ criticalPoints I f → J.IsComplexNegativeAt f x)
    {𝒰 : Set C^∞⟮I, M; 𝓘(ℝ), ℝ⟯} (h𝒰 : 𝒰 ∈ 𝓝 f) :
    ∃ g ∈ 𝒰, IsMorseOn I g K ∧ HasCompactSupport (fun y ↦ g y - f y) ∧
      tsupport (fun y ↦ g y - f y) ⊆ Cᶜ ∧
      ∀ x ∈ K, x ∈ criticalPoints I g → J.IsComplexNegativeAt g x := by
  obtain ⟨g, ⟨hg𝒰, hgJ⟩, hgm, hgc, hgs⟩ := f.exists_isMorseOn_hasCompactSupport_sub_compl hK hC
    hfKC (inter_mem h𝒰 (J.eventually_isComplexNegativeAt hK hf))
  exact ⟨g, hg𝒰, hgm, hgc, hgs, hgJ⟩

/-- **Relative Morse perturbation with Morse index at least half the dimension.** Under the
hypotheses of `TauCeti.SmoothAlmostComplexStructure.exists_isMorseOn_isComplexNegativeAt`,
every neighbourhood of `f` in the weak Whitney topology contains a function `g` which is Morse on
`K`, such that `g - f` has compact support disjoint from `C`, and whose Morse index at each of its
critical points in `K` is at least `dim E / 2`. -/
theorem SmoothAlmostComplexStructure.exists_isMorseOn_finrank_div_two_le_manifoldMorseIndex
    (J : SmoothAlmostComplexStructure I M) {K C : Set M} (hK : IsCompact K) (hC : IsClosed C)
    {f : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯} (hfKC : IsMorseOn I f (K ∩ C))
    (hf : ∀ x ∈ K, x ∈ criticalPoints I f → J.IsComplexNegativeAt f x)
    {𝒰 : Set C^∞⟮I, M; 𝓘(ℝ), ℝ⟯} (h𝒰 : 𝒰 ∈ 𝓝 f) :
    ∃ g ∈ 𝒰, IsMorseOn I g K ∧ HasCompactSupport (fun y ↦ g y - f y) ∧
      tsupport (fun y ↦ g y - f y) ⊆ Cᶜ ∧
      ∀ x ∈ K, x ∈ criticalPoints I g → Module.finrank ℝ E / 2 ≤ manifoldMorseIndex I g x := by
  obtain ⟨g, hg𝒰, hgm, hgc, hgs, hgJ⟩ :=
    J.exists_isMorseOn_isComplexNegativeAt hK hC hfKC hf h𝒰
  exact ⟨g, hg𝒰, hgm, hgc, hgs, fun x hxK hx ↦
    (hgJ x hxK hx).finrank_div_two_le_manifoldMorseIndex⟩

/-- **Morse perturbation fixed on a sublevel set, with Morse index at least half the dimension.**
Let `J` be a smooth almost complex structure on a Hausdorff boundaryless manifold with a
finite-dimensional model, `f` a smooth function and `c` a real number such that the superlevel
set `f⁻¹[c, ∞)` is compact, every critical point of `f` has value above `c`, and
`Hess f(v, v) + Hess f(Jv, Jv) < 0` for every nonzero tangent vector `v` at each critical point.
Then every neighbourhood of `f` in the weak Whitney topology contains a Morse function `g` which
agrees with `f` on the sublevel set `f⁻¹(-∞, c]`, such that `g - f` has compact support, whose
Morse index at each critical point is at least `dim E / 2`, for which `c` is a regular value and
`g⁻¹[c, ∞)` is compact, and which is bounded above by a regular value `b`. -/
theorem SmoothAlmostComplexStructure.exists_isMorse_eqOn_preimage_Iic
    (J : SmoothAlmostComplexStructure I M) {f : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯} {c : ℝ}
    (hc : IsCompact (f ⁻¹' Ici c)) (hcrit : ∀ x ∈ criticalPoints I f, c < f x)
    (hf : ∀ x ∈ criticalPoints I f, ∀ v : TangentSpace I x, v ≠ 0 →
      criticalHessian I f x v v + criticalHessian I f x (J x v) (J x v) < 0)
    {𝒰 : Set C^∞⟮I, M; 𝓘(ℝ), ℝ⟯} (h𝒰 : 𝒰 ∈ 𝓝 f) :
    ∃ g ∈ 𝒰, IsMorse I g ∧ EqOn g f (f ⁻¹' Iic c) ∧ HasCompactSupport (fun y ↦ g y - f y) ∧
      (∀ x ∈ criticalPoints I g, Module.finrank ℝ E / 2 ≤ manifoldMorseIndex I g x) ∧
      IsRegularValue I 𝓘(ℝ) g c ∧ IsCompact (g ⁻¹' Ici c) ∧
      ∃ b, IsRegularValue I 𝓘(ℝ) g b ∧ ∀ x, g x < b := by
  -- Every critical point of `g` lies in `f⁻¹[c, ∞)`, where complex negativity is kept.
  obtain ⟨g, ⟨hg𝒰, hgJ⟩, hgM, hgf, hgc, hgK, hreg, hgcomp, hb⟩ :=
    f.exists_isMorse_eqOn_preimage_Iic hc hcrit
      (inter_mem h𝒰 (J.eventually_criticalHessian_add_neg hc fun x _ hx ↦ hf x hx))
  exact ⟨g, hg𝒰, hgM, hgf, hgc, fun x hx ↦
    J.finrank_div_two_le_manifoldMorseIndex g x (hgJ x (hgK x hx).le hx), hreg, hgcomp, hb⟩

end TauCeti

end
