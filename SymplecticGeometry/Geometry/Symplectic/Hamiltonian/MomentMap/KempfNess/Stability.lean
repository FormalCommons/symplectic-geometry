/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.KempfNess.Function
import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.KempfNess.NormSquare
import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.ContMDiff
import TauCeti.Geometry.Manifold.Morse.GradientFlow
import TauCeti.LinearAlgebra.BilinearForm.Basic

/-!
# Stability and the Kempf–Ness function

In the Kähler setting of `KempfNess/NormSquare.lean` (a compact connected group `G` with
complexification `C`, a compact manifold `M` with a closed nondegenerate `G`-invariant form `σ`,
a complexified action, an equivariant moment map `-μ`, the metric `σ(·, J ·)`, and a symmetric,
positive definite, `Ad`-invariant form `B` on the Lie algebra), this file characterizes the
semistable points by their Kempf–Ness functions: `p` is semistable exactly when `Φ_p` is bounded
below on `Gc` (`SymplecticGeometry.isSemistable_iff_bddBelow_kempfNessFunction`).

Both directions use the curve `g` in `Gc` along which `(g t)⁻¹ • p` is the negative gradient flow
of `‖μ‖²` from `p` (`SymplecticGeometry.exists_mem_orbit_maximalIntegralCurve`), and its limit
`x` (`SymplecticGeometry.tendsto_maximalIntegralCurve_momentNormSq`).

* If `Φ_p` is bounded below, let `c = ‖μ x‖²`. Since `‖μ‖²` does not increase along the flow,
  it is at least `c` along it, so `Φ_p (g t) ≤ -2 c t` for `t ≥ 0`, as `Φ_p ∘ g` has derivative
  `-2 ‖μ‖²` and vanishes at `0`. Hence `c = 0`: the limit `x`, which lies in the closure of the
  orbit of `p`, is a zero of `μ`.
* If `p` is semistable, the infimum of `‖μ‖²` over the orbit of `p` is `0`, so by the moment
  limit theorem (`SymplecticGeometry.momentNormSq_limit_eq_iInf`) `μ x = 0`, and `Φ_p ∘ g` is
  bounded below by some `L` on `[0, ∞)`
  (`SymplecticGeometry.bddBelow_kempfNessFunction_image_Ici`). For `a : Gc`, let `g'` be the
  curve of the flow from `a⁻¹ • p`. By the cocycle identity
  (`SymplecticGeometry.kempfNessFunction_mul`), `Φ_p (a * g' t) = Φ_p a + Φ_{a⁻¹ • p} (g' t)`,
  which is at most `Φ_p a` for `t ≥ 0`. Writing `(g t)⁻¹ * a * g' t = C.expI η * C.toHom u`, the
  lower bound from convexity
  (`SymplecticGeometry.kempfNessFunction_sub_sqrt_momentNormSq_mul_sqrt_le`) gives
  `Φ_p (a * g' t) ≥ Φ_p (g t) - √(‖μ ((g t)⁻¹ • p)‖²) * √(B η η)`, and `B η η` is at most its
  value at `t = 0` (`SymplecticGeometry.antitoneOn_polar_symm_fst_inv_mul`). As `t → ∞`, the
  norm `‖μ ((g t)⁻¹ • p)‖²` tends to `0`, so `Φ_p a ≥ L`.

This is the proof of [GeorgoulasRobbinSalamon2021], Theorem 7.3, with the distance in `Gc ⧸ G`
replaced by the polar radius, as in `KempfNess/NormSquare.lean`.

The Kempf–Ness function of a stable point `p` is moreover proper
(`SymplecticGeometry.IsStable.isProperMap_kempfNessFunction`). By the cocycle identity it suffices
to treat a zero `q` of `μ` in the orbit, whose stabilizer in `Gc` is still discrete, so that no
nonzero `ξ` has `X_ξ(q) = 0`. Then `t ↦ μ (C.expI (-(t • ξ)) • q) ξ`, the derivative of
`t ↦ Φ_q (C.expI (t • ξ))`, vanishes at `0` and has positive derivative `‖X_ξ(q)‖²` there, so it
is positive at `t = 1`; by compactness of the unit sphere it is at least some `c > 0` there for
all unit `ξ`. Convexity then gives `Φ_q (C.expI η * C.toHom u) ≥ c (‖η‖ - 1)`, and since
`C.polar` is a homeomorphism and `G` is compact, the sublevel sets of `Φ_q` are compact. This is
the properness half of [GeorgoulasRobbinSalamon2021], Theorem 7.3, with the polar radius in place
of the distance in `Gc ⧸ G`.

Conversely, if `Φ_p` is bounded below and proper, it has a minimum `g`, as its sublevel sets are
compact; there its differential vanishes, so `q = g⁻¹ • p` is a zero of `μ`
(`SymplecticGeometry.mfderiv_kempfNessFunction_eq_zero_iff`), and `Φ_q` is proper by the cocycle
identity. If `X_ξ(q) = 0`, then `C.expI (s • ξ)` fixes `q` for every `s`
(`SymplecticGeometry.IsComplexifiedAction.expI_smul_smul_eq_self_iff`), so `Φ_q` vanishes along
`s ↦ C.expI (s • ξ)`, a curve whose polar radius is `‖s • ξ‖`; properness bounds it, so `ξ = 0`
and the stabilizer of `q` is discrete. Together these give
`SymplecticGeometry.isStable_iff_bddBelow_and_isProperMap_kempfNessFunction`, the stability half
of [GeorgoulasRobbinSalamon2021], Theorem 7.3 (with Theorem 4.3 there for the critical points).

## Main results

* `SymplecticGeometry.isSemistable_iff_bddBelow_kempfNessFunction`: `p` is semistable exactly
  when its Kempf–Ness function is bounded below.
* `SymplecticGeometry.IsSemistable.iInf_momentNormSq_smul_eq_zero`: at a semistable point, the
  infimum of `‖μ‖²` over the orbit is `0`.
* `SymplecticGeometry.moment_eq_zero_of_bddBelow_kempfNessFunction_image_Ici`: if `Φ_p` is
  bounded below along the flow curve `g`, then the limit of the flow is a zero of `μ`.
* `SymplecticGeometry.mem_lowerBounds_range_kempfNessFunction`: if the flow converges to a zero
  of `μ`, a lower bound of `Φ_p ∘ g` on `[0, ∞)` bounds `Φ_p` on all of `Gc`.
* `SymplecticGeometry.IsStable.isProperMap_kempfNessFunction`: the Kempf–Ness function of a stable
  point is proper.
* `SymplecticGeometry.isStable_of_bddBelow_of_isProperMap_kempfNessFunction`: a point whose
  Kempf–Ness function is bounded below and proper is stable.
* `SymplecticGeometry.isStable_iff_bddBelow_and_isProperMap_kempfNessFunction`: `p` is stable
  exactly when its Kempf–Ness function is bounded below and proper.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §5.7.
* [V. Georgoulas, J. W. Robbin and D. A. Salamon, *The Moment-Weight Inequality and the
  Hilbert–Mumford Criterion*][GeorgoulasRobbinSalamon2021], Theorems 4.3 and 7.3.
-/

public section

noncomputable section

open _root_.Bundle Filter Set Topology TauCeti TauCeti.Manifold
open scoped Manifold ContDiff RealInnerProductSpace

namespace SymplecticGeometry

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  [CompactSpace G] [T2Space G] [ConnectedSpace G]
  {EC : Type*} [NormedAddCommGroup EC] [NormedSpace ℝ EC] [CompleteSpace EC]
  {HC : Type*} [TopologicalSpace HC] {IC : ModelWithCorners ℝ EC HC} [IC.Boundaryless]
  {Gc : Type*} [TopologicalSpace Gc] [ChartedSpace HC Gc] [Group Gc] [LieGroup IC ∞ Gc]
  [T2Space Gc]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [CompactSpace M]
  [T2Space M]
  [MulAction G M] [MulAction Gc M] [ContMDiffSMul I I' ∞ G M] [ContMDiffSMul IC I' ∞ Gc M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I' x)]
  [IsContMDiffRiemannianBundle I' 1 E' (fun x : M ↦ TangentSpace I' x)]
  {σ : SmoothTwoForm I' M} {J : SmoothAlmostComplexStructure I' M}
  {C : LieComplexification I G IC Gc}
  {B : LinearMap.BilinForm ℝ (GroupLieAlgebra I G)}
  {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}

omit [I.Boundaryless] [CompactSpace G] [T2Space G] [ConnectedSpace G] [CompactSpace M]
  [T2Space M] [MulAction G M] in
/-- At a semistable point `p`, the infimum of `‖μ‖²` over the orbit of `p` is `0`, for a
nonnegative form `B` and a continuous `‖μ‖²`. -/
theorem IsSemistable.iInf_momentNormSq_smul_eq_zero {hB : B.Nondegenerate} {p : M}
    (hp : IsSemistable C μ p) (hpos : B.IsNonneg) (hf : Continuous (momentNormSq B hB μ)) :
    ⨅ a : Gc, momentNormSq B hB μ (a • p) = 0 := by
  have hbdd : BddBelow (range fun a : Gc ↦ momentNormSq B hB μ (a • p)) :=
    bddBelow_range_momentNormSq_comp hpos (· • p)
  obtain ⟨y, hy, hy0⟩ := isSemistable_iff.1 hp
  have hsub : closure (MulAction.orbit Gc p) ⊆
      {z | ⨅ a : Gc, momentNormSq B hB μ (a • p) ≤ momentNormSq B hB μ z} :=
    closure_minimal (by rintro _ ⟨a, rfl⟩; exact ciInf_le hbdd a)
      (isClosed_le continuous_const hf)
  refine le_antisymm ?_ (le_ciInf fun _ ↦ momentNormSq_nonneg hpos)
  simpa [momentNormSq_def, hy0] using hsub hy

variable {hB : B.Nondegenerate}

omit [ConnectedSpace G] [ContMDiffSMul IC I' ∞ Gc M] in
/-- Let `g : ℝ → Gc` be a curve with `g 0 = 1` such that `(g t)⁻¹ • p` is the negative gradient
flow of `‖μ‖²` from `p` at time `t`, and `t ↦ Φ_p (g t)` has derivative `-2 ‖μ ((g t)⁻¹ • p)‖²`;
for a complexified action, `exists_mem_orbit_maximalIntegralCurve` gives such a curve. If
`Φ_p ∘ g` is bounded below on `[0, ∞)`, then `μ` vanishes at the limit `x` of the flow. -/
theorem moment_eq_zero_of_bddBelow_kempfNessFunction_image_Ici (hσc : σ.IsClosed)
    (hσ : σ.IsNondegenerate)
    (hσG : ∀ g : G, SmoothForm.mpullback (fun y : M ↦ g • y)
      (ContMDiffSMul.contMDiff_const_smul (I := I) (I' := I') g) σ = σ)
    (hμ : σ.IsEquivariantMomentMap fun x ↦ -μ x) (hBp : B.toQuadraticMap.PosDef)
    (hBG : Representation.IsInvariantForm (Lie.adjointRepresentation ℝ I G) B) {p x : M}
    (hx : Tendsto (maximalIntegralCurve (-mgradient I' (momentNormSq B hB μ)) p) atTop (𝓝 x))
    {g : ℝ → Gc} (hg0 : g 0 = 1)
    (hgx : ∀ t, maximalIntegralCurve (-mgradient I' (momentNormSq B hB μ)) p t = (g t)⁻¹ • p)
    (hgd : ∀ t, HasDerivAt (fun s ↦ kempfNessFunction C μ p (g s))
      (-2 * momentNormSq B hB μ ((g t)⁻¹ • p)) t)
    (hL : BddBelow ((fun t ↦ kempfNessFunction C μ p (g t)) '' Ici 0)) : μ x = 0 := by
  obtain ⟨L, hL⟩ := hL
  have hpos : B.IsNonneg := LinearMap.BilinForm.isNonneg_def.2 hBp.nonneg
  have hf : ContMDiff I' 𝓘(ℝ) 2 (momentNormSq B hB μ) :=
    hμ.toIsMomentMap.contMDiff_momentNormSq_of_neg.of_le (by norm_cast)
  have hI := (tendsto_maximalIntegralCurve_momentNormSq hσc hσ hσG hμ hB hBG p).1
  rw [momentNormSq_neg'] at hI
  set c := momentNormSq B hB μ x
  -- `‖μ‖²` is at least `c` along the flow.
  have hle (t : ℝ) (ht : 0 ≤ t) : c ≤ momentNormSq B hB μ ((g t)⁻¹ • p) := by
    rw [← hgx]
    exact le_comp_maximalIntegralCurve_neg_mgradient hf hI hx.mapClusterPt ht
  -- `Φ_p (g t) + 2 c t` is antitone on `[0, ∞)` and vanishes at `0`.
  have hanti : AntitoneOn (fun t ↦ kempfNessFunction C μ p (g t) + 2 * c * t) (Ici 0) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
      (fun t _ ↦ ((hgd t).add ((hasDerivAt_id t).const_mul (2 * c))).continuousAt
        |>.continuousWithinAt)
      (fun t _ ↦ ((hgd t).add ((hasDerivAt_id t).const_mul (2 * c))).hasDerivWithinAt)
      fun t ht ↦ ?_
    rw [interior_Ici] at ht
    have := hle t (le_of_lt ht)
    simp only [mul_one]
    linarith
  have hc0 : c ≤ 0 := by
    by_contra! hc
    have ht : 0 ≤ (|L| + 1) / (2 * c) := by positivity
    have h1 := hanti (mem_Ici.2 le_rfl) ht ht
    have h2 := hL ⟨(|L| + 1) / (2 * c), ht, rfl⟩
    simp only [hg0, kempfNessFunction_one, mul_zero, add_zero] at h1
    rw [mul_div_cancel₀ _ (by positivity)] at h1
    linarith [neg_abs_le L]
  exact (momentNormSq_eq_zero_iff (hB := hB) hBp.anisotropic).1
    (le_antisymm hc0 (momentNormSq_nonneg hpos))

/-- If the negative gradient flow `t ↦ (g t)⁻¹ • p` of `‖μ‖²` from `p`, for a curve `g` in `Gc`
with left-trivialized derivative `-2 i μ♯((g t)⁻¹ • p)`, converges to a zero of `μ`, then every
lower bound of the Kempf–Ness function of `p` along `g` on `[0, ∞)` is a lower bound of it on
all of `Gc`. -/
theorem mem_lowerBounds_range_kempfNessFunction (h : IsComplexifiedAction C J)
    (hσc : σ.IsClosed) (hσ : σ.IsNondegenerate)
    (hσG : ∀ g : G, SmoothForm.mpullback (fun y : M ↦ g • y)
      (ContMDiffSMul.contMDiff_const_smul (I := I) (I' := I') g) σ = σ)
    (hμ : σ.IsEquivariantMomentMap fun x ↦ -μ x)
    (hgm : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w)) (hBs : B.IsSymm)
    (hpos : B.IsNonneg)
    (hBG : Representation.IsInvariantForm (Lie.adjointRepresentation ℝ I G) B) {p x : M}
    (hx : Tendsto (maximalIntegralCurve (-mgradient I' (momentNormSq B hB μ)) p) atTop (𝓝 x))
    (hx0 : μ x = 0) {g : ℝ → Gc}
    (hg : HasLeftTrivializedDerivOn g
      (fun t ↦ (-2 : ℝ) • C.cplx (C.lieMap (momentSharp B hB μ ((g t)⁻¹ • p)))) univ)
    (hgx : ∀ t, maximalIntegralCurve (-mgradient I' (momentNormSq B hB μ)) p t = (g t)⁻¹ • p)
    {L : ℝ} (hL : L ∈ lowerBounds ((fun t ↦ kempfNessFunction C μ p (g t)) '' Ici 0)) :
    L ∈ lowerBounds (range (kempfNessFunction C μ p)) := by
  rintro _ ⟨a, rfl⟩
  have hf : ContMDiff I' 𝓘(ℝ) 2 (momentNormSq B hB μ) :=
    hμ.toIsMomentMap.contMDiff_momentNormSq_of_neg.of_le (by norm_cast)
  have hI := (tendsto_maximalIntegralCurve_momentNormSq hσc hσ hσG hμ hB hBG p).1
  rw [momentNormSq_neg'] at hI
  -- The curve `g'` of the flow from `a⁻¹ • p`; `g₁ = a * g'` is a flow curve from `p`.
  obtain ⟨g', hg'0, hg', -, hg'd⟩ :=
    exists_mem_orbit_maximalIntegralCurve (hB := hB) h hμ hgm hBs (a⁻¹ • p)
  set g₁ : ℝ → Gc := fun t ↦ a * g' t
  have hg₁ : HasLeftTrivializedDerivOn g₁
      (fun t ↦ (-2 : ℝ) • C.cplx (C.lieMap (momentSharp B hB μ ((g₁ t)⁻¹ • p)))) univ :=
    hg'.const_mul_comp_inv_smul (F := fun x ↦ (-2 : ℝ) • C.cplx (C.lieMap (momentSharp B hB μ x)))
  -- `Φ_p ∘ g₁` stays below `Φ_p a`, by the cocycle identity.
  have hup (t : ℝ) (ht : 0 ≤ t) : kempfNessFunction C μ p (g₁ t) ≤ kempfNessFunction C μ p a := by
    have hanti : Antitone fun s ↦ kempfNessFunction C μ (a⁻¹ • p) (g' s) :=
      antitone_of_hasDerivAt_nonpos hg'd fun s ↦
        mul_nonpos_of_nonpos_of_nonneg (by norm_num) (momentNormSq_nonneg hpos)
    have := hanti ht
    simp only [hg'0, kempfNessFunction_one] at this
    rw [kempfNessFunction_mul C μ p h hμ hgm]
    linarith
  -- The polar radius of `(g t)⁻¹ * g₁ t` is at most its value `N₀` at `t = 0`.
  set N : ℝ → ℝ := fun t ↦
    B (C.polar.symm ((g t)⁻¹ * g₁ t)).1 (C.polar.symm ((g t)⁻¹ * g₁ t)).1
  have hN : Antitone N := antitoneOn_univ.1
    (antitoneOn_polar_symm_fst_inv_mul h hμ hgm hBs hBG hg hg₁ convex_univ)
  have hlow (t : ℝ) (ht : 0 ≤ t) :
      L - √(momentNormSq B hB μ ((g t)⁻¹ • p)) * √(N 0) ≤ kempfNessFunction C μ p a := by
    have hdec : g₁ t = g t * C.expI (C.polar.symm ((g t)⁻¹ * g₁ t)).1 *
        C.toHom (C.polar.symm ((g t)⁻¹ * g₁ t)).2 := by
      rw [mul_assoc, C.expI_mul_toHom_polar_symm, mul_inv_cancel_left]
    have hcv := kempfNessFunction_sub_sqrt_momentNormSq_mul_sqrt_le (hB := hB) C μ p h hμ hgm hBs
      hpos (g t) (C.polar.symm ((g t)⁻¹ * g₁ t)).1 (C.polar.symm ((g t)⁻¹ * g₁ t)).2
    rw [← hdec] at hcv
    have hLt := hL ⟨t, ht, rfl⟩
    have hsq : √(N t) ≤ √(N 0) := Real.sqrt_le_sqrt (hN ht)
    have := mul_le_mul_of_nonneg_left hsq (Real.sqrt_nonneg (momentNormSq B hB μ ((g t)⁻¹ • p)))
    linarith [hup t ht]
  -- As `t → ∞`, `‖μ ((g t)⁻¹ • p)‖²` tends to `‖μ x‖² = 0`.
  have hfx : Tendsto (fun t ↦ momentNormSq B hB μ ((g t)⁻¹ • p)) atTop
      (𝓝 (momentNormSq B hB μ x)) := by
    simpa only [hgx] using tendsto_comp_maximalIntegralCurve_neg_mgradient hf hI hx.mapClusterPt
  have hx0' : momentNormSq B hB μ x = 0 := by simp [momentNormSq_def, hx0]
  rw [hx0'] at hfx
  have hlim : Tendsto (fun t ↦ L - √(momentNormSq B hB μ ((g t)⁻¹ • p)) * √(N 0)) atTop
      (𝓝 L) := by
    have := ((Real.continuous_sqrt.tendsto 0).comp hfx).mul_const (√(N 0))
    simpa using this.const_sub L
  exact le_of_tendsto hlim ((eventually_ge_atTop 0).mono hlow)

/-- **Semistability is boundedness below of the Kempf–Ness function.** In the Kähler setting of
`momentNormSq_limit_eq_iInf`, with `σ` closed, nondegenerate and `G`-invariant, `G` compact and
connected, `-μ` an equivariant moment map for a complexified action, the metric `σ(·, J ·)`, and
`B` symmetric, positive definite and `Ad`-invariant: a point `p` is semistable exactly when its
Kempf–Ness function `Φ_p : Gc → ℝ` is bounded below.

This is [GeorgoulasRobbinSalamon2021], Theorem 7.3. -/
theorem isSemistable_iff_bddBelow_kempfNessFunction (h : IsComplexifiedAction C J)
    (hσc : σ.IsClosed) (hσ : σ.IsNondegenerate)
    (hσG : ∀ g : G, SmoothForm.mpullback (fun y : M ↦ g • y)
      (ContMDiffSMul.contMDiff_const_smul (I := I) (I' := I') g) σ = σ)
    (hμ : σ.IsEquivariantMomentMap fun x ↦ -μ x)
    (hgm : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w)) (hBs : B.IsSymm)
    (hBp : B.toQuadraticMap.PosDef)
    (hBG : Representation.IsInvariantForm (Lie.adjointRepresentation ℝ I G) B) (p : M) :
    IsSemistable C μ p ↔ BddBelow (range (kempfNessFunction C μ p)) := by
  have hB : B.Nondegenerate := B.nondegenerate_of_anisotropic hBp.anisotropic
  have hpos : B.IsNonneg := LinearMap.BilinForm.isNonneg_def.2 hBp.nonneg
  -- The flow from `p`, its limit `x`, and the curve `g` in `Gc` along which it runs.
  obtain ⟨-, x, -, hx, -⟩ := tendsto_maximalIntegralCurve_momentNormSq hσc hσ hσG hμ hB hBG p
  rw [momentNormSq_neg'] at hx
  obtain ⟨g, hg0, hg, hgx, hgd⟩ := exists_mem_orbit_maximalIntegralCurve (hB := hB) h hμ hgm hBs p
  constructor
  · intro hss
    have hx0 : μ x = 0 := by
      rw [← momentNormSq_eq_zero_iff (hB := hB) hBp.anisotropic,
        momentNormSq_limit_eq_iInf h hσc hσ hσG hμ hgm hBs hBp hBG hx]
      exact hss.iInf_momentNormSq_smul_eq_zero hpos
        hμ.toIsMomentMap.contMDiff_momentNormSq_of_neg.continuous
    obtain ⟨L, hL⟩ := bddBelow_kempfNessFunction_image_Ici hσc hσ hσG hμ hBG hx hx0 hgx hgd
    exact ⟨L, mem_lowerBounds_range_kempfNessFunction h hσc hσ hσG hμ hgm hBs hpos hBG hx hx0 hg
      hgx hL⟩
  · intro hL
    have hx0 := moment_eq_zero_of_bddBelow_kempfNessFunction_image_Ici hσc hσ hσG hμ hBp hBG hx
      hg0 hgx hgd (hL.mono (by rintro _ ⟨t, -, rfl⟩; exact ⟨g t, rfl⟩))
    refine isSemistable_iff.2 ⟨x, mem_closure_of_tendsto hx (Eventually.of_forall fun t ↦ ?_), hx0⟩
    rw [hgx]
    exact MulAction.mem_orbit p (g t)⁻¹

section Proper

omit [I.Boundaryless] [T2Space G] [CompactSpace M]
  [IsContMDiffRiemannianBundle I' 1 E' (fun x : M ↦ TangentSpace I' x)] in
/-- The Kempf–Ness function at a zero `q` of the moment map with discrete stabilizer in `Gc` is
proper, in the setting of `kempfNessFunction_add_moment_le`. -/
theorem isProperMap_kempfNessFunction_of_moment_eq_zero (h : IsComplexifiedAction C J)
    (hμ : σ.IsEquivariantMomentMap fun x ↦ -μ x)
    (hgm : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w)) {q : M} (hq : μ q = 0)
    [DiscreteTopology (MulAction.stabilizer Gc q)] :
    IsProperMap (kempfNessFunction C μ q) := by
  obtain ⟨c, hc0, hc⟩ := exists_pos_le_moment_expI_neg_smul_apply C μ q h hμ.toIsMomentMap hgm hq
    ((h.discreteTopology_stabilizer_iff_of_moment_eq_zero hμ hgm hq).1 ‹_›)
  have hcont : Continuous (kempfNessFunction C μ q) :=
    (contMDiff_kempfNessFunction C μ q hμ.toIsMomentMap.contMDiff_of_neg).continuous
  refine isProperMap_iff_isCompact_preimage.2 ⟨hcont, fun K hK ↦ ?_⟩
  obtain ⟨L, hL⟩ := hK.bddAbove
  -- The preimage of `K` lies in the image under `C.polar` of `closedBall 0 (L / c + 1) × G`.
  refine (((isCompact_closedBall (0 : E) (L / c + 1)).prod isCompact_univ).image
    C.polar.continuous).of_isClosed_subset (hK.isClosed.preimage hcont) fun g hg ↦
      ⟨C.polar.symm g, ⟨?_, mem_univ _⟩, C.polar.apply_symm_apply g⟩
  have hgrow := mul_norm_sub_one_le_kempfNessFunction C μ q h hμ hgm hq hc0.le hc
    (C.polar.symm g).1 (C.polar.symm g).2
  rw [C.expI_mul_toHom_polar_symm] at hgrow
  have hle : ‖(C.polar.symm g).1‖ - 1 ≤ L / c := (le_div_iff₀' hc0).2 (hgrow.trans (hL hg))
  rw [mem_closedBall_zero_iff]
  linarith

omit [I.Boundaryless] [T2Space G] [CompactSpace M]
  [IsContMDiffRiemannianBundle I' 1 E' (fun x : M ↦ TangentSpace I' x)] in
/-- **The Kempf–Ness function of a stable point is proper.** For a complexified action, with `-μ`
an equivariant moment map for `σ` and the metric `σ(·, J ·)`, the Kempf–Ness function
`Φ_p : Gc → ℝ` of a stable point `p` is a proper map.

This is one half of [GeorgoulasRobbinSalamon2021], Theorem 7.3. -/
theorem IsStable.isProperMap_kempfNessFunction (h : IsComplexifiedAction C J)
    (hμ : σ.IsEquivariantMomentMap fun x ↦ -μ x)
    (hgm : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w)) {p : M}
    (hp : IsStable C μ p) : IsProperMap (kempfNessFunction C μ p) := by
  obtain ⟨g, hg0⟩ := isPolystable_iff_exists_smul.1 hp.isPolystable
  have := topologicalGroup_of_lieGroup (G := Gc) IC ∞
  have := ((isStable_smul_iff g).2 hp).discreteTopology_stabilizer
  have hq := isProperMap_kempfNessFunction_of_moment_eq_zero h hμ hgm hg0
  -- By the cocycle identity, `Φ_p x = Φ_p g⁻¹ + Φ_{g • p} (g * x)`.
  have heq : kempfNessFunction C μ p = (kempfNessFunction C μ p g⁻¹ + ·) ∘
      kempfNessFunction C μ (g • p) ∘ (g * ·) := funext fun x ↦ by
    have := kempfNessFunction_mul C μ p h hμ hgm g⁻¹ (g * x)
    rwa [inv_mul_cancel_left, inv_inv] at this
  rw [heq]
  exact (Homeomorph.addLeft (kempfNessFunction C μ p g⁻¹)).isProperMap.comp
    (hq.comp (Homeomorph.mulLeft g).isProperMap)

omit [I.Boundaryless] [CompactSpace G] [T2Space G] [CompactSpace M]
  [IsContMDiffRiemannianBundle I' 1 E' (fun x : M ↦ TangentSpace I' x)] in
/-- A point whose Kempf–Ness function is bounded below and proper is stable, for a complexified
action, with `-μ` an equivariant moment map for `σ` and the metric `σ(·, J ·)`. -/
theorem isStable_of_bddBelow_of_isProperMap_kempfNessFunction (h : IsComplexifiedAction C J)
    (hμ : σ.IsEquivariantMomentMap fun x ↦ -μ x)
    (hgm : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w)) {p : M}
    (hbdd : BddBelow (range (kempfNessFunction C μ p)))
    (hprop : IsProperMap (kempfNessFunction C μ p)) : IsStable C μ p := by
  obtain ⟨L, hL⟩ := hbdd
  -- `Φ_p` attains its minimum at some `g`, since `Φ_p ⁻¹' [L, 0]` is compact and contains `1`.
  have hev : ∀ᶠ x in cocompact Gc, kempfNessFunction C μ p 1 ≤ kempfNessFunction C μ p x :=
    mem_of_superset (hprop.isCompact_preimage (isCompact_Icc (a := L) (b := 0))).compl_mem_cocompact
      fun x hx ↦ by
        rw [mem_ofPred_eq, kempfNessFunction_one]
        by_contra! hlt
        exact hx ⟨hL ⟨x, rfl⟩, hlt.le⟩
  obtain ⟨g, hg⟩ := hprop.continuous.exists_forall_le' 1 hev
  -- The minimum is a critical point, so `μ` vanishes at `q = g⁻¹ • p`.
  have hq : μ (g⁻¹ • p) = 0 := by
    rw [← mfderiv_kempfNessFunction_eq_zero_iff C μ p h hμ hgm g,
      ← mem_criticalPoints_iff_mfderiv_eq_zero]
    exact (isMinOn_univ_iff.2 hg).mem_criticalPoints BoundarylessManifold.isInteriorPoint
  set q := g⁻¹ • p
  have := topologicalGroup_of_lieGroup (G := Gc) IC ∞
  -- By the cocycle identity, `Φ_q x = Φ_p (g * x) - Φ_p g`, so `Φ_q` is proper.
  have heq : kempfNessFunction C μ q = (· - kempfNessFunction C μ p g) ∘
      kempfNessFunction C μ p ∘ (g * ·) := funext fun x ↦ by
    have := kempfNessFunction_mul C μ p h hμ hgm g x
    simp only [Function.comp_apply]
    linarith
  have hqprop : IsProperMap (kempfNessFunction C μ q) := by
    rw [heq]
    exact (Homeomorph.subRight (kempfNessFunction C μ p g)).isProperMap.comp
      (hprop.comp (Homeomorph.mulLeft g).isProperMap)
  -- If `X_ξ(q) = 0`, then `Φ_q` vanishes along `s ↦ C.expI (s • ξ)`, whose polar radius is
  -- `‖s • ξ‖`; properness bounds it, so `ξ = 0`.
  have : DiscreteTopology (MulAction.stabilizer Gc q) := by
    refine (h.discreteTopology_stabilizer_iff_of_moment_eq_zero hμ hgm hq).2 fun ξ hξ ↦ ?_
    have hfix := (h.expI_smul_smul_eq_self_iff (x := q)).2 hξ
    have hd (t : ℝ) :
        HasDerivAt (fun s : ℝ ↦ kempfNessFunction C μ q (1 * C.expI (s • ξ))) 0 t := by
      have := hasDerivAt_kempfNessFunction_geodesic C μ q h hμ hgm 1 ξ t
      rwa [inv_one, one_smul, ← neg_smul, hfix, hq, LinearMap.zero_apply] at this
    have hzero (s : ℝ) : C.expI (s • ξ) ∈ kempfNessFunction C μ q ⁻¹' {0} := by
      have := is_const_of_deriv_eq_zero (fun t ↦ (hd t).differentiableAt)
        (fun t ↦ (hd t).deriv) s 0
      simpa [C.expI_zero, kempfNessFunction_one] using this
    obtain ⟨r, hr⟩ := (((hqprop.isCompact_preimage isCompact_singleton).image
      C.polar.symm.continuous).image continuous_fst).isBounded.subset_closedBall 0
    -- A vector `η` with `s • η` in `closedBall 0 r` for every `s` is `0`.
    have hball (η : E) (hη : ∀ s : ℝ, s • η ∈ Metric.closedBall (0 : E) r) : η = 0 := by
      by_contra hne
      have hpos : 0 < ‖η‖ := norm_pos_iff.2 hne
      have hmem := hη ((|r| + 1) / ‖η‖)
      rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_div, abs_norm,
        div_mul_cancel₀ _ hpos.ne', abs_of_pos (by positivity : 0 < |r| + 1)] at hmem
      linarith [le_abs_self r]
    exact hball ξ fun s ↦ hr ⟨_, ⟨_, hzero s, rfl⟩, by
      rw [← mul_one (C.expI _), ← map_one C.toHom, C.polar_symm_expI_mul_toHom]
      -- The two sides differ only in the smul: that of `GroupLieAlgebra I G` and that of `E`,
      -- which agree since the Lie algebra is `E` by definition.
      rfl⟩
  exact (isStable_smul_iff g⁻¹).1 (isStable_of_moment_eq_zero hq)

/-- **Stability is boundedness below and properness of the Kempf–Ness function.** In the Kähler
setting of `isSemistable_iff_bddBelow_kempfNessFunction`, a point `p` is stable exactly when its
Kempf–Ness function `Φ_p : Gc → ℝ` is bounded below and proper.

This is [GeorgoulasRobbinSalamon2021], Theorem 7.3. -/
theorem isStable_iff_bddBelow_and_isProperMap_kempfNessFunction (h : IsComplexifiedAction C J)
    (hσc : σ.IsClosed) (hσ : σ.IsNondegenerate)
    (hσG : ∀ g : G, SmoothForm.mpullback (fun y : M ↦ g • y)
      (ContMDiffSMul.contMDiff_const_smul (I := I) (I' := I') g) σ = σ)
    (hμ : σ.IsEquivariantMomentMap fun x ↦ -μ x)
    (hgm : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w)) (hBs : B.IsSymm)
    (hBp : B.toQuadraticMap.PosDef)
    (hBG : Representation.IsInvariantForm (Lie.adjointRepresentation ℝ I G) B) (p : M) :
    IsStable C μ p ↔
      BddBelow (range (kempfNessFunction C μ p)) ∧ IsProperMap (kempfNessFunction C μ p) :=
  ⟨fun hp ↦ ⟨(isSemistable_iff_bddBelow_kempfNessFunction h hσc hσ hσG hμ hgm hBs hBp hBG
      p).1 hp.isSemistable, hp.isProperMap_kempfNessFunction h hμ hgm⟩,
    fun ⟨hb, hpr⟩ ↦ isStable_of_bddBelow_of_isProperMap_kempfNessFunction h hμ hgm hb hpr⟩

end Proper

end SymplecticGeometry

end
