/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import TauCeti.Geometry.Manifold.IntegralCurve.GlobalFlow
public import TauCeti.Geometry.Manifold.Morse.PseudoGradient.Existence
public import TauCeti.Geometry.Manifold.Morse.Stable.Manifold
import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.Neighborhood
import TauCeti.Geometry.Manifold.Flow.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.MFDeriv.ModelChart

/-!
# The time-`θ` flow-out of a ball of negative coordinates

Let `X` be a complete vector field on a boundaryless manifold `M` modelled on `E`, with flow
`Φ = TauCeti.globalFlow X`, and let `φ` be a Morse chart at `p` on whose source `X` is the linear
field `TauCeti.MorseChart.field`, so that `X` reads `c ↦ c` in the coordinates of negative weight
(weight `-1`). Write `N` for the Euclidean space of the coordinates of negative weight and
`S = φ.stableSubspace` for the vectors of the model space whose coordinates of negative weight
vanish. For a function `θ : N → ℝ`, this file studies the map

`Ψ (c, y) = Φ (θ c) (φ.toChart.symm (φ.negativeExtend c + y))`, `(c, y) ∈ N × S`,

which runs the flow from the point of the chart with coordinates `(c, y)` for the time `θ c`. It
is the differential half of the chart of the unstable set of `p` that `Morse/Core/Cube.lean`
builds; the other half is the injectivity of `c ↦ Ψ (c, 0)` on a ball.

## Main results

* `TauCeti.MorseChart.field_toChart_symm_negativeExtend`: at the point with coordinates `c` of
  negative weight (and `0` of positive weight) the linear field of the chart is the image of `c`
  under the differential of the inverse chart.
* `TauCeti.MorseChart.contMDiffOn_globalFlow_toChart_symm`: `Ψ` is smooth where the chart point is
  defined, for a smooth field and a smooth `θ`.
* `TauCeti.MorseChart.injective_mfderiv_globalFlow_toChart_symm`: the differential of `Ψ` is
  injective at `(c, 0)` as soon as `1 + dθ_c(c) > 0`, that is, as soon as
  `r ↦ θ (r • c) + log r` has a positive derivative at `r = 1`. Indeed the differential sends
  `(δc, δy)` to `dΦ` of the image under the inverse chart of `δc + dθ_c(δc) • c + δy`, by Tau
  Ceti's `TauCeti.mfderiv_flowOf_comp_prodMk_apply` and `TauCeti.mfderiv_globalFlow_apply_self`.
* `TauCeti.MorseChart.exists_isSmoothEmbedding_globalFlow_toChart_symm`: if moreover
  `c ↦ Ψ (c, 0)` is injective on the closed ball of radius `ρ`, then `Ψ` is a smooth embedding
  with open image of an open neighbourhood of that ball (with `y = 0`). The embedding comes from
  `TauCeti.exists_isOpen_isSmoothEmbedding_of_injOn`, and the image is open because `N × S` and
  `E` have the same dimension, so that `Ψ` is a local diffeomorphism near the ball.

The construction composes a Morse chart with the flow as Tau Ceti's
`TauCeti.IsAdaptedPseudoGradient.exists_isSliceChart_unstableSet` (`Morse/Stable/Manifold.lean`)
does on compact manifolds, with a time that depends on the point.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Part I, §3.
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Section 2.1.
-/

public section

open Function Set
open scoped ContDiff Manifold

namespace TauCeti

namespace MorseChart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {g : M → ℝ} {p : M} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}
  (φ : MorseChart E g p)

/-- The linear map `(c, y) ↦ c + y` from the coordinates of negative weight and the stable
subspace to the model space. -/
private noncomputable def thicken :
    (EuclideanSpace ℝ {i // φ.weight i < 0} × φ.stableSubspace) →ₗ[ℝ] E :=
  (φ.negativeExtend ∘ₗ (WithLp.linearEquiv 2 ℝ _).toLinearMap).coprod φ.stableSubspace.subtype

private theorem thicken_apply (q : EuclideanSpace ℝ {i // φ.weight i < 0} × φ.stableSubspace) :
    φ.thicken q = φ.negativeExtend q.1.ofLp + q.2 := rfl

private theorem negativeCoord_thicken
    (q : EuclideanSpace ℝ {i // φ.weight i < 0} × φ.stableSubspace) :
    φ.negativeCoord (φ.thicken q) = q.1.ofLp := by
  have h2 : φ.negativeCoord (q.2 : E) = 0 :=
    φ.mem_stableSubspace_iff_negativeCoord_eq_zero.1 q.2.property
  rw [thicken_apply, map_add, h2, add_zero, negativeCoord_negativeExtend]

/-- **The linear field on the coordinates of negative weight.** At the point of the chart with
coordinates `c` of negative weight and `0` of positive weight, the linear field of the Morse chart
is the image of `c` under the differential of the inverse chart: in the coordinates of negative
weight (weight `-1`) the field reads `c ↦ c`. -/
theorem field_toChart_symm_negativeExtend {c : {i // φ.weight i < 0} → ℝ}
    (hc : φ.negativeExtend c ∈ φ.toChart.target) :
    φ.field (φ.toChart.symm (φ.negativeExtend c)) =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart.symm (φ.negativeExtend c) (φ.negativeExtend c) := by
  have hy := φ.toChart.map_target hc
  have he := φ.mem_maximalAtlas_one
  -- The differential of the chart undoes that of the inverse chart.
  have hinv (w : TangentSpace 𝓘(ℝ, E) (φ.negativeExtend c)) :
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart (φ.toChart.symm (φ.negativeExtend c))
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart.symm (φ.negativeExtend c) w) = w := by
    have heq : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (φ.toChart ∘ φ.toChart.symm) (φ.negativeExtend c) =
        mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) id (φ.negativeExtend c) := by
      refine Filter.EventuallyEq.mfderiv_eq ?_
      filter_upwards [φ.toChart.open_target.mem_nhds hc] with w hw
      exact φ.toChart.right_inv hw
    rw [← mfderiv_comp_apply _ (φ.mdifferentiableAt_toChart hy)
      (mdifferentiableAt_symm_of_mem_maximalAtlas he hc), heq, mfderiv_id]
    rfl
  refine (isInvertible_mfderiv_chart he hy).injective (Eq.trans ?_ (hinv _).symm)
  refine φ.coord.injective (funext fun i ↦ (congrFun (φ.coord_mfderiv_field hy) i).trans ?_)
  rw [φ.toChart.right_inv hc]
  by_cases hi : φ.weight i < 0
  · have hw : φ.weight i = -1 := (φ.weight_eq_neg_one_or_eq_one i).resolve_right
      fun h ↦ by rw [h] at hi; norm_num at hi
    rw [hw]; ring
  · rw [φ.coord_negativeExtend_of_not_weight_neg c hi]; ring

variable [CompleteSpace E] [T2Space M] [IsManifold 𝓘(ℝ, E) 1 M]
  (hX : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent 1 (fun y ↦ (⟨y, X y⟩ : TangentBundle 𝓘(ℝ, E) M)))
  (hXc : IsCompleteVectorField X)

/-- **The time-`θ` flow-out is smooth.** For a smooth complete field `X` and a smooth function
`θ` of the coordinates of negative weight, the map `(c, y) ↦ Φ (θ c) (φ.toChart.symm (c + y))`,
`y` in the stable subspace, is smooth on the open set where `c + y` lies in the chart. -/
theorem contMDiffOn_globalFlow_toChart_symm [IsManifold 𝓘(ℝ, E) ∞ M]
    (hXs : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞ (fun y ↦ (⟨y, X y⟩ : TangentBundle 𝓘(ℝ, E) M)))
    {θ : EuclideanSpace ℝ {i // φ.weight i < 0} → ℝ} (hθ : ContDiff ℝ ∞ θ) :
    ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ {i // φ.weight i < 0} × φ.stableSubspace) 𝓘(ℝ, E) ∞
      (fun q : EuclideanSpace ℝ {i // φ.weight i < 0} × φ.stableSubspace ↦
        globalFlow X hX hXc (θ q.1) (φ.toChart.symm (φ.negativeExtend q.1.ofLp + q.2)))
      {q | φ.negativeExtend q.1.ofLp + q.2 ∈ φ.toChart.target} := by
  have := φ.finiteDimensional
  set T := LinearMap.toContinuousLinearMap φ.thicken
  have hsymm : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ φ.toChart.symm φ.toChart.target :=
    contMDiffOn_symm_of_mem_maximalAtlas φ.mem_maximalAtlas
  have hι : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ {i // φ.weight i < 0} × φ.stableSubspace) 𝓘(ℝ, E) ∞
      (fun q ↦ φ.toChart.symm (T q)) (T ⁻¹' φ.toChart.target) :=
    hsymm.comp T.contMDiff.contMDiffOn fun _ hq ↦ hq
  exact (contMDiff_globalFlow_uncurry hXc le_top hXs).comp_contMDiffOn
    ((hθ.comp contDiff_fst).contMDiff.contMDiffOn.prodMk hι)

/-- **The time-`θ` flow-out is an immersion along the ball.** Let `X` be the linear field of the
Morse chart `φ` on its source, with flow `Φ`, and let `c` be coordinates of negative weight whose
point lies in the chart. If `θ` is differentiable at `c` with `1 + dθ_c(c) > 0`, then the map
`(c', y) ↦ Φ (θ c') (φ.toChart.symm (c' + y))`, `y` in the stable subspace, has injective
differential at `(c, 0)`. -/
theorem injective_mfderiv_globalFlow_toChart_symm (hXφ : ∀ y ∈ φ.toChart.source, X y = φ.field y)
    {θ : EuclideanSpace ℝ {i // φ.weight i < 0} → ℝ} {c : EuclideanSpace ℝ {i // φ.weight i < 0}}
    (hθ : DifferentiableAt ℝ θ c) (hc : φ.negativeExtend c.ofLp ∈ φ.toChart.target)
    (hθc : 0 < 1 + fderiv ℝ θ c c) :
    Injective (mfderiv 𝓘(ℝ, EuclideanSpace ℝ {i // φ.weight i < 0} × φ.stableSubspace) 𝓘(ℝ, E)
      (fun q : EuclideanSpace ℝ {i // φ.weight i < 0} × φ.stableSubspace ↦
        globalFlow X hX hXc (θ q.1) (φ.toChart.symm (φ.negativeExtend q.1.ofLp + q.2)))
      (c, 0)) := by
  have := φ.finiteDimensional
  set T := LinearMap.toContinuousLinearMap φ.thicken
  have hT : ∀ q, T q = φ.negativeExtend q.1.ofLp + q.2 := fun _ ↦ rfl
  have hT0 : T (c, 0) = φ.negativeExtend c.ofLp := by rw [hT]; simp
  have hsymm : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart.symm (T (c, 0)) := by
    rw [hT0]; exact mdifferentiableAt_symm_of_mem_maximalAtlas φ.mem_maximalAtlas_one hc
  have hι : MDifferentiableAt 𝓘(ℝ, _) 𝓘(ℝ, E) (fun q ↦ φ.toChart.symm (T q)) (c, 0) :=
    hsymm.comp (c, 0) T.mdifferentiableAt
  have hτ : HasFDerivAt (θ ∘ Prod.fst) ((fderiv ℝ θ c).comp (ContinuousLinearMap.fst ℝ _ _))
      ((c, 0) : EuclideanSpace ℝ {i // φ.weight i < 0} × φ.stableSubspace) :=
    hθ.hasFDerivAt.comp (c, 0) hasFDerivAt_fst
  refine (injective_iff_map_eq_zero _).2 fun w hw ↦ ?_
  set y := φ.toChart.symm (T (c, 0))
  have h := mfderiv_flowOf_comp_prodMk_apply hX (τ := θ ∘ Prod.fst)
    (f := fun q ↦ φ.toChart.symm (T q)) hτ.differentiableAt.mdifferentiableAt hι
    (hXc.mem_flowDomain _ _) w
  have hτw : mvfderiv 𝓘(ℝ, _) (θ ∘ Prod.fst) (c, 0) w = fderiv ℝ θ c w.1 := by
    rw [mvfderiv_eq_fderiv, hτ.fderiv]
    rfl
  rw [flowOf_eq_globalFlow hX hXc, hτw] at h
  set dΦ := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (globalFlow X hX hXc (θ c)) y
  -- The flow carries `X` to itself, so the differential is `dΦ (dθ(w.1) • X y + dι w)`.
  have hXΦ : dΦ (X y) = X (globalFlow X hX hXc (θ c) y) :=
    mfderiv_globalFlow_apply_self hX hXc (θ c) y
  have hΦ : Injective dΦ := by
    have h := injective_mfderiv_flowOf hX hXc (θ c) y
    rwa [flowOf_eq_globalFlow hX hXc] at h
  have h1 : fderiv ℝ θ c w.1 • X y + mfderiv 𝓘(ℝ, _) 𝓘(ℝ, E)
      (fun q ↦ φ.toChart.symm (T q)) (c, 0) w = 0 := by
    refine hΦ (Eq.trans ?_ (map_zero dΦ).symm)
    refine (dΦ.map_add _ _).trans (Eq.trans ?_ (h.symm.trans hw))
    exact congrArg (· + dΦ (mfderiv 𝓘(ℝ, _) 𝓘(ℝ, E) (fun q ↦ φ.toChart.symm (T q)) (c, 0) w))
      ((dΦ.map_smul _ _).trans (congrArg _ hXΦ))
  have hy : φ.toChart.symm (T (c, 0)) ∈ φ.toChart.source := by
    rw [hT0]; exact φ.toChart.map_target hc
  have hιd : mfderiv 𝓘(ℝ, EuclideanSpace ℝ {i // φ.weight i < 0} × φ.stableSubspace) 𝓘(ℝ, E)
      (fun q ↦ φ.toChart.symm (T q)) (c, 0) w =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart.symm (T (c, 0)) (T w) := by
    have h := mfderiv_comp_apply (c, 0) hsymm T.mdifferentiableAt w
    rw [T.mfderiv_eq] at h
    exact h
  have hf := φ.field_toChart_symm_negativeExtend hc
  have hc' := hc
  rw [← hT0] at hf hc'
  rw [hιd, hXφ _ hy, hf] at h1
  set a := fderiv ℝ θ c w.1
  set D := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart.symm (T (c, 0))
  have h1' : D (a • T (c, 0) + T w) = 0 :=
    (D.map_add _ _).trans ((congrArg (· + D (T w)) (D.map_smul a (T (c, 0)))).trans h1)
  have h2 := (isInvertible_mfderiv_chart_symm φ.mem_maximalAtlas_one hc').injective
    (h1'.trans (map_zero _).symm)
  -- The coordinates of negative weight: `a • c + w.1 = 0`, with `a = dθ(w.1)`.
  have h3 : a • c + w.1 = 0 := by
    have h := congrArg φ.negativeCoord h2
    have e1 : φ.negativeCoord (T (c, 0)) = c.ofLp := φ.negativeCoord_thicken _
    have e2 : φ.negativeCoord (T w) = w.1.ofLp := φ.negativeCoord_thicken _
    rw [map_add, map_smul, e1, e2] at h
    exact WithLp.ofLp_injective 2 (by simpa using h.trans φ.negativeCoord.map_zero)
  have hw1 : w.1 = -(a • c) := eq_neg_iff_add_eq_zero.2 (by rwa [add_comm])
  have ha : a = 0 := by
    have h : a = -(a * fderiv ℝ θ c c) := by
      conv_lhs => rw [show a = fderiv ℝ θ c w.1 from rfl, hw1]
      rw [map_neg, map_smul, smul_eq_mul]
    have h' : a * (1 + fderiv ℝ θ c c) = 0 := by linarith
    exact (mul_eq_zero.1 h').resolve_right hθc.ne'
  have hw1' : w.1 = 0 := by rw [hw1, ha, zero_smul, neg_zero]
  have hw2 : (w.2 : E) = 0 := by
    have h : T w = 0 := (by rw [ha, zero_smul, zero_add] : T w = a • T (c, 0) + T w).trans h2
    replace h := (hT w).symm.trans h
    rw [hw1'] at h
    simpa using h
  exact Prod.ext hw1' (Subtype.ext hw2)

/-- **The time-`θ` flow-out is an open embedding near the ball.** Let `X` be a smooth complete
field equal to the linear field of the Morse chart `φ` on its source, with flow `Φ`, let the closed
Euclidean ball of radius `ρ` in the coordinates of negative weight lie in the chart, and let `θ` be
a smooth function with `1 + dθ_c(c) > 0` on that ball. If `c ↦ Φ (θ c) (φ.toChart.symm c)` is
injective on the ball, then on some open neighbourhood `V` of the ball (with stable component `0`)
inside the domain of the chart, the map `(c, y) ↦ Φ (θ c) (φ.toChart.symm (c + y))` is a smooth
embedding with open image. -/
theorem exists_isSmoothEmbedding_globalFlow_toChart_symm [IsManifold 𝓘(ℝ, E) ∞ M]
    (hXs : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞ (fun y ↦ (⟨y, X y⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hXφ : ∀ y ∈ φ.toChart.source, X y = φ.field y) {ρ : ℝ}
    (hρ : ∀ c : EuclideanSpace ℝ {i // φ.weight i < 0}, ‖c‖ ≤ ρ →
      φ.negativeExtend c.ofLp ∈ φ.toChart.target)
    {θ : EuclideanSpace ℝ {i // φ.weight i < 0} → ℝ} (hθ : ContDiff ℝ ∞ θ)
    (hθρ : ∀ c : EuclideanSpace ℝ {i // φ.weight i < 0}, ‖c‖ ≤ ρ → 0 < 1 + fderiv ℝ θ c c)
    (hinj : InjOn (fun c : EuclideanSpace ℝ {i // φ.weight i < 0} ↦
      globalFlow X hX hXc (θ c) (φ.toChart.symm (φ.negativeExtend c.ofLp)))
      (Metric.closedBall 0 ρ)) :
    ∃ V : TopologicalSpace.Opens (EuclideanSpace ℝ {i // φ.weight i < 0} × φ.stableSubspace),
      Metric.closedBall (0 : EuclideanSpace ℝ {i // φ.weight i < 0}) ρ ×ˢ
        ({0} : Set φ.stableSubspace) ⊆
        (V : Set (EuclideanSpace ℝ {i // φ.weight i < 0} × φ.stableSubspace)) ∧
      (∀ q ∈ V, φ.negativeExtend q.1.ofLp + q.2 ∈ φ.toChart.target) ∧
      Manifold.IsSmoothEmbedding 𝓘(ℝ, EuclideanSpace ℝ {i // φ.weight i < 0} × φ.stableSubspace)
        𝓘(ℝ, E) ∞ (fun q : V ↦
          globalFlow X hX hXc (θ q.val.1)
            (φ.toChart.symm (φ.negativeExtend q.val.1.ofLp + q.val.2))) ∧
      IsOpen (range fun q : V ↦
        globalFlow X hX hXc (θ q.val.1)
          (φ.toChart.symm (φ.negativeExtend q.val.1.ofLp + q.val.2))) := by
  have := φ.finiteDimensional
  set Ψ := fun q : EuclideanSpace ℝ {i // φ.weight i < 0} × φ.stableSubspace ↦
    globalFlow X hX hXc (θ q.1) (φ.toChart.symm (φ.negativeExtend q.1.ofLp + q.2))
  set O := {q : EuclideanSpace ℝ {i // φ.weight i < 0} × φ.stableSubspace |
    φ.negativeExtend q.1.ofLp + q.2 ∈ φ.toChart.target}
  have hO : IsOpen O := φ.toChart.open_target.preimage
    (LinearMap.toContinuousLinearMap φ.thicken).continuous
  have hΨ : ContMDiffOn _ _ ∞ Ψ O := φ.contMDiffOn_globalFlow_toChart_symm hX hXc hXs hθ
  set L := {q | IsLocalDiffeomorphAt
    𝓘(ℝ, EuclideanSpace ℝ {i // φ.weight i < 0} × φ.stableSubspace) 𝓘(ℝ, E) ∞ Ψ q}
  have hL : IsOpen L := isOpen_iff_mem_nhds.2 fun _ hq ↦ IsLocalDiffeomorphAt.eventually hq
  set K := Metric.closedBall (0 : EuclideanSpace ℝ {i // φ.weight i < 0}) ρ ×ˢ
    ({0} : Set φ.stableSubspace)
  have hK : IsCompact K := (isCompact_closedBall _ _).prod isCompact_singleton
  have hmemK {q} (hq : q ∈ K) : ‖q.1‖ ≤ ρ ∧ q = (q.1, 0) := by
    obtain ⟨h1, h2⟩ := hq
    exact ⟨mem_closedBall_zero_iff.1 h1, Prod.ext rfl h2⟩
  have hKO : K ⊆ O := fun q hq ↦ by
    obtain ⟨h1, h2⟩ := hmemK hq
    rw [h2]; simpa [O] using hρ _ h1
  have himm : ∀ q ∈ K, Injective (mfderiv 𝓘(ℝ, _) 𝓘(ℝ, E) Ψ q) := fun q hq ↦ by
    obtain ⟨h1, h2⟩ := hmemK hq
    rw [h2]
    exact φ.injective_mfderiv_globalFlow_toChart_symm hX hXc hXφ
      ((hθ.differentiable (by simp)) _) (hρ _ h1) (hθρ _ h1)
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ {i // φ.weight i < 0} × φ.stableSubspace) =
      Module.finrank ℝ E := by
    rw [Module.finrank_prod, finrank_euclideanSpace, ← Module.finrank_fintype_fun_eq_card (R := ℝ),
      φ.finrank_negativeWeight_fun, add_comm, φ.finrank_stableSubspace_add_manifoldMorseIndex]
  have hKL : K ⊆ L := fun q hq ↦ isLocalDiffeomorphAt_of_injective_mfderiv hΨ hO (hKO hq)
    BoundarylessManifold.isInteriorPoint (by simp) (himm q hq) hdim
  have hinjK : InjOn Ψ K := fun q hq q' hq' h ↦ by
    obtain ⟨h1, h2⟩ := hmemK hq
    obtain ⟨h1', h2'⟩ := hmemK hq'
    rw [h2, h2']
    rw [h2, h2'] at h
    simp only [Ψ, ZeroMemClass.coe_zero, add_zero] at h
    rw [hinj (mem_closedBall_zero_iff.2 h1) (mem_closedBall_zero_iff.2 h1') h]
  obtain ⟨V, hKV, hVO, hV⟩ := exists_isOpen_isSmoothEmbedding_of_injOn (hO.inter hL)
    (hΨ.mono inter_subset_left) hK (subset_inter hKO hKL) hinjK himm
  refine ⟨V, hKV, fun q hq ↦ (hVO hq).1, hV, ?_⟩
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨q, rfl⟩
  -- Near `Ψ q`, the local inverse of `Ψ` at `q` lands in `V`, so `Ψ q` is inside the image.
  have hq : IsLocalDiffeomorphAt _ _ ∞ Ψ q := (hVO q.property).2
  have hnhds : hq.localInverse ⁻¹' V ∈ nhds (Ψ q) := hq.continuousAt_localInverse.preimage_mem_nhds
    (by rw [hq.localInverse_left_inv hq.localInverse_mem_target]
        exact V.isOpen.mem_nhds q.property)
  filter_upwards [hnhds, hq.localInverse_open_source.mem_nhds hq.localInverse_mem_source]
    with y hyV hy
  exact ⟨⟨_, hyV⟩, hq.localInverse_right_inv hy⟩

end MorseChart

end TauCeti

end
