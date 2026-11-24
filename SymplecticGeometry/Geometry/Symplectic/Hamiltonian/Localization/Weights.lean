/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.GroupAction.Circle
public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.WeightModel.NormalForm
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Topology.DiscreteSubset
public import TauCeti.Topology.Algebra.ConstMulAction

/-!
# Weights of a circle action at a fixed point

Let the circle act on a symplectic manifold `(M, σ)`, with parameters of period one, so that
`t : ℝ` acts by `Circle.exp (2 * π * t)`. At a fixed point `p` the derivatives of the action form
a representation of the circle on `T_p M` that preserves `σ_p`. Its *weights* are integers
`k₀, …, k_{n-1}` for which `T_p M` is identified with `ℂⁿ`, carrying `σ_p` to the standard
symplectic form and the action of `t` to `zⱼ ↦ e^{2π i kⱼ t} zⱼ`.

## Main definitions

* `SymplecticGeometry.IsTangentWeights σ p k L`: the real-linear isomorphism
  `L : T_p M ≃ ℂⁿ` carries `σ_p` to `TauCeti.stdComplexPiSymplecticForm (Fin n)` and the
  derivative at `p` of the action of `Circle.exp (2 * π * t)` to the diagonal rotation with
  weights `k`, for every real `t`.

## Main results

* `SymplecticGeometry.exists_weights`: for a symplectic circle action with a moment map, every
  fixed point has weights. They come from the weight chart
  `SymplecticGeometry.exists_weightChart` of `WeightModel/NormalForm.lean`: `L` is the inverse of
  the chart's derivative at `0`, read in complex coordinates, and the weights are the chart's
  weights evaluated at the period-one generator `circlePeriodOneGenerator`, which are integers.
* `SymplecticGeometry.finite_fixedPoints`: a continuous action on a compact Hausdorff space whose
  fixed points are isolated has finitely many fixed points.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §5.6
* N. Berline, E. Getzler and M. Vergne, *Heat Kernels and Dirac Operators*, Grundlehren der
  mathematischen Wissenschaften 298, Springer, 1992, §7.2
-/

public section

noncomputable section

open Real Filter Topology
open scoped Manifold ContDiff

namespace SymplecticGeometry

open TauCeti

section Weights

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [MulAction Circle M] {σ : SmoothTwoForm I M} {n : ℕ}

variable (σ) in
/-- `k : Fin n → ℤ` are weights of the circle action at `p`, realized by the real-linear
isomorphism `L : T_p M ≃ ℂⁿ`: `L` carries `σ_p` to the standard symplectic form
`stdComplexPiSymplecticForm (Fin n)` of `ℂⁿ`, and for every `t : ℝ` it carries the derivative at
`p` of `x ↦ Circle.exp (2 * π * t) • x` to `z ↦ (e^{2π i kⱼ t} zⱼ)ⱼ`. -/
def IsTangentWeights (p : M) (k : Fin n → ℤ) (L : TangentSpace I p ≃L[ℝ] (Fin n → ℂ)) :
    Prop :=
  (∀ v w, σ.eval₂ p v w = stdComplexPiSymplecticForm (Fin n) (L v) (L w)) ∧
    ∀ (t : ℝ) v, L (mfderiv I I (fun x : M ↦ Circle.exp (2 * π * t) • x) p v) =
      fun j ↦ Complex.exp (2 * π * k j * t * Complex.I) * L v j

theorem isTangentWeights_iff {p : M} {k : Fin n → ℤ} {L : TangentSpace I p ≃L[ℝ] (Fin n → ℂ)} :
    IsTangentWeights σ p k L ↔
      (∀ v w, σ.eval₂ p v w = stdComplexPiSymplecticForm (Fin n) (L v) (L w)) ∧
        ∀ (t : ℝ) v, L (mfderiv I I (fun x : M ↦ Circle.exp (2 * π * t) • x) p v) =
          fun j ↦ Complex.exp (2 * π * k j * t * Complex.I) * L v j :=
  Iff.rfl

variable [FiniteDimensional ℝ E] [I.Boundaryless] [ContMDiffSMul (𝓡 1) I ∞ Circle M]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

/-- **Weights at a fixed point.** Let the circle act smoothly on a symplectic manifold `(M, σ)`
of dimension `2n` without boundary, preserving `σ`, with a moment map `μ` in the sign
`d⟨μ, ξ⟩ = -ι_{ξ_M} σ`. Then every fixed point `p` has weights `k : Fin n → ℤ`, realized by a
real-linear isomorphism `L : T_p M ≃ ℂⁿ` as in `IsTangentWeights`. -/
theorem exists_weights [Fact (Module.finrank ℝ E = 2 * n)]
    {μ : M → Module.Dual ℝ (GroupLieAlgebra (𝓡 1) Circle)}
    (hμ : σ.IsMomentMap (InfinitesimalAction.fundamental (𝓡 1) Circle I M) fun x ↦ -μ x)
    (hσ : σ.IsSymplectic)
    (hinv : ∀ g : Circle, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := 𝓡 1) g) σ = σ)
    {p : M} (hp : p ∈ MulAction.fixedPoints Circle M) :
    ∃ (k : Fin n → ℤ) (L : TangentSpace I p ≃L[ℝ] (Fin n → ℂ)), IsTangentWeights σ p k L := by
  obtain ⟨m, χ, α, Φ, r, hχ, hαℤ, hr, hsrc, hΦ0, -, hequiv, hform, -⟩ :=
    exists_weightChart hμ hσ hinv hp
  have h0 : (0 : StdSpace (Fin m)) ∈ Φ.source := by rw [hsrc]; exact Metric.mem_ball_self hr
  subst hΦ0
  have hloc := PartialDiffeomorph.isLocalDiffeomorphAt _ _ _ Φ h0
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  -- The derivative of the chart at `0`, an isomorphism onto `T_p M`.
  let D : StdSpace (Fin m) ≃L[ℝ] TangentSpace I (Φ 0) :=
    hloc.mfderivToContinuousLinearEquiv hn
  have hD (a : StdSpace (Fin m)) : D a = mfderiv 𝓘(ℝ, StdSpace (Fin m)) I Φ 0 a :=
    DFunLike.congr_fun (hloc.mfderivToContinuousLinearEquiv_coe hn) a
  obtain rfl : m = n := by
    have h := D.toLinearEquiv.finrank_eq
    rw [finrank_stdSpace, Fintype.card_fin] at h
    have h' : Module.finrank ℝ E = 2 * n := Fact.out
    -- `TangentSpace I (Φ 0)` is `E` by definition.
    change 2 * m = Module.finrank ℝ E at h
    omega
  set C := complexToRealEuclidean (Fin m)
  -- The weights, read at the period-one generator.
  choose k hk using fun j ↦ hαℤ j circlePeriodOneGenerator
    (mulInvariantExp_circlePeriodOneGenerator)
  refine ⟨k, D.symm.trans C.symm, fun v w ↦ ?_, fun t v ↦ ?_⟩
  · have h := hform 0 h0 (D.symm v) (D.symm w)
    rw [← hD, ← hD, D.apply_symm_apply, D.apply_symm_apply] at h
    rw [h, ← stdForm_complexToRealEuclidean]
    simp [C]
  · set g := Circle.exp (2 * π * t)
    have hχg (j : Fin m) : (χ j g : ℂ) = Complex.exp (2 * π * k j * t * Complex.I) := by
      have h := hχ j (t • circlePeriodOneGenerator)
      -- `α j` is a functional on the model space of the Lie algebra; apply its linearity there.
      have hs : α j (t • circlePeriodOneGenerator) = t * k j := by
        rw [← hk j]; exact (α j).map_smul t (circlePeriodOneGenerator : EuclideanSpace ℝ (Fin 1))
      rw [mulInvariantExp_smul_circlePeriodOneGenerator, hs] at h
      rw [h, Circle.coe_exp]
      push_cast; ring_nf
    -- The action of `g` in the chart: multiplication by `χ g` in complex coordinates.
    let rot : (Fin m → ℂ) →L[ℂ] (Fin m → ℂ) := ContinuousLinearMap.pi fun j ↦
      (χ j g : ℂ) • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin m ↦ ℂ) j
    let R : StdSpace (Fin m) →L[ℝ] StdSpace (Fin m) :=
      (C : (Fin m → ℂ) →L[ℝ] StdSpace (Fin m)).comp
        ((rot.restrictScalars ℝ).comp (C.symm : StdSpace (Fin m) →L[ℝ] (Fin m → ℂ)))
    have hR (z : StdSpace (Fin m)) : R z = C (fun j ↦ (χ j g : ℂ) * C.symm z j) := by
      simp [R, rot]
    have hsmooth : MDifferentiableAt I I (fun x : M ↦ g • x) (Φ 0) :=
      (ContMDiffSMul.contMDiff_const_smul (I := 𝓡 1) (n := ∞) g).mdifferentiableAt (by simp)
    have hΦd : MDifferentiableAt 𝓘(ℝ, StdSpace (Fin m)) I Φ 0 := hloc.mdifferentiableAt hn
    -- `Φ ∘ R = (g • ·) ∘ Φ` near `0`.
    have heq : (fun x : M ↦ g • x) ∘ Φ =ᶠ[𝓝 0] Φ ∘ R := by
      filter_upwards [Φ.open_source.mem_nhds h0] with z hz
      have hCz : C (C.symm z) = z := C.apply_symm_apply z
      have h := (hequiv g (C.symm z) (by rw [hCz]; exact hz)).2
      rw [hCz] at h
      rw [Function.comp_apply, Function.comp_apply, hR, h]
    have hcomp := (hsmooth.hasMFDerivAt.comp 0 hΦd.hasMFDerivAt).congr_of_eventuallyEq heq.symm
    have hR0 : HasMFDerivAt 𝓘(ℝ, StdSpace (Fin m)) 𝓘(ℝ, StdSpace (Fin m)) R 0 R :=
      R.hasMFDerivAt
    have hΦR : HasMFDerivAt 𝓘(ℝ, StdSpace (Fin m)) I Φ (R 0)
        (mfderiv 𝓘(ℝ, StdSpace (Fin m)) I Φ 0) := by
      rw [map_zero]; exact hΦd.hasMFDerivAt
    have hcomp' := (HasMFDerivAt.mfderiv (hΦR.comp 0 hR0)).symm.trans (HasMFDerivAt.mfderiv hcomp)
    have hv : mfderiv I I (fun x : M ↦ g • x) (Φ 0) v = D (R (D.symm v)) := by
      -- `T_{g • p} M` and `T_p M` are both `E`; the chain rule is stated between them.
      have h := DFunLike.congr_fun hcomp' (D.symm v)
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply] at h
      exact (congrArg (mfderiv I I (fun x : M ↦ g • x) (Φ 0)) (D.apply_symm_apply v).symm).trans
        h.symm
    rw [hv, ContinuousLinearEquiv.trans_apply, D.symm_apply_apply, hR, C.symm_apply_apply]
    exact funext fun j ↦ by rw [hχg, ContinuousLinearEquiv.trans_apply]

end Weights

/-- If the fixed points of a continuous action on a compact Hausdorff space are isolated, there
are finitely many of them. -/
theorem finite_fixedPoints {G X : Type*} [Monoid G] [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [MulAction G X] [ContinuousConstSMul G X]
    (hiso : ∀ p ∈ MulAction.fixedPoints G X, ∀ᶠ x in 𝓝[≠] p, x ∉ MulAction.fixedPoints G X) :
    (MulAction.fixedPoints G X).Finite :=
  isClosed_fixedPoints_of_continuousConstSMul.isCompact.finite <|
    isDiscrete_iff_nhdsNE.2 fun p hp ↦ inf_principal_eq_bot.2 (hiso p hp)

end SymplecticGeometry

end
