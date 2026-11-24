/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Basic
public import TauCeti.Geometry.Symplectic.Hamiltonian.WeightModel.NormalForm
import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.WeightModel.Basic
import TauCeti.Analysis.Fourier.AddCircle
import TauCeti.Geometry.Manifold.GroupAction.TangentRepresentation
import TauCeti.Geometry.Symplectic.Manifold.Invariants

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

* `SymplecticGeometry.exists_weights`: for a circle action preserving a nondegenerate two-form,
  every fixed point has weights. They come from the linear weight normal form
  `TauCeti.SymplecticForm.exists_continuousLinearEquiv_weightRotation`, applied to the tangent
  representation at the fixed point: its characters are integer powers of the circle
  (`ContinuousMonoidHom.existsUnique_circle_eq_zpow`), and its coordinates are read in `ℂⁿ`
  through `complexToRealEuclidean`. The first step follows the proof of Tau Ceti's
  `TauCeti.SmoothTwoForm.IsNondegenerate.exists_continuousLinearEquiv_mfderiv_smul`, for the
  circle.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §5.6
* N. Berline, E. Getzler and M. Vergne, *Heat Kernels and Dirac Operators*, Grundlehren der
  mathematischen Wissenschaften 298, Springer, 1992, §7.2
-/

public section

noncomputable section

open Real
open scoped Manifold ContDiff

namespace SymplecticGeometry

open TauCeti

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

variable [FiniteDimensional ℝ E] [ContMDiffSMul (𝓡 1) I ∞ Circle M]

/-- **Weights at a fixed point.** Let the circle act smoothly on a manifold `M` of dimension `2n`,
preserving a nondegenerate two-form `σ`. Then every fixed point `p` has weights `k : Fin n → ℤ`,
realized by a real-linear isomorphism `L : T_p M ≃ ℂⁿ` as in `IsTangentWeights`. -/
theorem exists_weights [Fact (Module.finrank ℝ E = 2 * n)] (hσ : σ.IsNondegenerate)
    (hinv : ∀ g : Circle, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := 𝓡 1) g) σ = σ)
    {p : M} (hp : p ∈ MulAction.fixedPoints Circle M) :
    ∃ (k : Fin n → ℤ) (L : TangentSpace I p ≃L[ℝ] (Fin n → ℂ)), IsTangentWeights σ p k L := by
  have hd : ∀ g ∈ MulAction.stabilizer Circle p, MDifferentiableAt I I (fun y : M ↦ g • y) p :=
    fun g _ ↦ (ContMDiffSMul.contMDiff_const_smul (I := 𝓡 1) (n := ∞) g).mdifferentiableAt
      (by simp)
  -- The tangent representation at `p`, read as a representation of the whole circle.
  let ρ : ContRepresentation ℝ Circle E :=
    .ofMonoidHom ((tangentRepresentation hd).toMonoidHom.comp
      (MonoidHom.codRestrict (MonoidHom.id Circle) (MulAction.stabilizer Circle p)
        fun g ↦ MulAction.mem_stabilizer_iff.2 (hp g)))
  have hρ (g : Circle) : ρ g = mfderiv I I (fun y : M ↦ g • y) p :=
    tangentRepresentation_apply hd _
  have hω (g : Circle) (u v : E) :
      hσ.symplecticFormAt p (ρ g u) (ρ g v) = hσ.symplecticFormAt p u v :=
    -- The invariance lemma is stated for actions by individually smooth maps.
    have : ContMDiffConstSMul I ∞ Circle M := ⟨ContMDiffSMul.contMDiff_const_smul (I := 𝓡 1)⟩
    hσ.symplecticFormAt_tangentRepresentation (fun g _ ↦ hinv g) hd ⟨g, hp g⟩ u v
  -- `σ_p`, as a symplectic form on the model space `E = T_p M`.
  let ωₚ : SymplecticForm E := hσ.symplecticFormAt p
  obtain ⟨m, χ, L₀, hL₀, hρL₀⟩ := SymplecticForm.exists_continuousLinearEquiv_weightRotation ωₚ ρ
      ((continuous_tangentRepresentation (𝓡 1) hd).comp (continuous_id.subtype_mk _)) hω
  obtain rfl : n = m := by
    have h := L₀.toLinearEquiv.finrank_eq
    rw [Module.finrank_prod, finrank_euclideanSpace_fin] at h
    have h' : Module.finrank ℝ E = 2 * n := Fact.out
    omega
  -- The weights: each character of the circle is an integer power.
  choose k hk using fun j ↦ (χ j).existsUnique_circle_eq_zpow.exists
  set A := EuclideanSpace.sumEquivProd (𝕜 := ℝ) (ι := Fin n) (κ := Fin n)
  set C := complexToRealEuclidean (Fin n)
  -- `L` is `L₀` followed by the identification of `ℝⁿ × ℝⁿ` with `ℂⁿ`, read on `T_p M = E`.
  obtain ⟨L, hL⟩ : ∃ L : TangentSpace I p ≃L[ℝ] (Fin n → ℂ), ∀ v, L v = C.symm (A.symm (L₀ v)) :=
    ⟨(L₀.trans A.symm).trans C.symm, fun _ ↦ rfl⟩
  have hform (u w : E) : stdComplexPiSymplecticForm (Fin n) (C.symm (A.symm (L₀ u)))
      (C.symm (A.symm (L₀ w))) = ωₚ u w := by
    rw [← stdForm_complexToRealEuclidean, C.apply_symm_apply, C.apply_symm_apply,
      ← isSymplectomorphism_sumEquivProd.apply]
    simp only [ContinuousLinearEquiv.coe_toLinearEquiv]
    rw [A.apply_symm_apply, A.apply_symm_apply]
    exact hL₀ u w
  have hrot (t : ℝ) (u : E) : C.symm (A.symm (L₀ (ρ (Circle.exp (2 * π * t)) u))) =
      fun j ↦ Complex.exp (2 * π * k j * t * Complex.I) * C.symm (A.symm (L₀ u)) j := by
    have hu : L₀ u = A (C (C.symm (A.symm (L₀ u)))) := by simp
    conv_lhs => rw [hρL₀, hu, weightRotation_sumEquivProd_complexToRealEuclidean,
      A.symm_apply_apply, C.symm_apply_apply]
    funext j
    rw [← Circle.coe_exp, Circle.exp_arg, hk j, Circle.coe_zpow, Circle.coe_exp,
      ← Complex.exp_intCast_mul]
    push_cast; ring_nf
  -- Tangent vectors at `p` and at `g • p` are vectors of `E` by definition, so `hform` and `hL`
  -- apply to them as they stand.
  refine ⟨k, L, fun v w ↦ ?_, fun t v ↦ ?_⟩
  · rw [hL, hL, ← SmoothTwoForm.IsNondegenerate.symplecticFormAt_apply hσ]
    exact (hform v w).symm
  · calc L (mfderiv I I (fun x : M ↦ Circle.exp (2 * π * t) • x) p v)
        = C.symm (A.symm (L₀ (ρ (Circle.exp (2 * π * t)) v))) := by rw [hρ]; exact hL _
      _ = _ := hrot t v
      _ = _ := by rw [hL]

end SymplecticGeometry

end
