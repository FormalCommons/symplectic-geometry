/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Basic
public import TauCeti.Geometry.Symplectic.Hamiltonian.WeightModel.NormalForm
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Norm.Transitivity
import SymplecticGeometry.Algebra.Order.BigOperators.Ring.Finset
import SymplecticGeometry.Geometry.Symplectic.Complex.CoordinateSpace
import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.WeightModel.Basic
import TauCeti.Analysis.Fourier.AddCircle
import TauCeti.Data.Set.Card
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
* `SymplecticGeometry.prod_weights_eq`: two families of weights at the same point have the same
  product. It is the case `Φ = L' ∘ L⁻¹` of the linear statement
  `SymplecticGeometry.prod_eq_prod_of_intertwines_rotation`: a real-linear automorphism `Φ` of
  `ℂ^ι` that preserves the standard symplectic form `ω₀` and conjugates the rotations with weights
  `k` to those with weights `k'` gives `∏ⱼ kⱼ = ∏ⱼ k'ⱼ`. Differentiating at `t = 0`
  (`SymplecticGeometry.map_mul_I_of_intertwines_rotation`), `Φ` conjugates `z ↦ (i kⱼ zⱼ)ⱼ` to
  `z ↦ (i k'ⱼ zⱼ)ⱼ`. Their determinants `∏ⱼ kⱼ²` and `∏ⱼ k'ⱼ²` agree, which gives the absolute
  values of the products, and `Φ` carries the quadratic form `z ↦ ω₀(z, (i kⱼ zⱼ)ⱼ)`, which is
  `Σⱼ kⱼ |zⱼ|²`, to the one for `k'`, so by Sylvester's law of inertia
  (`QuadraticForm.sigNeg_of_equiv_weightedSumSquares`) both families have as many negative
  weights, which gives the signs.

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

section Linear

variable {ι : Type*} [Fintype ι]

open QuadraticMap QuadraticForm

omit [Fintype ι] in
variable [Finite ι] in
/-- If a real-linear map `Φ` of `ℂ^ι` carries the rotation `z ↦ (e^{2π i kⱼ t} zⱼ)ⱼ` to
`z ↦ (e^{2π i k'ⱼ t} zⱼ)ⱼ` for every real `t`, then it carries `z ↦ (i kⱼ zⱼ)ⱼ` to
`z ↦ (i k'ⱼ zⱼ)ⱼ`: these are the derivatives at `t = 0`, divided by `2π`. -/
theorem map_mul_I_of_intertwines_rotation {k k' : ι → ℝ} (Φ : (ι → ℂ) →L[ℝ] (ι → ℂ))
    (hrot : ∀ (t : ℝ) v, Φ (fun j ↦ Complex.exp (2 * π * k j * t * Complex.I) * v j) =
      fun j ↦ Complex.exp (2 * π * k' j * t * Complex.I) * Φ v j) (v : ι → ℂ) :
    Φ (fun j ↦ (k j * Complex.I) * v j) = fun j ↦ (k' j * Complex.I) * Φ v j := by
  have := Fintype.ofFinite ι
  have hd (k : ι → ℝ) (v : ι → ℂ) : HasDerivAt
      (fun t : ℝ ↦ fun j ↦ Complex.exp (2 * π * k j * t * Complex.I) * v j)
      ((2 * π : ℝ) • fun j ↦ (k j * Complex.I) * v j) 0 := by
    refine hasDerivAt_pi.2 fun j ↦ ?_
    have := (((hasDerivAt_id (0 : ℝ)).ofReal_comp.const_mul (2 * π * k j : ℂ)).mul_const
      Complex.I).cexp.mul_const (v j)
    convert this using 1
    · ext t; simp [mul_assoc]
    · simp; ring
  have h₁ := Φ.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hd k v)
  rw [show (Φ ∘ _) = _ from funext fun t ↦ hrot t v] at h₁
  have h := h₁.unique (hd k' (Φ v))
  simpa [map_smul, Real.pi_ne_zero] using h

/-- **The product of the weights is determined by the rotations.** Let `Φ` be a real-linear
automorphism of `ℂ^ι` that preserves the standard symplectic form `ω₀` and conjugates the rotation
`z ↦ (e^{2π i kⱼ t} zⱼ)ⱼ` to `z ↦ (e^{2π i k'ⱼ t} zⱼ)ⱼ` for every real `t`. Then
`∏ⱼ kⱼ = ∏ⱼ k'ⱼ`. -/
theorem prod_eq_prod_of_intertwines_rotation {k k' : ι → ℝ} (Φ : (ι → ℂ) ≃L[ℝ] (ι → ℂ))
    (hω : ∀ v w, stdComplexPiSymplecticForm ι (Φ v) (Φ w) = stdComplexPiSymplecticForm ι v w)
    (hrot : ∀ (t : ℝ) v, Φ (fun j ↦ Complex.exp (2 * π * k j * t * Complex.I) * v j) =
      fun j ↦ Complex.exp (2 * π * k' j * t * Complex.I) * Φ v j) :
    ∏ j, k j = ∏ j, k' j := by
  classical
  have hJ (v : ι → ℂ) : Φ (fun j ↦ (k j * Complex.I) * v j) = fun j ↦ (k' j * Complex.I) * Φ v j :=
    map_mul_I_of_intertwines_rotation (Φ : (ι → ℂ) →L[ℝ] (ι → ℂ)) hrot v
  refine Finset.prod_eq_prod_of_abs_eq ?_ ?_
  · -- The determinant of `z ↦ (i kⱼ zⱼ)ⱼ` is `∏ⱼ kⱼ²`, and `Φ` conjugates the two maps.
    have hdet (k : ι → ℝ) : LinearMap.det
        ((Matrix.diagonal fun j ↦ (k j * Complex.I : ℂ)).toLin'.restrictScalars ℝ) =
          ∏ j, k j ^ 2 := by
      rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Matrix.det_diagonal,
        Algebra.norm_complex_apply, map_prod]
      simp [Complex.normSq_mul, _root_.sq]
    have hconj : (Φ.toLinearEquiv : (ι → ℂ) →ₗ[ℝ] (ι → ℂ)) ∘ₗ
        (Matrix.diagonal fun j ↦ (k j * Complex.I : ℂ)).toLin'.restrictScalars ℝ ∘ₗ
          (Φ.toLinearEquiv.symm : (ι → ℂ) →ₗ[ℝ] (ι → ℂ)) =
        (Matrix.diagonal fun j ↦ (k' j * Complex.I : ℂ)).toLin'.restrictScalars ℝ := by
      refine LinearMap.ext fun v ↦ ?_
      have hdiag (d w : ι → ℂ) : (Matrix.diagonal d).mulVec w = fun j ↦ d j * w j :=
        funext fun j ↦ Matrix.mulVec_diagonal d w j
      simpa [hdiag] using hJ (Φ.symm v)
    have h := LinearMap.det_conj
      ((Matrix.diagonal fun j ↦ (k j * Complex.I : ℂ)).toLin'.restrictScalars ℝ) Φ.toLinearEquiv
    rw [hconj, hdet, hdet, Finset.prod_pow, Finset.prod_pow] at h
    exact (sq_eq_sq_iff_abs_eq_abs _ _).1 h.symm
  · -- By Sylvester's law of inertia, both counts are half the negative index of
    -- `z ↦ ω₀(z, (i kⱼ zⱼ)ⱼ)`, which `Φ` carries to `z ↦ ω₀(z, (i k'ⱼ zⱼ)ⱼ)`.
    -- The real coordinates `(Re zⱼ)ⱼ ⊔ (Im zⱼ)ⱼ` of `ℂ^ι`.
    obtain ⟨C, hC⟩ : ∃ C : (ι → ℂ) ≃ₗ[ℝ] (ι ⊕ ι → ℝ),
        ∀ v, C v = (complexToRealEuclidean ι v).ofLp :=
      ⟨(complexToRealEuclidean ι).toLinearEquiv.trans (WithLp.linearEquiv 2 ℝ _), fun _ ↦ by simp⟩
    let e : (weightedSumSquares ℝ (Sum.elim k' k')).IsometryEquiv
        (weightedSumSquares ℝ (Sum.elim k k)) :=
      { (C.symm.trans Φ.toLinearEquiv.symm).trans C with
        map_app' x := by
          obtain ⟨u, rfl⟩ : ∃ u, C (Φ u) = x :=
            ⟨Φ.symm (C.symm x), by rw [Φ.apply_symm_apply, C.apply_symm_apply]⟩
          simp only [LinearEquiv.toFun_eq_coe, LinearEquiv.trans_apply,
            LinearEquiv.symm_apply_apply, ContinuousLinearEquiv.coe_symm_toLinearEquiv,
            ContinuousLinearEquiv.symm_apply_apply]
          rw [hC, hC, weightedSumSquares_complexToRealEuclidean,
            weightedSumSquares_complexToRealEuclidean,
            ← stdComplexPiSymplecticForm_apply_ofReal_mul_I_mul,
            ← stdComplexPiSymplecticForm_apply_ofReal_mul_I_mul, ← hJ, hω] }
    have h := sigNeg_of_equiv_weightedSumSquares ⟨e⟩
    rw [sigNeg_weightedSumSquares, Set.ncard_setOf_sumElim k' (· < 0),
      Set.ncard_setOf_sumElim k (· < 0)] at h
    rw [← Set.ncard_coe_finset, ← Set.ncard_coe_finset]
    simpa using (Nat.eq_of_mul_eq_mul_left two_pos h).symm

end Linear

/-- **The product of the weights at a fixed point is well defined.** Two families of weights `k`
and `k'` of the circle action at the same point `p`, realized as in `IsTangentWeights` by
isomorphisms `L` and `L'`, have the same product: `∏ⱼ kⱼ = ∏ⱼ k'ⱼ`. -/
theorem prod_weights_eq {p : M} {k k' : Fin n → ℤ} {L L' : TangentSpace I p ≃L[ℝ] (Fin n → ℂ)}
    (h : IsTangentWeights σ p k L) (h' : IsTangentWeights σ p k' L') :
    ∏ j, k j = ∏ j, k' j := by
  have key := prod_eq_prod_of_intertwines_rotation (k := fun j ↦ (k j : ℝ))
    (k' := fun j ↦ (k' j : ℝ)) (L.symm.trans L') (fun v w ↦ ?_) (fun t v ↦ ?_)
  · exact_mod_cast key
  · simp only [ContinuousLinearEquiv.trans_apply]
    refine (h'.1 _ _).symm.trans ((h.1 _ _).trans ?_)
    rw [L.apply_symm_apply, L.apply_symm_apply]
  · obtain ⟨u, rfl⟩ := L.surjective v
    simp only [ContinuousLinearEquiv.trans_apply, Complex.ofReal_intCast]
    rw [← h.2 t u, L.symm_apply_apply]
    exact (congrArg L' (L.symm_apply_apply _)).trans (h'.2 t u)

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
