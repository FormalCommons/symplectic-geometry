/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Projectivization.BaseChange
public import SymplecticGeometry.Geometry.Manifold.Projectivization.FubiniStudy.Basic
public import SymplecticGeometry.Geometry.Manifold.Instances.AddCircle
public import SymplecticGeometry.Geometry.Symplectic.Lagrangian.Submersion
public import TauCeti.Geometry.Manifold.Instances.AddCircle.Torus
public import TauCeti.Geometry.Symplectic.Lagrangian.Embedding.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import TauCeti.Geometry.Manifold.Immersion.Differential

/-!
# Lagrangian submanifolds of `ℂPⁿ`

Write `ρ = fubiniStudyLift n` for the pull-back of the Fubini–Study form `ω_FS = fubiniStudyForm n`
to `ℂⁿ⁺¹ ∖ 0` (`FubiniStudy/Basic.lean`). This file gives the two standard Lagrangian
submanifolds of `(ℂPⁿ, ω_FS)`.

* `SymplecticGeometry.isIsotropicMap_mkNonzero_comp_iff`: a map `x ↦ [G x]` into `ℂPⁿ`, for a
  differentiable map `G` into `ℂⁿ⁺¹ ∖ 0`, is isotropic exactly when `ρ` vanishes on the image of
  the derivative of `G`. With `TauCeti.SmoothTwoForm.IsNondegenerate.isIsotropicMap_of_comp`
  (`Geometry/Symplectic/Lagrangian/Submersion.lean`), which checks isotropy after a surjective
  map with surjective derivatives, this reduces both examples to a computation upstairs.
* `SymplecticGeometry.isLagrangianEmbedding_mapProjective_ofReal`: real projective space
  `ℝPⁿ`, embedded by the change of field `Complex.ofRealHom.mapProjective`
  (`Projectivization.isSmoothEmbedding_mapProjective_ofReal`), is a Lagrangian embedding. At a
  real point `x` and real vectors `v, w`, every term of `ρ_x(v, w)` contains `ω₀(a, b)` for real
  `a, b`, which vanishes since the real locus is Lagrangian for `ω₀`
  (`TauCeti.isLagrangian_stdComplexPiSymplecticForm_range_ofReal`).
* `SymplecticGeometry.cliffordTorus n` is the Clifford torus
  `θ ↦ [1 : e^{iθ₁} : ⋯ : e^{iθₙ}]` on `Fin n → AddCircle (2 * π)` (`cliffordTorus_apply`), with
  the lift `cliffordTorusLift n` to `ℂⁿ⁺¹ ∖ 0`. Its image is the set of points with a
  representative whose coordinates all have the same modulus (`range_cliffordTorus`). It is a
  smooth embedding (`isSmoothEmbedding_cliffordTorus`) and a Lagrangian embedding
  (`isLagrangianEmbedding_cliffordTorus`): at `z = (1, e^{iθ})` the derivative of the lift sends
  `a` to `(0, i a_k e^{iθ_k})_k`, whose coordinates are real multiples of `i zⱼ`, so that `ρ`
  vanishes on them.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  Example 4.3.3, p. 168, and Exercises 4.3.4–4.3.5, p. 169.
-/

public section

open Function Manifold TauCeti Projectivization AddCircle
open scoped Manifold ContDiff Real LinearAlgebra.Projectivization

namespace SymplecticGeometry

/-! ### Isotropic maps through `ℂⁿ⁺¹ ∖ 0` -/

section Isotropic

variable {n : ℕ} {F H' N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} [TopologicalSpace N] [ChartedSpace H' N]

/-- A map `x ↦ [G x]` into `ℂPⁿ`, for a differentiable map `G` into `ℂⁿ⁺¹ ∖ 0`, is isotropic for
the Fubini–Study form exactly when `fubiniStudyLift n` vanishes on every pair of tangent vectors in
the image of the derivative of `G`. -/
theorem isIsotropicMap_mkNonzero_comp_iff {G : N → puncturedSpace (Fin (n + 1) → ℂ)}
    (hG : MDifferentiable J 𝓘(ℝ, Fin (n + 1) → ℂ) G) :
    (isSymplectic_fubiniStudyForm n).isNondegenerate.IsIsotropicMap J (mkNonzero ℂ n ∘ G) ↔
      ∀ x (v w : TangentSpace J x), (fubiniStudyLift n).eval₂ (G x)
        (mfderiv J 𝓘(ℝ, Fin (n + 1) → ℂ) G x v) (mfderiv J 𝓘(ℝ, Fin (n + 1) → ℂ) G x w) = 0 := by
  rw [SmoothTwoForm.IsNondegenerate.isIsotropicMap_iff]
  refine forall_congr' fun x ↦ forall_congr' fun v ↦ forall_congr' fun w ↦ ?_
  rw [mfderiv_comp x ((contMDiff_mkNonzero ℂ n 1 _).mdifferentiableAt one_ne_zero) (hG x),
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, comp_apply,
    eval₂_fubiniStudyForm_mfderiv_mkNonzero]

end Isotropic

variable (n : ℕ)

/-! ### Real projective space -/

/-- Real projective space `ℝPⁿ`, embedded in `ℂPⁿ` by the change of field `[x] ↦ [x]`, is a
Lagrangian submanifold for the Fubini–Study form. -/
theorem isLagrangianEmbedding_mapProjective_ofReal :
    (isSymplectic_fubiniStudyForm n).isNondegenerate.IsLagrangianEmbedding 𝓘(ℝ, Fin n → ℝ)
      (Complex.ofRealHom.mapProjective : ℙ ℝ (Fin (n + 1) → ℝ) → ℙ ℂ (Fin (n + 1) → ℂ)) := by
  have he := isSmoothEmbedding_mapProjective_ofReal n
  refine SmoothTwoForm.IsNondegenerate.IsIsotropicMap.isLagrangianEmbedding_of_finrank ?_ he
    (by simp [Module.finrank_pi_fintype, mul_comm])
  refine SmoothTwoForm.IsNondegenerate.isIsotropicMap_of_comp (surjective_mkNonzero ℝ n)
    ((isSubmersion_mkNonzero ℝ n).surjective_mfderiv (by simp))
    ((contMDiff_mkNonzero ℝ n 1).mdifferentiable one_ne_zero) ?_
  rw [mapProjective_ofReal_comp_mkNonzero, isIsotropicMap_mkNonzero_comp_iff
    ((contMDiff_puncturedSpaceOfReal n 1).mdifferentiable one_ne_zero)]
  -- Read the tangent vectors as vectors of `Fin (n + 1) → ℝ`, to apply linear maps to them.
  intro x (v : Fin (n + 1) → ℝ) (w : Fin (n + 1) → ℝ)
  rw [fubiniStudyLift_apply, mfderiv_puncturedSpaceOfReal_apply x v,
    mfderiv_puncturedSpaceOfReal_apply x w]
  set L := ContinuousLinearMap.piMap fun _ : Fin (n + 1) ↦ Complex.ofRealCLM
  -- `ω₀` vanishes on pairs of real vectors.
  have h (a b : Fin (n + 1) → ℝ) : stdComplexPiSymplecticForm (Fin (n + 1)) (L a) (L b) = 0 :=
    isLagrangian_stdComplexPiSymplecticForm_range_ofReal.symplecticForm_apply_eq_zero
      ⟨a, rfl⟩ ⟨b, rfl⟩
  have hx : (puncturedSpaceOfReal n x : Fin (n + 1) → ℂ) = L x := funext fun i ↦ by simp [L]
  beta_reduce at h ⊢
  rw [hx, h, h, h]
  simp

/-! ### The Clifford torus -/

/-- The lift `θ ↦ (1, e^{iθ₁}, …, e^{iθₙ})` of the Clifford torus to `ℂⁿ⁺¹ ∖ 0`: its coordinates are
`AddCircle.toCircle` of those of `Fin.cons 0 θ`. -/
noncomputable def cliffordTorusLift (θ : Fin n → AddCircle (2 * π)) :
    puncturedSpace (Fin (n + 1) → ℂ) :=
  ⟨fun j ↦ (toCircle ((Fin.cons 0 θ : Fin (n + 1) → AddCircle (2 * π)) j) : ℂ),
    mem_puncturedSpace.2 fun h ↦ by simpa using congrFun h 0⟩

variable {n} in
/-- The coordinates of `cliffordTorusLift n θ` are `toCircle` of those of `Fin.cons 0 θ`. -/
@[simp]
theorem coe_cliffordTorusLift (θ : Fin n → AddCircle (2 * π)) :
    (cliffordTorusLift n θ : Fin (n + 1) → ℂ) =
      fun j ↦ (toCircle ((Fin.cons 0 θ : Fin (n + 1) → AddCircle (2 * π)) j) : ℂ) :=
  (rfl)

/-- The Clifford torus `θ ↦ [1 : e^{iθ₁} : ⋯ : e^{iθₙ}]` in `ℂPⁿ`, on the torus
`Fin n → AddCircle (2 * π)`. -/
noncomputable def cliffordTorus (θ : Fin n → AddCircle (2 * π)) : ℙ ℂ (Fin (n + 1) → ℂ) :=
  mkNonzero ℂ n (cliffordTorusLift n θ)

/-- The Clifford torus is the line through its lift to `ℂⁿ⁺¹ ∖ 0`. -/
theorem cliffordTorus_def : cliffordTorus n = mkNonzero ℂ n ∘ cliffordTorusLift n :=
  (rfl)

variable {n} in
/-- The Clifford torus sends `θ` to `[1 : e^{iθ₁} : ⋯ : e^{iθₙ}]`. -/
theorem cliffordTorus_apply (θ : Fin n → AddCircle (2 * π)) :
    cliffordTorus n θ = mk ℂ (Fin.cons 1 fun k ↦ (toCircle (θ k) : ℂ))
      (fun h ↦ one_ne_zero (congrFun h 0)) := by
  rw [cliffordTorus_def, comp_apply, mkNonzero_apply]
  congr 1
  funext j
  cases j using Fin.cases <;> simp

/-- The circle `AddCircle (2 * π)` has positive period, so that it is a smooth manifold. -/
local instance : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩

variable {n} in
/-- The lift of the Clifford torus to `ℂⁿ⁺¹ ∖ 0` is smooth. -/
theorem contMDiff_cliffordTorusLift (r : ℕ∞ω) :
    ContMDiff (ModelWithCorners.pi fun _ : Fin n ↦ 𝓘(ℝ)) 𝓘(ℝ, Fin (n + 1) → ℂ) r
      (cliffordTorusLift n) := by
  refine (TauCeti.ContMDiff.subtypeVal_comp_iff (n := r) _ _).1
    (contMDiff_pi_module_iff.2 fun j ↦ ?_)
  cases j using Fin.cases with
  | zero => simpa [comp_def] using contMDiff_const
  | succ k =>
    simpa [comp_def] using (contMDiff_toCircle r).comp (contMDiff_apply (i := k))

/-- The Clifford torus is smooth. -/
theorem contMDiff_cliffordTorus (r : ℕ∞ω) :
    ContMDiff (ModelWithCorners.pi fun _ : Fin n ↦ 𝓘(ℝ)) 𝓘(ℝ, Fin n → ℂ) r (cliffordTorus n) :=
  (contMDiff_mkNonzero ℂ n r).comp (contMDiff_cliffordTorusLift r)

variable {n} in
/-- Read through the covering map `t ↦ ([tₖ])ₖ` of the torus, the derivative of the lift
`z = cliffordTorusLift n [t]` of the Clifford torus sends `a` to the vector with coordinates
`aⱼ i zⱼ`, where `a` is extended by `a₀ = 0`. -/
theorem mfderiv_cliffordTorusLift_comp_coe_apply (t : Fin n → ℝ)
    (a : TangentSpace 𝓘(ℝ, Fin n → ℝ) t) (j : Fin (n + 1)) :
    (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin (n + 1) → ℂ)
        (cliffordTorusLift n ∘ fun t k ↦ (t k : AddCircle (2 * π))) t a : Fin (n + 1) → ℂ) j =
      ((Fin.cons 0 a : Fin (n + 1) → ℝ) j : ℂ) * Complex.I *
        (cliffordTorusLift n fun k ↦ (t k : AddCircle (2 * π)) : Fin (n + 1) → ℂ) j := by
  set ℓ : Fin (n + 1) → (Fin n → ℝ) →L[ℝ] ℝ := Fin.cons 0 fun k ↦ ContinuousLinearMap.proj k
  have hℓ (s : Fin n → ℝ) (j : Fin (n + 1)) : ℓ j s = (Fin.cons 0 s : Fin (n + 1) → ℝ) j := by
    cases j using Fin.cases <;> simp [ℓ]
  have hval : Subtype.val ∘ cliffordTorusLift n ∘ (fun t k ↦ (t k : AddCircle (2 * π))) =
      fun s j ↦ Complex.exp ((ℓ j s : ℂ) * Complex.I) := by
    funext s j
    cases j using Fin.cases <;>
      simp [ℓ, toCircle_apply_mk, Circle.coe_exp]
  have hd : HasFDerivAt (fun s j ↦ Complex.exp ((ℓ j s : ℂ) * Complex.I))
      (ContinuousLinearMap.pi fun j ↦
        (ℓ j).smulRight (Complex.exp ((ℓ j t : ℂ) * Complex.I) * Complex.I)) t := by
    refine hasFDerivAt_pi.2 fun j ↦ ?_
    have h₁ : HasDerivAt (fun x : ℝ ↦ Complex.exp ((x : ℂ) * Complex.I))
        (Complex.exp ((ℓ j t : ℂ) * Complex.I) * Complex.I) (ℓ j t) := by
      simpa using ((hasDerivAt_id (ℓ j t)).ofReal_comp.mul_const Complex.I).cexp
    refine (h₁.hasFDerivAt.comp t (ℓ j).hasFDerivAt).congr_fderiv ?_
    ext v
    simp [mul_comm]
  have hz := congrFun (congrFun hval t) j
  simp only [comp_apply] at hz
  have hcalc (b : Fin n → ℝ) : (ContinuousLinearMap.pi fun j ↦
      (ℓ j).smulRight (Complex.exp ((ℓ j t : ℂ) * Complex.I) * Complex.I)) b j =
        ((Fin.cons 0 b : Fin (n + 1) → ℝ) j : ℂ) * Complex.I *
          Complex.exp ((ℓ j t : ℂ) * Complex.I) := by
    simp only [ContinuousLinearMap.pi_apply, ContinuousLinearMap.smulRight_apply,
      Complex.real_smul, hℓ]
    ring
  rw [← TauCeti.Manifold.mfderiv_subtype_val_comp_apply, hval, mfderiv_eq_fderiv, hd.fderiv, hz]
  -- The identifications `NormedSpace.fromTangentSpace` of tangent spaces of normed spaces with
  -- the spaces are the identity.
  exact hcalc a

/-- The Clifford torus is injective. -/
theorem injective_cliffordTorus : Injective (cliffordTorus n) := by
  intro θ θ' h
  rw [cliffordTorus_apply, cliffordTorus_apply, mk_eq_mk_iff'] at h
  obtain ⟨c, hc⟩ := h
  have h₀ := congrFun hc 0
  simp only [Pi.smul_apply, Fin.cons_zero, smul_eq_mul, mul_one] at h₀
  funext k
  have hk := congrFun hc k.succ
  simp only [Pi.smul_apply, Fin.cons_succ, smul_eq_mul, h₀, one_mul] at hk
  exact injective_toCircle Real.two_pi_pos.ne' (Circle.ext hk.symm)

/-- The Clifford torus is a smooth embedding of the torus `Fin n → AddCircle (2 * π)` into
`ℂPⁿ`. -/
theorem isSmoothEmbedding_cliffordTorus :
    IsSmoothEmbedding (ModelWithCorners.pi fun _ : Fin n ↦ 𝓘(ℝ)) 𝓘(ℝ, Fin n → ℂ) ∞
      (cliffordTorus n) := by
  have himm : IsImmersion (ModelWithCorners.pi fun _ : Fin n ↦ 𝓘(ℝ)) 𝓘(ℝ, Fin n → ℂ) ∞
      (cliffordTorus n) := by
    refine (contMDiff_cliffordTorus n ∞).isImmersion_of_injective_mfderiv (by simp) fun θ ↦ ?_
    obtain ⟨t, rfl⟩ : ∃ t : Fin n → ℝ, (fun k ↦ (t k : AddCircle (2 * π))) = θ :=
      (Surjective.piMap fun _ ↦ QuotientAddGroup.mk_surjective) θ
    rw [injective_iff_map_eq_zero]
    -- Read the tangent vector as a vector of `Fin n → ℝ`, the tangent space of the covering.
    intro (a : Fin n → ℝ) ha
    have hq := (AddCircle.contMDiff_coe_pi (ι := Fin n) (2 * π) 1).mdifferentiable one_ne_zero
    have hG := ((contMDiff_cliffordTorusLift 1).comp
      (AddCircle.contMDiff_coe_pi (ι := Fin n) (2 * π) 1)).mdifferentiable one_ne_zero
    -- Through the covering map, whose derivative is the identity, `a` is in the kernel of the
    -- derivative of `mkNonzero ℂ n` after that of the lift.
    have e₁ := mfderiv_comp t ((contMDiff_cliffordTorus n 1 _).mdifferentiableAt one_ne_zero)
      (hq t)
    rw [AddCircle.mfderiv_coe_pi, cliffordTorus_def, comp_assoc,
      mfderiv_comp t ((contMDiff_mkNonzero ℂ n 1 _).mdifferentiableAt one_ne_zero) (hG t)] at e₁
    have h₁ : mfderiv 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin n → ℂ) (mkNonzero ℂ n)
        (cliffordTorusLift n fun k ↦ (t k : AddCircle (2 * π)))
        (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin (n + 1) → ℂ)
          (cliffordTorusLift n ∘ fun t k ↦ (t k : AddCircle (2 * π))) t a) = 0 :=
      (DFunLike.congr_fun e₁ a).trans ha
    -- The derivative of the lift, read as a vector of `Fin (n + 1) → ℂ`.
    set u : Fin (n + 1) → ℂ := mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin (n + 1) → ℂ)
        (cliffordTorusLift n ∘ fun t k ↦ (t k : AddCircle (2 * π))) t a
    have h₂ : u ∈ ℂ ∙ (cliffordTorusLift n fun k ↦ (t k : AddCircle (2 * π)) : Fin (n + 1) → ℂ) :=
      (SetLike.ext_iff.1 (ker_mfderiv_mkNonzero (𝕜 := ℂ) _) _).1 h₁
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 h₂
    have hc' (j : Fin (n + 1)) :
        c * (cliffordTorusLift n fun k ↦ (t k : AddCircle (2 * π)) : Fin (n + 1) → ℂ) j =
          ((Fin.cons 0 a : Fin (n + 1) → ℝ) j : ℂ) * Complex.I *
            (cliffordTorusLift n fun k ↦ (t k : AddCircle (2 * π)) : Fin (n + 1) → ℂ) j :=
      (congrFun hc j).trans (mfderiv_cliffordTorusLift_comp_coe_apply t a j)
    have hc₀ := hc' 0
    simp only [coe_cliffordTorusLift, Fin.cons_zero, toCircle_zero, Circle.coe_one, mul_one,
      Complex.ofReal_zero, zero_mul] at hc₀
    funext k
    exact (by simpa [hc₀, Complex.I_ne_zero] using (hc' k.succ).symm : a k = 0)
  exact ⟨himm,
    (himm.contMDiff.continuous.isClosedEmbedding (injective_cliffordTorus n)).isEmbedding⟩

/-- The image of the Clifford torus is the set of points of `ℂPⁿ` with a representative whose
coordinates all have the same modulus. -/
theorem range_cliffordTorus : Set.range (cliffordTorus n) =
    {x | ∃ (v : Fin (n + 1) → ℂ) (hv : v ≠ 0), mk ℂ v hv = x ∧ ∀ i j, ‖v i‖ = ‖v j‖} := by
  ext x
  constructor
  · rintro ⟨θ, rfl⟩
    refine ⟨_, _, (cliffordTorus_apply θ).symm, fun i j ↦ ?_⟩
    cases i using Fin.cases <;> cases j using Fin.cases <;> simp
  · rintro ⟨v, hv, rfl, hnorm⟩
    have h₀ : v 0 ≠ 0 := fun h ↦ hv <| funext fun i ↦ norm_eq_zero.1 <| by
      rw [hnorm i 0, h, norm_zero]
    refine ⟨fun k ↦ ((Complex.arg ((v 0)⁻¹ * v k.succ) : ℝ) : AddCircle (2 * π)), ?_⟩
    rw [cliffordTorus_apply, mk_eq_mk_iff']
    refine ⟨(v 0)⁻¹, funext fun j ↦ ?_⟩
    cases j using Fin.cases with
    | zero => simp [h₀]
    | succ k =>
      have hk : ‖(v 0)⁻¹ * v k.succ‖ = 1 := by
        rw [norm_mul, norm_inv, hnorm k.succ 0, inv_mul_cancel₀ (norm_ne_zero_iff.2 h₀)]
      have h := Complex.norm_mul_exp_arg_mul_I ((v 0)⁻¹ * v k.succ)
      rw [hk, Complex.ofReal_one, one_mul] at h
      simp [toCircle_apply_mk, Circle.coe_exp, h]

/-- The Clifford torus is a Lagrangian submanifold of `ℂPⁿ` for the Fubini–Study form. -/
theorem isLagrangianEmbedding_cliffordTorus :
    (isSymplectic_fubiniStudyForm n).isNondegenerate.IsLagrangianEmbedding
      (ModelWithCorners.pi fun _ : Fin n ↦ 𝓘(ℝ)) (cliffordTorus n) := by
  have he := isSmoothEmbedding_cliffordTorus n
  refine SmoothTwoForm.IsNondegenerate.IsIsotropicMap.isLagrangianEmbedding_of_finrank ?_ he
    (by simp [Module.finrank_pi_fintype, mul_comm])
  refine SmoothTwoForm.IsNondegenerate.isIsotropicMap_of_comp
    (q := fun t : Fin n → ℝ ↦ fun k ↦ (t k : AddCircle (2 * π)))
    (Surjective.piMap fun _ ↦ QuotientAddGroup.mk_surjective)
    (fun t ↦ by rw [AddCircle.mfderiv_coe_pi]; exact surjective_id)
    ((AddCircle.contMDiff_coe_pi (ι := Fin n) (2 * π) 1).mdifferentiable one_ne_zero) ?_
  rw [cliffordTorus_def, comp_assoc, isIsotropicMap_mkNonzero_comp_iff
    (((contMDiff_cliffordTorusLift 1).comp
      (AddCircle.contMDiff_coe_pi (ι := Fin n) (2 * π) 1)).mdifferentiable one_ne_zero)]
  -- Read the tangent vectors as vectors of `Fin n → ℝ`, the tangent space of the covering.
  intro t (a : Fin n → ℝ) (b : Fin n → ℝ)
  -- The derivative of the lift `z` sends `a` to the vector of real multiples `aⱼ • (i zⱼ)`.
  have hu (a : Fin n → ℝ) :
      (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin (n + 1) → ℂ)
        (cliffordTorusLift n ∘ fun t k ↦ (t k : AddCircle (2 * π))) t a : Fin (n + 1) → ℂ) =
        fun j ↦ (Fin.cons 0 a : Fin (n + 1) → ℝ) j • (Complex.I *
          ((cliffordTorusLift n ∘ fun t k ↦ (t k : AddCircle (2 * π))) t : Fin (n + 1) → ℂ) j) :=
    funext fun j ↦ (mfderiv_cliffordTorusLift_comp_coe_apply t a j).trans <| by
      rw [Complex.real_smul, mul_assoc, comp_apply]
  -- `ω₀` vanishes on two such vectors, and `⟨z, ·⟩` on each.
  have hω (z : Fin (n + 1) → ℂ) (α β : Fin (n + 1) → ℝ) : stdComplexPiSymplecticForm (Fin (n + 1))
      (fun j ↦ α j • (Complex.I * z j)) (fun j ↦ β j • (Complex.I * z j)) = 0 := by
    rw [stdComplexPiSymplecticForm_apply]
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    beta_reduce
    simp only [map_smul, LinearMap.smul_apply, stdComplexSymplecticForm.isAlt.self_eq_zero,
      smul_zero]
  have hre (z : Fin (n + 1) → ℂ) (α : Fin (n + 1) → ℝ) :
      (star z ⬝ᵥ fun j ↦ α j • (Complex.I * z j)).re = 0 := by
    rw [dotProduct, Complex.re_sum]
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    simp only [Pi.star_apply, Complex.star_def, Complex.real_smul, Complex.mul_re,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, Complex.mul_im]
    ring
  rw [fubiniStudyLift_apply, hu, hu, hω, hre, hre]
  simp

end SymplecticGeometry

end
