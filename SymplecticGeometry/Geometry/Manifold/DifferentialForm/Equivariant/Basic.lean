/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Algebra.GradedMonoid
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Interior
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Wedge.Smooth.Graded
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.BoundarylessStokes
public import TauCeti.Geometry.Manifold.DifferentialForm.LieDeriv
public import TauCeti.Geometry.Manifold.DifferentialForm.Squared
public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Leibniz

/-!
# The Cartan differential

Smooth forms of mixed degree are the direct sum `⨁ k, SmoothForm I M ℝ k`, a ring under the wedge
by `TauCeti.SmoothForm.gRing`. For a smooth vector field `X` and a real parameter `ħ`, this file
defines the Cartan differential `d_ħ = d - ħ ι_X` on them, the differential of the Cartan model of
equivariant cohomology for the flow of `X`. The vector field is arbitrary: invariance of a form is
the vanishing of its Lie derivative along `X`, which for the fundamental vector field of a group
action follows from invariance under the group by Tau Ceti's
`TauCeti.mlieDerivForm_fundamentalVectorField_eq_zero`. A form `β` is equivariantly closed when
`cartanDiff X hX ħ β = 0`; no predicate is defined for this.

## Main definitions

* `SymplecticGeometry.mixedExtDeriv I M`: the exterior derivative on forms of mixed degree.
* `SymplecticGeometry.mixedInterior X`: the interior product with a smooth vector field on forms of
  mixed degree, zero on functions.
* `SymplecticGeometry.cartanDiff X hX ħ`: the Cartan differential `d - ħ ι_X`.

## Main results

* `SymplecticGeometry.cartanDiff_of_zero`, `SymplecticGeometry.cartanDiff_of_succ`: its values on
  homogeneous forms, and `SymplecticGeometry.cartanDiff_zero_param`: at `ħ = 0` it is `d`.
* `SymplecticGeometry.cartanDiff_of_mul`: the graded Leibniz rule for a homogeneous left factor,
  and `SymplecticGeometry.cartanDiff_mul_of_even`: `d_ħ` is a derivation on products whose left
  factor has only components of even degree.
* `SymplecticGeometry.cartanDiff_cartanDiff`: `d_ħ² = -ħ L_X` on homogeneous forms, from Cartan's
  formula `TauCeti.mlieDerivForm_eq_interior_mextDeriv_add`; so
  `SymplecticGeometry.cartanDiff_cartanDiff_of_mlieDerivForm_eq_zero`: `d_ħ² = 0` on forms whose
  components have zero Lie derivative along `X`.
* `SymplecticGeometry.integralTopForm_cartanDiff_eq_zero`: on a compact boundaryless manifold the
  top component of `d_ħ γ` is exact, so its integral vanishes, by Tau Ceti's Stokes theorem
  `TauCeti.integralTopForm_mextDeriv_eq_zero`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §5.6.
* N. Berline, E. Getzler and M. Vergne, *Heat Kernels and Dirac Operators*, Grundlehren der
  mathematischen Wissenschaften 298, Springer, 1992, §7.1.
-/

public section

noncomputable section

open scoped ContDiff Manifold DirectSum

open TauCeti

namespace SymplecticGeometry

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {k l : ℕ}

section

variable [IsManifold I 2 M]

variable (I M) in
/-- The exterior derivative on smooth forms of mixed degree: on a form of degree `k` it is
`mextDerivₗ I k`, with values in degree `k + 1`. -/
def mixedExtDeriv : (⨁ k, SmoothForm I M ℝ k) →ₗ[ℝ] ⨁ k, SmoothForm I M ℝ k :=
  DirectSum.toModule ℝ ℕ _ fun k ↦
    (DirectSum.lof ℝ ℕ (fun k ↦ SmoothForm I M ℝ k) (k + 1)).comp (mextDerivₗ I k)

/-- The exterior derivative of a homogeneous form of mixed degree. -/
@[simp]
theorem mixedExtDeriv_of (φ : SmoothForm I M ℝ k) :
    mixedExtDeriv I M (DirectSum.of (fun k ↦ SmoothForm I M ℝ k) k φ) =
      DirectSum.of _ (k + 1) (mextDerivₗ I k φ) := by
  rw [← DirectSum.lof_eq_of ℝ, mixedExtDeriv, DirectSum.toModule_lof, LinearMap.comp_apply,
    DirectSum.lof_eq_of]

/-- The interior product with a smooth vector field on smooth forms of mixed degree: it is `0` on
functions, and `interiorProduct X` on forms of degree `k + 1`. -/
def mixedInterior (X : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯) :
    (⨁ k, SmoothForm I M ℝ k) →ₗ[ℝ] ⨁ k, SmoothForm I M ℝ k :=
  DirectSum.toModule ℝ ℕ _ fun k ↦ match k with
    | 0 => 0
    | k + 1 => (DirectSum.lof ℝ ℕ (fun k ↦ SmoothForm I M ℝ k) k).comp
        (SmoothForm.interiorProduct X)

/-- The interior product of a function, as a form of mixed degree, is zero. -/
@[simp]
theorem mixedInterior_of_zero (X : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯)
    (f : SmoothForm I M ℝ 0) :
    mixedInterior X (DirectSum.of (fun k ↦ SmoothForm I M ℝ k) 0 f) = 0 := by
  rw [← DirectSum.lof_eq_of ℝ, mixedInterior, DirectSum.toModule_lof, LinearMap.zero_apply]

/-- The interior product of a homogeneous form of degree `k + 1`, as a form of mixed degree. -/
@[simp]
theorem mixedInterior_of_succ (X : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯)
    (φ : SmoothForm I M ℝ (k + 1)) :
    mixedInterior X (DirectSum.of (fun k ↦ SmoothForm I M ℝ k) (k + 1) φ) =
      DirectSum.of _ k (SmoothForm.interiorProduct X φ) := by
  rw [← DirectSum.lof_eq_of ℝ, mixedInterior, DirectSum.toModule_lof, LinearMap.comp_apply,
    DirectSum.lof_eq_of]

/-- The exterior derivative of forms of mixed degree squares to zero. -/
@[simp]
theorem mixedExtDeriv_mixedExtDeriv (γ : ⨁ k, SmoothForm I M ℝ k) :
    mixedExtDeriv I M (mixedExtDeriv I M γ) = 0 := by
  induction γ using DirectSum.induction_on with
  | zero => simp
  | of k φ =>
    rw [mixedExtDeriv_of, mixedExtDeriv_of, ← LinearMap.comp_apply,
      mextDerivₗ_comp_mextDerivₗ, LinearMap.zero_apply, map_zero]
  | add γ δ hγ hδ => simp [hγ, hδ]

/-- The interior product of forms of mixed degree squares to zero. -/
@[simp]
theorem mixedInterior_mixedInterior (X : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯)
    (γ : ⨁ k, SmoothForm I M ℝ k) :
    mixedInterior X (mixedInterior X γ) = 0 := by
  induction γ using DirectSum.induction_on with
  | zero => simp
  | of k φ =>
    rcases k with _ | _ | k
    · simp
    · simp
    · simp
  | add γ δ hγ hδ => simp [hγ, hδ]

/-- The graded Leibniz rule for the exterior derivative of forms of mixed degree, for a
homogeneous left factor of degree `k`. -/
theorem mixedExtDeriv_of_mul (φ : SmoothForm I M ℝ k) (β : ⨁ k, SmoothForm I M ℝ k) :
    mixedExtDeriv I M (DirectSum.of (fun k ↦ SmoothForm I M ℝ k) k φ * β) =
      mixedExtDeriv I M (DirectSum.of _ k φ) * β +
        (-1 : ℝ) ^ k • (DirectSum.of _ k φ * mixedExtDeriv I M β) := by
  induction β using DirectSum.induction_on with
  | zero => simp
  | of l ψ =>
    simp only [mixedExtDeriv_of, SmoothForm.of_mul_of_eq_of_wedge, SmoothForm.mextDerivₗ_wedge,
      map_add, DirectSum.of_smul, DirectSum.of_linearEquivCast]
  | add β δ hβ hδ =>
    simp only [mul_add, map_add, hβ, hδ, smul_add]
    abel

/-- The interior product of the wedge of a form of degree `k + 1` with a function. -/
private theorem mixedInterior_of_mul_of_zero (X : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯)
    (φ : SmoothForm I M ℝ (k + 1)) (f : SmoothForm I M ℝ 0) :
    mixedInterior X (DirectSum.of (fun k ↦ SmoothForm I M ℝ k) (k + 1) φ * DirectSum.of _ 0 f) =
      mixedInterior X (DirectSum.of _ (k + 1) φ) * DirectSum.of _ 0 f := by
  rw [SmoothForm.of_mul_of_eq_of_wedge, mixedInterior_of_succ, mixedInterior_of_succ,
    SmoothForm.of_mul_of_eq_of_wedge]
  congr 1
  ext x v
  simp

/-- The graded Leibniz rule for the interior product of forms of mixed degree, for a homogeneous
left factor of degree `k`. -/
theorem mixedInterior_of_mul (X : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯)
    (φ : SmoothForm I M ℝ k) (β : ⨁ k, SmoothForm I M ℝ k) :
    mixedInterior X (DirectSum.of (fun k ↦ SmoothForm I M ℝ k) k φ * β) =
      mixedInterior X (DirectSum.of _ k φ) * β +
        (-1 : ℝ) ^ k • (DirectSum.of _ k φ * mixedInterior X β) := by
  induction β using DirectSum.induction_on with
  | zero => simp
  | of l ψ =>
    have h0 : Even 0 := ⟨0, rfl⟩
    rcases k with _ | k
    · rw [(SmoothForm.commute_of_of_of_even h0 φ ψ).eq, mixedInterior_of_zero, zero_mul,
        zero_add, pow_zero, one_smul]
      rcases l with _ | l
      · rw [mixedInterior_of_zero, mul_zero, SmoothForm.of_mul_of_eq_of_wedge]
        -- The degree `0 + 0` of the wedge is `0` by definition.
        exact mixedInterior_of_zero X _
      · rw [mixedInterior_of_mul_of_zero, mixedInterior_of_succ,
          (SmoothForm.commute_of_of_of_even h0 φ _).eq]
    · rcases l with _ | l
      · rw [mixedInterior_of_mul_of_zero, mixedInterior_of_zero, mul_zero, smul_zero, add_zero]
      · rw [SmoothForm.of_mul_of_eq_of_wedge, mixedInterior_of_succ, mixedInterior_of_succ,
          SmoothForm.of_mul_of_eq_of_wedge, SmoothForm.of_mul_of_eq_of_wedge]
        -- The degree `k + 1 + (l + 1)` of the wedge is `k + 1 + l + 1` by definition.
        erw [mixedInterior_of_succ (k := k + 1 + l)]
        rw [SmoothForm.interiorProduct_wedge, map_add, DirectSum.of_linearEquivCast,
          DirectSum.of_smul]
  | add β δ hβ hδ =>
    simp only [mul_add, map_add, hβ, hδ, smul_add]
    abel

/-- Cartan's formula `d ι_X + ι_X d = L_X` on a homogeneous form of mixed degree. -/
theorem mixedExtDeriv_mixedInterior_add (X : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯)
    (φ : SmoothForm I M ℝ k) :
    mixedExtDeriv I M (mixedInterior X (DirectSum.of (fun k ↦ SmoothForm I M ℝ k) k φ)) +
        mixedInterior X (mixedExtDeriv I M (DirectSum.of _ k φ)) =
      DirectSum.of _ k ⟨mlieDerivForm X φ.val,
        SmoothForm.mlieDerivForm_mem_smoothBundleForms φ X.contMDiff⟩ := by
  rcases k with _ | k
  · rw [mixedInterior_of_zero, map_zero, zero_add, mixedExtDeriv_of, mixedInterior_of_succ]
    congr 1
    refine Subtype.ext ?_
    rw [SmoothForm.coe_interiorProduct, mextDerivₗ_apply]
    exact (mlieDerivForm_eq_interior_mextDeriv _ _).symm
  · rw [mixedInterior_of_succ, mixedExtDeriv_of, mixedExtDeriv_of, mixedInterior_of_succ,
      ← map_add]
    congr 1
    refine Subtype.ext ?_
    rw [Submodule.coe_add, SmoothForm.coe_interiorProduct, mextDerivₗ_apply, mextDerivₗ_apply,
      SmoothForm.coe_interiorProduct]
    exact (add_comm _ _).trans (SmoothForm.mlieDerivForm_eq_interior_mextDeriv_add
      (X.contMDiff.mdifferentiable (by simp))).symm

/-- The Cartan differential `d_ħ = d - ħ ι_X` on smooth forms of mixed degree, for a smooth
vector field `X` and a real parameter `ħ`. -/
def cartanDiff (X : (x : M) → TangentSpace I x)
    (hX : ContMDiff I I.tangent ∞ (fun x ↦ (X x : TangentBundle I M))) (ħ : ℝ) :
    (⨁ k, SmoothForm I M ℝ k) →ₗ[ℝ] ⨁ k, SmoothForm I M ℝ k :=
  mixedExtDeriv I M - ħ • mixedInterior ⟨X, hX⟩

variable {X : (x : M) → TangentSpace I x}
  {hX : ContMDiff I I.tangent ∞ (fun x ↦ (X x : TangentBundle I M))} {ħ : ℝ}

theorem cartanDiff_def :
    cartanDiff X hX ħ = mixedExtDeriv I M - ħ • mixedInterior ⟨X, hX⟩ :=
  (rfl)

/-- The Cartan differential of a function is its exterior derivative. -/
@[simp]
theorem cartanDiff_of_zero (f : SmoothForm I M ℝ 0) :
    cartanDiff X hX ħ (DirectSum.of (fun k ↦ SmoothForm I M ℝ k) 0 f) =
      DirectSum.of _ 1 (mextDerivₗ I 0 f) := by
  rw [cartanDiff_def, LinearMap.sub_apply, LinearMap.smul_apply, mixedExtDeriv_of,
    mixedInterior_of_zero, smul_zero, sub_zero]

/-- The Cartan differential of a homogeneous form of degree `k + 1`: `dφ - ħ ι_X φ`. -/
@[simp]
theorem cartanDiff_of_succ (φ : SmoothForm I M ℝ (k + 1)) :
    cartanDiff X hX ħ (DirectSum.of (fun k ↦ SmoothForm I M ℝ k) (k + 1) φ) =
      DirectSum.of _ (k + 2) (mextDerivₗ I (k + 1) φ) -
        ħ • DirectSum.of _ k (SmoothForm.interiorProduct ⟨X, hX⟩ φ) := by
  rw [cartanDiff_def, LinearMap.sub_apply, LinearMap.smul_apply, mixedExtDeriv_of,
    mixedInterior_of_succ]

/-- At `ħ = 0` the Cartan differential is the exterior derivative. -/
@[simp]
theorem cartanDiff_zero_param : cartanDiff X hX 0 = mixedExtDeriv I M := by
  rw [cartanDiff_def, zero_smul, sub_zero]

/-- The graded Leibniz rule for the Cartan differential, for a homogeneous left factor of
degree `k`: `d_ħ (φ β) = d_ħ φ β + (-1) ^ k φ d_ħ β`. -/
theorem cartanDiff_of_mul (φ : SmoothForm I M ℝ k) (β : ⨁ k, SmoothForm I M ℝ k) :
    cartanDiff X hX ħ (DirectSum.of (fun k ↦ SmoothForm I M ℝ k) k φ * β) =
      cartanDiff X hX ħ (DirectSum.of _ k φ) * β +
        (-1 : ℝ) ^ k • (DirectSum.of _ k φ * cartanDiff X hX ħ β) := by
  simp only [cartanDiff_def, LinearMap.sub_apply, LinearMap.smul_apply, mixedExtDeriv_of_mul,
    mixedInterior_of_mul, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_sub,
    smul_add, smul_comm ħ ((-1 : ℝ) ^ k)]
  abel

/-- The Cartan differential is a derivation on products whose left factor has only components of
even degree: `d_ħ (α β) = d_ħ α β + α d_ħ β`. -/
theorem cartanDiff_mul_of_even {α : ⨁ k, SmoothForm I M ℝ k} (hα : ∀ k, Odd k → α k = 0)
    (β : ⨁ k, SmoothForm I M ℝ k) :
    cartanDiff X hX ħ (α * β) = cartanDiff X hX ħ α * β + α * cartanDiff X hX ħ β := by
  classical
  rw [← DirectSum.sum_support_of α]
  simp only [Finset.sum_mul, map_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rcases Nat.even_or_odd k with hk | hk
  · rw [cartanDiff_of_mul, hk.neg_one_pow, one_smul]
  · rw [hα k hk, map_zero, zero_mul, map_zero, zero_mul, zero_mul, add_zero]

/-- The square of the Cartan differential on a homogeneous form is `-ħ` times the Lie derivative
along `X`: `d_ħ² φ = -ħ L_X φ`. -/
theorem cartanDiff_cartanDiff (φ : SmoothForm I M ℝ k) :
    cartanDiff X hX ħ (cartanDiff X hX ħ (DirectSum.of (fun k ↦ SmoothForm I M ℝ k) k φ)) =
      -ħ • DirectSum.of _ k ⟨mlieDerivForm X φ.val,
        SmoothForm.mlieDerivForm_mem_smoothBundleForms φ hX⟩ := by
  -- The field of the bundled section `⟨X, hX⟩` is `X` by definition.
  have h : mixedExtDeriv I M
        (mixedInterior ⟨X, hX⟩ (DirectSum.of (fun k ↦ SmoothForm I M ℝ k) k φ)) +
      mixedInterior ⟨X, hX⟩ (mixedExtDeriv I M (DirectSum.of (fun k ↦ SmoothForm I M ℝ k) k φ)) =
      DirectSum.of _ k ⟨mlieDerivForm X φ.val,
        SmoothForm.mlieDerivForm_mem_smoothBundleForms φ hX⟩ :=
    mixedExtDeriv_mixedInterior_add ⟨X, hX⟩ φ
  simp only [cartanDiff_def, LinearMap.sub_apply, LinearMap.smul_apply, map_sub, map_smul,
    mixedExtDeriv_mixedExtDeriv, mixedInterior_mixedInterior, smul_zero, sub_zero, zero_sub]
  rw [← h]
  module

/-- The Cartan differential squares to zero on forms of mixed degree each of whose components
has zero Lie derivative along `X`. -/
theorem cartanDiff_cartanDiff_of_mlieDerivForm_eq_zero {γ : ⨁ k, SmoothForm I M ℝ k}
    (hγ : ∀ k, mlieDerivForm X (γ k).val = 0) :
    cartanDiff X hX ħ (cartanDiff X hX ħ γ) = 0 := by
  classical
  rw [← DirectSum.sum_support_of γ]
  simp only [map_sum]
  refine Finset.sum_eq_zero fun k _ ↦ ?_
  rw [cartanDiff_cartanDiff]
  have : (⟨mlieDerivForm X (γ k).val,
      SmoothForm.mlieDerivForm_mem_smoothBundleForms (γ k) hX⟩ : SmoothForm I M ℝ k) = 0 :=
    Subtype.ext (hγ k)
  rw [this, map_zero, smul_zero]

/-- The component of degree `m + 1` of the exterior derivative of a form of mixed degree is the
exterior derivative of its component of degree `m`. -/
@[simp]
theorem mixedExtDeriv_apply_succ (γ : ⨁ k, SmoothForm I M ℝ k) (m : ℕ) :
    mixedExtDeriv I M γ (m + 1) = mextDerivₗ I m (γ m) := by
  classical
  induction γ using DirectSum.induction_on with
  | zero => simp
  | of k φ =>
    rw [mixedExtDeriv_of]
    by_cases h : k = m
    · subst h
      rw [DirectSum.of_eq_same, DirectSum.of_eq_same]
    · rw [DirectSum.of_eq_of_ne _ _ _ (by omega), DirectSum.of_eq_of_ne _ _ _ (Ne.symm h), map_zero]
  | add γ δ hγ hδ => simp [hγ, hδ]

/-- The exterior derivative of a form of mixed degree has no component of degree `0`. -/
@[simp]
theorem mixedExtDeriv_apply_zero (γ : ⨁ k, SmoothForm I M ℝ k) :
    mixedExtDeriv I M γ 0 = 0 := by
  classical
  induction γ using DirectSum.induction_on with
  | zero => simp
  | of k φ => rw [mixedExtDeriv_of, DirectSum.of_eq_of_ne _ _ _ (by omega)]
  | add γ δ hγ hδ => simp [hγ, hδ]

/-- The component of degree `m` of the interior product of a form of mixed degree is the interior
product of its component of degree `m + 1`. -/
@[simp]
theorem mixedInterior_apply (X : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯)
    (γ : ⨁ k, SmoothForm I M ℝ k) (m : ℕ) :
    mixedInterior X γ m = SmoothForm.interiorProduct X (γ (m + 1)) := by
  classical
  induction γ using DirectSum.induction_on with
  | zero => simp
  | of k φ =>
    rcases k with _ | k
    · rw [mixedInterior_of_zero, DirectSum.zero_apply, DirectSum.of_eq_of_ne _ _ _ (by omega),
        map_zero]
    · rw [mixedInterior_of_succ]
      by_cases h : k = m
      · subst h
        rw [DirectSum.of_eq_same, DirectSum.of_eq_same]
      · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm h), DirectSum.of_eq_of_ne _ _ _ (by omega),
          map_zero]
  | add γ δ hγ hδ => simp [hγ, hδ]

end

/-- **Stokes' theorem for the Cartan differential.** On a compact boundaryless manifold of
dimension `m`, the top component of `d_ħ γ` integrates to zero against every orientation, since it
is the exterior derivative of the component of `γ` of degree `m - 1`. -/
theorem integralTopForm_cartanDiff_eq_zero [FiniteDimensional ℝ E] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] [BoundarylessManifold I M] {X : (x : M) → TangentSpace I x}
    {hX : ContMDiff I I.tangent ∞ (fun x ↦ (X x : TangentBundle I M))} {ħ : ℝ} {m : ℕ}
    (o : Manifold.Orientation I M (Fin m)) (γ : ⨁ k, SmoothForm I M ℝ k) :
    integralTopForm o (cartanDiff X hX ħ γ m).val = 0 := by
  obtain ⟨l, rfl⟩ := o.exists_lift
  have hm : Module.finrank ℝ E < m + 1 := by
    rw [← l.card_eq, Fintype.card_fin]
    omega
  have hι : SmoothForm.interiorProduct ⟨X, hX⟩ (γ (m + 1)) = 0 := by
    rw [SmoothForm.eq_zero_of_finrank_lt hm (γ (m + 1)), map_zero]
  rcases m with _ | m
  · rw [cartanDiff_def, LinearMap.sub_apply, LinearMap.smul_apply, DirectSum.sub_apply,
      DirectSum.smul_apply, mixedExtDeriv_apply_zero, mixedInterior_apply, hι, smul_zero,
      sub_zero, Submodule.coe_zero, integralTopForm_zero]
  · rw [cartanDiff_def, LinearMap.sub_apply, LinearMap.smul_apply, DirectSum.sub_apply,
      DirectSum.smul_apply, mixedExtDeriv_apply_succ, mixedInterior_apply, hι, smul_zero,
      sub_zero, mextDerivₗ_apply]
    exact integralTopForm_mextDeriv_eq_zero _ ((γ m).isSmoothForm.of_le (by simp))
      (isClosed_tsupport _).isCompact

end SymplecticGeometry

end
