/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Algebra.GradedMonoid
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Interior
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Wedge.Smooth.Graded
public import TauCeti.Geometry.Manifold.DifferentialForm.LieDeriv
public import TauCeti.Geometry.Manifold.DifferentialForm.Squared
public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Leibniz

/-!
# Exterior calculus on forms of mixed degree

Smooth forms of mixed degree are the direct sum `⨁ k, SmoothForm I M ℝ k`, a ring under the
wedge by `TauCeti.SmoothForm.gRing`. This file extends the exterior derivative `mextDerivₗ` and
the interior product `SmoothForm.interiorProduct` with a smooth vector field to them, degree by
degree, and proves the identities of the Cartan calculus for these extensions.

## Main definitions

* `SymplecticGeometry.mixedExtDeriv I M`: the exterior derivative on forms of mixed degree.
* `SymplecticGeometry.mixedInterior X`: the interior product with a smooth vector field on forms of
  mixed degree, zero on functions.

## Main results

* `SymplecticGeometry.mixedExtDeriv_of`, `SymplecticGeometry.mixedInterior_of_zero`,
  `SymplecticGeometry.mixedInterior_of_succ`: their values on homogeneous forms, and
  `SymplecticGeometry.mixedExtDeriv_apply_succ`, `SymplecticGeometry.mixedExtDeriv_apply_zero`,
  `SymplecticGeometry.mixedInterior_apply`: their components.
* `SymplecticGeometry.mixedExtDeriv_mixedExtDeriv` and
  `SymplecticGeometry.mixedInterior_mixedInterior`: both square to zero.
* `SymplecticGeometry.mixedExtDeriv_of_mul`, `SymplecticGeometry.mixedInterior_of_mul`: the graded
  Leibniz rules for a homogeneous left factor.
* `SymplecticGeometry.mixedExtDeriv_mixedInterior_add`: Cartan's formula `d ι_X + ι_X d = L_X` on
  homogeneous forms, from Tau Ceti's `TauCeti.mlieDerivForm_eq_interior_mextDeriv_add` and, in
  degree `0`, `TauCeti.mlieDerivForm_eq_interior_mextDeriv`.

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
    rcases k with _ | _ | k <;> simp
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


end SymplecticGeometry

end
