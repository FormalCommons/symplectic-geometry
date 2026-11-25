/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Mixed
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.BoundarylessStokes

/-!
# The Cartan differential

Smooth forms of mixed degree are the direct sum `⨁ k, SmoothForm I M ℝ k`, a ring under the wedge
by `TauCeti.SmoothForm.gRing`, with the exterior derivative `SymplecticGeometry.mixedExtDeriv` and
the interior product `SymplecticGeometry.mixedInterior` of `DifferentialForm/Mixed.lean`. For a
smooth vector field `X` and a real parameter `ħ`, this file defines the Cartan differential
`d_ħ = d - ħ ι_X` on them, the differential of the Cartan model of equivariant cohomology for the
flow of `X`. The vector field is arbitrary: invariance of a form is the vanishing of its Lie
derivative along `X`, which for the fundamental vector field of a group action follows from
invariance under the group by Tau Ceti's `TauCeti.mlieDerivForm_fundamentalVectorField_eq_zero`.
A form `β` is equivariantly closed when `cartanDiff X hX ħ β = 0`; no predicate is defined for
this.

## Main definitions

* `SymplecticGeometry.cartanDiff X hX ħ`: the Cartan differential `d - ħ ι_X`.

## Main results

* `SymplecticGeometry.cartanDiff_of_zero`, `SymplecticGeometry.cartanDiff_of_succ`: its values on
  homogeneous forms, `SymplecticGeometry.cartanDiff_apply_zero`,
  `SymplecticGeometry.cartanDiff_apply_succ`: its components, and
  `SymplecticGeometry.cartanDiff_zero_param`: at `ħ = 0` it is `d`.
* `SymplecticGeometry.cartanDiff_of_mul`: the graded Leibniz rule for a homogeneous left factor,
  and `SymplecticGeometry.cartanDiff_mul_of_even`: `d_ħ` is a derivation on products whose left
  factor has only components of even degree, and `SymplecticGeometry.cartanDiff_of_pow_succ`: the
  power rule for a homogeneous form of even degree.
* `SymplecticGeometry.cartanDiff_cartanDiff`: `d_ħ² = -ħ L_X` on homogeneous forms, from Cartan's
  formula `SymplecticGeometry.mixedExtDeriv_mixedInterior_add`; so
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

/-- The component of degree `0` of the Cartan differential of a form of mixed degree is `-ħ` times
the interior product of its component of degree `1`. -/
@[simp]
theorem cartanDiff_apply_zero (γ : ⨁ k, SmoothForm I M ℝ k) :
    cartanDiff X hX ħ γ 0 = -(ħ • SmoothForm.interiorProduct ⟨X, hX⟩ (γ 1)) := by
  rw [cartanDiff_def, LinearMap.sub_apply, LinearMap.smul_apply, DirectSum.sub_apply,
    DirectSum.smul_apply, mixedExtDeriv_apply_zero, mixedInterior_apply, zero_sub]

/-- The component of degree `m + 1` of the Cartan differential of a form of mixed degree is
`d (γ m) - ħ ι_X (γ (m + 2))`. -/
@[simp]
theorem cartanDiff_apply_succ (γ : ⨁ k, SmoothForm I M ℝ k) (m : ℕ) :
    cartanDiff X hX ħ γ (m + 1) =
      mextDerivₗ I m (γ m) - ħ • SmoothForm.interiorProduct ⟨X, hX⟩ (γ (m + 2)) := by
  rw [cartanDiff_def, LinearMap.sub_apply, LinearMap.smul_apply, DirectSum.sub_apply,
    DirectSum.smul_apply, mixedExtDeriv_apply_succ, mixedInterior_apply]

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

/-- The power rule for the Cartan differential of a homogeneous form `φ` of even degree:
`d_ħ φ ^ (n + 1) = (n + 1) φ ^ n d_ħ φ`. -/
theorem cartanDiff_of_pow_succ (hk : Even k) (φ : SmoothForm I M ℝ k) (n : ℕ) :
    cartanDiff X hX ħ (DirectSum.of (fun k ↦ SmoothForm I M ℝ k) k φ ^ (n + 1)) =
      ((n + 1 : ℕ) : ℝ) • (DirectSum.of _ k φ ^ n * cartanDiff X hX ħ (DirectSum.of _ k φ)) := by
  set T := DirectSum.of (fun k ↦ SmoothForm I M ℝ k) k φ
  have hT : Commute T (cartanDiff X hX ħ T) := SmoothForm.commute_of_of_even hk φ _
  induction n with
  | zero => rw [pow_one, pow_zero, one_mul, Nat.cast_one, one_smul]
  | succ n ih =>
    rw [pow_succ', cartanDiff_of_mul, ih, hk.neg_one_pow, one_smul, mul_smul_comm, ← mul_assoc,
      ← pow_succ', ← (hT.pow_left (n + 1)).eq]
    push_cast
    module

/-- The square of the Cartan differential on a homogeneous form is `-ħ` times the Lie derivative
along `X`: `d_ħ² φ = -ħ L_X φ`. -/
theorem cartanDiff_cartanDiff (φ : SmoothForm I M ℝ k) :
    cartanDiff X hX ħ (cartanDiff X hX ħ (DirectSum.of (fun k ↦ SmoothForm I M ℝ k) k φ)) =
      -ħ • DirectSum.of _ k (SmoothForm.lieDeriv ⟨X, hX⟩ φ) := by
  simp only [cartanDiff_def, LinearMap.sub_apply, LinearMap.smul_apply, map_sub, map_smul,
    mixedExtDeriv_mixedExtDeriv, mixedInterior_mixedInterior, smul_zero, sub_zero, zero_sub]
  rw [← mixedExtDeriv_mixedInterior_add]
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
  have : SmoothForm.lieDeriv ⟨X, hX⟩ (γ k) = 0 :=
    Subtype.ext <| by
      rw [SmoothForm.coe_lieDeriv, ContMDiffSection.coeFn_mk, hγ k, Submodule.coe_zero]
  rw [cartanDiff_cartanDiff, this, map_zero, smul_zero]

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
  · rw [cartanDiff_apply_zero, hι, smul_zero, neg_zero, Submodule.coe_zero,
      integralTopForm_zero]
  · rw [cartanDiff_apply_succ, hι, smul_zero, sub_zero, mextDerivₗ_apply]
    exact integralTopForm_mextDeriv_eq_zero _ ((γ m).isSmoothForm.of_le (by simp))
      (isClosed_tsupport _).isCompact

end SymplecticGeometry

end
