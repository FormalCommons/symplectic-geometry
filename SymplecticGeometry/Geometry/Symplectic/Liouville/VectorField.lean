/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.Linearization
public import TauCeti.Geometry.Symplectic.Liouville.VectorField
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.LieDeriv
import TauCeti.Geometry.Manifold.VectorField.Chart.Linearization
import TauCeti.Geometry.Manifold.DifferentialForm.LieDeriv

/-!
# Liouville vector fields: pullback along related fields, linearization at a zero, linear fields

Let `Φ : M' → M` be a smooth map, `σ` a smooth two-form on `M` and `X` a Liouville vector field
of `σ`. If a vector field `Y` on `M'` is `Φ`-related to `X`, that is `dΦ_x (Y x) = X (Φ x)` for
every `x`, then `Y` is a Liouville vector field of `Φ^* σ`
(`TauCeti.IsLiouvilleVectorField.mpullback`). The form need not be closed, the differential of
`Φ` need not be invertible, and the models are arbitrary models with corners, so this applies
for instance to the inclusion of a regular sublevel set, a manifold with boundary, into the
ambient manifold.

The proof applies the naturality of the Lie derivative along related fields,
`TauCeti.mpullback_mlieDerivForm_of_related`: `Φ^* (L_X σ) = L_Y (Φ^* σ)`.

At a zero `p` of a Liouville vector field `Z` of a two-form `σ`, the condition `L_Z σ = σ`, read
at `p`, says that the linearization `A` of `Z` (Tau Ceti's `TauCeti.sectionLinearization`)
satisfies `σ_p (A u, v) + σ_p (u, A v) = σ_p (u, v)`
(`TauCeti.IsLiouvilleVectorField.apply_sectionLinearization_add`). The Lie derivative at a zero
of the field involves only the derivative of the field (`TauCeti.mlieDerivForm_apply_of_eq_zero`),
so no regularity of `Z` or `σ` is needed.

On a finite-dimensional real normed space `V`, with a linear symplectic form `σ` seen as a
constant form, a linear vector field `x ↦ A x` is Liouville as soon as
`σ (A u) v + σ u (A v) = σ u v` for all `u`, `v`
(`TauCeti.SymplecticForm.isLiouvilleVectorField_constSmooth`). Since the form is constant, its
Lie derivative along the field involves only the derivative `A` of the field. For linear fields
this is the converse of `TauCeti.IsLiouvilleVectorField.apply_sectionLinearization_add`, read at
the zero `0`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §3.5
  (Liouville vector fields)
* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  §11.1, where Liouville fields are defined by `L_X ω = ω`. The identity at a zero is the
  derivative at `t = 0` of `e^t ω_p (v, w) = ω_p (e^{tA} v, e^{tA} w)`, the expansion of `ω_p`
  by the linearized flow in the proof of Proposition 11.9 (a). The radial field of
  Example 11.12 (1) and the field of Example 11.18 are linear Liouville fields
-/

public section

open scoped Manifold ContDiff

namespace TauCeti

variable {E H M E' H' M' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H}
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  [TopologicalSpace M'] [ChartedSpace H' M'] {I' : ModelWithCorners ℝ E' H'}
  [IsManifold I 2 M] [IsManifold I' 2 M']

/-- **Liouville fields pull back along related fields.** Let `Φ : M' → M` be smooth, `σ` a
smooth two-form on `M`, and `X` a `C¹` Liouville vector field of `σ`. A differentiable vector
field `Y` on `M'` with `dΦ_x (Y x) = X (Φ x)` for every `x` is a Liouville vector field of the
pulled-back form `Φ^* σ`. No invertibility of `dΦ` is assumed, and `M'` may have a
boundary. -/
theorem IsLiouvilleVectorField.mpullback {Φ : M' → M} (hΦ : ContMDiff I' I ∞ Φ)
    {σ : SmoothForm I M ℝ 2} {X : (x : M) → TangentSpace I x}
    (hX : ContMDiff I I.tangent 1 (fun y ↦ (X y : TangentBundle I M)))
    (hXσ : IsLiouvilleVectorField σ.val X) {Y : (x : M') → TangentSpace I' x}
    (hY : MDifferentiable I' I'.tangent (fun y ↦ (Y y : TangentBundle I' M')))
    (hXY : ∀ x, mfderiv I' I Φ x (Y x) = X (Φ x)) :
    IsLiouvilleVectorField (SmoothForm.mpullback Φ hΦ σ).val Y := by
  rw [isLiouvilleVectorField_iff, SmoothForm.coe_mpullback,
    ← mpullback_mlieDerivForm_of_related (k := 2) (hΦ.of_le (by simp))
      (σ.isSmoothForm.of_le (by simp)) hX hY hXY, isLiouvilleVectorField_iff.mp hXσ]

section Linearization

variable {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [I.Boundaryless] [IsManifold I 1 N]

/-- **The linearized Liouville identity.** Let `Z` be a Liouville vector field of a two-form `σ`
(`L_Z σ = σ`) on a boundaryless manifold, and let `p` be a zero of `Z`, with linearization `A`.
Then `σ_p (A u, v) + σ_p (u, A v) = σ_p (u, v)` for all tangent vectors `u`, `v` at `p`: the
Lie derivative at a zero of the field is read off its linearization. -/
theorem IsLiouvilleVectorField.apply_sectionLinearization_add {σ : RoughForm I N ℝ 2}
    {Z : (x : N) → TangentSpace I x} (hZ : IsLiouvilleVectorField σ Z) {p : N} (hp : Z p = 0)
    (u v : TangentSpace I p) :
    σ p ![sectionLinearization (F := E) I id Z p u, v] +
        σ p ![u, sectionLinearization (F := E) I id Z p v] = σ p ![u, v] := by
  conv_rhs => rw [← isLiouvilleVectorField_iff.1 hZ]
  rw [mlieDerivForm_apply_of_eq_zero hp, Fin.sum_univ_two,
    sectionLinearization_apply_eq_vectorFieldChartDerivative,
    sectionLinearization_apply_eq_vectorFieldChartDerivative]
  -- Each entry of the updated pairs is computed by `Function.update` on `Fin 2`; the entries are
  -- tangent vectors at `p`, which `simp` does not match against vectors of `E`.
  congr 2 <;> funext i <;> fin_cases i <;> rfl

end Linearization

section Linear

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **Linear Liouville fields.** Let `σ` be a linear symplectic form and `A` an operator with
`σ (A u) v + σ u (A v) = σ u v` for all `u`, `v`. Then the linear vector field `x ↦ A x` is a
Liouville vector field of the constant form `σ`. -/
theorem SymplecticForm.isLiouvilleVectorField_constSmooth (σ : SymplecticForm V)
    {A : V →L[ℝ] V} (hA : ∀ u v, σ (A u) v + σ u (A v) = σ u v) :
    IsLiouvilleVectorField σ.constSmooth.val
      (fun x ↦ A x : (x : V) → TangentSpace 𝓘(ℝ, V) x) := by
  refine isLiouvilleVectorField_iff.2 (funext fun x ↦ ?_)
  refine (mlieDerivForm_eq_lieDerivForm _ _ x).trans ?_
  ext v
  refine (lieDerivForm_apply _ v).trans ?_
  rw [Fin.sum_univ_two]
  -- The form, read in the model space, is the constant map `u ↦ σ (u 0) (u 1)`.
  set W : V → V [⋀^Fin 2]→L[ℝ] ℝ := σ.constSmooth.val
  have h (y : V) (u : Fin 2 → V) : W y u = σ (u 0) (u 1) := by
    have hu : u = ![u 0, u 1] := (FinVec.etaExpand_eq u).symm
    rw [hu]
    exact (SmoothBundleForm.eval₂_apply _ _ _ _).symm.trans (σ.constSmooth_apply y (u 0) (u 1))
  have hc : W = fun _ ↦ W x := funext fun y ↦ by ext u; rw [h, h]
  rw [hc]
  simp only [fderiv_fun_const, Pi.zero_apply, zero_apply, h, A.fderiv]
  simpa using hA (v 0) (v 1)

end Linear

end TauCeti

end
