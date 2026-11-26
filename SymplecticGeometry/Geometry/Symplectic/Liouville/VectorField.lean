/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.LieDeriv
public import TauCeti.Geometry.Symplectic.Liouville.VectorField

/-!
# Pulling Liouville vector fields back along related fields

Let `Φ : M' → M` be a smooth map, `σ` a smooth two-form on `M` and `X` a Liouville vector field
of `σ`. If a vector field `Y` on `M'` is `Φ`-related to `X`, that is `dΦ_x (Y x) = X (Φ x)` for
every `x`, then `Y` is a Liouville vector field of `Φ^* σ`
(`TauCeti.IsLiouvilleVectorField.mpullback`). The form need not be closed, the differential of
`Φ` need not be invertible, and the models are arbitrary models with corners, so this applies
for instance to the inclusion of a regular sublevel set, a manifold with boundary, into the
ambient manifold.

The proof applies the naturality of the Lie derivative along related fields,
`TauCeti.mpullback_mlieDerivForm_of_related`: `Φ^* (L_X σ) = L_Y (Φ^* σ)`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §3.5
  (Liouville vector fields)
* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  Chapter 11 (Liouville and Weinstein structures)
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
  rw [isLiouvilleVectorField_iff, ← mpullback_mlieDerivForm_of_related (k := 1) hΦ hX hY hXY,
    isLiouvilleVectorField_iff.mp hXσ, SmoothForm.coe_mpullback]

end TauCeti

end
