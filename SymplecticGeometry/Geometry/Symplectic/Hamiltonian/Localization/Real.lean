/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Equivariant.Calculus
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Smooth
public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.Localization.WeightOneForm
public import TauCeti.Geometry.Symplectic.Manifold.SymplecticMap
public import TauCeti.Geometry.Symplectic.Manifold.Volume
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Interior
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.Localization.LocalizingForm
import SymplecticGeometry.Geometry.Symplectic.Manifold.SymplecticMap
import TauCeti.Geometry.Symplectic.Manifold.NeighborhoodGerm

/-!
# Equivariant localization for real `ħ` on a weight chart

Let `Φ` be a partial diffeomorphism from `StdSpace (Fin n)` to `M` that pulls `σ` back to the
standard form `ω₀` on its source, and let `θ` be a one-form on `M` that, on the image `Φ '' B` of
a ball `B` about `0`, is the model one-form `θₖ = ∑ⱼ kⱼ (xⱼ dyⱼ - yⱼ dxⱼ)` read through `Φ`
(`SymplecticGeometry.weightOneForm`), as the localizing form of
`SymplecticGeometry.exists_localizingForm` is. Let `X` be a vector field that `Φ` relates on `B`
to the generator `∑ⱼ 2π kⱼ (xⱼ ∂_{yⱼ} - yⱼ ∂_{xⱼ})` of the circle action with weights `k`.

For a smooth `F : ℝ → ℝ` and real `ħ`, put `f = -ħ θ(X)`. The component of degree `2 n` of
`F(f + dθ) = ∑ₘ F⁽ᵐ⁾(f) (dθ)ᵐ / m!` (`SymplecticGeometry.formCalculus`) at `Φ z`, for `z ∈ B`, is
`2ⁿ ∏ⱼ kⱼ · F⁽ⁿ⁾(-2πħ ∑ⱼ kⱼ² (xⱼ² + yⱼ²)) · σⁿ / n!`
(`SymplecticGeometry.formCalculus_apply_weightChart`). The proof reads every factor through `Φ`:
`θ(X) = 2π ∑ⱼ kⱼ² (xⱼ² + yⱼ²)` by `mpullback_symm_weightOneForm_apply_weightChart`,
`dθ` is `dθₖ` read through `Φ` by `TauCeti.mextDerivₗ_apply_eq_of_eventuallyEq_mpullback`, and
`(dθₖ)ⁿ = 2ⁿ ∏ⱼ kⱼ · ω₀ⁿ` by `wedgePow_mextDerivₗ_weightOneForm_apply`, while `σ` is `ω₀` read
through `Φ` since `Φ` is symplectic.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §5.6
* N. Berline, E. Getzler and M. Vergne, *Heat Kernels and Dirac Operators*, Grundlehren der
  mathematischen Wissenschaften 298, Springer, 1992, §7.2
-/

public section

noncomputable section

open Set Metric Real
open scoped Manifold ContDiff Topology

namespace SymplecticGeometry

open TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {n : ℕ} {Φ : PartialDiffeomorph 𝓘(ℝ, StdSpace (Fin n)) I (StdSpace (Fin n)) M ∞}
  {k : Fin n → ℝ} {θ : SmoothForm I M ℝ 1} {s : ℝ}

/-- At `Φ z`, the function `θ(X)` takes the value `2π ∑ⱼ kⱼ² (xⱼ(z)² + yⱼ(z)²)`. -/
private theorem interiorProduct_apply_weightChart {X : (x : M) → TangentSpace I x}
    {hX : ContMDiff I I.tangent ∞ (fun x ↦ (X x : TangentBundle I M))} {z : StdSpace (Fin n)}
    (hθ : θ.val (Φ z) =
      TauCeti.mpullback I 𝓘(ℝ, StdSpace (Fin n)) Φ.symm (weightOneForm k).val (Φ z))
    (hz : z ∈ Φ.source)
    (hXz : mfderiv 𝓘(ℝ, StdSpace (Fin n)) I Φ z (EuclideanSpace.sumEquivProd.symm
        (weightGenerator ((2 * π) • k) (EuclideanSpace.sumEquivProd z))) = X (Φ z)) :
    SmoothForm.ofFunctionEquiv.symm (SmoothForm.interiorProduct ⟨X, hX⟩ θ) (Φ z) =
      2 * π * ∑ j, k j ^ 2 * (z.x j ^ 2 + z.y j ^ 2) := by
  rw [SmoothForm.ofFunctionEquiv_symm_apply, SmoothForm.interiorProduct_apply_degree_one,
    ContMDiffSection.coeFn_mk, hθ, mpullback_symm_weightOneForm_apply_weightChart k k hz hXz]
  simp only [sq]

/-- **The top component of `F(d_ħ θ)` on a weight chart.** Let `Φ` be a partial diffeomorphism
from `StdSpace (Fin n)` to `M` that pulls `σ` back to the standard form on its source, let
`ball 0 s` lie in its source, let `θ` be the model one-form `θₖ` read through `Φ` on
`Φ '' ball 0 s`, and let `Φ` relate on `ball 0 s` the generator of the rotations by the angles
`2π kⱼ` to the vector field `X`. For a smooth `F : ℝ → ℝ`, real `ħ` and `z ∈ ball 0 s`, the
component of degree `2 n` of `F(-ħ θ(X) + dθ)` at `Φ z` is
`2ⁿ ∏ⱼ kⱼ · F⁽ⁿ⁾(-2πħ ∑ⱼ kⱼ² (xⱼ(z)² + yⱼ(z)²))` times the symplectic volume form `σⁿ / n!`. -/
theorem formCalculus_apply_weightChart [FiniteDimensional ℝ E] {σ : SmoothTwoForm I M}
    (hσ : SmoothTwoForm.IsSymplecticMapOn (stdForm (Fin n)).constSmooth σ Φ Φ.source)
    (hs : ball 0 s ⊆ Φ.source)
    (hθ : ∀ x ∈ Φ '' ball 0 s,
      θ.val x = TauCeti.mpullback I 𝓘(ℝ, StdSpace (Fin n)) Φ.symm (weightOneForm k).val x)
    {X : (x : M) → TangentSpace I x}
    {hX : ContMDiff I I.tangent ∞ (fun x ↦ (X x : TangentBundle I M))}
    (hXΦ : ∀ z ∈ ball 0 s, mfderiv 𝓘(ℝ, StdSpace (Fin n)) I Φ z (EuclideanSpace.sumEquivProd.symm
        (weightGenerator ((2 * π) • k) (EuclideanSpace.sumEquivProd z))) = X (Φ z))
    (F : ℝ → ℝ) (hF : ContDiff ℝ ∞ F) (ħ : ℝ) {z : StdSpace (Fin n)} (hz : z ∈ ball 0 s) :
    (formCalculus F hF
        (-ħ • SmoothForm.ofFunctionEquiv.symm (SmoothForm.interiorProduct ⟨X, hX⟩ θ))
        (mextDerivₗ I 1 θ) (2 * n)).val (Φ z) =
      ((2 ^ n * ∏ j, k j) *
          iteratedDeriv n F (-(2 * π * ħ) * ∑ j, k j ^ 2 * (z.x j ^ 2 + z.y j ^ 2))) •
        (σ.volumeForm n).val (Φ z) := by
  have hzs : z ∈ Φ.source := hs hz
  have hxt : Φ z ∈ Φ.target := Φ.map_source hzs
  -- `σ` is the standard form read through `Φ`, since `Φ⁻¹` is symplectic on the target.
  have hσx : σ.val (Φ z) =
      ((stdForm (Fin n)).constSmooth.val (Φ.symm (Φ z))).compContinuousLinearMap
        (mfderiv I 𝓘(ℝ, StdSpace (Fin n)) Φ.symm (Φ z)) :=
    ((Φ.isSymplecticMapOn_symm hσ (by simp)).mpullback_apply hxt).symm.trans
      (mpullback_apply_eq_compContinuousLinearMap _ _ _)
  have hω₀ (v w : StdSpace (Fin n)) :
      (stdForm (Fin n)).constSmooth.val (Φ.symm (Φ z)) ![v, w] = stdForm (Fin n) v w :=
    (SmoothBundleForm.eval₂_apply _ _ _ _).symm.trans (SymplecticForm.constSmooth_apply _ _ _ _)
  have hpow :
      ((mextDerivₗ 𝓘(ℝ, StdSpace (Fin n)) 1 (weightOneForm k)).val (Φ.symm (Φ z))).wedgePow n =
      (2 ^ n * ∏ j, k j) • ((stdForm (Fin n)).constSmooth.val (Φ.symm (Φ z))).wedgePow n := by
    have h := wedgePow_mextDerivₗ_weightOneForm_apply k (Φ.symm (Φ z)) hω₀
    rw [Fintype.card_fin] at h
    -- `h` is stated on `StdSpace (Fin n)`, the goal on the tangent space at `Φ.symm (Φ z)`.
    exact h
  -- `θ` is `(Φ⁻¹)^* θₖ` on the open set `Φ '' ball 0 s`, a neighbourhood of `Φ z`.
  have hθx : ∀ᶠ y in 𝓝 (Φ z),
      θ.val y = TauCeti.mpullback I 𝓘(ℝ, StdSpace (Fin n)) Φ.symm (weightOneForm k).val y :=
    Filter.eventually_of_mem ((Φ.toOpenPartialHomeomorph.isOpen_image_of_subset_source
      isOpen_ball hs).mem_nhds (mem_image_of_mem _ hz)) hθ
  rw [formCalculus_apply_val, mextDerivₗ_apply_eq_of_eventuallyEq_mpullback
      ((Φ.symm.contMDiffOn.contMDiffAt (Φ.open_target.mem_nhds hxt)).of_le (by simp)) hθx,
    ← ContinuousAlternatingMap.wedgePow_compContinuousLinearMap, hpow,
    SmoothTwoForm.volumeForm_apply, hσx,
    ← ContinuousAlternatingMap.wedgePow_compContinuousLinearMap, ContMDiffMap.coe_smul,
    Pi.smul_apply, interiorProduct_apply_weightChart (hθ _ (mem_image_of_mem _ hz)) hzs (hXΦ z hz),
    smul_eq_mul]
  ext v
  simp only [ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, smul_eq_mul]
  rw [show -ħ * (2 * π * ∑ j, k j ^ 2 * (z.x j ^ 2 + z.y j ^ 2)) =
    -(2 * π * ħ) * ∑ j, k j ^ 2 * (z.x j ^ 2 + z.y j ^ 2) by ring]
  ring

end SymplecticGeometry

end
