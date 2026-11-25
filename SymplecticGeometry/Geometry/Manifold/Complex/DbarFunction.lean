/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Basic
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.Trivial
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.MFDeriv

/-!
# `∂bar_J` of a function read in a chart that carries `J` to `i`

Let `J` be a smooth almost complex structure on a manifold `M`, and `ψ : M → ℂ` a partial
diffeomorphism that is pseudoholomorphic from `J` to multiplication by `i` at every point of its
source (`TauCeti.IsPseudoholomorphicAt`), as the
isothermal charts of `TauCeti.SmoothAlmostComplexStructure.exists_isothermal_partialDiffeomorph`
do. This file shows that the operator `∂bar_J` on functions (`dbarFunction`), evaluated on the
preimage under `dψ` of a vector `z : ℂ`, is the conjugate Wirtinger derivative of the function
read through `ψ⁻¹`, in the direction `z`. It uses Tau Ceti's
`OpenPartialHomeomorph.MDifferentiable.isPseudoholomorphicAt_symm`, by which `ψ⁻¹` is
pseudoholomorphic from `i` to `J`.

## Main results

* `TauCeti.SmoothAlmostComplexStructure.dbarFunction_apply_mfderiv_symm_eq_conjWirtingerDeriv`:
  `∂bar_J f (dψ⁻¹ z) = conjWirtingerDeriv (f ∘ ψ.symm) · z`.

## References

* [D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*][McDuffSalamon2012],
  Appendix C.1.
-/

public section

open TauCeti
open scoped Manifold ContDiff

namespace TauCeti.SmoothAlmostComplexStructure

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Let `ψ` be a partial diffeomorphism from `M` to `ℂ` that is pseudoholomorphic from `J` to
multiplication by `i` at every point of its source. At `w` in its target, `∂bar_J f` at
`ψ.symm w`, evaluated on the preimage `dψ⁻¹ z` of `z : ℂ`, is the conjugate Wirtinger derivative
of `f ∘ ψ.symm` at `w` in the direction `z`. -/
theorem dbarFunction_apply_mfderiv_symm_eq_conjWirtingerDeriv
    (J : SmoothAlmostComplexStructure I M) {ψ : PartialDiffeomorph I 𝓘(ℝ, ℂ) M ℂ ∞}
    (hψ : ∀ y ∈ ψ.source, IsPseudoholomorphicAt J (ofComplexManifold ℂ ℂ) ψ y)
    {w : ℂ} (hw : w ∈ ψ.target) {f : M → F} (hf : MDifferentiableAt I 𝓘(ℝ, F) f (ψ.symm w))
    (z : ℂ) :
    J.dbarFunction f (ψ.symm w) (mfderiv 𝓘(ℝ, ℂ) I ψ.symm w z) =
      conjWirtingerDeriv (f ∘ ψ.symm) w z := by
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hs : MDifferentiableAt 𝓘(ℝ, ℂ) I ψ.symm w := ψ.symm.mdifferentiableAt hn hw
  set u := mfderiv 𝓘(ℝ, ℂ) I ψ.symm w z
  -- `ψ⁻¹` is pseudoholomorphic from `i` to `J` at `w`.
  have hJ : mfderiv 𝓘(ℝ, ℂ) I ψ.symm w (Complex.I • z) = J (ψ.symm w) u :=
    (ofComplexManifold_apply (E := ℂ) w z).symm ▸
      ((ψ.toOpenPartialHomeomorph_mdifferentiable hn).isPseudoholomorphicAt_symm hw
        (hψ _ (ψ.map_target hw))).mfderiv_apply_commute z
  have hd (v : ℂ) : fderiv ℝ (f ∘ ψ.symm) w v =
      mvfderiv I f (ψ.symm w) (mfderiv 𝓘(ℝ, ℂ) I ψ.symm w v) := by
    rw [← mvfderiv_eq_fderiv_apply (𝕜 := ℝ) (f ∘ ψ.symm) w v, mvfderiv_comp w hf hs]
    -- `ContinuousLinearMap.comp_apply` cannot rewrite here: `v` lives in `ℂ` and not in its type
    -- synonym `TangentSpace 𝓘(ℝ, ℂ) w`.
    rfl
  rw [conjWirtingerDeriv_apply, hd, hd, hJ, dbarFunction_apply, ← Complex.coe_smul]
  norm_num
  rfl

end TauCeti.SmoothAlmostComplexStructure

end
