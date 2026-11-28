/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Complex.Module.Basic
public import TauCeti.LinearAlgebra.Complex.LinearPart

/-!
# Complex-linear parts and composition with complex-linear maps

For linear complex structures `J`, `J'`, `J''` on `V`, `W`, `U` and a map `G : W → U` that is
complex linear for `J'` and `J''`, taking Tau Ceti's complex-linear part
(`TauCeti.complexLinearPart`) or complex-antilinear part (`TauCeti.complexAntilinearPart`) of a
map `F : V → W` commutes with composing on the left by `G`. Likewise, for a map `T : U → V` that
is complex linear for `J''` and `J`, both parts commute with composing on the right by `T`.

When the target `W` is a complex module whose real structure is compatible with the complex one,
and `J'` is multiplication by `i` (`TauCeti.AlmostComplexStructure.ofComplexModule W`), both
parts of a real-linear map `F : V → W` also commute with complex scalars, for any endomorphism
`J` of `V`. Tau Ceti's `TauCeti.complexLinearPart_smul` covers only real scalars.

## Main results

* `TauCeti.IsComplexLinear.complexLinearPart_comp`: `∂(G ∘ F) = G ∘ ∂F`.
* `TauCeti.IsComplexLinear.complexAntilinearPart_comp`: `∂̄(G ∘ F) = G ∘ ∂̄F`.
* `TauCeti.IsComplexLinear.complexLinearPart_comp_right`: `∂(F ∘ T) = ∂F ∘ T`.
* `TauCeti.IsComplexLinear.complexAntilinearPart_comp_right`: `∂̄(F ∘ T) = ∂̄F ∘ T`.
* `TauCeti.complexLinearPart_complex_smul`: `∂(c • F) = c • ∂F` for `c : ℂ`.
* `TauCeti.complexAntilinearPart_complex_smul`: `∂̄(c • F) = c • ∂̄F` for `c : ℂ`.

## References

* [D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*][McDuffSalamon2012],
  §2.2.
-/

public section

namespace TauCeti

variable {𝕜 V W U : Type*} [Field 𝕜] [AddCommMonoid V] [Module 𝕜 V] [AddCommGroup W]
  [Module 𝕜 W] [AddCommGroup U] [Module 𝕜 U] {J : V →ₗ[𝕜] V} {J' : W →ₗ[𝕜] W}
  {J'' : U →ₗ[𝕜] U} {G : W →ₗ[𝕜] U}

/-- Composing on the left with a complex-linear map commutes with taking the complex-linear
part: `∂(G ∘ F) = G ∘ ∂F`. -/
theorem IsComplexLinear.complexLinearPart_comp (hG : IsComplexLinear J' J'' G) (F : V →ₗ[𝕜] W) :
    complexLinearPart J J'' (G ∘ₗ F) = G ∘ₗ complexLinearPart J J' F := by
  ext v
  simp [hG.apply]

/-- Composing on the left with a complex-linear map commutes with taking the complex-antilinear
part: `∂̄(G ∘ F) = G ∘ ∂̄F`. -/
theorem IsComplexLinear.complexAntilinearPart_comp (hG : IsComplexLinear J' J'' G)
    (F : V →ₗ[𝕜] W) :
    complexAntilinearPart J J'' (G ∘ₗ F) = G ∘ₗ complexAntilinearPart J J' F := by
  ext v
  simp [hG.apply]

/-- Composing on the right with a complex-linear map commutes with taking the complex-linear
part: `∂(F ∘ T) = ∂F ∘ T`. -/
theorem IsComplexLinear.complexLinearPart_comp_right {T : U →ₗ[𝕜] V}
    (hT : IsComplexLinear J'' J T) (F : V →ₗ[𝕜] W) :
    complexLinearPart J'' J' (F ∘ₗ T) = complexLinearPart J J' F ∘ₗ T := by
  ext v
  simp [hT.apply]

/-- Composing on the right with a complex-linear map commutes with taking the complex-antilinear
part: `∂̄(F ∘ T) = ∂̄F ∘ T`. -/
theorem IsComplexLinear.complexAntilinearPart_comp_right {T : U →ₗ[𝕜] V}
    (hT : IsComplexLinear J'' J T) (F : V →ₗ[𝕜] W) :
    complexAntilinearPart J'' J' (F ∘ₗ T) = complexAntilinearPart J J' F ∘ₗ T := by
  ext v
  simp [hT.apply]

section ComplexScalars

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  [Module ℂ W] [IsScalarTower ℝ ℂ W]

/-- For a real-linear map `F` into a complex module and any endomorphism `J` of its source, the
complex-linear part for multiplication by `i` on the target commutes with complex scalars:
`∂(c • F) = c • ∂F`. -/
@[simp]
theorem complexLinearPart_complex_smul (J : V →ₗ[ℝ] V) (c : ℂ) (F : V →ₗ[ℝ] W) :
    complexLinearPart J (AlmostComplexStructure.ofComplexModule W).toLinearMap (c • F) =
      c • complexLinearPart J (AlmostComplexStructure.ofComplexModule W).toLinearMap F := by
  ext v
  simp only [complexLinearPart_apply, LinearMap.smul_apply,
    AlmostComplexStructure.ofComplexModule_apply, smul_comm Complex.I c, smul_comm (2⁻¹ : ℝ) c,
    smul_sub]

/-- For a real-linear map `F` into a complex module and any endomorphism `J` of its source, the
complex-antilinear part for multiplication by `i` on the target commutes with complex scalars:
`∂̄(c • F) = c • ∂̄F`. -/
@[simp]
theorem complexAntilinearPart_complex_smul (J : V →ₗ[ℝ] V) (c : ℂ) (F : V →ₗ[ℝ] W) :
    complexAntilinearPart J (AlmostComplexStructure.ofComplexModule W).toLinearMap (c • F) =
      c • complexAntilinearPart J (AlmostComplexStructure.ofComplexModule W).toLinearMap F := by
  ext v
  simp only [complexAntilinearPart_apply, LinearMap.smul_apply,
    AlmostComplexStructure.ofComplexModule_apply, smul_comm Complex.I c, smul_comm (2⁻¹ : ℝ) c,
    smul_add]

end ComplexScalars

end TauCeti

end
