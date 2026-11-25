/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.LinearAlgebra.Complex.LinearPart

/-!
# Complex-linear parts and composition with complex-linear maps

For linear complex structures `J`, `J'`, `J''` on `V`, `W`, `U` and a map `G : W → U` that is
complex linear for `J'` and `J''`, taking Tau Ceti's complex-linear part
(`TauCeti.complexLinearPart`) or complex-antilinear part (`TauCeti.complexAntilinearPart`) of a
map `F : V → W` commutes with composing on the left by `G`.

## Main results

* `TauCeti.IsComplexLinear.complexLinearPart_comp`: `∂(G ∘ F) = G ∘ ∂F`.
* `TauCeti.IsComplexLinear.complexAntilinearPart_comp`: `∂̄(G ∘ F) = G ∘ ∂̄F`.

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

end TauCeti

end
