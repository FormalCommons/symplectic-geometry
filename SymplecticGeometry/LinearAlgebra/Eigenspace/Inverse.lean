/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Generalized eigenspaces of an invertible endomorphism

For an endomorphism `f` of a module and an inverse `g` of `f`:

* `Module.End.genEigenspace_zero_eq_bot_of_injective`: an injective endomorphism has no nonzero
  generalized eigenvector for the eigenvalue `0`;
* `Module.End.mem_genEigenspace_inv`: over a field, a generalized `ν`-eigenvector of `f` is a
  generalized `ν⁻¹`-eigenvector of `g`, of the same order. For `ν ≠ 0` this holds since
  `g - ν⁻¹ = (-ν⁻¹ g) (f - ν)` with commuting factors; for `ν = 0` the vector is `0`, since
  `f` is injective.
-/

public section

namespace Module.End

variable {R K V : Type*}

/-- An injective endomorphism has no nonzero generalized eigenvector for the eigenvalue `0`. -/
theorem genEigenspace_zero_eq_bot_of_injective [CommRing R] [AddCommGroup V] [Module R V]
    {f : End R V} (hf : Function.Injective f) (k : ℕ∞) : f.genEigenspace 0 k = ⊥ := by
  refine eq_bot_iff.2 fun w hw ↦ ?_
  obtain ⟨n, -, hw⟩ := mem_genEigenspace.1 hw
  rw [zero_smul, sub_zero, LinearMap.mem_ker, ← map_zero (f ^ n)] at hw
  exact (Submodule.mem_bot R).2 (iterate_injective hf n hw)

/-- For an invertible endomorphism `f` with inverse `g`, a generalized `ν`-eigenvector of `f`
is a generalized `ν⁻¹`-eigenvector of `g`, of the same order. For `ν = 0` the statement is
trivial, as the only generalized `0`-eigenvector of `f` is `0`. -/
theorem mem_genEigenspace_inv [Field K] [AddCommGroup V] [Module K V]
    {f g : End K V} (hfg : f * g = 1) (hgf : g * f = 1) {ν : K} {k : ℕ∞}
    {w : V} (hw : w ∈ f.genEigenspace ν k) : w ∈ g.genEigenspace ν⁻¹ k := by
  rcases eq_or_ne ν 0 with rfl | hν
  · have hf : Function.Injective f := fun x y hxy ↦ by
      simpa [← mul_apply_eq_comp, hgf] using congr_arg g hxy
    rw [genEigenspace_zero_eq_bot_of_injective hf, Submodule.mem_bot] at hw
    exact hw ▸ Submodule.zero_mem _
  obtain ⟨n, hn, hw⟩ := mem_genEigenspace.1 hw
  refine mem_genEigenspace.2 ⟨n, hn, ?_⟩
  have hfac : g - ν⁻¹ • 1 = ((-ν⁻¹) • g) * (f - ν • 1) := by
    rw [smul_mul_assoc, mul_sub, hgf, mul_smul_comm, mul_one, smul_sub, smul_smul, neg_mul,
      inv_mul_cancel₀ hν, neg_one_smul, neg_smul]
    abel
  have hcomm : Commute ((-ν⁻¹) • g) (f - ν • 1) :=
    (((show Commute g f from hgf.trans hfg.symm).sub_right
      ((Commute.one_right g).smul_right ν)).smul_left (-ν⁻¹))
  rw [LinearMap.mem_ker, hfac, hcomm.mul_pow, mul_apply_eq_comp, LinearMap.mem_ker.1 hw,
    map_zero]

end Module.End

end
