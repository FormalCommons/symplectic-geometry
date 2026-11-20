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
* `Module.End.mem_genEigenspace_inv`: over a field, a generalized `ν`-eigenvector of `f` with
  `ν ≠ 0` is a generalized `ν⁻¹`-eigenvector of `g`, of the same order, since
  `g - ν⁻¹ = (-ν⁻¹ g) (f - ν)` with commuting factors.
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
  exact (Submodule.mem_bot R).2 ((FunLike.coe_pow_eq_iterate f n ▸ hf.iterate n) hw)

/-- For an invertible endomorphism `f` with inverse `g`, a generalized `ν`-eigenvector of `f`
with `ν ≠ 0` is a generalized `ν⁻¹`-eigenvector of `g`, of the same order. -/
theorem mem_genEigenspace_inv [Field K] [AddCommGroup V] [Module K V]
    {f g : End K V} (hfg : f * g = 1) (hgf : g * f = 1) {ν : K} (hν : ν ≠ 0) {k : ℕ∞}
    {w : V} (hw : w ∈ f.genEigenspace ν k) : w ∈ g.genEigenspace ν⁻¹ k := by
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
