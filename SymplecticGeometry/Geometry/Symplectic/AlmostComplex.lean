/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.AlmostComplex

/-!
# Maps that are antilinear for one tamed structure and linear for another

Let `ω` be a symplectic form on a finite-dimensional real vector space `V` that tames two
almost complex structures `J` and `K`. Tau Ceti's `TauCeti.SymplecticForm.Tames.injective_add`
shows that `J + K` is injective, hence bijective. A real linear map `F : V → W` into a space
with a complex structure `J'` that is complex antilinear for `J` and complex linear for `K`
satisfies `F ((J + K) v) = -J' (F v) + J' (F v) = 0`, so it vanishes
(`TauCeti.SymplecticForm.Tames.eq_zero_of_isComplexAntilinear_of_isComplexLinear`).

On a surface this says that, for two almost complex structures tamed by a common form, the
`(0,1)`-projection for one is injective on the `(0,1)`-forms of the other: this is used to
compare Cauchy–Riemann operators of different structures on the Riemann sphere.

## Main results

* `TauCeti.SymplecticForm.Tames.eq_zero_of_isComplexAntilinear_of_isComplexLinear`.

## References

* [D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*][McDuffSalamon2012],
  Appendix C.1.
-/

public section

namespace TauCeti.SymplecticForm

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

/-- Let `ω` tame two almost complex structures `J` and `K` on a finite-dimensional real vector
space `V`, and let `J'` be an endomorphism of a real vector space `W`. A real linear map
`F : V → W` that is complex antilinear for `J` and `J'`, and complex linear for `K` and `J'`, is
zero. -/
theorem Tames.eq_zero_of_isComplexAntilinear_of_isComplexLinear [FiniteDimensional ℝ V]
    {ω : SymplecticForm V} {J K : AlmostComplexStructure V} (hJ : ω.Tames J) (hK : ω.Tames K)
    {J' : W →ₗ[ℝ] W} {F : V →ₗ[ℝ] W} (hFJ : IsComplexAntilinear J.toLinearMap J' F)
    (hFK : IsComplexLinear K.toLinearMap J' F) : F = 0 := by
  have hsurj := LinearMap.injective_iff_surjective.1 (hJ.injective_add hK)
  ext w
  obtain ⟨v, rfl⟩ := hsurj w
  simp [hFJ.apply, hFK.apply]

end TauCeti.SymplecticForm
