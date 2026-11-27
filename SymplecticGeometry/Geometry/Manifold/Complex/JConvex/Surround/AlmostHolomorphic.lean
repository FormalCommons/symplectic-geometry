/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import TauCeti.Analysis.InnerProductSpace.Euclidean.Complex

import Mathlib.Analysis.Analytic.CPolynomial
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Almost holomorphic Taylor extensions

For a finite type `ι'`, write a point `z` of `EuclideanSpace ℂ ι'` as `x + i y`, with `x` and
`y` in `EuclideanSpace ℝ ι'` the two components of Tau Ceti's
`TauCeti.complexEuclideanEquivRealProd ι' z`. For a map `f : EuclideanSpace ℝ ι' → W` into a
complex normed space, the truncated Taylor extension of order `N` is
`taylorExtension N f (x + i y) = ∑_{j ≤ N} (i ^ j / j!) • D^j f(x) (y, …, y)`,
the Taylor polynomial of `f` at `x`, of order `N`, evaluated at the imaginary increment `i y`.
It is the classical almost analytic extension of `f`, truncated at order `N`, and it restricts
to `f` on the real points.

## Main definitions and results

* `SymplecticGeometry.taylorExtension N f`: the truncated Taylor extension of `f`
  (`SymplecticGeometry.taylorExtension_def`);
* `SymplecticGeometry.taylorExtension_ofReal`: on a real point `x + i 0` it equals `f x`;
* `SymplecticGeometry.taylorExtension_zero`: of order zero, it is `f` applied to the real part;
* `SymplecticGeometry.contDiff_taylorExtension`: if `f` is `C^(r + N)`, then
  `taylorExtension N f` is `C^r` over `ℝ`.

## References

* [K. Cieliebak, Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012]:
  the proof of Proposition 5.55 builds its charts from such extensions.
-/

public section

namespace SymplecticGeometry

open TauCeti

variable {ι' : Type*} [Fintype ι'] {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- The truncated Taylor extension of order `N` of `f : ℝⁿ → W` to `ℂⁿ`: at `z = x + i y` it is
`∑_{j ≤ N} (i ^ j / j!) • D^j f(x) (y, …, y)`, the Taylor polynomial of `f` at `x` of order `N`
evaluated at the increment `i y`. -/
noncomputable def taylorExtension (N : ℕ) (f : EuclideanSpace ℝ ι' → W)
    (z : EuclideanSpace ℂ ι') : W :=
  ∑ j ∈ Finset.range (N + 1), (Complex.I ^ j / j.factorial) •
    iteratedFDeriv ℝ j f (complexEuclideanEquivRealProd ι' z).1
      (fun _ ↦ (complexEuclideanEquivRealProd ι' z).2)

theorem taylorExtension_def (N : ℕ) (f : EuclideanSpace ℝ ι' → W) (z : EuclideanSpace ℂ ι') :
    taylorExtension N f z = ∑ j ∈ Finset.range (N + 1), (Complex.I ^ j / j.factorial) •
      iteratedFDeriv ℝ j f (complexEuclideanEquivRealProd ι' z).1
        (fun _ ↦ (complexEuclideanEquivRealProd ι' z).2) :=
  (rfl)

/-- On a real point `x + i 0`, the truncated Taylor extension of `f` is `f x`. -/
@[simp]
theorem taylorExtension_ofReal (N : ℕ) (f : EuclideanSpace ℝ ι' → W)
    (x : EuclideanSpace ℝ ι') :
    taylorExtension N f ((complexEuclideanEquivRealProd ι').symm (x, 0)) = f x := by
  rw [taylorExtension_def, ContinuousLinearEquiv.apply_symm_apply,
    Finset.sum_eq_single_of_mem 0 (by simp)]
  · simp
  · intro j _ hj
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    rw [← Pi.zero_def, ContinuousMultilinearMap.map_zero, smul_zero]

/-- The truncated Taylor extension of order zero is `f` applied to the real part. -/
@[simp]
theorem taylorExtension_zero (f : EuclideanSpace ℝ ι' → W) (z : EuclideanSpace ℂ ι') :
    taylorExtension 0 f z = f (complexEuclideanEquivRealProd ι' z).1 := by
  simp [taylorExtension_def]

/-- If `f` is `C^(r + N)`, then its truncated Taylor extension of order `N` is `C^r` over `ℝ`. -/
theorem contDiff_taylorExtension {N : ℕ} {r : WithTop ℕ∞} {f : EuclideanSpace ℝ ι' → W}
    (hf : ContDiff ℝ (r + N) f) : ContDiff ℝ r (taylorExtension N f) := by
  have hre : ContDiff ℝ r fun z : EuclideanSpace ℂ ι' ↦ (complexEuclideanEquivRealProd ι' z).1 :=
    (complexEuclideanEquivRealProd ι').contDiff.fst
  have him : ContDiff ℝ r fun z : EuclideanSpace ℂ ι' ↦ (complexEuclideanEquivRealProd ι' z).2 :=
    (complexEuclideanEquivRealProd ι').contDiff.snd
  refine ContDiff.sum fun j hj ↦ ContDiff.const_smul _ ?_
  have hD : ContDiff ℝ r (iteratedFDeriv ℝ j f) :=
    hf.iteratedFDeriv_right (add_le_add_right (by exact_mod_cast Finset.mem_range_succ_iff.1 hj) _)
  have heval : ContDiff ℝ r fun p : ContinuousMultilinearMap ℝ (fun _ : Fin j ↦
      EuclideanSpace ℝ ι') W × (Fin j → EuclideanSpace ℝ ι') ↦ p.1 p.2 :=
    (ContinuousLinearMap.id ℝ (ContinuousMultilinearMap ℝ
      (fun _ : Fin j ↦ EuclideanSpace ℝ ι') W)).analyticOnNhd_uncurry_of_multilinear.contDiff
  exact heval.comp ((hD.comp hre).prodMk (contDiff_pi.2 fun _ ↦ him))

end SymplecticGeometry

end
