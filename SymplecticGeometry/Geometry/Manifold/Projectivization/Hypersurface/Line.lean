/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Projectivization.Hypersurface.Basic
public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.FiniteCWType
import Mathlib.Analysis.Complex.Polynomial.Basic
import SymplecticGeometry.Algebra.Module.LinearMap.Polynomial
import SymplecticGeometry.LinearAlgebra.Projectivization.BinaryForm
import TauCeti.Algebra.MvPolynomial.PDeriv

/-!
# Lines meeting a smooth projective hypersurface

Let `X ⊆ ℂℙⁿ⁺¹` be a smooth projective hypersurface of degree `d`, the zero locus of a homogeneous
polynomial `f`. A projective line is the image of an injective linear map
`ι : ℂ² → ℂⁿ⁺²`. Restricted to the line, `f` becomes the binary form `f ∘ ι` of degree `d`, whose
zeros on `ℂℙ¹` are the points where the line meets `X`. If the line is transverse to `X` at each
of these points, that is, if the differential of `f` there does not vanish on the plane
`range ι`, then the binary form has only simple zeros, and there are exactly `d` of them
(`SymplecticGeometry.SmoothProjectiveHypersurface.card_inter_line`).

The binary form is `aeval (LinearMap.toMatrix' ι).toMvPolynomial f`, whose zeros Tau Ceti's
`TauCeti.preimage_map_complexProjectiveZeroLocus` identifies with the points of the line on `X`.

In complex dimension `n = 0` the hypersurface is a set of points of `ℂℙ¹`, and the line is all of
`ℂℙ¹`: the hypersurface has `d` points
(`SymplecticGeometry.SmoothProjectiveHypersurface.card_eq`), it is discrete and finite, and its
Euler characteristic is `d`
(`SymplecticGeometry.SmoothProjectiveHypersurface.eulerChar_eq_of_dim_zero`). These are the case
`n = 0` of the statements `⟨ι^* h ^ n, [X]⟩ = d` and `χ(X) = ⟨c_n(TX), [X]⟩` about the Chern classes
of `X`, where the fundamental class of a zero-dimensional manifold is read as its count of points.

## Main results

* `SymplecticGeometry.SmoothProjectiveHypersurface.card_inter_line`: a line transverse to `X` at
  each common point meets it in exactly `d` points.
* `SymplecticGeometry.SmoothProjectiveHypersurface.card_eq`: for `n = 0`, `Nat.card X = d`.
* `SymplecticGeometry.SmoothProjectiveHypersurface.eulerChar_eq_of_dim_zero`: for `n = 0`,
  `TauCeti.eulerChar X = d`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Example 4.4.3.
* [P. Griffiths and J. Harris, *Principles of Algebraic Geometry*][GriffithsHarris1978],
  Chapter 0, §2.
-/

public section

open MvPolynomial Set TauCeti
open scoped LinearAlgebra.Projectivization

namespace SymplecticGeometry

namespace SmoothProjectiveHypersurface

variable {n d : ℕ} (X : SmoothProjectiveHypersurface n d)

/-- **A transverse line meets a hypersurface of degree `d` in `d` points.** Let
`ι : ℂ² → ℂⁿ⁺²` be injective, so that its image in `ℂℙⁿ⁺¹` is a projective line. Suppose that at
each point `p` of `ℂℙ¹` that it sends into `X`, the differential of the polynomial of `X` at
`ι p.rep` does not vanish on `range ι`: the line is transverse to `X` there. Then the line meets
`X` in exactly `d` points. -/
theorem card_inter_line {ι : (Fin 2 → ℂ) →ₗ[ℂ] (Fin (n + 2) → ℂ)} (hι : Function.Injective ι)
    (htr : ∀ p : ℙ ℂ (Fin 2 → ℂ), Projectivization.map ι hι p ∈ X.carrier →
      ∃ w, ∑ i, ι w i * eval (ι p.rep) (pderiv i X.poly) ≠ 0) :
    Nat.card ↥(X.carrier ∩ range (Projectivization.map ι hι)) = d := by
  -- The restriction of the polynomial to the line: the binary form `F = X.poly ∘ ι`.
  set M := (LinearMap.toMatrix' ι).toMvPolynomial
  set F := aeval M X.poly with hFdef
  have hF : F.IsHomogeneous d := by
    simpa using X.isHomogeneous.aeval _ (Matrix.toMvPolynomial_isHomogeneous _)
  have hmem (p : ℙ ℂ (Fin 2 → ℂ)) : Projectivization.map ι hι p ∈ X.carrier ↔ eval p.rep F = 0 := by
    rw [← mem_preimage, carrier_def, preimage_map_complexProjectiveZeroLocus,
      mem_complexProjectiveZeroLocus_iff_eval_rep (fun _ ↦ hF)]
    simp [hFdef, M]
  have hsing (p : ℙ ℂ (Fin 2 → ℂ)) (hp : eval p.rep F = 0) :
      ∃ j, eval p.rep (pderiv j F) ≠ 0 := by
    obtain ⟨w, hw⟩ := htr p ((hmem p).2 hp)
    by_contra! h
    refine hw ?_
    have hj (j : Fin 2) :
        ∑ i, ι (Pi.single j 1) i * eval (ι p.rep) (pderiv i X.poly) = 0 := by
      rw [← h j, hFdef, pderiv_aeval, map_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [map_mul, Matrix.eval_aeval_toMvPolynomial, LinearMap.toMatrix'_mulVec, mul_comm]
      simp [M, LinearMap.toMatrix'_apply]
    conv_lhs => rw [pi_eq_sum_univ' w]
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp [mul_assoc, ← Finset.mul_sum, hj]
  have hset : X.carrier ∩ range (Projectivization.map ι hι) =
      Projectivization.map ι hι '' {p | eval p.rep F = 0} := by
    rw [← image_preimage_eq_inter_range]
    congr 1
    ext p
    exact hmem p
  rw [Nat.card_coe_set_eq, hset,
    ncard_image_of_injective _ (Projectivization.map_injective ι hι),
    IsHomogeneous.ncard_setOf_eval_rep_eq_zero hF hsing]

/-- **A zero-dimensional hypersurface has `d` points.** A smooth projective hypersurface of degree
`d` in `ℂℙ¹` consists of exactly `d` points.

Milestone: *Chern classes of projective hypersurfaces*. -/
theorem card_eq (X : SmoothProjectiveHypersurface 0 d) : Nat.card X = d := by
  have h := X.card_inter_line (ι := LinearMap.id) Function.injective_id fun p hp ↦ by
    rw [Projectivization.map_id, id, carrier_def] at hp
    obtain ⟨i, hi⟩ := X.smooth p hp
    exact ⟨Pi.single i 1, by simpa [Pi.single_apply] using hi⟩
  rwa [Projectivization.map_id, range_id, inter_univ] at h

/-- A zero-dimensional smooth projective hypersurface is discrete, as every manifold modelled on
a point is. -/
instance instDiscreteTopology (X : SmoothProjectiveHypersurface 0 d) : DiscreteTopology X :=
  ChartedSpace.discreteTopology (Fin 0 → ℂ) X.carrier

/-- A zero-dimensional smooth projective hypersurface is finite, being compact and discrete. -/
instance instFinite (X : SmoothProjectiveHypersurface 0 d) : Finite X :=
  finite_of_compact_of_discrete

/-- **The Euler characteristic of a zero-dimensional hypersurface.** A smooth projective
hypersurface of degree `d` in `ℂℙ¹` is a finite discrete space, of Euler characteristic `d`.

Milestone: *Chern classes of projective hypersurfaces*. -/
theorem eulerChar_eq_of_dim_zero (X : SmoothProjectiveHypersurface 0 d) : eulerChar X = d := by
  rw [eulerChar_of_discreteTopology, card_eq]

end SmoothProjectiveHypersurface

end SymplecticGeometry

end
