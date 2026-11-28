/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Tactic.LinearCombination
import TauCeti.LinearAlgebra.SesquilinearForm.Separating

/-!
# Symmetric `j`-bilinear maps with a prescribed symmetrization against a form

Let `j ∘ j = -1` on `V`, finite-dimensional over a field of characteristic zero, let `G` be a
left-separating symmetric `j`-invariant bilinear form, and let `A` be a trilinear form that is
symmetric and `j`-invariant in its last two arguments and satisfies the cyclic identity
`A(h, u, j v) - A(u, h, j v) + A(v, h, j u) = 0`. Then there is a symmetric bilinear map `Q` that
commutes with `j` in each argument and satisfies `G(Q(h, u), v) + G(u, Q(h, v)) = A(h, u, v)`.

For the derivative `A` of a Kähler metric `G` in holomorphic coordinates, the cyclic identity
comes from the closedness of the Kähler form, and `Q` is the quadratic part of the holomorphic
change of coordinates that kills the first derivative of the metric
([GriffithsHarris1978], Chapter 0, §7).

## Main results

* `LinearMap.BilinForm.exists_symm_complexBilinear_apply_add_apply_eq`: the map `Q` above.

## References

* [P. Griffiths, J. Harris, *Principles of Algebraic Geometry*][GriffithsHarris1978],
  Chapter 0, §7.
-/

public section

namespace LinearMap.BilinForm

variable {K V : Type*} [Field K] [CharZero K] [AddCommGroup V]
  [Module K V] [FiniteDimensional K V]

/-- Let `j ∘ j = -1` on `V`, finite-dimensional over a field `K` of characteristic zero, let `G`
be a symmetric left-separating bilinear form with `G (j u) (j v) = G u v`, and let `A` be a
trilinear form, symmetric and `j`-invariant in its last two arguments, with
`A h u (j v) - A u h (j v) + A v h (j u) = 0`. Then there is a symmetric bilinear map `Q` with
`Q h (j u) = j (Q h u)` such that `G (Q h u) v + G u (Q h v) = A h u v`. It is given by
`G (Q h u) v = (A h u v + A (j h) u (j v)) / 2`.

For the derivative `A` at a point of a Kähler metric `G` written in holomorphic coordinates, the
cyclic identity is the closedness of the Kähler form, and `Q` is the quadratic part of a
holomorphic change of coordinates that kills the first derivative of the metric. -/
theorem exists_symm_complexBilinear_apply_add_apply_eq {j : V →ₗ[K] V}
    (hj : j ∘ₗ j = -LinearMap.id) {G : LinearMap.BilinForm K V} (hG : G.SeparatingLeft)
    (hGs : G.IsSymm) (hGj : ∀ u v, G (j u) (j v) = G u v) {A : V →ₗ[K] V →ₗ[K] V →ₗ[K] K}
    (hA : ∀ h u v, A h u v = A h v u) (hAj : ∀ h u v, A h (j u) (j v) = A h u v)
    (hd : ∀ h u v, A h u (j v) - A u h (j v) + A v h (j u) = 0) :
    ∃ Q : V →ₗ[K] V →ₗ[K] V, (∀ h u, Q h u = Q u h) ∧ (∀ h u, Q h (j u) = j (Q h u)) ∧
      ∀ h u v, G (Q h u) v + G u (Q h v) = A h u v := by
  have hjj (a : V) : j (j a) = -a := by simpa using congr($hj a)
  have hB : G.Nondegenerate :=
    (LinearMap.IsRefl.nondegenerate_iff_separatingLeft hGs.isRefl).2 hG
  -- The trilinear form that `G (Q h u) ·` must be.
  let T : V →ₗ[K] V →ₗ[K] Module.Dual K V := LinearMap.mk₂ K
    (fun h u ↦ (1 / 2 : K) • (A h u + A (j h) u ∘ₗ j))
    (fun h h' u ↦ by ext v; simp; ring)
    (fun c h u ↦ by ext v; simp; ring)
    (fun h u u' ↦ by ext v; simp; ring)
    (fun c h u ↦ by ext v; simp; ring)
  let Q : V →ₗ[K] V →ₗ[K] V := T.compr₂ (G.toDual hB).symm.toLinearMap
  have hQ (h u v : V) : G (Q h u) v = 2⁻¹ * A h u v + 2⁻¹ * A (j h) u (j v) := by
    have := LinearMap.BilinForm.apply_toDual_symm_apply (hB := hB) (T h u) v
    simp only [Q, T] at this ⊢
    simp
  have hinj {x y : V} (h : ∀ v, G x v = G y v) : x = y := hG.injective (LinearMap.ext h)
  have hGj' (x v : V) : G (j x) v = - G x (j v) := by
    simpa [hjj] using (hGj (j x) v).symm
  -- Symmetry of `Q`, from the cyclic identity.
  have hsymm (h u : V) : Q h u = Q u h := by
    refine hinj fun v ↦ ?_
    rw [hQ, hQ]
    have h1 := hd h u (j v)
    have h2 := hd (j u) h v
    have h3 := hd (j h) u v
    have h4 := hd (j v) h u
    have e1 := hA v (j u) (j h)
    have e2 := hA h (j v) (j u)
    have e3 := hA u (j v) (j h)
    simp only [hjj, map_neg] at h1
    linear_combination (2⁻¹ : K) * (-h1 + h4 + h3 - h2 + e1 + e2 - e3)
  have hJl (h u : V) : Q (j h) u = j (Q h u) := by
    refine hinj fun v ↦ ?_
    rw [hQ, hGj', hQ]
    simp [hjj]
  refine ⟨Q, hsymm, fun h u ↦ by rw [hsymm, hJl, hsymm], fun h u v ↦ ?_⟩
  rw [hGs.eq u, hQ, hQ]
  have e1 := hAj (j h) v (j u)
  have e2 := hA (j h) (j v) u
  have e3 := hA h v u
  simp only [hjj, map_neg] at e1
  linear_combination (2⁻¹ : K) * e3 - (2⁻¹ : K) * e1 - (2⁻¹ : K) * e2

end LinearMap.BilinForm

end
