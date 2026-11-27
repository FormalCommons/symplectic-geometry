/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.Basic
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.NormedSpace
import SymplecticGeometry.Geometry.Symplectic.HPrinciple.HandleCore.Approximation
import SymplecticGeometry.Geometry.Symplectic.HPrinciple.HandleCore.CompressionIsotopy
import SymplecticGeometry.Geometry.Symplectic.HPrinciple.HandleCore.Homotopy

/-!
# The handle-core lemma

Let `D = (Fin m → ℝ) × (Fin k → ℝ)` with the sup norms, `0 < k`, with the cube
`Q = closedBall 0 1` and the attaching faces `A = sphere 0 1 ×ˢ closedBall 0 1`. Let `τ` be a
smooth family of two-forms on `D` over a finite-dimensional normed space `L`, nondegenerate on `Q`
for the parameters of a compact `K ⊆ L`, and `β` a smooth family of one-forms with `dβ l = τ l` on
a fixed open `W ⊇ A` for those parameters.
`SymplecticGeometry.exists_homotopy_exact_of_exact_near_attaching` deforms `τ`, smoothly in the
parameter and in time, through forms nondegenerate on `Q` and equal to `τ` near `A`, to forms
exact on all of `D`; a parameter at which `τ` is exact near `Q` stays exact near `Q`. This is the
working lemma behind McDuff–Salamon's Lemma 7.3.2, for a core of any dimension.

## The construction

In place of McDuff–Salamon's induction on the dimension of the core, the proof follows
Eliashberg–Mishachev's approximation-and-compression argument (§10.2).

1. Let `r > 0` be a nondegeneracy margin of `τ` over `K × Q`
   (`SymplecticGeometry.IsSmoothFamily.exists_pos_forall_nondegenerate`).
2. Holonomic approximation of the formal primitive of `τ` near the core
   (`SymplecticGeometry.exists_diffeotopy_norm_mextDerivₗ_sub_lt_near_core`) gives a slab width
   `ε₀`, a family of diffeotopies `H`, a smooth family `β'` of one-forms equal to `β` on the slab
   `1 - ε₀ < ‖u‖`, and an open set `V` around the moved core on which `dβ'` is within `r` of `τ`.
3. Composing `H` with the compression of the cube onto a thin tube around its core
   (`SymplecticGeometry.exists_isotopy_mapsTo_of_diffeotopy`) gives isotopies `e l s` of `D`,
   preserving `Q`, the identity where `1 - ε₀ / 2 < ‖u‖`, with `e l 1` mapping `Q` into the slice
   of `V` over `l` or into the slab, where `dβ' l = dβ l = τ l`.

The homotopy is `σ (l, t) = (e l (a t))^* ((1 - b t) • τ l + b t • dβ' l)` for smooth steps `a`
and `b`, with `b` starting once `a` has reached `1`; at time `1` it is `d ((e l 1)^* β' l)`.
Its construction is shared with the one-dimensional case
(`SymplecticGeometry.exists_homotopy_exact_of_closed_near_attaching_fin_one`) and proved once in
`SymplecticGeometry.exists_homotopy_exact_of_isotopy`.

## Main results

* `SymplecticGeometry.exists_homotopy_exact_of_exact_near_attaching`

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Lemma 7.3.2.
* [Y. Eliashberg and N. Mishachev, *Introduction to the h-principle*][EliashbergMishachev2002],
  §10.2.
-/

public section

open Set Metric Filter TauCeti
open scoped Manifold ContDiff Topology

namespace SymplecticGeometry

variable {m k : ℕ} {L : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L] [FiniteDimensional ℝ L]

/-- **The handle-core lemma.** On `D = (Fin m → ℝ) × (Fin k → ℝ)` with the sup norms and `0 < k`,
let `Q = closedBall 0 1` be the cube and `A = sphere 0 1 ×ˢ closedBall 0 1` its attaching faces.
Let `τ` be a smooth family of two-forms and `β` a smooth family of one-forms on `D`, over a
finite-dimensional normed space `L`, and `K ⊆ L` compact, such that for `l ∈ K` the form `τ l` is
nondegenerate on `Q` and equal to `dβ l` on the open set `W ⊇ A`. Then there is a smooth family
`σ` of two-forms over `L × [0, 1]` with `σ (l, 0) = τ l` such that:

* `σ (l, t)` is nondegenerate on `Q` for `l ∈ K` and every `t`;
* `σ (l, t) = τ l` on a neighbourhood `W'` of `A`, the same for all `l ∈ K` and all `t`;
* `σ (l, 1)` is exact on `D`, for every `l`;
* if `τ l` has a primitive on a neighbourhood of `Q`, then so does every `σ (l, t)`. -/
theorem exists_homotopy_exact_of_exact_near_attaching (hk : 0 < k) {K : Set L}
    (hK : IsCompact K) {τ : L → SmoothTwoForm 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ))
      ((Fin m → ℝ) × (Fin k → ℝ))} (hτ : IsSmoothFamily 𝓘(ℝ, L) τ)
    (hnd : ∀ l ∈ K, ∀ x ∈ closedBall (0 : (Fin m → ℝ) × (Fin k → ℝ)) 1,
      ((τ l).bilinFormAt x).Nondegenerate)
    {β : L → SmoothForm 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ)) ((Fin m → ℝ) × (Fin k → ℝ)) ℝ 1}
    (hβ : IsSmoothFamily 𝓘(ℝ, L) β) {W : Set ((Fin m → ℝ) × (Fin k → ℝ))} (hW : IsOpen W)
    (hAW : sphere (0 : Fin m → ℝ) 1 ×ˢ closedBall (0 : Fin k → ℝ) 1 ⊆ W)
    (hτβ : ∀ l ∈ K, ∀ x ∈ W,
      (mextDerivₗ 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ)) 1 (β l)).val x = (τ l).val x) :
    ∃ σ : L × unitInterval →
        SmoothTwoForm 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ)) ((Fin m → ℝ) × (Fin k → ℝ)),
      IsSmoothFamily (𝓘(ℝ, L).prod (𝓡∂ 1)) σ ∧
      (∀ l, σ (l, 0) = τ l) ∧
      (∀ l ∈ K, ∀ t, ∀ x ∈ closedBall (0 : (Fin m → ℝ) × (Fin k → ℝ)) 1,
        ((σ (l, t)).bilinFormAt x).Nondegenerate) ∧
      (∃ W' ∈ 𝓝ˢ (sphere (0 : Fin m → ℝ) 1 ×ˢ closedBall (0 : Fin k → ℝ) 1), ∀ l ∈ K, ∀ t,
        ∀ x ∈ W', (σ (l, t)).val x = (τ l).val x) ∧
      (∀ l, ∃ γ : SmoothForm 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ)) ((Fin m → ℝ) × (Fin k → ℝ)) ℝ 1,
        mextDerivₗ 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ)) 1 γ = σ (l, 1)) ∧
      ∀ l, (∃ V ∈ 𝓝ˢ (closedBall (0 : (Fin m → ℝ) × (Fin k → ℝ)) 1),
          ∃ γ : SmoothForm 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ)) ((Fin m → ℝ) × (Fin k → ℝ)) ℝ 1,
            ∀ x ∈ V, (mextDerivₗ 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ)) 1 γ).val x = (τ l).val x) →
        ∀ t, ∃ V ∈ 𝓝ˢ (closedBall (0 : (Fin m → ℝ) × (Fin k → ℝ)) 1),
          ∃ γ : SmoothForm 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ)) ((Fin m → ℝ) × (Fin k → ℝ)) ℝ 1,
            ∀ x ∈ V, (mextDerivₗ 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ)) 1 γ).val x =
              (σ (l, t)).val x := by
  -- The nondegeneracy margin.
  obtain ⟨r, hr, hnd'⟩ := hτ.exists_pos_forall_nondegenerate hK (isCompact_closedBall _ _) hnd
  -- Holonomic approximation near the core, then the compression of the cube.
  obtain ⟨ε₀, hε₀, hε₀₁, hslab, H, β', V, hHfst, hβ', hV, hHid, hKV, happrox⟩ :=
    exists_diffeotopy_norm_mextDerivₗ_sub_lt_near_core hk hK hτ hβ hW hAW hτβ hr
  obtain ⟨e, he, hediff, he0, heQ, heA, he1⟩ := exists_isotopy_mapsTo_of_diffeotopy hε₀
    (by linarith) H hHfst (fun t p hp ↦ (hHid t p hp).1) hK hV hKV
  -- On the slab next to the faces, `dβ' = dβ`, which is `τ` on `W`.
  have hS : IsOpen {x : (Fin m → ℝ) × (Fin k → ℝ) | 1 - ε₀ < ‖x.1‖} :=
    isOpen_lt continuous_const continuous_fst.norm
  have hdβ' (l : L) (x : (Fin m → ℝ) × (Fin k → ℝ)) (hx : 1 - ε₀ < ‖x.1‖) :
      (mextDerivₗ 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ)) 1 (β' l)).val x =
        (mextDerivₗ 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ)) 1 (β l)).val x := by
    rw [mextDerivₗ_apply, mextDerivₗ_apply]
    exact mextDeriv_congr_of_eventuallyEq
      (eventually_of_mem (hS.mem_nhds hx) fun y hy ↦ (hHid 0 (l, y) (Or.inl hy)).2)
  -- The shared homotopy, with `dβ' = τ` on the open set where `x ∈ W` and `1 - ε₀ / 2 < ‖u‖`.
  have hSε : IsOpen {x : (Fin m → ℝ) × (Fin k → ℝ) | 1 - ε₀ / 2 < ‖x.1‖} :=
    isOpen_lt continuous_const continuous_fst.norm
  refine exists_homotopy_exact_of_isotopy hτ hr hnd' hβ' he
    (fun p x ↦ by
      obtain ⟨φ, hφ⟩ := hediff p
      have := φ.isLocalDiffeomorph.isInvertible_mfderiv (by simp) x
      rwa [hφ] at this)
    he0 heQ (hW.inter hSε) (fun x hx ↦ ⟨hAW hx, ?_⟩) (fun p x hx ↦ heA p x hx.2)
    (fun l hl x hx ↦ ?_) (fun l hl x hx ↦ ?_)
  · rw [mem_ofPred_eq, mem_sphere_zero_iff_norm.1 hx.1]
    linarith
  · have hx₁ : 1 - ε₀ < ‖x.1‖ := by have := hx.2; simp only [mem_ofPred_eq] at this; linarith
    rw [hdβ' l x hx₁, hτβ l hl x hx.1]
  · set y := e ((l, 1), x)
    rcases he1 l hl hx with hyV | hyS
    · exact happrox (l, y) hyV hl
    · have hyS' : 1 - ε₀ < ‖y.1‖ := hyS
      rw [hdβ' l y hyS, hτβ l hl y (hslab y (heQ (l, 1) hx) (by linarith)), sub_self]
      exact (norm_zero (E := ((Fin m → ℝ) × (Fin k → ℝ)) [⋀^Fin 2]→L[ℝ] ℝ)).trans_lt hr

end SymplecticGeometry

end
